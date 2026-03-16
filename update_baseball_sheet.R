# ============================================================
# update_baseball_sheet.R
# Daily refresh of baseball statistics in Google Sheets
# ============================================================

suppressPackageStartupMessages({
  library(baseballr)
  library(dplyr)
  library(googlesheets4)
  library(lubridate)
  library(purrr)
  library(readr)
  library(tibble)
  library(rvest)
  library(xml2)
  library(stringr)
  library(janitor)
  library(tidyr)
})

# ============================================================
# AUTHENTICATION & CONFIGURATION
# ============================================================

gs4_auth(path = "gs4-auth.json")

ss_id <- Sys.getenv("SPREADSHEET_ID")
if (nchar(ss_id) == 0) stop("SPREADSHEET_ID environment variable not set.")

current_year  <- as.integer(format(Sys.Date(), "%Y"))
last_14_start <- format(Sys.Date() - 14, "%Y-%m-%d")
today_str     <- format(Sys.Date(), "%Y-%m-%d")

message("Baseball sheet refresh started | ", today_str)

# ============================================================
# HELPER FUNCTIONS
# ============================================================

# Normalize a metric to 0-100 percentile scale (100 = best).
# invert = TRUE for metrics where lower is better (FIP, BB%, K%).
normalize_metric <- function(x, invert = FALSE) {
  if (length(x) == 0) return(numeric(0))
  out   <- rep(NA_real_, length(x))
  valid <- !is.na(x) & is.finite(x)
  n     <- sum(valid)
  if (n < 2) {
    out[valid] <- 50
    return(out)
  }
  r          <- rank(x[valid], ties.method = "average")
  out[valid] <- (r - 1) / (n - 1) * 100
  if (invert) out <- 100 - out
  round(out, 1)
}

# Safely retrieve a numeric column from a data frame,
# returning a vector of `default` if the column is absent.
safe_col <- function(df, col, default = 0) {
  if (col %in% names(df)) {
    v <- suppressWarnings(as.numeric(df[[col]]))
    v[is.na(v)] <- as.numeric(default)
    return(v)
  }
  rep(as.numeric(default), nrow(df))
}

# Try the first named column that exists; fall back to `default`.
first_col <- function(df, cols, default = 0) {
  for (col in cols) {
    if (col %in% names(df)) {
      v <- suppressWarnings(as.numeric(df[[col]]))
      v[is.na(v)] <- as.numeric(default)
      return(v)
    }
  }
  rep(as.numeric(default), nrow(df))
}

# Clamp to [0, 100].
clamp100 <- function(x) pmin(100, pmax(0, replace(x, is.na(x), 0)))

# Volatility risk = normalized absolute gap between season and trend scores.
calc_volatility_risk <- function(s, t) normalize_metric(abs(s - t))

# Hitter risk: 30% PT risk, 25% volatility, 25% K-risk, 20% role
calculate_hitter_risk <- function(df, s, t) {
  pa    <- safe_col(df, "pa", 200)
  k_pct <- first_col(df, c("k_percent", "k_pct"), 20)
  pt_r  <- normalize_metric(-pa)
  vol_r <- coalesce(calc_volatility_risk(s, t), rep(20, nrow(df)))
  k_r   <- normalize_metric(k_pct)
  rol_r <- rep(20, nrow(df))
  round(clamp100(0.30 * pt_r + 0.25 * vol_r + 0.25 * k_r + 0.20 * rol_r), 1)
}

# SP risk: 30% role/workload, 25% command, 25% volatility, 20% stuff decline
calculate_sp_risk <- function(df, s, t) {
  ip    <- safe_col(df, "ip", 50)
  bb    <- first_col(df, c("bb_percent", "bb_pct"), 8)
  velo  <- first_col(df, c("fb_v", "fbv"), 92)
  rol_r <- normalize_metric(-ip)
  cmd_r <- normalize_metric(bb)
  vol_r <- coalesce(calc_volatility_risk(s, t), rep(20, nrow(df)))
  stf_r <- normalize_metric(-velo)
  round(clamp100(0.30 * rol_r + 0.25 * cmd_r + 0.25 * vol_r + 0.20 * stf_r), 1)
}

# RP risk: 35% role, 25% command, 20% usage volatility, 20% save context
calculate_rp_risk <- function(df, s, t) {
  sv    <- safe_col(df, "sv", 0)
  bb    <- first_col(df, c("bb_percent", "bb_pct"), 8)
  rol_r <- normalize_metric(-sv)
  cmd_r <- normalize_metric(bb)
  vol_r <- coalesce(calc_volatility_risk(s, t), rep(20, nrow(df)))
  sav_r <- normalize_metric(-sv)
  round(clamp100(0.35 * rol_r + 0.25 * cmd_r + 0.20 * vol_r + 0.20 * sav_r), 1)
}

# Prospect hitter risk: 30% K-risk, 25% age/level, 25% sample, 20% volatility
calculate_prospect_hitter_risk <- function(df, s, t) {
  pa    <- safe_col(df, "pa", 100)
  k_pct <- first_col(df, c("k_percent", "k_pct"), 25)
  age   <- safe_col(df, "age", 22)
  k_r   <- normalize_metric(k_pct)
  age_r <- normalize_metric(age)
  smp_r <- normalize_metric(-pa)
  vol_r <- coalesce(calc_volatility_risk(s, t), rep(20, nrow(df)))
  round(clamp100(0.30 * k_r + 0.25 * age_r + 0.25 * smp_r + 0.20 * vol_r), 1)
}

# Prospect pitcher risk: 30% command, 25% role, 20% age/level, 25% volatility
calculate_prospect_pitcher_risk <- function(df, s, t) {
  bb    <- first_col(df, c("bb_percent", "bb_pct"), 10)
  ip    <- safe_col(df, "ip", 40)
  age   <- safe_col(df, "age", 22)
  cmd_r <- normalize_metric(bb)
  rol_r <- normalize_metric(-ip)
  age_r <- normalize_metric(age)
  vol_r <- coalesce(calc_volatility_risk(s, t), rep(20, nrow(df)))
  round(clamp100(0.30 * cmd_r + 0.25 * rol_r + 0.20 * age_r + 0.25 * vol_r), 1)
}

# Upside score for prospects: young player at a high level = high upside.
calculate_upside_score <- function(df) {
  age   <- safe_col(df, "age", 22)
  level <- if ("Level" %in% names(df)) df$Level else rep("A+", nrow(df))
  lvl_num <- case_when(
    level %in% c("Rk", "ROK", "FCL", "DSL", "CPX") ~ 1L,
    level %in% c("A", "Lo-A", "Low-A")              ~ 2L,
    level %in% c("A+", "Hi-A", "High-A")            ~ 3L,
    level %in% c("AA", "Double-A")                  ~ 4L,
    level %in% c("AAA", "Triple-A")                 ~ 5L,
    TRUE                                             ~ 3L
  )
  age_base <- case_when(
    age <= 19 ~ 100, age == 20 ~ 90, age == 21 ~ 80,
    age == 22 ~  70, age == 23 ~ 55, age == 24 ~ 40,
    age >= 25 ~  25, TRUE ~ 50
  )
  round(clamp100(age_base - (5L - lvl_num) * 8L), 1)
}

# Generate Trend, Breakout, Regression flags and Why explanation.
generate_flags <- function(s, t, strong_count = 0) {
  diff <- t - s
  trend_flag <- case_when(
    diff >= 20  ~ "\U0001F525",   # 🔥
    diff >= 10  ~ "\U0001F4C8",   # 📈
    diff <= -20 ~ "\U00002744\U0000FE0F", # ❄️
    diff <= -10 ~ "\U0001F4C9",   # 📉
    TRUE        ~ ""
  )
  breakout_flag <- case_when(
    t >= 75 & diff >= 12 & strong_count >= 2 ~ "\U0001F525", # 🔥
    t >= 80 & s >= 45   & s <= 60            ~ "\U0001F440", # 👀
    TRUE ~ ""
  )
  regression_flag <- case_when(
    s >= 70 & diff <= -12 & strong_count == 0 ~ "\U0001F6D1", # 🛑
    TRUE ~ ""
  )
  why <- case_when(
    breakout_flag    == "\U0001F525" ~ "Trending sharply with multiple strong metrics",
    breakout_flag    == "\U0001F440" ~ "Breakout watch: elevated trend with emerging season score",
    regression_flag  == "\U0001F6D1" ~ "High season score with significant declining trend",
    trend_flag       == "\U0001F525" ~ "Hot streak: trend 20+ points above season average",
    trend_flag       == "\U0001F4C8" ~ "Positive momentum in recent games",
    trend_flag       == "\U00002744\U0000FE0F" ~ "Cold streak: significant recent decline",
    trend_flag       == "\U0001F4C9" ~ "Slight decline in recent performance",
    TRUE ~ "Stable performance"
  )
  list(Trend_Flag = trend_flag, Breakout_Flag = breakout_flag,
       Regression_Flag = regression_flag, Why = why)
}

# Final score formula selected by player type.
calc_final_score <- function(s, t, risk, upside = NULL, type = "fa") {
  u  <- if (is.null(upside)) rep(50, length(s)) else upside
  fs <- switch(type,
    fa       = 0.65 * s + 0.35 * t - 0.20 * risk,
    rostered = 0.75 * s + 0.25 * t - 0.15 * risk,
    prospect = 0.70 * s + 0.20 * t + 0.10 * u - 0.15 * risk,
    s
  )
  round(clamp100(fs), 1)
}

# Insert a percentile column immediately after its base column.
insert_after <- function(df, base_col, pct_col) {
  if (!pct_col %in% names(df) || !base_col %in% names(df)) return(df)
  rest <- setdiff(names(df), pct_col)
  pos  <- match(base_col, rest)
  if (is.na(pos)) return(df)
  new_order <- c(rest[seq_len(pos)], pct_col,
                 rest[seq(pos + 1L, length(rest))])
  df[, new_order, drop = FALSE]
}

# Safely write a data frame to a Google Sheet tab.
# Creates the tab if it does not already exist.
write_sheet_safe <- function(data, ss, sheet_name) {
  if (is.null(data) || nrow(data) == 0) {
    message("Skipping empty sheet: ", sheet_name)
    return(invisible(NULL))
  }
  tryCatch({
    existing <- tryCatch(sheet_names(ss), error = function(e) character(0))
    if (!sheet_name %in% existing) sheet_add(ss, sheet = sheet_name)
    range_write(ss, data = data, range = sheet_name,
                col_names = TRUE, reformat = FALSE)
    message("Written: ", sheet_name, " (", nrow(data), " rows)")
  }, error = function(e) {
    message("Error writing '", sheet_name, "': ", e$message)
  })
}

# ============================================================
# DATA FETCHING
# ============================================================

fetch_safely <- function(fn, label) {
  message("Fetching: ", label, " ...")
  result <- tryCatch(fn(), error = function(e) {
    message("  ERROR [", label, "]: ", e$message)
    tibble()
  })
  if (!is.null(result) && nrow(result) > 0)
    message("  OK: ", nrow(result), " rows")
  result
}

# ---- MLB Hitters ----
mlb_hit_season <- fetch_safely(
  function() fg_batter_leaders(
    x = current_year, y = current_year,
    league = "all", qual = 0, ind = 0) %>% clean_names(),
  "MLB hitters (season)")

mlb_hit_14 <- fetch_safely(
  function() fg_batter_leaders(
    x = current_year, y = current_year,
    league = "all", qual = 0, ind = 0,
    startdate = last_14_start, enddate = today_str) %>% clean_names(),
  "MLB hitters (last 14)")

# ---- MLB Pitchers ----
mlb_pit_season <- fetch_safely(
  function() fg_pitcher_leaders(
    x = current_year, y = current_year,
    league = "all", qual = 0, ind = 0) %>% clean_names(),
  "MLB pitchers (season)")

mlb_pit_14 <- fetch_safely(
  function() fg_pitcher_leaders(
    x = current_year, y = current_year,
    league = "all", qual = 0, ind = 0,
    startdate = last_14_start, enddate = today_str) %>% clean_names(),
  "MLB pitchers (last 14)")

# ---- MiLB Hitters (by level) ----
milb_levels <- c("AAA", "AA", "A+", "A", "Rk")

milb_hit_all <- map_dfr(milb_levels, function(lvl) {
  fetch_safely(
    function() fg_milb_batter_leaders(
      year = current_year, level = lvl, qual = 0) %>%
      clean_names() %>% mutate(Level = lvl),
    paste0("MiLB hitters ", lvl))
})

milb_hit_14_all <- map_dfr(milb_levels, function(lvl) {
  fetch_safely(
    function() fg_milb_batter_leaders(
      year = current_year, level = lvl, qual = 0,
      startdate = last_14_start, enddate = today_str) %>%
      clean_names() %>% mutate(Level = lvl),
    paste0("MiLB hitters ", lvl, " L14"))
})

# ---- MiLB Pitchers (by level) ----
milb_pit_all <- map_dfr(milb_levels, function(lvl) {
  fetch_safely(
    function() fg_milb_pitcher_leaders(
      year = current_year, level = lvl, qual = 0) %>%
      clean_names() %>% mutate(Level = lvl),
    paste0("MiLB pitchers ", lvl))
})

milb_pit_14_all <- map_dfr(milb_levels, function(lvl) {
  fetch_safely(
    function() fg_milb_pitcher_leaders(
      year = current_year, level = lvl, qual = 0,
      startdate = last_14_start, enddate = today_str) %>%
      clean_names() %>% mutate(Level = lvl),
    paste0("MiLB pitchers ", lvl, " L14"))
})

# ============================================================
# MILB LEVEL FIX
# Use the most recent level each player has appeared in.
# Strategy:
#   1. From last-14-day data, find the highest-priority level
#      each player appeared at (most recent promotion).
#   2. De-duplicate the season data keeping the highest-level
#      record per player.
#   3. Override the season level with the recent level.
# ============================================================

level_priority <- c(
  "AAA" = 5L, "Triple-A" = 5L,
  "AA"  = 4L, "Double-A" = 4L,
  "A+"  = 3L, "Hi-A" = 3L, "High-A" = 3L,
  "A"   = 2L, "Lo-A" = 2L, "Low-A" = 2L,
  "Rk"  = 1L, "ROK" = 1L, "FCL" = 1L, "DSL" = 1L, "CPX" = 1L
)

fix_milb_levels <- function(season_df, recent_df) {
  if (nrow(season_df) == 0) return(season_df)
  id_col <- if ("playerid" %in% names(season_df)) "playerid" else "player_id"
  if (!id_col %in% names(season_df)) return(season_df)

  # Most-recent level per player from last-14-day data
  # Use a named list to avoid non-standard evaluation in tibble()
  recent_levels <- as_tibble(setNames(
    list(character(0), character(0)),
    c(id_col, "Recent_Level")
  ))
  if (nrow(recent_df) > 0 && id_col %in% names(recent_df) && "Level" %in% names(recent_df)) {
    recent_levels <- recent_df %>%
      filter(!is.na(.data[[id_col]])) %>%
      mutate(lvl_num = coalesce(level_priority[Level], 0L)) %>%
      group_by(.data[[id_col]]) %>%
      arrange(desc(lvl_num), .by_group = TRUE) %>%
      slice_head(n = 1) %>%
      ungroup() %>%
      select(all_of(id_col), Recent_Level = Level)
  }

  # De-duplicate season data: one record per player at highest level
  season_dedup <- season_df %>%
    mutate(lvl_num = coalesce(as.integer(level_priority[Level]), 0L)) %>%
    group_by(.data[[id_col]]) %>%
    arrange(desc(lvl_num), .by_group = TRUE) %>%
    slice_head(n = 1) %>%
    ungroup() %>%
    select(-lvl_num)

  # Override with recent level where available
  if (nrow(recent_levels) > 0) {
    season_dedup <- season_dedup %>%
      left_join(recent_levels, by = id_col) %>%
      mutate(Level = coalesce(Recent_Level, Level)) %>%
      select(-Recent_Level)
  }
  season_dedup
}

milb_hit_season <- fix_milb_levels(milb_hit_all, milb_hit_14_all)
milb_pit_season <- fix_milb_levels(milb_pit_all, milb_pit_14_all)

# Deduplicated L14 data (one record per player at highest recent level)
dedup_l14 <- function(df) {
  if (nrow(df) == 0) return(df)
  id_col <- if ("playerid" %in% names(df)) "playerid" else "player_id"
  if (!id_col %in% names(df) || !"Level" %in% names(df)) return(df)
  df %>%
    mutate(lvl_num = coalesce(as.integer(level_priority[Level]), 0L)) %>%
    group_by(.data[[id_col]]) %>%
    arrange(desc(lvl_num), .by_group = TRUE) %>%
    slice_head(n = 1) %>%
    ungroup() %>%
    select(-lvl_num)
}

milb_hit_14 <- dedup_l14(milb_hit_14_all)
milb_pit_14 <- dedup_l14(milb_pit_14_all)

# ============================================================
# PART 1 — RAW DATA SHEETS WITH PERCENTILE RANKINGS
# ============================================================

# ---- raw_hitters ----
message("Building raw_hitters ...")
raw_hitters <- if (nrow(mlb_hit_season) > 0) {
  df <- mlb_hit_season %>%
    mutate(
      ISO      = coalesce(
                   suppressWarnings(as.numeric(iso)),
                   suppressWarnings(as.numeric(slg)) -
                     suppressWarnings(as.numeric(avg))),
      BB_pct   = first_col(., c("bb_percent", "bb_pct"), NA_real_),
      K_pct    = first_col(., c("k_percent",  "k_pct"),  NA_real_),
      wOBA     = first_col(., c("w_oba",  "woba"),       NA_real_),
      wRC_plus = first_col(., c("w_rc_plus", "wrc_plus"), NA_real_)
    ) %>%
    mutate(
      ISO_Percentile      = normalize_metric(ISO),
      BB_Pct_Percentile   = normalize_metric(BB_pct),
      K_Pct_Percentile    = normalize_metric(K_pct,    invert = TRUE),
      wOBA_Percentile     = normalize_metric(wOBA),
      wRC_Plus_Percentile = normalize_metric(wRC_plus)
    )
  df <- insert_after(df, "ISO",      "ISO_Percentile")
  df <- insert_after(df, "BB_pct",   "BB_Pct_Percentile")
  df <- insert_after(df, "K_pct",    "K_Pct_Percentile")
  df <- insert_after(df, "wOBA",     "wOBA_Percentile")
  df <- insert_after(df, "wRC_plus", "wRC_Plus_Percentile")
  df
} else tibble()

# ---- raw_pitchers ----
message("Building raw_pitchers ...")
raw_pitchers <- if (nrow(mlb_pit_season) > 0) {
  df <- mlb_pit_season %>%
    mutate(
      FIP    = suppressWarnings(as.numeric(first_col(., c("fip"), NA_real_))),
      K_pct  = first_col(., c("k_percent", "k_pct"), NA_real_),
      BB_pct = first_col(., c("bb_percent", "bb_pct"), NA_real_),
      velo   = first_col(., c("fb_v", "fbv", "fb_v_1"), NA_real_)
    ) %>%
    mutate(
      FIP_Percentile    = normalize_metric(FIP,    invert = TRUE),
      K_Pct_Percentile  = normalize_metric(K_pct),
      BB_Pct_Percentile = normalize_metric(BB_pct, invert = TRUE),
      Velo_Percentile   = normalize_metric(velo)
    )
  df <- insert_after(df, "FIP",    "FIP_Percentile")
  df <- insert_after(df, "K_pct",  "K_Pct_Percentile")
  df <- insert_after(df, "BB_pct", "BB_Pct_Percentile")
  df <- insert_after(df, "velo",   "Velo_Percentile")
  df
} else tibble()

# ---- raw_milb_hitters ----
message("Building raw_milb_hitters ...")
raw_milb_hitters <- if (nrow(milb_hit_season) > 0) {
  milb_hit_season %>%
    mutate(
      ISO      = coalesce(
                   suppressWarnings(as.numeric(iso)),
                   suppressWarnings(as.numeric(slg)) -
                     suppressWarnings(as.numeric(avg))),
      BB_pct   = first_col(., c("bb_percent", "bb_pct"), NA_real_),
      K_pct    = first_col(., c("k_percent",  "k_pct"),  NA_real_),
      wOBA     = first_col(., c("w_oba",  "woba"),       NA_real_),
      wRC_plus = first_col(., c("w_rc_plus", "wrc_plus"), NA_real_)
    ) %>%
    group_by(Level) %>%
    mutate(
      ISO_Percentile_ByLevel      = normalize_metric(ISO),
      BB_Pct_Percentile_ByLevel   = normalize_metric(BB_pct),
      K_Pct_Percentile_ByLevel    = normalize_metric(K_pct,    invert = TRUE),
      wOBA_Percentile_ByLevel     = normalize_metric(wOBA),
      wRC_Plus_Percentile_ByLevel = normalize_metric(wRC_plus)
    ) %>%
    ungroup()
} else tibble()

# ---- raw_milb_pitchers ----
message("Building raw_milb_pitchers ...")
raw_milb_pitchers <- if (nrow(milb_pit_season) > 0) {
  milb_pit_season %>%
    mutate(
      FIP    = first_col(., c("fip"), NA_real_),
      K_pct  = first_col(., c("k_percent", "k_pct"), NA_real_),
      BB_pct = first_col(., c("bb_percent", "bb_pct"), NA_real_),
      velo   = first_col(., c("fb_v", "fbv", "fb_v_1"), NA_real_)
    ) %>%
    group_by(Level) %>%
    mutate(
      FIP_Percentile_ByLevel    = normalize_metric(FIP,    invert = TRUE),
      K_Pct_Percentile_ByLevel  = normalize_metric(K_pct),
      BB_Pct_Percentile_ByLevel = normalize_metric(BB_pct, invert = TRUE),
      Velo_Percentile_ByLevel   = normalize_metric(velo)
    ) %>%
    ungroup()
} else tibble()

# ============================================================
# READ FREE AGENT AND ROSTERED PLAYER LISTS
# ============================================================

message("Reading Free Agent Helper tab ...")
fa_list <- tryCatch({
  raw <- range_read(ss_id, sheet = "Free Agent Helper", col_names = FALSE)
  if (ncol(raw) >= 4) {
    raw[, c(2, 3, 4)] %>%
      setNames(c("MLBID", "FanGraphs_ID", "Name")) %>%
      mutate(across(everything(), as.character)) %>%
      filter(!is.na(Name), !Name %in% c("", "Name", "Player"))
  } else {
    tibble(MLBID = character(), FanGraphs_ID = character(), Name = character())
  }
}, error = function(e) {
  message("Error reading Free Agent Helper tab: ", e$message)
  tibble(MLBID = character(), FanGraphs_ID = character(), Name = character())
})
message("Free agents: ", nrow(fa_list))

message("Reading Test tab (rostered) ...")
test_list <- tryCatch({
  raw <- range_read(ss_id, sheet = "Test", col_names = FALSE)
  ncols <- ncol(raw)
  result <- tibble(Name = character(), MLBID = character(), FanGraphs_ID = character())
  if (ncols >= 2) result$Name         <- as.character(raw[[2]])
  if (ncols >= 4) result$MLBID        <- as.character(raw[[4]])
  if (ncols >= 6) result$FanGraphs_ID <- as.character(raw[[6]])
  result %>%
    mutate(across(everything(), as.character)) %>%
    filter(!is.na(Name), !Name %in% c("", "Name", "Player"))
}, error = function(e) {
  message("Error reading Test tab: ", e$message)
  tibble(Name = character(), MLBID = character(), FanGraphs_ID = character())
})
message("Rostered players: ", nrow(test_list))

# ============================================================
# PART 2 — SCORING HELPERS
# ============================================================

# Identify the player-ID column name in a stats data frame.
id_col_of <- function(df) {
  for (col in c("playerid", "player_id")) {
    if (col %in% names(df)) return(col)
  }
  NULL
}

# Identify the player-name column name in a stats data frame.
name_col_of <- function(df) {
  for (col in c("name", "player_name", "Name")) {
    if (col %in% names(df)) return(col)
  }
  NULL
}

# Match players from `player_list` against a stats data frame.
# Matches first by FanGraphs ID, then falls back to player name.
match_players <- function(stats_df, player_list) {
  if (nrow(stats_df) == 0 || nrow(player_list) == 0) return(stats_df[0, ])
  id_col  <- id_col_of(stats_df)
  nm_col  <- name_col_of(stats_df)

  fg_ids <- na.omit(as.character(player_list$FanGraphs_ID))
  fg_ids <- fg_ids[nchar(fg_ids) > 0]

  names_list <- na.omit(as.character(player_list$Name))
  names_list <- names_list[nchar(names_list) > 0]

  id_rows   <- if (!is.null(id_col) && length(fg_ids) > 0)
    stats_df %>% filter(as.character(.data[[id_col]]) %in% fg_ids)
  else stats_df[0, ]

  already_found <- if (!is.null(id_col) && nrow(id_rows) > 0)
    as.character(id_rows[[id_col]])
  else character(0)

  name_rows <- if (!is.null(nm_col) && length(names_list) > 0) {
    stats_df %>%
      filter(
        tolower(.data[[nm_col]]) %in% tolower(names_list),
        if (!is.null(id_col)) !as.character(.data[[id_col]]) %in% already_found
        else TRUE
      )
  } else stats_df[0, ]

  bind_rows(id_rows, name_rows)
}

# Align last-14-day component scores to the ordering in the season subset.
# Returns a vector the same length as season_subset.
align_l14 <- function(season_df, l14_df, l14_scores) {
  id_col <- id_col_of(season_df)
  if (is.null(id_col) || is.null(l14_df) || nrow(l14_df) == 0 ||
      !id_col %in% names(l14_df)) {
    return(rep(NA_real_, nrow(season_df)))
  }
  idx <- match(as.character(season_df[[id_col]]),
               as.character(l14_df[[id_col]]))
  l14_scores[idx]
}

# Build a compact output data frame for any player type.
make_output <- function(df, season_score, trend_score, risk_score,
                        final_score, flags, upside_score = NULL) {
  id_col <- id_col_of(df)
  nm_col <- name_col_of(df)
  tm_col <- if ("team"      %in% names(df)) "team"      else
            if ("team_name" %in% names(df)) "team_name" else NULL

  keep <- unique(na.omit(c(
    nm_col, tm_col, id_col,
    intersect(c("pa", "hr", "r", "rbi", "sb", "avg", "obp", "slg",
                "iso", "bb_percent", "k_percent", "w_oba", "w_rc_plus",
                "ip", "era", "fip", "x_fip", "siera",
                "fb_v", "sv", "hld",
                "age", "Level"), names(df))
  )))

  out <- df %>% select(all_of(keep))
  if (!is.null(upside_score)) out$Upside_Score <- upside_score
  out %>%
    mutate(
      Season_Score    = season_score,
      Trend_Score     = trend_score,
      Risk_Score      = risk_score,
      Final_Score     = final_score,
      Trend_Flag      = flags$Trend_Flag,
      Breakout_Flag   = flags$Breakout_Flag,
      Regression_Flag = flags$Regression_Flag,
      Why             = flags$Why
    ) %>%
    arrange(desc(Final_Score))
}

# ---- Score MLB Hitters ----
score_mlb_hitters <- function(season_df, l14_df, player_list, score_type) {
  if (nrow(season_df) == 0 || nrow(player_list) == 0) return(tibble())
  matched <- match_players(season_df, player_list)
  {
    .pa_v <- safe_col(matched, "pa", 0)
    matched <- matched[.pa_v >= 3, , drop = FALSE]
  }
  if (nrow(matched) == 0) return(tibble())

  l14m <- if (!is.null(l14_df) && nrow(l14_df) > 0) {
    id_col <- id_col_of(matched)
    if (!is.null(id_col)) {
      l14_df %>%
        filter(as.character(.data[[id_col]]) %in%
                 as.character(matched[[id_col]]))
    } else tibble()
  } else tibble()

  # Season score
  xwoba_s    <- normalize_metric(first_col(matched, c("xw_oba","x_w_oba","xwoba","w_oba"), 0.320))
  barrel_s   <- normalize_metric(first_col(matched, c("barrel_percent","barrel","brls_pa_percent"), 0))
  hardhit_s  <- normalize_metric(first_col(matched, c("hard_hit_percent","hard_hit","hard_hit_rate"), 0))
  bb_k_s     <- normalize_metric(
    first_col(matched, c("bb_percent","bb_pct"), 8) -
    first_col(matched, c("k_percent","k_pct"),  22))
  speed_s    <- normalize_metric(first_col(matched, c("sprint_speed","spd"), 27))

  l14_woba_all <- if (nrow(l14m) > 0)
    normalize_metric(first_col(l14m, c("w_oba","woba"), 0.320))
  else rep(50, nrow(l14m))
  l14_woba_s <- align_l14(matched, l14m, l14_woba_all)
  l14_woba_s[is.na(l14_woba_s)] <- 50

  season_score <- round(clamp100(
    0.25 * xwoba_s + 0.20 * barrel_s + 0.15 * hardhit_s +
    0.15 * bb_k_s  + 0.10 * speed_s  + 0.15 * l14_woba_s), 1)

  # Trend score (L14)
  trend_score <- if (nrow(l14m) > 0) {
    xwoba_t   <- normalize_metric(first_col(l14m, c("xw_oba","x_w_oba","xwoba","w_oba"), 0.320))
    barrel_t  <- normalize_metric(first_col(l14m, c("barrel_percent","barrel"), 0))
    hardhit_t <- normalize_metric(first_col(l14m, c("hard_hit_percent","hard_hit"), 0))
    bb_k_t    <- normalize_metric(
      first_col(l14m, c("bb_percent","bb_pct"), 8) -
      first_col(l14m, c("k_percent","k_pct"), 22))
    speed_t   <- normalize_metric(first_col(l14m, c("sprint_speed","spd"), 27))
    t_raw <- round(clamp100(
      0.25 * xwoba_t + 0.20 * barrel_t + 0.15 * hardhit_t +
      0.15 * bb_k_t  + 0.10 * speed_t  + 0.15 * 50), 1)
    aligned <- align_l14(matched, l14m, t_raw)
    aligned[is.na(aligned)] <- season_score[is.na(aligned)]
    round(aligned, 1)
  } else season_score

  risk  <- calculate_hitter_risk(matched, season_score, trend_score)
  final <- calc_final_score(season_score, trend_score, risk, type = score_type)

  strong <- as.integer(xwoba_s > 60) + as.integer(barrel_s > 60) + as.integer(hardhit_s > 60)
  flags  <- generate_flags(season_score, trend_score, strong)

  make_output(matched, season_score, trend_score, risk, final, flags)
}

# ---- Score MLB Starters ----
score_mlb_pitchers <- function(season_df, l14_df, player_list, score_type,
                                role = "SP") {
  if (nrow(season_df) == 0 || nrow(player_list) == 0) return(tibble())
  matched <- match_players(season_df, player_list)
  if (nrow(matched) == 0) return(tibble())

  # Role filter — pre-compute values outside dplyr data-mask to avoid ambiguity
  {
    .ip_v  <- safe_col(matched, "ip", 0)
    .g_v   <- pmax(safe_col(matched, "g", 1), 1)
    .gs_v  <- safe_col(matched, "gs", 0)
    .ratio <- .gs_v / .g_v
    if (role == "SP") {
      matched <- matched[.ip_v >= 1 & .ratio >= 0.4, , drop = FALSE]
    } else {
      matched <- matched[.ip_v >= 1 & .ratio <  0.4, , drop = FALSE]
    }
  }
  if (nrow(matched) == 0) return(tibble())

  l14m <- if (!is.null(l14_df) && nrow(l14_df) > 0) {
    id_col <- id_col_of(matched)
    if (!is.null(id_col))
      l14_df %>% filter(as.character(.data[[id_col]]) %in% as.character(matched[[id_col]]))
    else tibble()
  } else tibble()

  if (role == "SP") {
    # Season score: 25% K-BB%, 20% CSW%, 20% Velo, 15% xFIP/SIERA, 10% Role, 10% L14
    k_bb_s  <- normalize_metric(
      first_col(matched, c("k_percent","k_pct"), 20) -
      first_col(matched, c("bb_percent","bb_pct"), 8))
    csw_s   <- normalize_metric(first_col(matched, c("csw_percent","csw"), 28))
    velo_s  <- normalize_metric(first_col(matched, c("fb_v","fbv"), 92))
    xfip_s  <- normalize_metric(first_col(matched, c("x_fip","xfip","siera","fip"), 4.0), invert = TRUE)
    role_s  <- normalize_metric(safe_col(matched, "ip", 50))
    l14_ip  <- if (nrow(l14m) > 0) {
      r <- normalize_metric(safe_col(l14m, "ip", 0))
      align_l14(matched, l14m, r)
    } else rep(50, nrow(matched))
    l14_ip[is.na(l14_ip)] <- 50

    season_score <- round(clamp100(
      0.25 * k_bb_s + 0.20 * csw_s + 0.20 * velo_s +
      0.15 * xfip_s + 0.10 * role_s + 0.10 * l14_ip), 1)

    trend_score <- if (nrow(l14m) > 0) {
      kb_t  <- normalize_metric(
        first_col(l14m, c("k_percent","k_pct"), 20) -
        first_col(l14m, c("bb_percent","bb_pct"), 8))
      csw_t <- normalize_metric(first_col(l14m, c("csw_percent","csw"), 28))
      vel_t <- normalize_metric(first_col(l14m, c("fb_v","fbv"), 92))
      xf_t  <- normalize_metric(first_col(l14m, c("x_fip","xfip","siera","fip"), 4.0), invert = TRUE)
      rol_t <- normalize_metric(safe_col(l14m, "ip", 0))
      t_raw <- round(clamp100(
        0.25 * kb_t + 0.20 * csw_t + 0.20 * vel_t + 0.15 * xf_t + 0.20 * rol_t), 1)
      al    <- align_l14(matched, l14m, t_raw)
      al[is.na(al)] <- season_score[is.na(al)]
      round(al, 1)
    } else season_score

    risk  <- calculate_sp_risk(matched, season_score, trend_score)
    final <- calc_final_score(season_score, trend_score, risk, type = score_type)
    strong <- as.integer(k_bb_s > 60) + as.integer(csw_s > 60) + as.integer(velo_s > 60)
    flags <- generate_flags(season_score, trend_score, strong)

  } else {
    # RP: 30% Dominance (K-BB+CSW+SwStr), 20% Role (SV/HLD), 20% Stuff, 15% xFIP, 15% L14
    dom_s  <- normalize_metric(
      first_col(matched, c("k_percent","k_pct"), 20) -
      first_col(matched, c("bb_percent","bb_pct"), 8) +
      first_col(matched, c("csw_percent","csw"), 28) +
      first_col(matched, c("sw_str_percent","swstr_percent","swstr"), 10))
    role_s <- normalize_metric(
      safe_col(matched, "sv", 0) + safe_col(matched, "hld", 0))
    velo_s <- normalize_metric(first_col(matched, c("fb_v","fbv"), 93))
    xfip_s <- normalize_metric(first_col(matched, c("x_fip","xfip","siera","fip"), 3.8), invert = TRUE)
    l14_k  <- if (nrow(l14m) > 0) {
      r <- normalize_metric(first_col(l14m, c("k_percent","k_pct"), 20))
      align_l14(matched, l14m, r)
    } else rep(50, nrow(matched))
    l14_k[is.na(l14_k)] <- 50

    season_score <- round(clamp100(
      0.30 * dom_s + 0.20 * role_s + 0.20 * velo_s +
      0.15 * xfip_s + 0.15 * l14_k), 1)

    trend_score <- if (nrow(l14m) > 0) {
      d_t  <- normalize_metric(
        first_col(l14m, c("k_percent","k_pct"), 20) -
        first_col(l14m, c("bb_percent","bb_pct"), 8) +
        first_col(l14m, c("csw_percent","csw"), 28))
      r_t  <- normalize_metric(
        safe_col(l14m, "sv", 0) + safe_col(l14m, "hld", 0))
      v_t  <- normalize_metric(first_col(l14m, c("fb_v","fbv"), 93))
      xf_t <- normalize_metric(first_col(l14m, c("x_fip","xfip","fip"), 3.8), invert = TRUE)
      t_raw <- round(clamp100(0.30 * d_t + 0.20 * r_t + 0.20 * v_t + 0.15 * xf_t + 0.15 * 50), 1)
      al    <- align_l14(matched, l14m, t_raw)
      al[is.na(al)] <- season_score[is.na(al)]
      round(al, 1)
    } else season_score

    risk  <- calculate_rp_risk(matched, season_score, trend_score)
    final <- calc_final_score(season_score, trend_score, risk, type = score_type)
    strong <- as.integer(dom_s > 60) + as.integer(velo_s > 60)
    flags <- generate_flags(season_score, trend_score, strong)
  }

  make_output(matched, season_score, trend_score, risk, final, flags)
}

# ---- Score Prospect Hitters ----
score_prospect_hitters <- function(season_df, l14_df, player_list, score_type) {
  if (nrow(season_df) == 0 || nrow(player_list) == 0) return(tibble())
  matched <- match_players(season_df, player_list)
  if (nrow(matched) == 0) return(tibble())

  l14m <- if (!is.null(l14_df) && nrow(l14_df) > 0) {
    id_col <- id_col_of(matched)
    if (!is.null(id_col))
      l14_df %>% filter(as.character(.data[[id_col]]) %in% as.character(matched[[id_col]]))
    else tibble()
  } else tibble()

  # Season score: 25% wRC+, 25% Age vs Level, 20% BB-K%, 20% ISO, 10% L14
  wrc_s  <- normalize_metric(first_col(matched, c("w_rc_plus","wrc_plus"), 100))
  age_s  <- calculate_upside_score(matched)
  bb_k_s <- normalize_metric(
    first_col(matched, c("bb_percent","bb_pct"), 8) -
    first_col(matched, c("k_percent","k_pct"), 25))
  iso_s  <- normalize_metric(coalesce(
    suppressWarnings(as.numeric(if ("iso" %in% names(matched)) matched$iso else NA_real_)),
    suppressWarnings(as.numeric(if ("slg" %in% names(matched)) matched$slg else NA_real_)) -
    suppressWarnings(as.numeric(if ("avg" %in% names(matched)) matched$avg else NA_real_))))
  iso_s[is.na(iso_s)] <- 50
  l14_wrc <- if (nrow(l14m) > 0) {
    r <- normalize_metric(first_col(l14m, c("w_rc_plus","wrc_plus"), 100))
    al <- align_l14(matched, l14m, r)
    al[is.na(al)] <- 50; al
  } else rep(50, nrow(matched))

  season_score <- round(clamp100(
    0.25 * wrc_s + 0.25 * age_s + 0.20 * bb_k_s +
    0.20 * iso_s + 0.10 * l14_wrc), 1)

  trend_score <- if (nrow(l14m) > 0) {
    w_t  <- normalize_metric(first_col(l14m, c("w_rc_plus","wrc_plus"), 100))
    bk_t <- normalize_metric(
      first_col(l14m, c("bb_percent","bb_pct"), 8) -
      first_col(l14m, c("k_percent","k_pct"), 25))
    iso_t <- normalize_metric(coalesce(
      suppressWarnings(as.numeric(if ("iso" %in% names(l14m)) l14m$iso else NA_real_)),
      suppressWarnings(as.numeric(if ("slg" %in% names(l14m)) l14m$slg else NA_real_)) -
      suppressWarnings(as.numeric(if ("avg" %in% names(l14m)) l14m$avg else NA_real_))))
    iso_t[is.na(iso_t)] <- 50
    t_raw <- round(clamp100(0.30 * w_t + 0.25 * bk_t + 0.25 * iso_t + 0.20 * 50), 1)
    al    <- align_l14(matched, l14m, t_raw)
    al[is.na(al)] <- season_score[is.na(al)]
    round(al, 1)
  } else season_score

  upside <- calculate_upside_score(matched)
  risk   <- calculate_prospect_hitter_risk(matched, season_score, trend_score)
  final  <- calc_final_score(season_score, trend_score, risk, upside, type = "prospect")

  strong <- as.integer(wrc_s > 60) + as.integer(bb_k_s > 60) + as.integer(iso_s > 60)
  flags  <- generate_flags(season_score, trend_score, strong)

  make_output(matched, season_score, trend_score, risk, final, flags, upside)
}

# ---- Score Prospect Pitchers ----
score_prospect_pitchers <- function(season_df, l14_df, player_list, score_type) {
  if (nrow(season_df) == 0 || nrow(player_list) == 0) return(tibble())
  matched <- match_players(season_df, player_list)
  if (nrow(matched) == 0) return(tibble())

  l14m <- if (!is.null(l14_df) && nrow(l14_df) > 0) {
    id_col <- id_col_of(matched)
    if (!is.null(id_col))
      l14_df %>% filter(as.character(.data[[id_col]]) %in% as.character(matched[[id_col]]))
    else tibble()
  } else tibble()

  age_s  <- calculate_upside_score(matched)
  k_bb_s <- normalize_metric(
    first_col(matched, c("k_percent","k_pct"), 20) -
    first_col(matched, c("bb_percent","bb_pct"), 10))
  bb_s   <- normalize_metric(first_col(matched, c("bb_percent","bb_pct"), 10), invert = TRUE)
  ip_s   <- normalize_metric(safe_col(matched, "ip", 0))

  l14_k <- if (nrow(l14m) > 0) {
    r <- normalize_metric(first_col(l14m, c("k_percent","k_pct"), 20))
    al <- align_l14(matched, l14m, r)
    al[is.na(al)] <- 50; al
  } else rep(50, nrow(matched))

  season_score <- round(clamp100(
    0.30 * k_bb_s + 0.25 * age_s + 0.15 * bb_s +
    0.15 * ip_s   + 0.15 * l14_k), 1)

  trend_score <- if (nrow(l14m) > 0) {
    kb_t <- normalize_metric(
      first_col(l14m, c("k_percent","k_pct"), 20) -
      first_col(l14m, c("bb_percent","bb_pct"), 10))
    bb_t <- normalize_metric(first_col(l14m, c("bb_percent","bb_pct"), 10), invert = TRUE)
    ip_t <- normalize_metric(safe_col(l14m, "ip", 0))
    t_raw <- round(clamp100(0.35 * kb_t + 0.25 * bb_t + 0.25 * ip_t + 0.15 * 50), 1)
    al    <- align_l14(matched, l14m, t_raw)
    al[is.na(al)] <- season_score[is.na(al)]
    round(al, 1)
  } else season_score

  upside <- calculate_upside_score(matched)
  risk   <- calculate_prospect_pitcher_risk(matched, season_score, trend_score)
  final  <- calc_final_score(season_score, trend_score, risk, upside, type = "prospect")

  strong <- as.integer(k_bb_s > 60) + as.integer(bb_s > 60) + as.integer(ip_s > 60)
  flags  <- generate_flags(season_score, trend_score, strong)

  make_output(matched, season_score, trend_score, risk, final, flags, upside)
}

# ============================================================
# PART 2 — FREE AGENT SCORING SHEETS
# ============================================================

message("Scoring free agent hitters ...")
fa_hitters <- score_mlb_hitters(mlb_hit_season, mlb_hit_14, fa_list, "fa")

message("Scoring free agent starters ...")
fa_pitchers <- score_mlb_pitchers(mlb_pit_season, mlb_pit_14, fa_list, "fa", role = "SP")

message("Scoring free agent relievers ...")
fa_relievers <- score_mlb_pitchers(mlb_pit_season, mlb_pit_14, fa_list, "fa", role = "RP")

message("Scoring free agent prospect hitters ...")
fa_prospect_hitters <- score_prospect_hitters(milb_hit_season, milb_hit_14, fa_list, "prospect")

message("Scoring free agent prospect pitchers ...")
fa_prospect_pitchers <- score_prospect_pitchers(milb_pit_season, milb_pit_14, fa_list, "prospect")

# ============================================================
# PART 2 — ROSTERED PLAYER SCORING SHEETS
# ============================================================

message("Scoring rostered hitters ...")
rostered_hitters <- score_mlb_hitters(mlb_hit_season, mlb_hit_14, test_list, "rostered")

message("Scoring rostered starters ...")
rostered_pitchers <- score_mlb_pitchers(mlb_pit_season, mlb_pit_14, test_list, "rostered", role = "SP")

message("Scoring rostered relievers ...")
rostered_relievers <- score_mlb_pitchers(mlb_pit_season, mlb_pit_14, test_list, "rostered", role = "RP")

message("Scoring rostered prospect hitters ...")
rostered_prospect_hitters <- score_prospect_hitters(milb_hit_season, milb_hit_14, test_list, "prospect")

message("Scoring rostered prospect pitchers ...")
rostered_prospect_pitchers <- score_prospect_pitchers(milb_pit_season, milb_pit_14, test_list, "prospect")

# ============================================================
# WRITE ALL SHEETS TO GOOGLE SHEETS
# ============================================================

message("Writing sheets to Google Sheets ...")

# -- Raw data sheets (4) --
write_sheet_safe(raw_hitters,       ss_id, "raw_hitters")
write_sheet_safe(raw_pitchers,      ss_id, "raw_pitchers")
write_sheet_safe(raw_milb_hitters,  ss_id, "raw_milb_hitters")
write_sheet_safe(raw_milb_pitchers, ss_id, "raw_milb_pitchers")

# -- Free agent scoring sheets (5) --
write_sheet_safe(fa_hitters,           ss_id, "fa_hitters")
write_sheet_safe(fa_pitchers,          ss_id, "fa_pitchers")
write_sheet_safe(fa_relievers,         ss_id, "fa_relievers")
write_sheet_safe(fa_prospect_hitters,  ss_id, "fa_prospect_hitters")
write_sheet_safe(fa_prospect_pitchers, ss_id, "fa_prospect_pitchers")

# -- Rostered player scoring sheets (5) --
write_sheet_safe(rostered_hitters,           ss_id, "rostered_hitters")
write_sheet_safe(rostered_pitchers,          ss_id, "rostered_pitchers")
write_sheet_safe(rostered_relievers,         ss_id, "rostered_relievers")
write_sheet_safe(rostered_prospect_hitters,  ss_id, "rostered_prospect_hitters")
write_sheet_safe(rostered_prospect_pitchers, ss_id, "rostered_prospect_pitchers")

message("Baseball sheet refresh complete: ", Sys.time())
