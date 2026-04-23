suppressPackageStartupMessages({
  library(baseballr)
  library(googlesheets4)
  library(gargle)
  library(dplyr)
  library(rlang)
  library(purrr)
  library(tidyr)
  library(stringr)
  library(lubridate)
  library(janitor)
  library(readr)
  library(tibble)
  library(glue)
  library(jsonlite)
  library(httr)
})

# Set a browser-like User-Agent so FanGraphs doesn't reject requests from GH Actions
set_config(user_agent("Mozilla/5.0 (X11; Linux x86_64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/131.0.0.0 Safari/537.36"))

`%||%` <- function(x, y) if (is.null(x) || length(x) == 0 || all(is.na(x))) y else x

# Convert baseball IP notation to true decimal.
# In baseball, the fractional part represents thirds of an inning:
#   "182.1" -> 182 + 1/3,  "182.2" -> 182 + 2/3,  "182.0" -> 182.0
parse_ip <- function(x) {
  x <- as.numeric(x)
  whole <- trunc(x)
  thirds <- round((x - whole) * 10)
  whole + thirds / 3
}

# ============================================================
# SCORING CONFIGURATION
# Adjust weights below to change how players are scored.
# Each group of weights should sum to 1.0.
# ============================================================

WEIGHTS <- list(

  # MLB Hitters: current_score
  mlb_h_current = c(
    xwoba = 0.14, barrel_pct = 0.14, hard_hit_pct = 0.14,
    bb_minus_k_pct = 0.14, sb = 0.14,
    hr = 0.06, ops = 0.06, iso = 0.06, xba = 0.06, exit_velocity = 0.06
  ),
  # MLB Hitters: trend_score (last 14 days emphasis)
  mlb_h_trend = c(
    xwoba = 0.20, barrel_pct = 0.20, hard_hit_pct = 0.15,
    bb_minus_k_pct = 0.15, sb = 0.10,
    hr = 0.05, iso = 0.05, exit_velocity = 0.05, ops = 0.05
  ),

  # MLB Pitchers: current_score
  mlb_p_current = c(
    k_minus_bb_pct = 0.14, siera = 0.14, xfip = 0.14,
    swstr_pct = 0.14, velocity = 0.14,
    era = 0.06, whip = 0.06, saves_holds = 0.06,
    hard_hit_pct_against = 0.06, hr_against = 0.06
  ),
  # MLB Pitchers: trend_score
  mlb_p_trend = c(
    k_minus_bb_pct = 0.20, swstr_pct = 0.20, velocity = 0.15,
    xfip = 0.15, siera = 0.10,
    era = 0.05, whip = 0.05, saves_holds = 0.05,
    hard_hit_pct_against = 0.05
  ),

  # MiLB Hitters: current_score
  milb_h_current = c(
    wrc_plus = 0.14, bb_minus_k_pct = 0.14, iso = 0.14,
    age_vs_level = 0.14, obp = 0.14,
    avg = 0.06, hr = 0.06, steals = 0.06, woba = 0.06, pa = 0.06
  ),
  # MiLB Hitters: trend_score
  milb_h_trend = c(
    wrc_plus = 0.20, iso = 0.20, bb_minus_k_pct = 0.20,
    obp = 0.10, age_vs_level = 0.10,
    hr = 0.05, steals = 0.05, avg = 0.05, pa = 0.05
  ),

  # MiLB Pitchers: current_score
  milb_p_current = c(
    k_minus_bb_pct = 0.14, fip = 0.14, xfip = 0.14,
    siera = 0.14, velocity = 0.14,
    whip = 0.06, earned_runs = 0.06, hr = 0.06,
    holds_plus_saves = 0.06, placeholder = 0.06
  ),
  # MiLB Pitchers: trend_score
  milb_p_trend = c(
    k_minus_bb_pct = 0.20, xfip = 0.20, siera = 0.20,
    velocity = 0.10, fip = 0.10,
    whip = 0.05, earned_runs = 0.05, hr = 0.05, placeholder = 0.05
  )
)

# Dynasty WAR calculation parameters
WAR_PARAMS <- list(
  current_war_score_div  = 12,
  current_war_risk_div   = 150,
  dynasty_score_div      = 10,
  dynasty_risk_div       = 100,
  future_score_div       = 14,
  future_risk_div        = 175,
  prospect_bonus         = 0.75,
  mlb_prospect_bonus     = 0.15,
  future_bonus_prospect  = 1.20,
  future_bonus_mlb       = 0.30,
  extra_prospect_bump    = 0.35,
  future_war_multiplier  = 1.5,
  trade_value_multiplier = 10
)

# ============================================================

sheet_id <- Sys.getenv("GOOGLE_SHEET_ID")
svc_file <- Sys.getenv("GOOGLE_APPLICATION_CREDENTIALS")
refresh_type <- Sys.getenv("REFRESH_TYPE")
if (refresh_type == "") refresh_type <- ifelse(Sys.getenv("GITHUB_EVENT_NAME") == "schedule", "scheduled", "manual")

if (sheet_id == "") stop("GOOGLE_SHEET_ID is missing.")
if (svc_file == "") stop("GOOGLE_APPLICATION_CREDENTIALS is missing.")

gs4_auth(path = svc_file)

retry_with_backoff <- function(fn, max_attempts = 3, base_delay = 2) {
  for (attempt in seq_len(max_attempts)) {
    result <- tryCatch(fn(), error = function(e) e)
    if (!inherits(result, "error")) return(result)
    if (attempt == max_attempts) stop(result)
    delay <- base_delay * (2 ^ (attempt - 1))
    message(sprintf("  Retry %d/%d in %ds: %s", attempt, max_attempts, delay, conditionMessage(result)))
    Sys.sleep(delay)
  }
}

safe_read_sheet <- function(tab) {
  tryCatch({
    df <- retry_with_backoff(function() read_sheet(sheet_id, sheet = tab) |> clean_names())
    # Google Sheets returns list columns when cells have mixed types or are empty.
    # Unlist them here so downstream code can safely do numeric/character operations.
    if (any(sapply(df, is.list))) {
      df <- df |> mutate(across(where(is.list), ~sapply(., function(x) if (is.null(x) || length(x) == 0) NA else x[[1]])))
    }
    df
  },
    error = function(e) {
      message(sprintf("  Warning: could not read tab '%s': %s", tab, conditionMessage(e)))
      tibble()
    }
  )
}

safe_write_sheet <- function(df, tab) {
  df <- as_tibble(df)
  retry_with_backoff(function() {
    tryCatch(
      sheet_write(df, ss = sheet_id, sheet = tab),
      error = function(e) {
        try(sheet_add(sheet_id, tab), silent = TRUE)
        sheet_write(df, ss = sheet_id, sheet = tab)
      }
    )
  })
}

safe_num <- function(x) suppressWarnings(as.numeric(x))
safe_chr <- function(x) ifelse(is.na(x), NA_character_, as.character(x))

coalesce_col <- function(df, candidates, default = NA) {
  nm <- names(df)
  nm_lower <- tolower(nm)
  for (cand in candidates) {
    idx <- which(nm_lower == tolower(cand))
    if (length(idx) > 0) return(df[[nm[idx[1]]]])
  }
  rep(default, nrow(df))
}

find_col_by_prefix <- function(df, prefix) {
  nm <- names(df)
  exact <- nm[nm == prefix]
  if (length(exact) > 0) return(exact[1])
  pattern <- nm[grepl(paste0("^", prefix, "_\\d+$"), nm)]
  if (length(pattern) > 0) return(pattern[1])
  NULL
}

first_non_na <- function(...) {
  xs <- list(...)
  out <- xs[[1]]
  if (length(xs) == 1) return(out)
  for (i in 2:length(xs)) {
    fill_idx <- is.na(out) | out == ""
    out[fill_idx] <- xs[[i]][fill_idx]
  }
  out
}

norm_name <- function(x) {
  x |>
    str_to_lower() |>
    str_replace_all("[^a-z0-9 ]", " ") |>
    str_squish()
}

season_year_to_use <- function(today = with_tz(now("America/Chicago"), "America/Chicago")) {
  yr <- year(today)
  cutoff <- as.Date(sprintf("%s-04-01", yr))
  if (as.Date(today) < cutoff) yr - 1 else yr
}

today_chi <- with_tz(now("America/Chicago"), "America/Chicago")
season_year <- season_year_to_use(today_chi)
t14_start <- as.Date(today_chi) - 13
t14_end <- as.Date(today_chi)

fg_url <- function(fg_id) {
  ifelse(
    is.na(fg_id) | fg_id == "",
    NA_character_,
    glue("https://www.fangraphs.com/players/{fg_id}")
  )
}

savant_url <- function(mlb_id) {
  ifelse(
    is.na(mlb_id) | mlb_id == "",
    NA_character_,
    glue("https://baseballsavant.mlb.com/savant-player/{mlb_id}")
  )
}

fg_link_formula <- function(fg_id) {
  ifelse(
    is.na(fg_id) | fg_id == "",
    "",
    glue('=HYPERLINK("{fg_url(fg_id)}","FanGraphs")')
  )
}

savant_link_formula <- function(mlb_id) {
  ifelse(
    is.na(mlb_id) | mlb_id == "",
    "",
    glue('=HYPERLINK("{savant_url(mlb_id)}","Savant")')
  )
}

sum_or_na <- function(x) {
  x <- safe_num(x)
  if (length(x) == 0 || all(is.na(x))) NA_real_ else sum(x, na.rm = TRUE)
}

mean_or_na <- function(x) {
  x <- safe_num(x)
  if (length(x) == 0 || all(is.na(x))) NA_real_ else mean(x, na.rm = TRUE)
}

mode_chr <- function(x) {
  x <- x[!is.na(x) & x != ""]
  if (length(x) == 0) return(NA_character_)
  names(sort(table(x), decreasing = TRUE))[1]
}

scale_0_100 <- function(x) {
  x <- safe_num(x)
  if (length(x) == 0) return(numeric())
  if (all(is.na(x))) return(rep(50, length(x)))
  rng <- range(x, na.rm = TRUE)
  if (diff(rng) == 0) return(rep(50, length(x)))
  100 * (x - rng[1]) / diff(rng)
}

percentile_rank <- function(x, higher_is_better = TRUE) {
  x <- safe_num(x)
  out <- rep(NA_real_, length(x))
  idx <- which(!is.na(x))
  if (length(idx) == 0) return(out)
  vals <- x[idx]
  if (!higher_is_better) vals <- -vals
  if (length(unique(vals)) == 1) {
    out[idx] <- 50
    return(out)
  }
  ranks <- rank(vals, ties.method = "average")
  out[idx] <- round(100 * (ranks - 1) / (length(vals) - 1), 1)
  out
}

# Rank player values against a full reference distribution (league-wide percentiles)
percentile_rank_vs_ref <- function(player_vals, ref_vals, higher_is_better = TRUE) {
  player_vals <- safe_num(player_vals)
  ref_vals <- safe_num(ref_vals)
  ref_clean <- ref_vals[!is.na(ref_vals)]
  if (length(ref_clean) < 2) return(rep(NA_real_, length(player_vals)))
  out <- rep(NA_real_, length(player_vals))
  for (i in seq_along(player_vals)) {
    v <- player_vals[i]
    if (is.na(v)) next
    if (higher_is_better) {
      out[i] <- round(100 * sum(ref_clean <= v) / length(ref_clean), 1)
    } else {
      out[i] <- round(100 * sum(ref_clean >= v) / length(ref_clean), 1)
    }
  }
  out
}

# Column name mapping: roster column (after stripping season_) -> leaderboard column
LDR_COL_MAP <- c(
  xwoba = "xwoba", xba = "xba", woba = "woba",
  barrel_pct = "barrel_batted_rate", hard_hit_pct = "hard_hit_percent",
  exit_velocity = "ev", bb_minus_k_pct = "bb_minus_k_pct",
  hr = "hr", sb = "sb", ops = "ops", iso = "iso",
  avg = "avg", obp = "obp", slg = "slg",
  bb_pct = "bb_percent", k_pct = "k_percent",
  wrc_plus = "wrc_plus",
  # Pitcher columns
  k_minus_bb_pct = "k_minus_bb_pct",
  siera = "siera", xfip = "x_fip", fip = "fip",
  swstr_pct = "sw_str_percent", velocity = "f_bv",
  era = "era", whip = "whip", innings = "ip",
  stuff_plus = "sp_stuff",
  hard_hit_pct_against = "hard_hit_percent",
  saves_holds = "saves_holds", hr_against = "hr",
  xera = "xera", games = "g", earned_runs = "er",
  xfip_minus = "xfip_minus", fip_minus = "fip_minus",
  # MiLB columns
  obp = "obp", avg = "avg", pa = "pa",
  steals = "sb", woba = "woba",
  age_vs_level = "age_vs_level",
  throwing_velocity = "f_bv",
  holds_plus_saves = "saves_holds",
  bb_pct = "bb_percent", k_pct = "k_percent",
  wrc_plus = "wrc_plus"
)

add_percentiles <- function(df, metric_map, ref_df = NULL) {
  # Pre-compute derived columns in ref_df if needed
  if (!is.null(ref_df)) {
    if ("bb_percent" %in% names(ref_df) && "k_percent" %in% names(ref_df)) {
      ref_df$bb_minus_k_pct <- safe_num(ref_df$bb_percent) - safe_num(ref_df$k_percent)
      ref_df$k_minus_bb_pct <- safe_num(ref_df$k_percent) - safe_num(ref_df$bb_percent)
    }
    if ("sv" %in% names(ref_df) && "hld" %in% names(ref_df)) {
      ref_df$saves_holds <- safe_num(ref_df$sv) + safe_num(ref_df$hld)
    }
  }
  out <- df
  for (nm in names(metric_map)) {
    if (nm %in% names(out)) {
      stripped <- sub("^(t14_|season_)", "", nm)
      ldr_col <- if (stripped %in% names(LDR_COL_MAP)) LDR_COL_MAP[[stripped]] else NULL
      if (!is.null(ref_df) && !is.null(ldr_col) && ldr_col %in% names(ref_df) && !grepl("^t14_", nm)) {
        out[[paste0(nm, "_pctile")]] <- percentile_rank_vs_ref(
          out[[nm]], ref_df[[ldr_col]], higher_is_better = metric_map[[nm]]
        )
      } else {
        out[[paste0(nm, "_pctile")]] <- percentile_rank(out[[nm]], higher_is_better = metric_map[[nm]])
      }
    } else {
      out[[paste0(nm, "_pctile")]] <- NA_real_
    }
  }
  out
}

safe_statcast_batter <- function(mlb_id, start_date, end_date) {
  tryCatch(
    baseballr::statcast_search_batters(
      start_date = as.character(start_date),
      end_date = as.character(end_date),
      batterid = as.numeric(mlb_id)
    ) |> clean_names(),
    error = function(e) tibble()
  )
}

safe_statcast_pitcher <- function(mlb_id, start_date, end_date) {
  tryCatch(
    baseballr::statcast_search_pitchers(
      start_date = as.character(start_date),
      end_date = as.character(end_date),
      pitcherid = as.numeric(mlb_id)
    ) |> clean_names(),
    error = function(e) tibble()
  )
}

agg_statcast_hitter <- function(sc) {
  if (nrow(sc) == 0) {
    return(tibble(
      xwoba = NA_real_,
      xba = NA_real_,
      barrel_pct = NA_real_,
      exit_velocity = NA_real_,
      hard_hit_pct = NA_real_
    ))
  }

  # Log Statcast columns on first call to help diagnose missing fields
  sc_cols_with_est <- names(sc)[grepl("estimated|xba|xwoba|woba", names(sc), ignore.case = TRUE)]
  if (length(sc_cols_with_est) > 0) message(sprintf("    Statcast xBA/xwOBA columns: %s", paste(sc_cols_with_est, collapse = ", ")))

  launch_speed <- safe_num(coalesce_col(sc, c("launch_speed")))
  est_woba <- safe_num(coalesce_col(sc, c("estimated_woba_using_speedangle", "est_woba", "xwoba", "woba_value")))
  est_ba <- safe_num(coalesce_col(sc, c("estimated_ba_using_speedangle", "est_ba", "xba")))

  barrel_flag <- baseballr::code_barrel(
    launch_speed = launch_speed,
    launch_angle = safe_num(coalesce_col(sc, c("launch_angle")))
  )
  hard_hit_flag <- ifelse(!is.na(launch_speed) & launch_speed >= 95, 1, 0)

  tibble(
    xwoba = mean(est_woba, na.rm = TRUE),
    xba = mean(est_ba, na.rm = TRUE),
    barrel_pct = mean(barrel_flag, na.rm = TRUE) * 100,
    exit_velocity = mean(launch_speed, na.rm = TRUE),
    hard_hit_pct = mean(hard_hit_flag, na.rm = TRUE) * 100
  ) |> mutate(across(everything(), ~ ifelse(is.nan(.x), NA_real_, .x)))
}

agg_statcast_pitcher <- function(sc) {
  if (nrow(sc) == 0) {
    return(tibble(
      xera = NA_real_,
      barrel_pct_against = NA_real_,
      exit_velocity_against = NA_real_,
      hard_hit_pct_against = NA_real_,
      velo = NA_real_
    ))
  }

  launch_speed <- safe_num(coalesce_col(sc, c("launch_speed")))
  launch_angle <- safe_num(coalesce_col(sc, c("launch_angle")))
  velo <- safe_num(coalesce_col(sc, c("release_speed")))

  barrel_flag <- baseballr::code_barrel(launch_speed = launch_speed, launch_angle = launch_angle)
  hard_hit_flag <- ifelse(!is.na(launch_speed) & launch_speed >= 95, 1, 0)

  tibble(
    xera = NA_real_,
    barrel_pct_against = mean(barrel_flag, na.rm = TRUE) * 100,
    exit_velocity_against = mean(launch_speed, na.rm = TRUE),
    hard_hit_pct_against = mean(hard_hit_flag, na.rm = TRUE) * 100,
    velo = mean(velo, na.rm = TRUE)
  ) |> mutate(across(everything(), ~ ifelse(is.nan(.x), NA_real_, .x)))
}

safe_fg_batter_logs <- function(fg_id, yr) {
  tryCatch(baseballr::fg_batter_game_logs(playerid = fg_id, year = yr) |> clean_names(),
           error = function(e) tibble())
}

safe_fg_pitcher_logs <- function(fg_id, yr) {
  tryCatch(baseballr::fg_pitcher_game_logs(playerid = fg_id, year = yr) |> clean_names(),
           error = function(e) tibble())
}

safe_fg_milb_batter_logs <- function(fg_id, yr) {
  tryCatch(baseballr::fg_milb_batter_game_logs(playerid = fg_id, year = yr) |> clean_names(),
           error = function(e) tibble())
}

safe_fg_milb_pitcher_logs <- function(fg_id, yr) {
  tryCatch(baseballr::fg_milb_pitcher_game_logs(playerid = fg_id, year = yr) |> clean_names(),
           error = function(e) tibble())
}

safe_fg_bat_leaders <- function(yr) {
  tryCatch(
    baseballr::fg_batter_leaders(startseason = yr, endseason = yr, qual = 0) |> clean_names(),
    error = function(e) tibble()
  )
}

safe_fg_pitch_leaders <- function(yr) {
  tryCatch(
    baseballr::fg_pitcher_leaders(startseason = yr, endseason = yr, qual = 0) |> clean_names(),
    error = function(e) tibble()
  )
}

# Leaderboard cache: save on success, load on failure (FanGraphs 403s from GH Actions)
cache_dir <- file.path(getwd(), "cache")
if (!dir.exists(cache_dir)) dir.create(cache_dir, recursive = TRUE)

save_leader_cache <- function(df, label, yr) {
  if (nrow(df) > 0) {
    path <- file.path(cache_dir, sprintf("%s_%d.csv", label, yr))
    write_csv(df, path)
    message(sprintf("  Cached %s: %d rows -> %s", label, nrow(df), basename(path)))
  }
}

load_leader_cache <- function(label, yr) {
  path <- file.path(cache_dir, sprintf("%s_%d.csv", label, yr))
  if (file.exists(path)) {
    cached <- read_csv(path, show_col_types = FALSE) |> clean_names()
    message(sprintf("  Loaded %s from cache: %d rows (file: %s)", label, nrow(cached), basename(path)))
    return(cached)
  }
  message(sprintf("  No cache found for %s_%d", label, yr))
  tibble()
}

fetch_with_retry <- function(fetch_fn, label, yr, max_retries = 2) {
  for (attempt in seq_len(max_retries + 1)) {
    result <- fetch_fn(yr)
    if (nrow(result) > 0) return(result)
    if (attempt <= max_retries) {
      wait <- attempt * 3
      message(sprintf("  %s returned 0 rows, retrying in %ds (attempt %d/%d)...",
                       label, wait, attempt, max_retries + 1))
      Sys.sleep(wait)
    }
  }
  result
}

# Alternative leaderboard source: MLB Stats API + Baseball Savant
# Used when FanGraphs is blocked (Cloudflare 403) and no file cache exists
fetch_alt_bat_leaders <- function(yr) {
  message("  Trying alternative source: MLB Stats API + Baseball Savant...")
  tryCatch({
    mlb_url <- sprintf("https://statsapi.mlb.com/api/v1/stats?stats=season&group=hitting&season=%d&sportId=1&limit=5000&sortStat=plateAppearances&order=desc", yr)
    mlb_resp <- GET(mlb_url)
    if (status_code(mlb_resp) != 200) { message("    MLB Stats API failed"); return(tibble()) }
    mlb_data <- content(mlb_resp, as = "parsed")
    splits <- mlb_data$stats[[1]]$splits
    if (length(splits) == 0) { message("    MLB Stats API returned 0 splits"); return(tibble()) }

    mlb_df <- map_dfr(splits, function(s) {
      st <- s$stat
      tibble(
        playerid = as.character(s$player$id),
        name = s$player$fullName,
        team = ifelse(!is.null(s$team$abbreviation), s$team$abbreviation, ""),
        age = st$age %||% NA_real_,
        pa = st$plateAppearances %||% 0,
        hr = st$homeRuns %||% 0,
        sb = st$stolenBases %||% 0,
        avg = as.numeric(st$avg %||% 0),
        obp = as.numeric(st$obp %||% 0),
        slg = as.numeric(st$slg %||% 0),
        ops = as.numeric(st$ops %||% 0),
        bb = st$baseOnBalls %||% 0,
        so = st$strikeOuts %||% 0
      )
    }) |> mutate(
      iso = slg - avg,
      bb_percent = ifelse(pa > 0, bb / pa, 0),
      k_percent = ifelse(pa > 0, so / pa, 0)
    )
    message(sprintf("    MLB Stats API: %d batters", nrow(mlb_df)))

    # Savant expected stats (xwOBA, xBA)
    sv_url <- sprintf("https://baseballsavant.mlb.com/leaderboard/expected_statistics?type=batter&year=%d&position=&team=&min=0&csv=true", yr)
    sv_resp <- GET(sv_url, add_headers(`User-Agent` = "Mozilla/5.0"))
    if (status_code(sv_resp) == 200) {
      sv_text <- content(sv_resp, as = "text", encoding = "UTF-8")
      sv_df <- read_csv(sv_text, show_col_types = FALSE) |> clean_names()
      nm_sv <- names(sv_df)
      pid_col <- nm_sv[grepl("player_id|playerid", nm_sv)][1]
      xwoba_col <- nm_sv[grepl("est_woba", nm_sv)][1]
      xba_col <- nm_sv[grepl("est_ba$", nm_sv)][1]
      woba_col <- nm_sv[nm_sv == "woba"][1]
      if (!is.na(pid_col)) {
        sv_slim <- sv_df |> transmute(
          playerid = as.character(.data[[pid_col]]),
          xwoba = if (!is.na(xwoba_col)) safe_num(.data[[xwoba_col]]) else NA_real_,
          xba = if (!is.na(xba_col)) safe_num(.data[[xba_col]]) else NA_real_,
          woba = if (!is.na(woba_col)) safe_num(.data[[woba_col]]) else NA_real_
        )
        mlb_df <- mlb_df |> left_join(sv_slim, by = "playerid")
        message(sprintf("    Savant expected stats merged: %d rows", nrow(sv_slim)))
      }
    }

    # Savant statcast (barrel%, hard_hit%, exit_velocity)
    sc_url <- sprintf("https://baseballsavant.mlb.com/leaderboard/statcast?type=batter&year=%d&position=&team=&min=0&csv=true", yr)
    sc_resp <- GET(sc_url, add_headers(`User-Agent` = "Mozilla/5.0"))
    if (status_code(sc_resp) == 200) {
      sc_text <- content(sc_resp, as = "text", encoding = "UTF-8")
      sc_df <- read_csv(sc_text, show_col_types = FALSE) |> clean_names()
      nm_sc <- names(sc_df)
      pid_col2 <- nm_sc[grepl("player_id|playerid", nm_sc)][1]
      ev_col <- nm_sc[grepl("avg_hit_speed", nm_sc)][1]
      brl_col <- nm_sc[grepl("brl_percent", nm_sc)][1]
      hh_col <- nm_sc[grepl("ev95percent", nm_sc)][1]
      if (!is.na(pid_col2)) {
        sc_slim <- sc_df |> transmute(
          playerid = as.character(.data[[pid_col2]]),
          ev = if (!is.na(ev_col)) safe_num(.data[[ev_col]]) else NA_real_,
          barrel_batted_rate = if (!is.na(brl_col)) safe_num(.data[[brl_col]]) else NA_real_,
          hard_hit_percent = if (!is.na(hh_col)) safe_num(.data[[hh_col]]) else NA_real_
        )
        mlb_df <- mlb_df |> left_join(sc_slim, by = "playerid")
        message(sprintf("    Savant statcast merged: %d rows", nrow(sc_slim)))
      }
    }

    # Approximate wRC+ from wOBA: wRC+ = ((wOBA - lgwOBA) / wOBA_scale + lgR_PA) / lgR_PA * 100
    # Using 2025 league averages: lgwOBA ~.310, wOBA_scale ~1.15, lgR/PA ~.115
    if ("woba" %in% names(mlb_df)) {
      mlb_df <- mlb_df |> mutate(
        wrc_plus = ifelse(!is.na(woba), round(((woba - 0.310) / 1.15 + 0.115) / 0.115 * 100, 1), NA_real_)
      )
    }

    mlb_df
  }, error = function(e) { message(sprintf("    Alt batter fetch failed: %s", e$message)); tibble() })
}

fetch_alt_pitch_leaders <- function(yr) {
  message("  Trying alternative source: MLB Stats API + Baseball Savant (pitchers)...")
  tryCatch({
    mlb_url <- sprintf("https://statsapi.mlb.com/api/v1/stats?stats=season&group=pitching&season=%d&sportId=1&limit=5000&sortStat=inningsPitched&order=desc", yr)
    mlb_resp <- GET(mlb_url)
    if (status_code(mlb_resp) != 200) return(tibble())
    mlb_data <- content(mlb_resp, as = "parsed")
    splits <- mlb_data$stats[[1]]$splits
    if (length(splits) == 0) return(tibble())

    mlb_df <- map_dfr(splits, function(s) {
      st <- s$stat
      tibble(
        playerid = as.character(s$player$id),
        name = s$player$fullName,
        team = ifelse(!is.null(s$team$abbreviation), s$team$abbreviation, ""),
        age = st$age %||% NA_real_,
        g = st$gamesPitched %||% st$gamesPlayed %||% 0,
        gs = st$gamesStarted %||% 0,
        ip = parse_ip(st$inningsPitched %||% 0),
        era = as.numeric(st$era %||% 0),
        whip = as.numeric(st$whip %||% 0),
        so = st$strikeOuts %||% 0,
        bb = st$baseOnBalls %||% 0,
        bf = st$battersFaced %||% 0,
        sv = st$saves %||% 0,
        hld = st$holds %||% 0,
        hr = st$homeRuns %||% 0
      )
    }) |> mutate(
      k_percent = ifelse(bf > 0, so / bf, 0),
      bb_percent = ifelse(bf > 0, bb / bf, 0)
    )

    # Calculate FIP using league-derived constant instead of hardcoded 3.2.
    # FIP constant = lgERA - ((13*lgHR + 3*lgBB - 2*lgSO) / lgIP)
    lg_era <- weighted.mean(mlb_df$era, mlb_df$ip, na.rm = TRUE)
    lg_hr  <- sum(mlb_df$hr, na.rm = TRUE)
    lg_bb  <- sum(mlb_df$bb, na.rm = TRUE)
    lg_so  <- sum(mlb_df$so, na.rm = TRUE)
    lg_ip  <- sum(mlb_df$ip, na.rm = TRUE)
    fip_constant <- if (lg_ip > 0) lg_era - ((13 * lg_hr + 3 * lg_bb - 2 * lg_so) / lg_ip) else 3.2
    message(sprintf("    FIP constant: %.3f (lgERA=%.3f, lgIP=%.1f)", fip_constant, lg_era, lg_ip))
    mlb_df <- mlb_df |> mutate(
      fip = ifelse(ip > 0, ((13 * hr) + (3 * bb) - (2 * so)) / ip + fip_constant, NA_real_)
    )
    message(sprintf("    MLB Stats API: %d pitchers", nrow(mlb_df)))

    # Savant pitcher statcast (exit velo, hard hit against)
    sc_url <- sprintf("https://baseballsavant.mlb.com/leaderboard/statcast?type=pitcher&year=%d&position=&team=&min=0&csv=true", yr)
    sc_resp <- GET(sc_url, add_headers(`User-Agent` = "Mozilla/5.0"))
    if (status_code(sc_resp) == 200) {
      sc_text <- content(sc_resp, as = "text", encoding = "UTF-8")
      sc_df <- read_csv(sc_text, show_col_types = FALSE) |> clean_names()
      nm_sc <- names(sc_df)
      pid_col <- nm_sc[grepl("player_id|playerid", nm_sc)][1]
      hh_col <- nm_sc[grepl("ev95percent", nm_sc)][1]
      ev_col <- nm_sc[grepl("avg_hit_speed", nm_sc)][1]
      if (!is.na(pid_col)) {
        sc_slim <- sc_df |> transmute(
          playerid = as.character(.data[[pid_col]]),
          ev_against = if (!is.na(ev_col)) safe_num(.data[[ev_col]]) else NA_real_,
          hard_hit_percent = if (!is.na(hh_col)) safe_num(.data[[hh_col]]) else NA_real_
        )
        mlb_df <- mlb_df |> left_join(sc_slim, by = "playerid")
        message(sprintf("    Savant statcast merged: %d rows", nrow(sc_slim)))
      }
    }

    # Savant expected pitching stats (xERA)
    xp_url <- sprintf("https://baseballsavant.mlb.com/leaderboard/expected_statistics?type=pitcher&year=%d&position=&team=&min=0&csv=true", yr)
    xp_resp <- GET(xp_url, add_headers(`User-Agent` = "Mozilla/5.0"))
    if (status_code(xp_resp) == 200) {
      xp_text <- content(xp_resp, as = "text", encoding = "UTF-8")
      xp_df <- read_csv(xp_text, show_col_types = FALSE) |> clean_names()
      nm_xp <- names(xp_df)
      pid_col_xp <- nm_xp[grepl("player_id|playerid", nm_xp)][1]
      xera_col <- nm_xp[nm_xp == "xera"][1]
      xwoba_col <- nm_xp[grepl("est_woba", nm_xp)][1]
      if (!is.na(pid_col_xp)) {
        xp_slim <- xp_df |> transmute(
          playerid = as.character(.data[[pid_col_xp]]),
          xera = if (!is.na(xera_col)) safe_num(.data[[xera_col]]) else NA_real_,
          xwoba_against = if (!is.na(xwoba_col)) safe_num(.data[[xwoba_col]]) else NA_real_
        )
        mlb_df <- mlb_df |> left_join(xp_slim, by = "playerid")
        message(sprintf("    Savant expected stats merged: %d rows", nrow(xp_slim)))
      }
    }

    # Savant pitch arsenals (fastball velocity)
    pa_url <- sprintf("https://baseballsavant.mlb.com/leaderboard/pitch-arsenals?year=%d&min=0&type=avg_speed&hand=&csv=true", yr)
    pa_resp <- GET(pa_url, add_headers(`User-Agent` = "Mozilla/5.0"))
    if (status_code(pa_resp) == 200) {
      pa_text <- content(pa_resp, as = "text", encoding = "UTF-8")
      pa_df <- read_csv(pa_text, show_col_types = FALSE) |> clean_names()
      nm_pa <- names(pa_df)
      pid_col_pa <- nm_pa[grepl("^pitcher$|player_id|playerid", nm_pa)][1]
      ff_col <- nm_pa[grepl("ff_avg_speed", nm_pa)][1]
      if (!is.na(pid_col_pa) && !is.na(ff_col)) {
        pa_slim <- pa_df |> transmute(
          playerid = as.character(.data[[pid_col_pa]]),
          f_bv = safe_num(.data[[ff_col]])
        )
        mlb_df <- mlb_df |> left_join(pa_slim, by = "playerid")
        message(sprintf("    Savant pitch arsenals merged: %d rows", nrow(pa_slim)))
      }
    }

    # xFIP requires fly ball data which MLB Stats API doesn't provide.
    # Leave blank rather than calculate with wrong inputs.

    mlb_df
  }, error = function(e) { message(sprintf("    Alt pitcher fetch failed: %s", e$message)); tibble() })
}

message(sprintf("Fetching FanGraphs leaderboards for %d...", season_year))
bat_leaders <- fetch_with_retry(safe_fg_bat_leaders, "bat_leaders", season_year)
if (nrow(bat_leaders) > 0) {
  save_leader_cache(bat_leaders, "bat_leaders", season_year)
} else {
  message("  FanGraphs batter leaders unavailable, trying cache...")
  bat_leaders <- load_leader_cache("bat_leaders", season_year)
  if (nrow(bat_leaders) == 0) {
    bat_leaders <- fetch_alt_bat_leaders(season_year)
    if (nrow(bat_leaders) > 0) save_leader_cache(bat_leaders, "bat_leaders", season_year)
  }
}
message(sprintf("  Batter leaders: %d rows", nrow(bat_leaders)))

Sys.sleep(2)

pitch_leaders <- fetch_with_retry(safe_fg_pitch_leaders, "pitch_leaders", season_year)
if (nrow(pitch_leaders) > 0) {
  save_leader_cache(pitch_leaders, "pitch_leaders", season_year)
} else {
  message("  FanGraphs pitcher leaders unavailable, trying cache...")
  pitch_leaders <- load_leader_cache("pitch_leaders", season_year)
  if (nrow(pitch_leaders) == 0) {
    pitch_leaders <- fetch_alt_pitch_leaders(season_year)
    if (nrow(pitch_leaders) > 0) save_leader_cache(pitch_leaders, "pitch_leaders", season_year)
  }
}
message(sprintf("  Pitcher leaders: %d rows", nrow(pitch_leaders)))

# Recalculate FIP with league-derived constant regardless of data source.
if (nrow(pitch_leaders) > 0 && all(c("ip", "era", "hr", "bb", "so") %in% names(pitch_leaders))) {
  pl_ip <- pitch_leaders$ip
  # Convert baseball IP notation if needed (values like 182.1 where .1 = 1/3 inning)
  frac <- round((pl_ip - trunc(pl_ip)) * 10)
  if (any(frac > 2, na.rm = TRUE) == FALSE && any(frac > 0, na.rm = TRUE)) {
    pl_ip <- trunc(pl_ip) + frac / 3
  }
  lg_era <- weighted.mean(pitch_leaders$era, pl_ip, na.rm = TRUE)
  lg_hr  <- sum(pitch_leaders$hr, na.rm = TRUE)
  lg_bb  <- sum(pitch_leaders$bb, na.rm = TRUE)
  lg_so  <- sum(pitch_leaders$so, na.rm = TRUE)
  lg_ip  <- sum(pl_ip, na.rm = TRUE)
  fip_c  <- if (lg_ip > 0) lg_era - ((13 * lg_hr + 3 * lg_bb - 2 * lg_so) / lg_ip) else 3.2
  message(sprintf("  FIP constant: %.3f (lgERA=%.3f, lgIP=%.1f)", fip_c, lg_era, lg_ip))
  pitch_leaders <- pitch_leaders |> mutate(
    fip = ifelse(pl_ip > 0, ((13 * hr) + (3 * bb) - (2 * so)) / pl_ip + fip_c, NA_real_)
  )
  save_leader_cache(pitch_leaders, "pitch_leaders", season_year)
}

resolve_player_ids <- function(df) {
  df <- df |> clean_names()
  # Unlist any list-type columns from Google Sheets (mixed types / empty cells)
  df <- df |>
    mutate(across(where(is.list), ~sapply(., function(x) if (is.null(x) || length(x) == 0) NA else x[[1]])))
  nm <- names(df)

  message(sprintf("  Columns after clean_names: %s", paste(names(df), collapse = ", ")))
  # Find the player name column (handles name, player_name, player, plus
  # suffixed variants like name_1 that appear with duplicate sheet columns)
  name_col <- NULL
  for (cand in c("player_name", "player", "name")) {
    found <- find_col_by_prefix(df, cand)
    if (!is.null(found)) { name_col <- found; break }
  }
  if (!is.null(name_col) && name_col != "player_name") {
    df <- df |> rename(player_name = !!sym(name_col))
  }
  if (is.null(name_col)) stop("Cannot find player name column in roster tab. Expected one of: player_name, player, name. Found: ", paste(names(df), collapse = ", "))

  # Find ID and metadata columns, handling numeric suffixes from
  # duplicate sheet columns (e.g. mlbid_2 instead of mlbid)
  col_defaults <- list(
    fangraphs_id = NA, mlbid = NA, team = NA,
    role = NA, level = NA, position = NA, age = NA
  )
  for (col_name in names(col_defaults)) {
    if (!col_name %in% names(df)) {
      found <- find_col_by_prefix(df, col_name)
      if (!is.null(found)) {
        df <- df |> rename(!!col_name := !!sym(found))
      } else if (col_name == "mlbid" && "manual_id" %in% names(df)) {
        df <- df |> rename(mlbid = manual_id)
      } else {
        df[[col_name]] <- col_defaults[[col_name]]
      }
    }
  }

  # The Test tab has two Fangraphs ID columns: the first is an encoded/display
  # value (e.g. *05udp*), the second is the real numeric ID. After read_sheet +
  # clean_names, duplicates get suffixed as _1/_2 or _N (from ...N notation).
  # Find any alternate fangraphs_id column with more numeric values and use it.
  fg_alt_cols <- grep("^fangraphs_id_\\d+$", names(df), value = TRUE)
  message(sprintf("  fangraphs_id columns found: fangraphs_id, %s", paste(fg_alt_cols, collapse = ", ")))
  if (length(fg_alt_cols) > 0) {
    primary_numeric <- suppressWarnings(sum(!is.na(as.numeric(df$fangraphs_id))))
    for (alt_col in fg_alt_cols) {
      alt_numeric <- suppressWarnings(sum(!is.na(as.numeric(df[[alt_col]]))))
      if (alt_numeric > primary_numeric) {
        message(sprintf("  Swapping fangraphs_id with %s (primary had %d numeric, alt has %d)", alt_col, primary_numeric, alt_numeric))
        df$fangraphs_id <- df[[alt_col]]
        break
      }
    }
  }

  # Use MiLB FanGraphs ID when the main one is missing or zero,
  # and infer MiLB level from the presence of a milb_fg_id
  milb_col <- grep("mi.?lb.*fg|milb.*fg|fg.*milb", names(df), value = TRUE, ignore.case = TRUE)
  message(sprintf("  MiLB FG ID columns found: %s", paste(milb_col, collapse = ", ")))
  if (length(milb_col) > 0 && milb_col[1] != "milb_fg_id") {
    df <- df |> rename(milb_fg_id = !!sym(milb_col[1]))
  }
  if ("milb_fg_id" %in% names(df)) {
    has_milb_id <- !is.na(df$milb_fg_id) & df$milb_fg_id != "" & df$milb_fg_id != "0"
    missing_fg <- is.na(df$fangraphs_id) | df$fangraphs_id == "" | df$fangraphs_id == "0" | df$fangraphs_id == "NA"
    df$fangraphs_id[missing_fg & has_milb_id] <- safe_chr(df$milb_fg_id[missing_fg & has_milb_id])
    missing_level <- is.na(df$level) | df$level == ""
    df$level[missing_level & has_milb_id] <- "MiLB"
    message(sprintf("  MiLB FG IDs applied: %d players", sum(missing_fg & has_milb_id)))
  }

  # Use level_overide when set
  if ("level_overide" %in% names(df)) {
    has_override <- !is.na(df$level_overide) & df$level_overide != ""
    df$level[has_override] <- df$level_overide[has_override]
  }

  df <- df |>
  mutate(
    fangraphs_id = safe_chr(fangraphs_id),
    mlbid = safe_chr(mlbid),
    player_name_clean = norm_name(player_name),
    team_clean = norm_name(team),
    # Normalize level: MILB/milb/Milb all become MiLB
    level = case_when(
      toupper(level) == "MILB" ~ "MiLB",
      toupper(level) == "MLB" ~ "MLB",
      TRUE ~ level
    )
  )

  bat_ref <- bat_leaders |>
    transmute(
      fg_ref = safe_chr(coalesce_col(pick(everything()), c("playerid"))),
      mlb_ref = safe_chr(coalesce_col(pick(everything()), c("playeridmlb", "playerid_mlb", "mlbid"))),
      name_ref = norm_name(coalesce_col(pick(everything()), c("name", "player_name"))),
      team_ref = norm_name(coalesce_col(pick(everything()), c("team", "team_name", "teamid"))),
      age_ref = safe_num(coalesce_col(pick(everything()), c("age"))),
      pos_ref = safe_chr(coalesce_col(pick(everything()), c("pos")))
    )

  pitch_ref <- pitch_leaders |>
    transmute(
      fg_ref = safe_chr(coalesce_col(pick(everything()), c("playerid"))),
      mlb_ref = safe_chr(coalesce_col(pick(everything()), c("playeridmlb", "playerid_mlb", "mlbid"))),
      name_ref = norm_name(coalesce_col(pick(everything()), c("name", "player_name"))),
      team_ref = norm_name(coalesce_col(pick(everything()), c("team", "team_name", "teamid"))),
      age_ref = safe_num(coalesce_col(pick(everything()), c("age"))),
      pos_ref = "P"
    )

  joined_bat <- df |>
    filter(role == "H") |>
    left_join(bat_ref, by = c("player_name_clean" = "name_ref")) |>
    mutate(
      fangraphs_id = first_non_na(fangraphs_id, fg_ref),
      mlbid = first_non_na(mlbid, mlb_ref),
      age = age_ref,
      position = pos_ref
    ) |>
    select(-fg_ref, -mlb_ref, -age_ref, -pos_ref)

  joined_pitch <- df |>
    filter(role == "P") |>
    left_join(pitch_ref, by = c("player_name_clean" = "name_ref")) |>
    mutate(
      fangraphs_id = first_non_na(fangraphs_id, fg_ref),
      mlbid = first_non_na(mlbid, mlb_ref),
      age = age_ref,
      position = "P"
    ) |>
    select(-fg_ref, -mlb_ref, -age_ref, -pos_ref)

  result <- bind_rows(joined_bat, joined_pitch)
  level_counts <- table(result$level, useNA = "ifany")
  message(sprintf("  Level distribution: %s", paste(names(level_counts), level_counts, sep = "=", collapse = ", ")))
  role_counts <- table(result$role, useNA = "ifany")
  message(sprintf("  Role distribution: %s", paste(names(role_counts), role_counts, sep = "=", collapse = ", ")))
  # Log players with unexpected/missing levels
  bad_level <- result |> filter(is.na(level) | !level %in% c("MLB", "MiLB"))
  if (nrow(bad_level) > 0) {
    message(sprintf("  WARNING: %d players with unexpected level: %s",
      nrow(bad_level), paste(sprintf("%s(level=%s)", bad_level$player_name, bad_level$level), collapse = ", ")))
  }
  result
}

agg_hitter_logs <- function(logs, start_date = NULL, end_date = NULL) {
  empty_hitter <- tibble(
    games = NA_real_, pa = NA_real_, ab = NA_real_, h = NA_real_, hr = NA_real_,
    so = NA_real_, bb = NA_real_, sb = NA_real_, avg = NA_real_, obp = NA_real_,
    slg = NA_real_, ops = NA_real_, iso = NA_real_, woba = NA_real_,
    bb_pct = NA_real_, k_pct = NA_real_, wrc_plus = NA_real_,
    hard_hit_pct = NA_real_, barrel_pct = NA_real_, exit_velocity = NA_real_
  )
  if (nrow(logs) == 0) return(empty_hitter)
  logs <- logs |>
    mutate(gamedate2 = as.Date(coalesce_col(pick(everything()), c("gamedate", "date"))))
  if (!is.null(start_date)) logs <- logs |> filter(gamedate2 >= as.Date(start_date))
  if (!is.null(end_date)) logs <- logs |> filter(gamedate2 <= as.Date(end_date))
  if (nrow(logs) == 0) return(empty_hitter)

  # Sum counting stats
  t_pa <- sum_or_na(coalesce_col(logs, c("pa")))
  t_ab <- sum_or_na(coalesce_col(logs, c("ab")))
  t_h  <- sum_or_na(coalesce_col(logs, c("h")))
  t_hr <- sum_or_na(coalesce_col(logs, c("hr")))
  t_so <- sum_or_na(coalesce_col(logs, c("so")))
  t_bb <- sum_or_na(coalesce_col(logs, c("bb")))
  t_sb <- sum_or_na(coalesce_col(logs, c("sb")))
  t_hbp <- sum_or_na(coalesce_col(logs, c("hbp")))
  t_sf  <- sum_or_na(coalesce_col(logs, c("sf")))
  t_tb  <- sum_or_na(coalesce_col(logs, c("tb", "total_bases")))
  t_2b  <- sum_or_na(coalesce_col(logs, c("x2b", "doubles")))
  t_3b  <- sum_or_na(coalesce_col(logs, c("x3b", "triples")))

  # Calculate rate stats from totals (not simple averages of per-game rates)
  calc_avg <- if (!is.na(t_ab) && t_ab > 0) t_h / t_ab else NA_real_
  denom_obp <- sum(t_ab %||% 0, t_bb %||% 0, t_hbp %||% 0, t_sf %||% 0, na.rm = TRUE)
  calc_obp <- if (denom_obp > 0) sum(t_h %||% 0, t_bb %||% 0, t_hbp %||% 0) / denom_obp else NA_real_
  # SLG from total bases, or calculate from hit components
  if (!is.na(t_tb) && !is.na(t_ab) && t_ab > 0) {
    calc_slg <- t_tb / t_ab
  } else if (!is.na(t_h) && !is.na(t_ab) && t_ab > 0) {
    singles <- t_h - (t_2b %||% 0) - (t_3b %||% 0) - (t_hr %||% 0)
    calc_tb <- singles + 2 * (t_2b %||% 0) + 3 * (t_3b %||% 0) + 4 * (t_hr %||% 0)
    calc_slg <- calc_tb / t_ab
  } else {
    calc_slg <- NA_real_
  }
  calc_ops <- if (!is.na(calc_obp) && !is.na(calc_slg)) calc_obp + calc_slg else NA_real_
  calc_iso <- if (!is.na(calc_slg) && !is.na(calc_avg)) calc_slg - calc_avg else NA_real_
  calc_bb_pct <- if (!is.na(t_pa) && t_pa > 0) (t_bb %||% 0) / t_pa else NA_real_
  calc_k_pct <- if (!is.na(t_pa) && t_pa > 0) (t_so %||% 0) / t_pa else NA_real_

  tibble(
    games = sum_or_na(coalesce_col(logs, c("g"))),
    pa = t_pa, ab = t_ab, h = t_h, hr = t_hr, so = t_so, bb = t_bb, sb = t_sb,
    avg = calc_avg,
    obp = calc_obp,
    slg = calc_slg,
    ops = calc_ops,
    iso = calc_iso,
    woba = mean_or_na(coalesce_col(logs, c("w_oba", "woba"))),
    bb_pct = calc_bb_pct,
    k_pct = calc_k_pct,
    wrc_plus = mean_or_na(coalesce_col(logs, c("wrc_plus", "wrc_2", "w_rc_2"))),
    hard_hit_pct = mean_or_na(coalesce_col(logs, c("hard_hit_percent", "hard_percent", "hardhit%", "hard%"))),
    barrel_pct = mean_or_na(coalesce_col(logs, c("barrel_percent", "barrel%", "barrels_per_bbe"))),
    exit_velocity = mean_or_na(coalesce_col(logs, c("ev", "max_ev", "maxev"))),
    age = mean_or_na(coalesce_col(logs, c("age"))),
    team = mode_chr(coalesce_col(logs, c("team"))),
    level = mode_chr(coalesce_col(logs, c("level", "league"))),
    position = mode_chr(coalesce_col(logs, c("pos")))
  )
}

agg_pitcher_logs <- function(logs, start_date = NULL, end_date = NULL) {
  empty_pitcher <- tibble(
    games = NA_real_, gs = NA_real_, ip = NA_real_, er = NA_real_,
    so = NA_real_, bb = NA_real_, hr = NA_real_, era = NA_real_,
    whip = NA_real_, fip = NA_real_, xfip = NA_real_, siera = NA_real_,
    k_pct = NA_real_, bb_pct = NA_real_, k_minus_bb_pct = NA_real_,
    swstr_pct = NA_real_, hard_hit_pct_against = NA_real_,
    barrel_pct_against = NA_real_, exit_velocity_against = NA_real_,
    velo = NA_real_, saves_holds = NA_real_
  )
  if (nrow(logs) == 0) return(empty_pitcher)
  logs <- logs |>
    mutate(gamedate2 = as.Date(coalesce_col(pick(everything()), c("gamedate", "date"))))
  if (!is.null(start_date)) logs <- logs |> filter(gamedate2 >= as.Date(start_date))
  if (!is.null(end_date)) logs <- logs |> filter(gamedate2 <= as.Date(end_date))
  if (nrow(logs) == 0) return(empty_pitcher)

  # Sum counting stats
  t_ip <- sum_or_na(coalesce_col(logs, c("ip")))
  # Convert baseball IP notation: sum of per-game IPs in baseball notation
  # Each game IP is like 6.2 meaning 6 and 2/3. Sum them correctly.
  raw_ips <- as.numeric(coalesce_col(logs, c("ip")))
  raw_ips <- raw_ips[!is.na(raw_ips)]
  if (length(raw_ips) > 0) {
    thirds <- sum(trunc(raw_ips) * 3 + round((raw_ips - trunc(raw_ips)) * 10))
    t_ip <- trunc(thirds / 3) + (thirds %% 3) / 10  # back to baseball notation for display
    t_ip_decimal <- thirds / 3  # true decimal for calculations
  } else {
    t_ip <- NA_real_
    t_ip_decimal <- NA_real_
  }
  t_er <- sum_or_na(coalesce_col(logs, c("er")))
  t_so <- sum_or_na(coalesce_col(logs, c("so")))
  t_bb <- sum_or_na(coalesce_col(logs, c("bb")))
  t_hr <- sum_or_na(coalesce_col(logs, c("hr")))
  t_h  <- sum_or_na(coalesce_col(logs, c("h")))
  t_bf <- sum_or_na(coalesce_col(logs, c("bf", "tbf", "batters_faced")))

  # Calculate rate stats from totals
  calc_era <- if (!is.na(t_ip_decimal) && t_ip_decimal > 0 && !is.na(t_er)) (t_er / t_ip_decimal) * 9 else NA_real_
  calc_whip <- if (!is.na(t_ip_decimal) && t_ip_decimal > 0) ((t_h %||% 0) + (t_bb %||% 0)) / t_ip_decimal else NA_real_
  calc_k_pct <- if (!is.na(t_bf) && t_bf > 0) (t_so %||% 0) / t_bf else NA_real_
  calc_bb_pct <- if (!is.na(t_bf) && t_bf > 0) (t_bb %||% 0) / t_bf else NA_real_
  calc_k_minus_bb <- if (!is.na(calc_k_pct) && !is.na(calc_bb_pct)) calc_k_pct - calc_bb_pct else NA_real_

  tibble(
    games = sum_or_na(coalesce_col(logs, c("g"))),
    gs = sum_or_na(coalesce_col(logs, c("gs"))),
    ip = t_ip,
    er = t_er,
    so = t_so,
    bb = t_bb,
    hr = t_hr,
    era = calc_era,
    whip = calc_whip,
    fip = mean_or_na(coalesce_col(logs, c("fip"))),
    xfip = mean_or_na(coalesce_col(logs, c("xfip"))),
    siera = mean_or_na(coalesce_col(logs, c("siera"))),
    k_pct = calc_k_pct,
    bb_pct = calc_bb_pct,
    k_minus_bb_pct = calc_k_minus_bb,
    swstr_pct = mean_or_na(coalesce_col(logs, c("sw_str_percent", "swstr_percent", "swstr%"))),
    hard_hit_pct_against = mean_or_na(coalesce_col(logs, c("hard_hit_percent", "hard_percent", "hardhit%", "hard%"))),
    barrel_pct_against = mean_or_na(coalesce_col(logs, c("barrel_percent", "barrel%", "barrels_per_bbe"))),
    exit_velocity_against = mean_or_na(coalesce_col(logs, c("ev"))),
    velo = mean_or_na(coalesce_col(logs, c("fbv", "v_fa", "vfa"))),
    saves_holds = sum_or_na(coalesce_col(logs, c("sv"))) + sum_or_na(coalesce_col(logs, c("hld"))),
    age = mean_or_na(coalesce_col(logs, c("age"))),
    team = mode_chr(coalesce_col(logs, c("team"))),
    level = mode_chr(coalesce_col(logs, c("level", "league")))
  )
}

# Look up a player in a leaderboard by FG ID, MLB ID, or normalized name
find_in_leaders <- function(ldr, fg_id, mlb_id, player_name) {
  if (nrow(ldr) == 0) return(ldr[0, , drop = FALSE])
  pid_col <- safe_chr(coalesce_col(ldr, c("playerid")))
  # Try FG ID
  row <- ldr[pid_col == safe_chr(fg_id), , drop = FALSE]
  if (nrow(row) > 0) {
    message(sprintf("    [ldr] %s matched by FG ID (%s)", player_name, fg_id))
    return(row[1, , drop = FALSE])
  }
  # Try MLB ID
  row <- ldr[pid_col == safe_chr(mlb_id), , drop = FALSE]
  if (nrow(row) > 0) {
    message(sprintf("    [ldr] %s matched by MLB ID (%s)", player_name, mlb_id))
    return(row[1, , drop = FALSE])
  }
  # Try name
  ldr_names <- norm_name(coalesce_col(ldr, c("name", "player_name")))
  row <- ldr[ldr_names == norm_name(player_name), , drop = FALSE]
  if (nrow(row) > 0) {
    message(sprintf("    [ldr] %s matched by name", player_name))
    return(row[1, , drop = FALSE])
  }
  message(sprintf("    [ldr] %s NOT FOUND (fg=%s, mlb=%s)", player_name, fg_id, mlb_id))
  ldr[0, , drop = FALSE]
}

# Test if FG game logs are working (called once per build function)
fg_game_logs_available <- NULL
test_fg_availability <- function(fg_id) {
  if (!is.null(fg_game_logs_available)) return(fg_game_logs_available)
  test <- safe_fg_batter_logs(fg_id, season_year)
  fg_game_logs_available <<- nrow(test) > 0
  if (!fg_game_logs_available) message("  FG game logs unavailable, using leaderboard data")
  fg_game_logs_available
}

build_raw_mlb_hitters <- function(players, ldr_ref = NULL) {
  pool <- players |> filter(level == "MLB", role == "H")
  n_total <- nrow(pool)
  message(sprintf("Building raw MLB hitters: %d players", n_total))
  if (n_total == 0) return(tibble())

  # Test FG availability with first player
  fg_ok <- test_fg_availability(pool$fangraphs_id[[1]])

  out <- pool |>
    mutate(row_id = row_number()) |>
    group_split(row_id, .keep = TRUE) |>
    map_dfr(function(p) {
      message(sprintf("  [%d/%d] %s", p$row_id[[1]], n_total, p$player_name[[1]]))

      # FG game logs path (when available)
      if (fg_ok) {
        if (p$row_id[[1]] > 1) Sys.sleep(1.5)
        logs <- safe_fg_batter_logs(p$fangraphs_id[[1]], season_year)
        t14 <- agg_hitter_logs(logs, t14_start, t14_end)
        season <- agg_hitter_logs(logs)
        sc14 <- safe_statcast_batter(p$mlbid[[1]], t14_start, t14_end) |> agg_statcast_hitter()
        sc_end <- min(t14_end, as.Date(paste0(season_year, "-12-31")))
        sc_season <- safe_statcast_batter(p$mlbid[[1]], paste0(season_year, "-01-01"), sc_end) |> agg_statcast_hitter()
      } else {
        t14 <- agg_hitter_logs(tibble())
        season <- agg_hitter_logs(tibble())
        sc14 <- agg_statcast_hitter(tibble())
        sc_season <- agg_statcast_hitter(tibble())
      }

      # Leaderboard fallback for season stats (works with both FG and alt cache data)
      ldr_row <- find_in_leaders(bat_leaders, p$fangraphs_id[[1]], p$mlbid[[1]], p$player_name[[1]])
      if (nrow(ldr_row) > 0) {
        ldr_xwoba <- safe_num(coalesce_col(ldr_row[1,], c("xwoba", "x_woba", "xw_oba")))
        ldr_xba <- safe_num(coalesce_col(ldr_row[1,], c("xba", "x_ba", "x_avg")))
        ldr_wrc <- safe_num(coalesce_col(ldr_row[1,], c("wrc_2", "wrc_plus", "w_rc_2")))
        ldr_ev <- safe_num(coalesce_col(ldr_row[1,], c("ev", "exit_velocity")))
        ldr_brl <- safe_num(coalesce_col(ldr_row[1,], c("barrel_batted_rate", "barrel_pct")))
        ldr_hh <- safe_num(coalesce_col(ldr_row[1,], c("hard_hit_percent", "hard_hit_pct")))
        if (!is.na(ldr_xwoba[1])) sc_season$xwoba <- sc_season$xwoba %||% ldr_xwoba[1]
        if (!is.na(ldr_xba[1])) sc_season$xba <- sc_season$xba %||% ldr_xba[1]
        if (!is.na(ldr_wrc[1]) && ldr_wrc[1] > 10) season$wrc_plus <- season$wrc_plus %||% ldr_wrc[1]
        if (!is.na(ldr_ev[1])) sc_season$exit_velocity <- sc_season$exit_velocity %||% ldr_ev[1]
        if (!is.na(ldr_brl[1])) sc_season$barrel_pct <- sc_season$barrel_pct %||% ldr_brl[1]
        if (!is.na(ldr_hh[1])) sc_season$hard_hit_pct <- sc_season$hard_hit_pct %||% ldr_hh[1]
        # Fill basic season stats from leaderboard when game logs are empty
        ldr_pa <- safe_num(coalesce_col(ldr_row[1,], c("pa")))[1]
        ldr_hr <- safe_num(coalesce_col(ldr_row[1,], c("hr")))[1]
        ldr_sb <- safe_num(coalesce_col(ldr_row[1,], c("sb")))[1]
        ldr_avg <- safe_num(coalesce_col(ldr_row[1,], c("avg")))[1]
        ldr_obp <- safe_num(coalesce_col(ldr_row[1,], c("obp")))[1]
        ldr_slg <- safe_num(coalesce_col(ldr_row[1,], c("slg")))[1]
        ldr_ops <- safe_num(coalesce_col(ldr_row[1,], c("ops")))[1]
        ldr_iso <- safe_num(coalesce_col(ldr_row[1,], c("iso")))[1]
        ldr_woba <- safe_num(coalesce_col(ldr_row[1,], c("woba")))[1]
        ldr_bb_pct <- safe_num(coalesce_col(ldr_row[1,], c("bb_percent", "bb_pct")))[1]
        ldr_k_pct <- safe_num(coalesce_col(ldr_row[1,], c("k_percent", "k_pct")))[1]
        ldr_age <- safe_num(coalesce_col(ldr_row[1,], c("age")))[1]
        ldr_team <- safe_chr(coalesce_col(ldr_row[1,], c("team")))[1]
        if (!is.na(ldr_pa)) season$pa <- season$pa %||% ldr_pa
        if (!is.na(ldr_hr)) season$hr <- season$hr %||% ldr_hr
        if (!is.na(ldr_sb)) season$sb <- season$sb %||% ldr_sb
        if (!is.na(ldr_avg)) season$avg <- season$avg %||% ldr_avg
        if (!is.na(ldr_obp)) season$obp <- season$obp %||% ldr_obp
        if (!is.na(ldr_slg)) season$slg <- season$slg %||% ldr_slg
        if (!is.na(ldr_ops)) season$ops <- season$ops %||% ldr_ops
        if (!is.na(ldr_iso)) season$iso <- season$iso %||% ldr_iso
        if (!is.na(ldr_woba)) season$woba <- season$woba %||% ldr_woba
        if (!is.na(ldr_bb_pct)) season$bb_pct <- season$bb_pct %||% ldr_bb_pct
        if (!is.na(ldr_k_pct)) season$k_pct <- season$k_pct %||% ldr_k_pct
        if (!is.na(ldr_age)) season$age <- season$age %||% ldr_age
        if (!is.na(ldr_team) && ldr_team != "") season$team <- season$team %||% ldr_team
      }

      tibble(
        name = p$player_name[[1]],
        team = season$team %||% p$team[[1]],
        age = season$age %||% p$age[[1]],
        mlbid = p$mlbid[[1]],
        fangraphs_id = p$fangraphs_id[[1]],
        fg_url = fg_url(p$fangraphs_id[[1]]),
        savant_url = savant_url(p$mlbid[[1]]),
        fg_profile = fg_link_formula(p$fangraphs_id[[1]]),
        savant_profile = savant_link_formula(p$mlbid[[1]]),

        t14_games = t14$games,
        t14_pa = t14$pa,
        t14_ab = t14$ab,
        t14_hr = t14$hr,
        t14_sb = t14$sb,
        t14_avg = t14$avg,
        t14_obp = t14$obp,
        t14_slg = t14$slg,
        t14_ops = t14$ops,
        t14_iso = t14$iso,
        t14_woba = t14$woba,
        t14_xwoba = sc14$xwoba,
        t14_xba = sc14$xba,
        t14_bb_pct = t14$bb_pct,
        t14_k_pct = t14$k_pct,
        t14_bb_minus_k_pct = ifelse(is.na(t14$bb_pct) | is.na(t14$k_pct), NA_real_, t14$bb_pct - t14$k_pct),
        t14_wrc_plus = t14$wrc_plus,
        t14_hard_hit_pct = sc14$hard_hit_pct %||% t14$hard_hit_pct,
        t14_barrel_pct = sc14$barrel_pct %||% t14$barrel_pct,
        t14_exit_velocity = sc14$exit_velocity %||% t14$exit_velocity,

        season_games = season$games,
        season_pa = season$pa,
        season_ab = season$ab,
        season_hr = season$hr,
        season_sb = season$sb,
        season_avg = season$avg,
        season_obp = season$obp,
        season_slg = season$slg,
        season_ops = season$ops,
        season_iso = season$iso,
        season_woba = season$woba,
        season_xwoba = sc_season$xwoba,
        season_xba = sc_season$xba,
        season_bb_pct = season$bb_pct,
        season_k_pct = season$k_pct,
        season_bb_minus_k_pct = ifelse(is.na(season$bb_pct) | is.na(season$k_pct), NA_real_, season$bb_pct - season$k_pct),
        season_wrc_plus = season$wrc_plus,
        season_hard_hit_pct = sc_season$hard_hit_pct %||% season$hard_hit_pct,
        season_barrel_pct = sc_season$barrel_pct %||% season$barrel_pct,
        season_exit_velocity = sc_season$exit_velocity %||% season$exit_velocity
      )
    })

  message(sprintf("  raw_hitters columns (%d): %s", ncol(out), paste(names(out), collapse = ", ")))

  add_percentiles(out, c(
    t14_xwoba = TRUE,
    t14_barrel_pct = TRUE,
    t14_hard_hit_pct = TRUE,
    t14_bb_minus_k_pct = TRUE,
    t14_sb = TRUE,
    t14_hr = TRUE,
    t14_ops = TRUE,
    t14_iso = TRUE,
    t14_xba = TRUE,
    t14_exit_velocity = TRUE,
    t14_wrc_plus = TRUE,
    season_xwoba = TRUE,
    season_barrel_pct = TRUE,
    season_hard_hit_pct = TRUE,
    season_bb_minus_k_pct = TRUE,
    season_sb = TRUE,
    season_hr = TRUE,
    season_ops = TRUE,
    season_iso = TRUE,
    season_xba = TRUE,
    season_exit_velocity = TRUE,
    season_wrc_plus = TRUE
  ), ref_df = ldr_ref)
}

build_raw_mlb_pitchers <- function(players, ldr_ref = NULL) {
  pool <- players |> filter(level == "MLB", role == "P")
  n_total <- nrow(pool)
  message(sprintf("Building raw MLB pitchers: %d players", n_total))
  if (n_total == 0) return(tibble())

  fg_ok <- !is.null(fg_game_logs_available) && fg_game_logs_available

  out <- pool |>
    mutate(row_id = row_number()) |>
    group_split(row_id, .keep = TRUE) |>
    map_dfr(function(p) {
      message(sprintf("  [%d/%d] %s", p$row_id[[1]], n_total, p$player_name[[1]]))

      if (fg_ok) {
        if (p$row_id[[1]] > 1) Sys.sleep(1.5)
        logs <- safe_fg_pitcher_logs(p$fangraphs_id[[1]], season_year)
        t14 <- agg_pitcher_logs(logs, t14_start, t14_end)
        season <- agg_pitcher_logs(logs)
        sc14 <- safe_statcast_pitcher(p$mlbid[[1]], t14_start, t14_end) |> agg_statcast_pitcher()
        sc_end_p <- min(t14_end, as.Date(paste0(season_year, "-12-31")))
        sc_season <- safe_statcast_pitcher(p$mlbid[[1]], paste0(season_year, "-01-01"), sc_end_p) |> agg_statcast_pitcher()
      } else {
        t14 <- agg_pitcher_logs(tibble())
        season <- agg_pitcher_logs(tibble())
        sc14 <- agg_statcast_pitcher(tibble())
        sc_season <- agg_statcast_pitcher(tibble())
      }

      # Pull leaderboard stats (works with both FG and alt cache data)
      ldr_p <- find_in_leaders(pitch_leaders, p$fangraphs_id[[1]], p$mlbid[[1]], p$player_name[[1]])
      ldr_stuff <- NA_real_; ldr_loc <- NA_real_; ldr_pitching <- NA_real_
      ldr_xfip_minus <- NA_real_; ldr_fip_minus <- NA_real_
      ldr_velo <- NA_real_; ldr_xfip <- NA_real_
      if (nrow(ldr_p) > 0) {
        ldr_stuff <- safe_num(coalesce_col(ldr_p[1,], c("sp_stuff", "stuff_plus")))[1]
        ldr_loc <- safe_num(coalesce_col(ldr_p[1,], c("sp_location", "location_plus")))[1]
        ldr_pitching <- safe_num(coalesce_col(ldr_p[1,], c("sp_pitching", "pitching_plus")))[1]
        ldr_xfip_minus <- safe_num(coalesce_col(ldr_p[1,], c("x_fip_2", "xfip_minus")))[1]
        ldr_fip_minus <- safe_num(coalesce_col(ldr_p[1,], c("fip_2", "fip_minus")))[1]
        ldr_velo <- safe_num(coalesce_col(ldr_p[1,], c("f_bv", "fbv", "velo")))[1]
        ldr_xfip <- safe_num(coalesce_col(ldr_p[1,], c("x_fip", "xfip")))[1]
        # Fill basic season stats from leaderboard
        ldr_era <- safe_num(coalesce_col(ldr_p[1,], c("era")))[1]
        ldr_whip <- safe_num(coalesce_col(ldr_p[1,], c("whip")))[1]
        ldr_ip <- safe_num(coalesce_col(ldr_p[1,], c("ip")))[1]
        ldr_g <- safe_num(coalesce_col(ldr_p[1,], c("g")))[1]
        ldr_gs <- safe_num(coalesce_col(ldr_p[1,], c("gs")))[1]
        ldr_k_pct <- safe_num(coalesce_col(ldr_p[1,], c("k_percent", "k_pct")))[1]
        ldr_bb_pct <- safe_num(coalesce_col(ldr_p[1,], c("bb_percent", "bb_pct")))[1]
        ldr_sv <- safe_num(coalesce_col(ldr_p[1,], c("sv")))[1]
        ldr_hld <- safe_num(coalesce_col(ldr_p[1,], c("hld")))[1]
        ldr_hr <- safe_num(coalesce_col(ldr_p[1,], c("hr")))[1]
        ldr_fip_val <- safe_num(coalesce_col(ldr_p[1,], c("fip")))[1]
        ldr_siera <- safe_num(coalesce_col(ldr_p[1,], c("siera")))[1]
        ldr_swstr <- safe_num(coalesce_col(ldr_p[1,], c("sw_str_percent", "sw_str_pct")))[1]
        ldr_hh <- safe_num(coalesce_col(ldr_p[1,], c("hard_hit_percent", "hard_hit_pct")))[1]
        ldr_age <- safe_num(coalesce_col(ldr_p[1,], c("age")))[1]
        ldr_team <- safe_chr(coalesce_col(ldr_p[1,], c("team")))[1]
        if (!is.na(ldr_era)) season$era <- season$era %||% ldr_era
        if (!is.na(ldr_whip)) season$whip <- season$whip %||% ldr_whip
        if (!is.na(ldr_ip)) season$ip <- season$ip %||% ldr_ip
        if (!is.na(ldr_g)) season$games <- season$games %||% ldr_g
        if (!is.na(ldr_gs)) season$gs <- season$gs %||% ldr_gs
        if (!is.na(ldr_k_pct)) season$k_pct <- season$k_pct %||% ldr_k_pct
        if (!is.na(ldr_bb_pct)) season$bb_pct <- season$bb_pct %||% ldr_bb_pct
        if (!is.na(ldr_fip_val)) season$fip <- season$fip %||% ldr_fip_val
        if (!is.na(ldr_siera)) season$siera <- season$siera %||% ldr_siera
        if (!is.na(ldr_swstr)) season$swstr_pct <- season$swstr_pct %||% ldr_swstr
        if (!is.na(ldr_hh)) season$hard_hit_pct_against <- season$hard_hit_pct_against %||% ldr_hh
        if (!is.na(ldr_hr)) season$hr <- season$hr %||% ldr_hr
        ldr_sh <- ifelse(is.na(ldr_sv), 0, ldr_sv) + ifelse(is.na(ldr_hld), 0, ldr_hld)
        if (ldr_sh > 0) season$saves_holds <- season$saves_holds %||% ldr_sh
        if (!is.na(ldr_age)) season$age <- season$age %||% ldr_age
        if (!is.na(ldr_team) && ldr_team != "") season$team <- season$team %||% ldr_team
      }

      tibble(
        name = p$player_name[[1]],
        team = season$team %||% p$team[[1]],
        age = season$age %||% p$age[[1]],
        mlbid = p$mlbid[[1]],
        fangraphs_id = p$fangraphs_id[[1]],
        fg_url = fg_url(p$fangraphs_id[[1]]),
        savant_url = savant_url(p$mlbid[[1]]),
        fg_profile = fg_link_formula(p$fangraphs_id[[1]]),
        savant_profile = savant_link_formula(p$mlbid[[1]]),

        t14_games = t14$games,
        t14_innings = t14$ip,
        t14_era = t14$era,
        t14_xera = sc14$xera,
        t14_whip = t14$whip,
        t14_fip = t14$fip,
        t14_xfip = t14$xfip,
        t14_siera = t14$siera,
        t14_k_pct = t14$k_pct,
        t14_bb_pct = t14$bb_pct,
        t14_k_minus_bb_pct = ifelse(is.na(t14$k_pct) | is.na(t14$bb_pct), NA_real_, t14$k_pct - t14$bb_pct),
        t14_velocity = sc14$velo %||% t14$velo %||% ldr_velo,
        t14_stuff_plus = ldr_stuff,
        t14_saves_holds = t14$saves_holds,
        t14_swstr_pct = t14$swstr_pct,
        t14_hard_hit_pct_against = sc14$hard_hit_pct_against %||% t14$hard_hit_pct_against,
        t14_hr_against = t14$hr,

        season_games = season$games,
        season_innings = season$ip,
        season_era = season$era,
        season_xera = sc_season$xera,
        season_whip = season$whip,
        season_fip = season$fip,
        season_xfip = season$xfip %||% ldr_xfip,
        season_siera = season$siera,
        season_k_pct = season$k_pct,
        season_bb_pct = season$bb_pct,
        season_k_minus_bb_pct = ifelse(is.na(season$k_pct) | is.na(season$bb_pct), NA_real_, season$k_pct - season$bb_pct),
        season_velocity = sc_season$velo %||% season$velo %||% ldr_velo,
        season_stuff_plus = ldr_stuff,
        season_location_plus = ldr_loc,
        season_pitching_plus = ldr_pitching,
        season_xfip_minus = ldr_xfip_minus,
        season_fip_minus = ldr_fip_minus,
        season_saves_holds = season$saves_holds,
        season_swstr_pct = season$swstr_pct,
        season_hard_hit_pct_against = sc_season$hard_hit_pct_against %||% season$hard_hit_pct_against,
        season_hr_against = season$hr
      )
    })

  add_percentiles(out, c(
    t14_k_minus_bb_pct = TRUE,
    t14_siera = FALSE,
    t14_xfip = FALSE,
    t14_swstr_pct = TRUE,
    t14_velocity = TRUE,
    t14_era = FALSE,
    t14_whip = FALSE,
    t14_saves_holds = TRUE,
    t14_hard_hit_pct_against = FALSE,
    t14_hr_against = FALSE,
    season_k_minus_bb_pct = TRUE,
    season_siera = FALSE,
    season_xfip = FALSE,
    season_swstr_pct = TRUE,
    season_velocity = TRUE,
    season_era = FALSE,
    season_whip = FALSE,
    season_saves_holds = TRUE,
    season_hard_hit_pct_against = FALSE,
    season_hr_against = FALSE,
    season_stuff_plus = TRUE,
    season_location_plus = TRUE,
    season_pitching_plus = TRUE,
    season_xfip_minus = FALSE,
    season_fip_minus = FALSE
  ), ref_df = ldr_ref)
}

build_raw_milb_hitters <- function(players) {
  pool <- players |> filter(level == "MiLB", role == "H")
  n_total <- nrow(pool)
  message(sprintf("Building raw MiLB hitters: %d players", n_total))
  if (n_total == 0) return(tibble())

  fg_ok <- !is.null(fg_game_logs_available) && fg_game_logs_available

  out <- pool |>
    mutate(row_id = row_number()) |>
    group_split(row_id, .keep = TRUE) |>
    map_dfr(function(p) {
      if (fg_ok && p$row_id[[1]] > 1) Sys.sleep(1.5)
      message(sprintf("  [%d/%d] %s", p$row_id[[1]], n_total, p$player_name[[1]]))
      logs <- if (fg_ok) safe_fg_milb_batter_logs(p$fangraphs_id[[1]], season_year) else tibble()
      t14 <- agg_hitter_logs(logs, t14_start, t14_end)
      season <- agg_hitter_logs(logs)

      # MLB Stats API fallback for MiLB hitters when FG game logs are empty
      if (is.na(season$avg) && !is.na(p$mlbid[[1]])) {
        for (sid in c(11, 12, 13, 14)) {
          milb_url <- sprintf("https://statsapi.mlb.com/api/v1/people/%s/stats?stats=season&season=%d&group=hitting&sportId=%d",
            p$mlbid[[1]], season_year, sid)
          milb_resp <- tryCatch(GET(milb_url), error = function(e) NULL)
          if (!is.null(milb_resp) && status_code(milb_resp) == 200) {
            milb_data <- content(milb_resp, as = "parsed")
            splits <- if (length(milb_data$stats) > 0) milb_data$stats[[1]]$splits else list()
            if (length(splits) > 0) {
              st <- splits[[1]]$stat
              season$avg <- season$avg %||% as.numeric(st$avg %||% NA)
              season$obp <- season$obp %||% as.numeric(st$obp %||% NA)
              season$slg <- season$slg %||% as.numeric(st$slg %||% NA)
              season$ops <- season$ops %||% as.numeric(st$ops %||% NA)
              season$iso <- if (!is.na(season$slg) && !is.na(season$avg)) season$slg - season$avg else NA_real_
              season$pa <- season$pa %||% (st$plateAppearances %||% NA)
              season$ab <- season$ab %||% (st$atBats %||% NA)
              season$h <- season$h %||% (st$hits %||% NA)
              season$hr <- season$hr %||% (st$homeRuns %||% NA)
              season$bb <- season$bb %||% (st$baseOnBalls %||% NA)
              season$so <- season$so %||% (st$strikeOuts %||% NA)
              season$sb <- season$sb %||% (st$stolenBases %||% NA)
              season$games <- season$games %||% (st$gamesPlayed %||% NA)
              t_pa <- st$plateAppearances %||% 0
              if (t_pa > 0) {
                season$bb_pct <- season$bb_pct %||% ((st$baseOnBalls %||% 0) / t_pa)
                season$k_pct <- season$k_pct %||% ((st$strikeOuts %||% 0) / t_pa)
              }
              message(sprintf("    [milb-api] %s: AVG=%s OBP=%s (sportId=%d)", p$player_name[[1]], st$avg, st$obp, sid))
              break
            }
          }
        }
      }

      tibble(
        name = p$player_name[[1]],
        team = season$team %||% p$team[[1]],
        level = season$level,
        age = season$age %||% p$age[[1]],
        mlbid = p$mlbid[[1]],
        fangraphs_id = p$fangraphs_id[[1]],
        fg_url = fg_url(p$fangraphs_id[[1]]),
        savant_url = savant_url(p$mlbid[[1]]),
        fg_profile = fg_link_formula(p$fangraphs_id[[1]]),
        savant_profile = savant_link_formula(p$mlbid[[1]]),

        t14_games = t14$games,
        t14_pa = t14$pa,
        t14_ab = t14$ab,
        t14_h = t14$h,
        t14_hr = t14$hr,
        t14_so = t14$so,
        t14_bb = t14$bb,
        t14_avg = t14$avg,
        t14_iso = t14$iso,
        t14_obp = t14$obp,
        t14_woba = t14$woba,
        t14_xwoba = NA_real_,
        t14_bb_pct = t14$bb_pct,
        t14_k_pct = t14$k_pct,
        t14_bb_minus_k_pct = ifelse(is.na(t14$bb_pct) | is.na(t14$k_pct), NA_real_, t14$bb_pct - t14$k_pct),
        t14_steals = t14$sb,
        t14_wrc_plus = t14$wrc_plus,
        t14_age_vs_level = NA_real_,
        t14_xba = NA_real_,
        t14_hard_hit_pct = t14$hard_hit_pct,
        t14_barrel_pct = t14$barrel_pct,
        t14_exit_velocity = t14$exit_velocity,

        season_games = season$games,
        season_pa = season$pa,
        season_ab = season$ab,
        season_h = season$h,
        season_hr = season$hr,
        season_so = season$so,
        season_bb = season$bb,
        season_avg = season$avg,
        season_iso = season$iso,
        season_obp = season$obp,
        season_woba = season$woba,
        season_xwoba = NA_real_,
        season_bb_pct = season$bb_pct,
        season_k_pct = season$k_pct,
        season_bb_minus_k_pct = ifelse(is.na(season$bb_pct) | is.na(season$k_pct), NA_real_, season$bb_pct - season$k_pct),
        season_steals = season$sb,
        season_wrc_plus = season$wrc_plus,
        season_age_vs_level = NA_real_,
        season_xba = NA_real_,
        season_hard_hit_pct = season$hard_hit_pct,
        season_barrel_pct = season$barrel_pct,
        season_exit_velocity = season$exit_velocity
      )
    })

  add_percentiles(out, c(
    t14_wrc_plus = TRUE,
    t14_bb_minus_k_pct = TRUE,
    t14_iso = TRUE,
    t14_obp = TRUE,
    t14_avg = TRUE,
    t14_hr = TRUE,
    t14_steals = TRUE,
    t14_woba = TRUE,
    t14_pa = TRUE,
    season_wrc_plus = TRUE,
    season_bb_minus_k_pct = TRUE,
    season_iso = TRUE,
    season_obp = TRUE,
    season_avg = TRUE,
    season_hr = TRUE,
    season_steals = TRUE,
    season_woba = TRUE,
    season_pa = TRUE
  ))
}

build_raw_milb_pitchers <- function(players) {
  pool <- players |> filter(level == "MiLB", role == "P")
  n_total <- nrow(pool)
  message(sprintf("Building raw MiLB pitchers: %d players", n_total))
  if (n_total == 0) return(tibble())

  fg_ok <- !is.null(fg_game_logs_available) && fg_game_logs_available

  out <- pool |>
    mutate(row_id = row_number()) |>
    group_split(row_id, .keep = TRUE) |>
    map_dfr(function(p) {
      if (fg_ok && p$row_id[[1]] > 1) Sys.sleep(1.5)
      message(sprintf("  [%d/%d] %s", p$row_id[[1]], n_total, p$player_name[[1]]))
      logs <- if (fg_ok) safe_fg_milb_pitcher_logs(p$fangraphs_id[[1]], season_year) else tibble()
      t14 <- agg_pitcher_logs(logs, t14_start, t14_end)
      season <- agg_pitcher_logs(logs)

      # MLB Stats API fallback for MiLB pitchers when FG game logs are empty
      if (is.na(season$era) && !is.na(p$mlbid[[1]])) {
        for (sid in c(11, 12, 13, 14)) {
          milb_url <- sprintf("https://statsapi.mlb.com/api/v1/people/%s/stats?stats=season&season=%d&group=pitching&sportId=%d",
            p$mlbid[[1]], season_year, sid)
          milb_resp <- tryCatch(GET(milb_url), error = function(e) NULL)
          if (!is.null(milb_resp) && status_code(milb_resp) == 200) {
            milb_data <- content(milb_resp, as = "parsed")
            splits <- if (length(milb_data$stats) > 0) milb_data$stats[[1]]$splits else list()
            if (length(splits) > 0) {
              st <- splits[[1]]$stat
              milb_ip <- parse_ip(st$inningsPitched %||% 0)
              season$era <- season$era %||% as.numeric(st$era %||% NA)
              season$whip <- season$whip %||% as.numeric(st$whip %||% NA)
              season$ip <- season$ip %||% as.numeric(st$inningsPitched %||% NA)
              season$games <- season$games %||% (st$gamesPitched %||% NA)
              season$gs <- season$gs %||% (st$gamesStarted %||% NA)
              season$so <- season$so %||% (st$strikeOuts %||% NA)
              season$bb <- season$bb %||% (st$baseOnBalls %||% NA)
              season$hr <- season$hr %||% (st$homeRuns %||% NA)
              season$er <- season$er %||% (st$earnedRuns %||% NA)
              t_bf <- st$battersFaced %||% 0
              if (t_bf > 0) {
                season$k_pct <- season$k_pct %||% ((st$strikeOuts %||% 0) / t_bf)
                season$bb_pct <- season$bb_pct %||% ((st$baseOnBalls %||% 0) / t_bf)
              }
              if (milb_ip > 0) {
                season$fip <- season$fip %||% (((13 * (st$homeRuns %||% 0)) + (3 * (st$baseOnBalls %||% 0)) - (2 * (st$strikeOuts %||% 0))) / milb_ip + 3.2)
              }
              message(sprintf("    [milb-api] %s: ERA=%s IP=%s (sportId=%d)", p$player_name[[1]], st$era, st$inningsPitched, sid))
              break
            }
          }
        }
      }

      tibble(
        name = p$player_name[[1]],
        team = season$team %||% p$team[[1]],
        level = season$level,
        mlbid = p$mlbid[[1]],
        fangraphs_id = p$fangraphs_id[[1]],
        fg_url = fg_url(p$fangraphs_id[[1]]),
        savant_url = savant_url(p$mlbid[[1]]),
        fg_profile = fg_link_formula(p$fangraphs_id[[1]]),
        savant_profile = savant_link_formula(p$mlbid[[1]]),

        t14_games = t14$games,
        t14_innings = t14$ip,
        t14_earned_runs = t14$er,
        t14_strikeouts = t14$so,
        t14_walks = t14$bb,
        t14_k_pct = t14$k_pct,
        t14_bb_pct = t14$bb_pct,
        t14_k_minus_bb_pct = ifelse(is.na(t14$k_pct) | is.na(t14$bb_pct), NA_real_, t14$k_pct - t14$bb_pct),
        t14_hr = t14$hr,
        t14_xera = NA_real_,
        t14_whip = t14$whip,
        t14_fip = t14$fip,
        t14_xfip = t14$xfip,
        t14_siera = t14$siera,
        t14_barrel_pct = t14$barrel_pct_against,
        t14_exit_velocity = t14$exit_velocity_against,
        t14_throwing_velocity = t14$velo,
        t14_holds_plus_saves = t14$saves_holds,

        season_games = season$games,
        season_innings = season$ip,
        season_earned_runs = season$er,
        season_strikeouts = season$so,
        season_walks = season$bb,
        season_k_pct = season$k_pct,
        season_bb_pct = season$bb_pct,
        season_k_minus_bb_pct = ifelse(is.na(season$k_pct) | is.na(season$bb_pct), NA_real_, season$k_pct - season$bb_pct),
        season_hr = season$hr,
        season_xera = NA_real_,
        season_whip = season$whip,
        season_fip = season$fip,
        season_xfip = season$xfip,
        season_siera = season$siera,
        season_barrel_pct = season$barrel_pct_against,
        season_exit_velocity = season$exit_velocity_against,
        season_throwing_velocity = season$velo,
        season_holds_plus_saves = season$saves_holds
      )
    })

  add_percentiles(out, c(
    t14_k_minus_bb_pct = TRUE,
    t14_fip = FALSE,
    t14_xfip = FALSE,
    t14_siera = FALSE,
    t14_throwing_velocity = TRUE,
    t14_whip = FALSE,
    t14_earned_runs = FALSE,
    t14_hr = FALSE,
    t14_holds_plus_saves = TRUE,
    season_k_minus_bb_pct = TRUE,
    season_fip = FALSE,
    season_xfip = FALSE,
    season_siera = FALSE,
    season_throwing_velocity = TRUE,
    season_whip = FALSE,
    season_earned_runs = FALSE,
    season_hr = FALSE,
    season_holds_plus_saves = TRUE
  ))
}

compute_asset_scores <- function(asset_df, raw_hitters, raw_pitchers, raw_milb_hitters, raw_milb_pitchers) {
  if (nrow(asset_df) == 0) {
    message("  asset_df is empty, writing column headers and returning empty scores")
    header_df <- tibble(
      Player = character(), Team = character(), Level = character(),
      Role = character(), MLBID = character(), `Fangraphs ID` = character()
    )
    tryCatch(safe_write_sheet(header_df, "asset_database"), error = function(e) message(sprintf("  Could not write asset_database headers: %s", conditionMessage(e))))
    return(tibble(
      player = character(), fantasy_team = character(), position = character(),
      team = character(), role = character(), mlbid = character(), fangraphs_id = character(),
      level = character(), asset_type = character(),
      current_score = numeric(), trend_score = numeric(), risk_score = numeric(),
      dynasty_war = numeric(), trade_value = numeric(), buy_low_flag = character(),
      x3yr_dynasty_war = numeric()
    ))
  }

  asset_df <- asset_df |> clean_names()

  # Find player name column
  if (!"player" %in% names(asset_df)) {
    for (cand in c("player_name", "name")) {
      found <- find_col_by_prefix(asset_df, cand)
      if (!is.null(found)) { asset_df <- asset_df |> rename(player = !!sym(found)); break }
    }
  }

  # Find other columns, handling numeric suffixes from duplicate sheet columns
  for (col_name in c("team", "level", "role", "mlbid", "fangraphs_id")) {
    if (!col_name %in% names(asset_df)) {
      found <- find_col_by_prefix(asset_df, col_name)
      if (!is.null(found)) {
        asset_df <- asset_df |> rename(!!col_name := !!sym(found))
      } else {
        asset_df[[col_name]] <- NA
      }
    }
  }

  empty_pool_tibble <- function() {
    tibble(
      player = character(), team = character(), mlbid = character(), fangraphs_id = character(),
      core_1 = numeric(), core_2 = numeric(), core_3 = numeric(), core_4 = numeric(), core_5 = numeric(),
      core_1_name = character(), core_2_name = character(), core_3_name = character(),
      core_4_name = character(), core_5_name = character(),
      current_score = numeric(), trend_score = numeric(), risk_score = numeric(), bucket = character()
    )
  }

  wh <- WEIGHTS$mlb_h_current
  wht <- WEIGHTS$mlb_h_trend
  if (nrow(raw_hitters) == 0) {
    mlb_h <- empty_pool_tibble()
  } else {
  mlb_h <- raw_hitters |>
    transmute(
      player = name, team, mlbid, fangraphs_id,
      core_1 = season_xwoba,
      core_2 = season_barrel_pct,
      core_3 = season_hard_hit_pct,
      core_4 = season_bb_minus_k_pct,
      core_5 = season_sb,
      core_1_name = "xwOBA",
      core_2_name = "Barrel%",
      core_3_name = "HardHit%",
      core_4_name = "BB%-K%",
      core_5_name = "SB",
      current_score = (
        wh[["xwoba"]] * coalesce(season_xwoba_pctile, 50) +
        wh[["barrel_pct"]] * coalesce(season_barrel_pct_pctile, 50) +
        wh[["hard_hit_pct"]] * coalesce(season_hard_hit_pct_pctile, 50) +
        wh[["bb_minus_k_pct"]] * coalesce(season_bb_minus_k_pct_pctile, 50) +
        wh[["sb"]] * coalesce(season_sb_pctile, 50) +
        wh[["hr"]] * coalesce(season_hr_pctile, 50) +
        wh[["ops"]] * coalesce(season_ops_pctile, 50) +
        wh[["iso"]] * coalesce(season_iso_pctile, 50) +
        wh[["xba"]] * coalesce(season_xba_pctile, 50) +
        wh[["exit_velocity"]] * coalesce(season_exit_velocity_pctile, 50)
      ),
      trend_score = (
        wht[["xwoba"]] * coalesce(t14_xwoba_pctile, 50) +
        wht[["barrel_pct"]] * coalesce(t14_barrel_pct_pctile, 50) +
        wht[["hard_hit_pct"]] * coalesce(t14_hard_hit_pct_pctile, 50) +
        wht[["bb_minus_k_pct"]] * coalesce(t14_bb_minus_k_pct_pctile, 50) +
        wht[["sb"]] * coalesce(t14_sb_pctile, 50) +
        wht[["hr"]] * coalesce(t14_hr_pctile, 50) +
        wht[["iso"]] * coalesce(t14_iso_pctile, 50) +
        wht[["exit_velocity"]] * coalesce(t14_exit_velocity_pctile, 50) +
        wht[["ops"]] * coalesce(t14_ops_pctile, 50)
      ),
      risk_score = (
        0.30 * coalesce(percentile_rank(season_k_pct, FALSE), 50) +
        0.25 * abs(coalesce(t14_xwoba_pctile, 50) - coalesce(season_xwoba_pctile, 50)) +
        0.15 * coalesce(percentile_rank(season_hard_hit_pct, FALSE), 50) +
        0.15 * coalesce(percentile_rank(season_bb_pct, FALSE), 50) +
        0.15 * abs(coalesce(t14_ops_pctile, 50) - coalesce(season_ops_pctile, 50))
      ),
      bucket = "MLB_H"
    )
  }

  wp <- WEIGHTS$mlb_p_current
  wpt <- WEIGHTS$mlb_p_trend
  if (nrow(raw_pitchers) == 0) {
    mlb_p <- empty_pool_tibble()
  } else {
  mlb_p <- raw_pitchers |>
    transmute(
      player = name, team, mlbid, fangraphs_id,
      core_1 = season_k_minus_bb_pct,
      core_2 = season_siera,
      core_3 = season_xfip,
      core_4 = season_swstr_pct,
      core_5 = season_velocity,
      core_1_name = "K-BB%",
      core_2_name = "SIERA",
      core_3_name = "xFIP",
      core_4_name = "SwStr%",
      core_5_name = "Velocity",
      current_score = (
        wp[["k_minus_bb_pct"]] * coalesce(season_k_minus_bb_pct_pctile, 50) +
        wp[["siera"]] * coalesce(season_siera_pctile, 50) +
        wp[["xfip"]] * coalesce(season_xfip_pctile, 50) +
        wp[["swstr_pct"]] * coalesce(season_swstr_pct_pctile, 50) +
        wp[["velocity"]] * coalesce(season_velocity_pctile, 50) +
        wp[["era"]] * coalesce(season_era_pctile, 50) +
        wp[["whip"]] * coalesce(season_whip_pctile, 50) +
        wp[["saves_holds"]] * coalesce(season_saves_holds_pctile, 50) +
        wp[["hard_hit_pct_against"]] * coalesce(season_hard_hit_pct_against_pctile, 50) +
        wp[["hr_against"]] * coalesce(season_hr_against_pctile, 50)
      ),
      trend_score = (
        wpt[["k_minus_bb_pct"]] * coalesce(t14_k_minus_bb_pct_pctile, 50) +
        wpt[["swstr_pct"]] * coalesce(t14_swstr_pct_pctile, 50) +
        wpt[["velocity"]] * coalesce(t14_velocity_pctile, 50) +
        wpt[["xfip"]] * coalesce(t14_xfip_pctile, 50) +
        wpt[["siera"]] * coalesce(t14_siera_pctile, 50) +
        wpt[["era"]] * coalesce(t14_era_pctile, 50) +
        wpt[["whip"]] * coalesce(t14_whip_pctile, 50) +
        wpt[["saves_holds"]] * coalesce(t14_saves_holds_pctile, 50) +
        wpt[["hard_hit_pct_against"]] * coalesce(t14_hard_hit_pct_against_pctile, 50)
      ),
      risk_score = (
        0.30 * coalesce(percentile_rank(season_bb_pct, TRUE), 50) +
        0.20 * coalesce(percentile_rank(season_hard_hit_pct_against, TRUE), 50) +
        0.15 * coalesce(percentile_rank(season_hr_against, TRUE), 50) +
        0.20 * abs(coalesce(t14_xfip_pctile, 50) - coalesce(season_xfip_pctile, 50)) +
        0.15 * ifelse(coalesce(season_saves_holds, 0) > 0 & coalesce(season_games, 0) > 0 & coalesce(season_innings, 999) < 80, 65, 35)
      ),
      bucket = "MLB_P"
    )
  }

  wmh <- WEIGHTS$milb_h_current
  wmht <- WEIGHTS$milb_h_trend
  if (nrow(raw_milb_hitters) == 0) {
    milb_h <- empty_pool_tibble()
  } else {
  milb_h <- raw_milb_hitters |>
    transmute(
      player = name, team, mlbid, fangraphs_id,
      core_1 = season_wrc_plus,
      core_2 = season_bb_minus_k_pct,
      core_3 = season_iso,
      core_4 = season_age_vs_level,
      core_5 = season_obp,
      core_1_name = "wRC+",
      core_2_name = "BB%-K%",
      core_3_name = "ISO",
      core_4_name = "AgeVsLevel",
      core_5_name = "OBP",
      current_score = (
        wmh[["wrc_plus"]] * coalesce(season_wrc_plus_pctile, 50) +
        wmh[["bb_minus_k_pct"]] * coalesce(season_bb_minus_k_pct_pctile, 50) +
        wmh[["iso"]] * coalesce(season_iso_pctile, 50) +
        wmh[["age_vs_level"]] * 50 +
        wmh[["obp"]] * coalesce(season_obp_pctile, 50) +
        wmh[["avg"]] * coalesce(season_avg_pctile, 50) +
        wmh[["hr"]] * coalesce(season_hr_pctile, 50) +
        wmh[["steals"]] * coalesce(season_steals_pctile, 50) +
        wmh[["woba"]] * coalesce(season_woba_pctile, 50) +
        wmh[["pa"]] * coalesce(season_pa_pctile, 50)
      ),
      trend_score = (
        wmht[["wrc_plus"]] * coalesce(t14_wrc_plus_pctile, 50) +
        wmht[["iso"]] * coalesce(t14_iso_pctile, 50) +
        wmht[["bb_minus_k_pct"]] * coalesce(t14_bb_minus_k_pct_pctile, 50) +
        wmht[["obp"]] * coalesce(percentile_rank(t14_obp, TRUE), 50) +
        wmht[["age_vs_level"]] * 50 +
        wmht[["hr"]] * coalesce(t14_hr_pctile, 50) +
        wmht[["steals"]] * coalesce(t14_steals_pctile, 50) +
        wmht[["avg"]] * coalesce(t14_avg_pctile, 50) +
        wmht[["pa"]] * coalesce(t14_pa_pctile, 50)
      ),
      risk_score = (
        0.30 * coalesce(percentile_rank(season_k_pct, TRUE), 50) +
        0.20 * coalesce(percentile_rank(season_bb_pct, FALSE), 50) +
        0.20 * coalesce(percentile_rank(season_wrc_plus, FALSE), 50) +
        0.15 * 50 +
        0.15 * coalesce(percentile_rank(season_pa, FALSE), 50)
      ),
      bucket = "MiLB_H"
    )
  }

  wmp <- WEIGHTS$milb_p_current
  wmpt <- WEIGHTS$milb_p_trend
  if (nrow(raw_milb_pitchers) == 0) {
    milb_p <- empty_pool_tibble()
  } else {
  milb_p <- raw_milb_pitchers |>
    transmute(
      player = name, team, mlbid, fangraphs_id,
      core_1 = season_k_minus_bb_pct,
      core_2 = season_fip,
      core_3 = season_xfip,
      core_4 = season_siera,
      core_5 = season_throwing_velocity,
      core_1_name = "K-BB%",
      core_2_name = "FIP",
      core_3_name = "xFIP",
      core_4_name = "SIERA",
      core_5_name = "Velocity",
      current_score = (
        wmp[["k_minus_bb_pct"]] * coalesce(season_k_minus_bb_pct_pctile, 50) +
        wmp[["fip"]] * coalesce(season_fip_pctile, 50) +
        wmp[["xfip"]] * coalesce(season_xfip_pctile, 50) +
        wmp[["siera"]] * coalesce(season_siera_pctile, 50) +
        wmp[["velocity"]] * coalesce(season_throwing_velocity_pctile, 50) +
        wmp[["whip"]] * coalesce(season_whip_pctile, 50) +
        wmp[["earned_runs"]] * coalesce(percentile_rank(season_earned_runs, FALSE), 50) +
        wmp[["hr"]] * coalesce(percentile_rank(season_hr, FALSE), 50) +
        wmp[["holds_plus_saves"]] * coalesce(season_holds_plus_saves_pctile, 50) +
        wmp[["placeholder"]] * 50
      ),
      trend_score = (
        wmpt[["k_minus_bb_pct"]] * coalesce(t14_k_minus_bb_pct_pctile, 50) +
        wmpt[["xfip"]] * coalesce(t14_xfip_pctile, 50) +
        wmpt[["siera"]] * coalesce(t14_siera_pctile, 50) +
        wmpt[["velocity"]] * coalesce(t14_throwing_velocity_pctile, 50) +
        wmpt[["fip"]] * coalesce(t14_fip_pctile, 50) +
        wmpt[["whip"]] * coalesce(t14_whip_pctile, 50) +
        wmpt[["earned_runs"]] * coalesce(percentile_rank(t14_earned_runs, FALSE), 50) +
        wmpt[["hr"]] * coalesce(percentile_rank(t14_hr, FALSE), 50) +
        wmpt[["placeholder"]] * 50
      ),
      risk_score = (
        0.30 * coalesce(percentile_rank(season_bb_pct, TRUE), 50) +
        0.20 * coalesce(percentile_rank(season_hr, TRUE), 50) +
        0.20 * rowMeans(cbind(
          coalesce(percentile_rank(season_fip, TRUE), 50),
          coalesce(percentile_rank(season_xfip, TRUE), 50)
        ), na.rm = TRUE) +
        0.15 * 50 +
        0.15 * ifelse(coalesce(season_holds_plus_saves, 0) > 0, 55, 45)
      ),
      bucket = "MiLB_P"
    )
  }

  pool <- bind_rows(mlb_h, mlb_p, milb_h, milb_p) |>
    mutate(
      player_clean = norm_name(player),
      team_clean = norm_name(team),
      current_score = round(current_score, 1),
      trend_score = round(trend_score, 1),
      risk_score = round(risk_score, 1)
    )

  message(sprintf("  pool: %d rows x %d cols: %s", nrow(pool), ncol(pool), paste(names(pool), collapse = ", ")))
  message(sprintf("  asset_df: %d rows x %d cols: %s", nrow(asset_df), ncol(asset_df), paste(names(asset_df), collapse = ", ")))

  # Keep only identifying columns from asset_df to avoid name collisions
  # (the sheet may carry output columns from a previous run)
  out <- asset_df |>
    select(player, team, level, role, mlbid, fangraphs_id) |>
    mutate(
      mlbid = safe_chr(mlbid),
      fangraphs_id = safe_chr(fangraphs_id),
      player_clean = norm_name(player),
      team_clean = norm_name(team)
    ) |>
    left_join(pool |> select(-player, -team, -mlbid, -fangraphs_id), by = "player_clean") |>
    mutate(
      prospect_bonus = case_when(level == "MiLB" ~ WAR_PARAMS$prospect_bonus, TRUE ~ WAR_PARAMS$mlb_prospect_bonus),
      future_bonus = case_when(level == "MiLB" ~ WAR_PARAMS$future_bonus_prospect, TRUE ~ WAR_PARAMS$future_bonus_mlb),
      extra_prospect_bump = case_when(level == "MiLB" ~ WAR_PARAMS$extra_prospect_bump, TRUE ~ 0.00),
      current_war = round((current_score / WAR_PARAMS$current_war_score_div) - (risk_score / WAR_PARAMS$current_war_risk_div), 2),
      future_war = round((trend_score / WAR_PARAMS$future_score_div) + future_bonus - (risk_score / WAR_PARAMS$future_risk_div), 2),
      dynasty_war = round((current_score / WAR_PARAMS$dynasty_score_div) + prospect_bonus - (risk_score / WAR_PARAMS$dynasty_risk_div), 2),
      dynasty_war_3yr = round(current_war + (future_war * WAR_PARAMS$future_war_multiplier) + extra_prospect_bump, 2),
      trade_value = round(dynasty_war_3yr * WAR_PARAMS$trade_value_multiplier, 0)
    ) |>
    select(
      player, team, level, role, mlbid, fangraphs_id,
      core_1_name, core_1,
      core_2_name, core_2,
      core_3_name, core_3,
      core_4_name, core_4,
      core_5_name, core_5,
      current_score, trend_score, risk_score,
      current_war, future_war, dynasty_war, dynasty_war_3yr, trade_value
    )

  out <- out |>
    mutate(
      current_score_pctile = percentile_rank(current_score, TRUE),
      trend_score_pctile = percentile_rank(trend_score, TRUE),
      risk_score_pctile = percentile_rank(risk_score, FALSE),
      current_war_pctile = percentile_rank(current_war, TRUE),
      future_war_pctile = percentile_rank(future_war, TRUE),
      dynasty_war_pctile = percentile_rank(dynasty_war, TRUE),
      dynasty_war_3yr_pctile = percentile_rank(dynasty_war_3yr, TRUE),
      trade_value_pctile = percentile_rank(trade_value, TRUE)
    ) |>
    arrange(desc(trade_value))

  out
}

compute_free_agents <- function(fa_df) {
  empty_list <- list(
    fa_hitters = tibble(Name = character(), Team = character(), Age = numeric(), Position = character(),
                        PA = numeric(), HR = numeric(), SB = numeric(), AVG = numeric(), OBP = numeric(),
                        OPS = numeric(), xwOBA = numeric(), `Barrel%` = numeric(), `HardHit%` = numeric(),
                        `BB-K%` = numeric(), Score = numeric()),
    fa_sp = tibble(Name = character(), Team = character(), Age = numeric(), IP = numeric(), GS = numeric(),
                   ERA = numeric(), WHIP = numeric(), `K%` = numeric(), `BB%` = numeric(), FIP = numeric(),
                   xFIP = numeric(), SIERA = numeric(), Velocity = numeric(), `SwStr%` = numeric(), Score = numeric()),
    fa_rp = tibble(Name = character(), Team = character(), Age = numeric(), IP = numeric(),
                   ERA = numeric(), WHIP = numeric(), `K%` = numeric(), `BB%` = numeric(), FIP = numeric(),
                   xFIP = numeric(), `SV+HLD` = numeric(), Velocity = numeric(), `SwStr%` = numeric(), Score = numeric()),
    fa_prospects = tibble(Name = character(), Team = character(), Age = numeric(), Position = character(),
                          DD_Rank = numeric(), BP_Rank = numeric(), Score = numeric())
  )

  if (nrow(fa_df) == 0) {
    message("  fa_df is empty, returning empty categories")
    return(empty_list)
  }

  fa_df <- fa_df |> clean_names()

  # Unlist any list-type columns from Google Sheets (mixed types / empty cells)
  fa_df <- fa_df |>
    mutate(across(where(is.list), ~sapply(., function(x) if (is.null(x) || length(x) == 0) NA else x[[1]])))

  # Resolve column names
  if (!"player" %in% names(fa_df)) {
    for (cand in c("player_name", "name")) {
      found <- find_col_by_prefix(fa_df, cand)
      if (!is.null(found)) { fa_df <- fa_df |> rename(player = !!sym(found)); break }
    }
  }
  for (col_name in c("team", "position", "age", "fangraphs_id", "mlbid", "ineligible", "dd", "bp")) {
    if (!col_name %in% names(fa_df)) {
      found <- find_col_by_prefix(fa_df, col_name)
      if (!is.null(found)) {
        fa_df <- fa_df |> rename(!!col_name := !!sym(found))
      } else {
        fa_df[[col_name]] <- NA
      }
    }
  }

  fa_df <- fa_df |>
    mutate(
      player_clean = norm_name(player),
      team_clean = norm_name(team),
      age = safe_num(sapply(age, function(x) if (is.null(x) || length(x) == 0) NA else x[[1]])),
      position = ifelse(is.na(position) | position == "#REF!", "Unknown", safe_chr(position)),
      fangraphs_id = safe_chr(fangraphs_id),
      dd = safe_num(sapply(dd, function(x) if (is.null(x) || length(x) == 0) NA else x[[1]])),
      bp = safe_num(sapply(bp, function(x) if (is.null(x) || length(x) == 0) NA else x[[1]]))
    ) |>
    filter(is.na(ineligible) | ineligible == "")

  message(sprintf("  FA pool after filtering: %d players", nrow(fa_df)))

  # Build batter reference from leaderboard
  bat_ref <- bat_leaders |>
    transmute(
      fg_id = safe_chr(coalesce_col(pick(everything()), c("playerid"))),
      name_ref = norm_name(coalesce_col(pick(everything()), c("name", "player_name"))),
      team_ref = norm_name(coalesce_col(pick(everything()), c("team"))),
      ref_age = safe_num(coalesce_col(pick(everything()), c("age"))),
      pa = safe_num(coalesce_col(pick(everything()), c("pa"))),
      hr = safe_num(coalesce_col(pick(everything()), c("hr"))),
      sb = safe_num(coalesce_col(pick(everything()), c("sb"))),
      avg = safe_num(coalesce_col(pick(everything()), c("avg"))),
      obp = safe_num(coalesce_col(pick(everything()), c("obp"))),
      ops = safe_num(coalesce_col(pick(everything()), c("ops"))),
      iso = safe_num(coalesce_col(pick(everything()), c("iso"))),
      woba = safe_num(coalesce_col(pick(everything()), c("woba"))),
      xwoba = safe_num(coalesce_col(pick(everything()), c("xwoba", "x_woba"))),
      xba = safe_num(coalesce_col(pick(everything()), c("xba", "x_ba"))),
      bb_pct = safe_num(coalesce_col(pick(everything()), c("bb_percent", "bb_pct"))),
      k_pct = safe_num(coalesce_col(pick(everything()), c("k_percent", "k_pct"))),
      hard_hit_pct = safe_num(coalesce_col(pick(everything()), c("hard_hit_percent", "hard_hit_pct"))),
      barrel_pct = safe_num(coalesce_col(pick(everything()), c("barrel_batted_rate", "barrel_pct"))),
      exit_velocity = safe_num(coalesce_col(pick(everything()), c("ev", "exit_velocity")))
    ) |>
    mutate(bb_minus_k_pct = ifelse(!is.na(bb_pct) & !is.na(k_pct), bb_pct - k_pct, NA_real_))

  # Build pitcher reference from leaderboard
  pitch_ref <- pitch_leaders |>
    transmute(
      fg_id = safe_chr(coalesce_col(pick(everything()), c("playerid"))),
      name_ref = norm_name(coalesce_col(pick(everything()), c("name", "player_name"))),
      team_ref = norm_name(coalesce_col(pick(everything()), c("team"))),
      ref_age = safe_num(coalesce_col(pick(everything()), c("age"))),
      g = safe_num(coalesce_col(pick(everything()), c("g"))),
      gs = safe_num(coalesce_col(pick(everything()), c("gs"))),
      ip = safe_num(coalesce_col(pick(everything()), c("ip"))),
      era = safe_num(coalesce_col(pick(everything()), c("era"))),
      whip = safe_num(coalesce_col(pick(everything()), c("whip"))),
      k_pct = safe_num(coalesce_col(pick(everything()), c("k_percent", "k_pct"))),
      bb_pct = safe_num(coalesce_col(pick(everything()), c("bb_percent", "bb_pct"))),
      fip = safe_num(coalesce_col(pick(everything()), c("fip"))),
      xfip = safe_num(coalesce_col(pick(everything()), c("x_fip", "xfip"))),
      siera = safe_num(coalesce_col(pick(everything()), c("siera"))),
      velocity = safe_num(coalesce_col(pick(everything()), c("f_bv", "fbv"))),
      sv = safe_num(coalesce_col(pick(everything()), c("sv"))),
      hld = safe_num(coalesce_col(pick(everything()), c("hld"))),
      swstr_pct = safe_num(coalesce_col(pick(everything()), c("sw_str_percent", "sw_str_pct"))),
      hard_hit_pct = safe_num(coalesce_col(pick(everything()), c("hard_hit_percent", "hard_hit_pct"))),
      hr_against = safe_num(coalesce_col(pick(everything()), c("hr")))
    ) |>
    mutate(
      saves_holds = ifelse(is.na(sv), 0, sv) + ifelse(is.na(hld), 0, hld),
      k_minus_bb_pct = ifelse(!is.na(k_pct) & !is.na(bb_pct), k_pct - bb_pct, NA_real_)
    )

  # Join FA to batter leaderboard: FG ID -> MLB ID -> name fallback
  fa_bat <- fa_df |>
    inner_join(bat_ref, by = c("fangraphs_id" = "fg_id")) |>
    filter(!is.na(pa) & pa > 0)
  # MLB ID fallback for unmatched (cache uses MLB IDs as playerid)
  if ("mlbid" %in% names(fa_df)) {
    unmatched_mlb_bat <- fa_df |>
      filter(!player_clean %in% fa_bat$player_clean) |>
      mutate(mlbid_chr = safe_chr(mlbid)) |>
      inner_join(bat_ref, by = c("mlbid_chr" = "fg_id")) |>
      filter(!is.na(pa) & pa > 0)
    fa_bat <- bind_rows(fa_bat, unmatched_mlb_bat) |> distinct(player_clean, .keep_all = TRUE)
  }
  # Name fallback for still-unmatched
  unmatched_bat <- fa_df |>
    filter(!player_clean %in% fa_bat$player_clean) |>
    inner_join(bat_ref, by = c("player_clean" = "name_ref")) |>
    filter(!is.na(pa) & pa > 0)
  fa_bat <- bind_rows(fa_bat, unmatched_bat) |> distinct(player_clean, .keep_all = TRUE)

  # Join FA to pitcher leaderboard: FG ID -> MLB ID -> name fallback
  fa_pitch <- fa_df |>
    inner_join(pitch_ref, by = c("fangraphs_id" = "fg_id")) |>
    filter(!is.na(ip) & ip > 0)
  if ("mlbid" %in% names(fa_df)) {
    unmatched_mlb_pitch <- fa_df |>
      filter(!player_clean %in% fa_pitch$player_clean) |>
      mutate(mlbid_chr = safe_chr(mlbid)) |>
      inner_join(pitch_ref, by = c("mlbid_chr" = "fg_id")) |>
      filter(!is.na(ip) & ip > 0)
    fa_pitch <- bind_rows(fa_pitch, unmatched_mlb_pitch) |> distinct(player_clean, .keep_all = TRUE)
  }
  unmatched_pitch <- fa_df |>
    filter(!player_clean %in% fa_pitch$player_clean) |>
    inner_join(pitch_ref, by = c("player_clean" = "name_ref")) |>
    filter(!is.na(ip) & ip > 0)
  fa_pitch <- bind_rows(fa_pitch, unmatched_pitch) |> distinct(player_clean, .keep_all = TRUE)

  message(sprintf("  FA matched: %d hitters, %d pitchers", nrow(fa_bat), nrow(fa_pitch)))

  # Helper: replace NA percentiles with neutral 50th percentile
  na50 <- function(x) ifelse(is.na(x), 50, x)

  # --- FA HITTERS (Top 10) ---
  fa_hitters_out <- empty_list$fa_hitters
  if (nrow(fa_bat) > 0) {
    wh <- WEIGHTS$mlb_h_current
    scored <- fa_bat |>
      mutate(
        xwoba_p = na50(percentile_rank(xwoba, TRUE)), barrel_pct_p = na50(percentile_rank(barrel_pct, TRUE)),
        hard_hit_pct_p = na50(percentile_rank(hard_hit_pct, TRUE)), bb_minus_k_pct_p = na50(percentile_rank(bb_minus_k_pct, TRUE)),
        sb_p = na50(percentile_rank(sb, TRUE)), hr_p = na50(percentile_rank(hr, TRUE)),
        ops_p = na50(percentile_rank(ops, TRUE)), iso_p = na50(percentile_rank(iso, TRUE)),
        xba_p = na50(percentile_rank(xba, TRUE)), ev_p = na50(percentile_rank(exit_velocity, TRUE)),
        score = round(
          wh[["xwoba"]] * xwoba_p + wh[["barrel_pct"]] * barrel_pct_p +
          wh[["hard_hit_pct"]] * hard_hit_pct_p + wh[["bb_minus_k_pct"]] * bb_minus_k_pct_p +
          wh[["sb"]] * sb_p + wh[["hr"]] * hr_p + wh[["ops"]] * ops_p +
          wh[["iso"]] * iso_p + wh[["xba"]] * xba_p + wh[["exit_velocity"]] * ev_p, 1)
      ) |>
      arrange(desc(score)) |>
      slice_head(n = 10)
    fa_hitters_out <- scored |>
      transmute(Name = player, Team = team, Age = age, Position = position,
                PA = round(pa), HR = round(hr), SB = round(sb),
                AVG = round(avg, 3), OBP = round(obp, 3), OPS = round(ops, 3),
                xwOBA = round(xwoba, 3), `Barrel%` = round(barrel_pct * 100, 1),
                `HardHit%` = round(hard_hit_pct * 100, 1),
                `BB-K%` = round(bb_minus_k_pct * 100, 1), Score = score)
  }

  # --- SP vs RP split ---
  fa_sp_pool <- fa_pitch |> filter(!is.na(gs) & gs > 0 & (gs / g) >= 0.5)
  fa_rp_pool <- fa_pitch |> filter(is.na(gs) | gs == 0 | (gs / g) < 0.5)
  # Also use position hint for borderline cases
  rp_by_pos <- fa_pitch |> filter(grepl("RP", position, ignore.case = TRUE)) |> pull(player_clean)
  fa_rp_pool <- bind_rows(fa_rp_pool, fa_sp_pool |> filter(player_clean %in% rp_by_pos)) |> distinct(player_clean, .keep_all = TRUE)
  fa_sp_pool <- fa_sp_pool |> filter(!player_clean %in% rp_by_pos)

  message(sprintf("  FA pitchers split: %d SP, %d RP", nrow(fa_sp_pool), nrow(fa_rp_pool)))

  # --- FA STARTING PITCHERS (Top 10) ---
  fa_sp_out <- empty_list$fa_sp
  if (nrow(fa_sp_pool) > 0) {
    wp <- WEIGHTS$mlb_p_current
    scored_sp <- fa_sp_pool |>
      mutate(
        k_minus_bb_p = na50(percentile_rank(k_minus_bb_pct, TRUE)), siera_p = na50(percentile_rank(siera, FALSE)),
        xfip_p = na50(percentile_rank(xfip, FALSE)), swstr_p = na50(percentile_rank(swstr_pct, TRUE)),
        velo_p = na50(percentile_rank(velocity, TRUE)), era_p = na50(percentile_rank(era, FALSE)),
        whip_p = na50(percentile_rank(whip, FALSE)), sh_p = na50(percentile_rank(saves_holds, TRUE)),
        hh_p = na50(percentile_rank(hard_hit_pct, FALSE)), hra_p = na50(percentile_rank(hr_against, FALSE)),
        score = round(
          wp[["k_minus_bb_pct"]] * k_minus_bb_p + wp[["siera"]] * siera_p +
          wp[["xfip"]] * xfip_p + wp[["swstr_pct"]] * swstr_p + wp[["velocity"]] * velo_p +
          wp[["era"]] * era_p + wp[["whip"]] * whip_p + wp[["saves_holds"]] * sh_p +
          wp[["hard_hit_pct_against"]] * hh_p + wp[["hr_against"]] * hra_p, 1)
      ) |>
      arrange(desc(score)) |>
      slice_head(n = 10)
    fa_sp_out <- scored_sp |>
      transmute(Name = player, Team = team, Age = age, IP = round(ip, 1), GS = round(gs),
                ERA = round(era, 2), WHIP = round(whip, 2), `K%` = round(k_pct * 100, 1),
                `BB%` = round(bb_pct * 100, 1), FIP = round(fip, 2), xFIP = round(xfip, 2),
                SIERA = round(siera, 2), Velocity = round(velocity, 1),
                `SwStr%` = round(swstr_pct * 100, 1), Score = score)
  }

  # --- FA RELIEF PITCHERS (Top 10) ---
  fa_rp_out <- empty_list$fa_rp
  if (nrow(fa_rp_pool) > 0) {
    wp <- WEIGHTS$mlb_p_current
    scored_rp <- fa_rp_pool |>
      mutate(
        k_minus_bb_p = na50(percentile_rank(k_minus_bb_pct, TRUE)), siera_p = na50(percentile_rank(siera, FALSE)),
        xfip_p = na50(percentile_rank(xfip, FALSE)), swstr_p = na50(percentile_rank(swstr_pct, TRUE)),
        velo_p = na50(percentile_rank(velocity, TRUE)), era_p = na50(percentile_rank(era, FALSE)),
        whip_p = na50(percentile_rank(whip, FALSE)), sh_p = na50(percentile_rank(saves_holds, TRUE)),
        hh_p = na50(percentile_rank(hard_hit_pct, FALSE)), hra_p = na50(percentile_rank(hr_against, FALSE)),
        score = round(
          wp[["k_minus_bb_pct"]] * k_minus_bb_p + wp[["siera"]] * siera_p +
          wp[["xfip"]] * xfip_p + wp[["swstr_pct"]] * swstr_p + wp[["velocity"]] * velo_p +
          wp[["era"]] * era_p + wp[["whip"]] * whip_p + wp[["saves_holds"]] * sh_p +
          wp[["hard_hit_pct_against"]] * hh_p + wp[["hr_against"]] * hra_p, 1)
      ) |>
      arrange(desc(score)) |>
      slice_head(n = 10)
    fa_rp_out <- scored_rp |>
      transmute(Name = player, Team = team, Age = age, IP = round(ip, 1),
                ERA = round(era, 2), WHIP = round(whip, 2), `K%` = round(k_pct * 100, 1),
                `BB%` = round(bb_pct * 100, 1), FIP = round(fip, 2), xFIP = round(xfip, 2),
                `SV+HLD` = round(saves_holds), Velocity = round(velocity, 1),
                `SwStr%` = round(swstr_pct * 100, 1), Score = score)
  }

  # --- FA PROSPECTS (Top 10) ---
  # Players not found in either MLB leaderboard with DD or BP rankings
  matched_ids <- unique(c(fa_bat$player_clean, fa_pitch$player_clean))
  fa_prospects <- fa_df |>
    filter(!player_clean %in% matched_ids) |>
    filter(!is.na(dd) | !is.na(bp)) |>
    mutate(
      dd_p = percentile_rank(dd, FALSE),  # lower rank = better
      bp_p = percentile_rank(bp, FALSE),
      score = round(ifelse(!is.na(dd_p) & !is.na(bp_p), 0.5 * dd_p + 0.5 * bp_p,
                           coalesce(dd_p, bp_p)), 1)
    ) |>
    arrange(desc(score)) |>
    slice_head(n = 10)
  fa_prospects_out <- empty_list$fa_prospects
  if (nrow(fa_prospects) > 0) {
    fa_prospects_out <- fa_prospects |>
      transmute(Name = player, Team = team, Age = age, Position = position,
                DD_Rank = dd, BP_Rank = bp, Score = score)
  }

  message(sprintf("  FA results: %d hitters, %d SP, %d RP, %d prospects",
                  nrow(fa_hitters_out), nrow(fa_sp_out), nrow(fa_rp_out), nrow(fa_prospects_out)))

  list(fa_hitters = fa_hitters_out, fa_sp = fa_sp_out, fa_rp = fa_rp_out, fa_prospects = fa_prospects_out)
}

main <- function() {
  started_at <- with_tz(now("America/Chicago"), "America/Chicago")
  message(sprintf("=== Fantasy Baseball Dashboard Refresh ==="))
  message(sprintf("Season year: %d | Refresh type: %s", season_year, refresh_type))
  message(sprintf("T14 window: %s to %s", t14_start, t14_end))

  all_tabs <- sheet_names(sheet_id)
  message(sprintf("  Available tabs: %s", paste(all_tabs, collapse = ", ")))

  find_tab <- function(candidates) {
    for (c in candidates) {
      match <- all_tabs[tolower(all_tabs) == tolower(c)]
      if (length(match) > 0) return(match[1])
    }
    candidates[1]
  }

  roster_tab_name <- find_tab(c("Test", "test", "Roster", "roster", "My Roster"))
  message(sprintf("  Using roster tab: '%s'", roster_tab_name))

  message("Reading input tabs from Google Sheets...")
  test_tab <- safe_read_sheet(roster_tab_name)
  message(sprintf("  %s: %d rows x %d cols", roster_tab_name, nrow(test_tab), ncol(test_tab)))
  asset_tab <- safe_read_sheet("asset_database")
  message(sprintf("  asset_database: %d rows x %d cols", nrow(asset_tab), ncol(asset_tab)))
  fa_tab <- safe_read_sheet("Free Agent Helper")
  message(sprintf("  Free Agent Helper: %d rows x %d cols", nrow(fa_tab), ncol(fa_tab)))

  message("Resolving player IDs against FanGraphs leaderboards...")
  test_players <- resolve_player_ids(test_tab)
  message(sprintf("  Resolved %d players (%d H, %d P)",
    nrow(test_players),
    sum(test_players$role == "H", na.rm = TRUE),
    sum(test_players$role == "P", na.rm = TRUE)
  ))

  raw_hitters <- build_raw_mlb_hitters(test_players, ldr_ref = bat_leaders)
  raw_pitchers <- build_raw_mlb_pitchers(test_players, ldr_ref = pitch_leaders)
  raw_milb_hitters <- build_raw_milb_hitters(test_players)
  raw_milb_pitchers <- build_raw_milb_pitchers(test_players)

  message("Computing asset scores and free agent rankings...")
  asset_scores <- compute_asset_scores(asset_tab, raw_hitters, raw_pitchers, raw_milb_hitters, raw_milb_pitchers)
  fa_results <- compute_free_agents(fa_tab)
  message(sprintf("  Asset scores: %d rows", nrow(asset_scores)))

  message("Writing output tabs to Google Sheets...")
  safe_write_sheet(raw_hitters, "raw_hitters")
  message(sprintf("  raw_hitters: %d rows", nrow(raw_hitters)))
  safe_write_sheet(raw_pitchers, "raw_pitchers")
  message(sprintf("  raw_pitchers: %d rows", nrow(raw_pitchers)))
  safe_write_sheet(raw_milb_hitters, "raw_milb_hitters")
  message(sprintf("  raw_milb_hitters: %d rows", nrow(raw_milb_hitters)))
  safe_write_sheet(raw_milb_pitchers, "raw_milb_pitchers")
  message(sprintf("  raw_milb_pitchers: %d rows", nrow(raw_milb_pitchers)))
  safe_write_sheet(asset_scores, "asset_scores")
  message(sprintf("  asset_scores: %d rows", nrow(asset_scores)))
  safe_write_sheet(fa_results$fa_hitters, "fa_hitters")
  message(sprintf("  fa_hitters: %d rows", nrow(fa_results$fa_hitters)))
  safe_write_sheet(fa_results$fa_sp, "fa_sp")
  message(sprintf("  fa_sp: %d rows", nrow(fa_results$fa_sp)))
  safe_write_sheet(fa_results$fa_rp, "fa_rp")
  message(sprintf("  fa_rp: %d rows", nrow(fa_results$fa_rp)))
  safe_write_sheet(fa_results$fa_prospects, "fa_prospects")
  message(sprintf("  fa_prospects: %d rows", nrow(fa_results$fa_prospects)))

  finished_at <- with_tz(now("America/Chicago"), "America/Chicago")
  duration <- round(as.numeric(difftime(finished_at, started_at, units = "mins")), 2)
  last_update <- tibble(
    refresh_status = "success",
    refresh_type = refresh_type,
    started_at = as.character(started_at),
    finished_at = as.character(finished_at),
    duration_minutes = duration,
    season_year_used = season_year,
    raw_hitters_rows = nrow(raw_hitters),
    raw_pitchers_rows = nrow(raw_pitchers),
    raw_milb_hitters_rows = nrow(raw_milb_hitters),
    raw_milb_pitchers_rows = nrow(raw_milb_pitchers),
    asset_scores_rows = nrow(asset_scores),
    fa_hitters_rows = nrow(fa_results$fa_hitters),
    fa_sp_rows = nrow(fa_results$fa_sp),
    fa_rp_rows = nrow(fa_results$fa_rp),
    fa_prospects_rows = nrow(fa_results$fa_prospects),
    notes = "Percentiles added to raw tabs and asset scores. Unsupported source fields remain NA."
  )
  safe_write_sheet(last_update, "last_update")
  message(sprintf("=== Refresh complete in %.1f minutes ===", duration))
}

tryCatch(
  main(),
  error = function(e) {
    fail_df <- tibble(
      refresh_status = "failed",
      refresh_type = refresh_type,
      started_at = as.character(with_tz(now("America/Chicago"), "America/Chicago")),
      finished_at = as.character(with_tz(now("America/Chicago"), "America/Chicago")),
      duration_minutes = NA_real_,
      season_year_used = season_year,
      raw_hitters_rows = NA_real_,
      raw_pitchers_rows = NA_real_,
      raw_milb_hitters_rows = NA_real_,
      raw_milb_pitchers_rows = NA_real_,
      asset_scores_rows = NA_real_,
      free_agent_rows = NA_real_,
      notes = substr(conditionMessage(e), 1, 450)
    )
    try(safe_write_sheet(fail_df, "last_update"), silent = TRUE)
    stop(e)
  }
)
