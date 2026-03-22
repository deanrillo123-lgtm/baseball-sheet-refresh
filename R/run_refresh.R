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
})

`%||%` <- function(x, y) if (is.null(x) || length(x) == 0 || all(is.na(x))) y else x

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
  tryCatch(
    retry_with_backoff(function() read_sheet(sheet_id, sheet = tab) |> clean_names()),
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

add_percentiles <- function(df, metric_map) {
  out <- df
  for (nm in names(metric_map)) {
    if (nm %in% names(out)) {
      out[[paste0(nm, "_pctile")]] <- percentile_rank(out[[nm]], higher_is_better = metric_map[[nm]])
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

  launch_speed <- safe_num(coalesce_col(sc, c("launch_speed")))
  est_woba <- safe_num(coalesce_col(sc, c("estimated_woba_using_speedangle", "woba_value")))
  est_ba <- safe_num(coalesce_col(sc, c("estimated_ba_using_speedangle")))

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

message(sprintf("Fetching FanGraphs leaderboards for %d...", season_year))
bat_leaders <- safe_fg_bat_leaders(season_year)
message(sprintf("  Batter leaders: %d rows", nrow(bat_leaders)))
pitch_leaders <- safe_fg_pitch_leaders(season_year)
message(sprintf("  Pitcher leaders: %d rows", nrow(pitch_leaders)))

resolve_player_ids <- function(df) {
  df <- df |> clean_names()
  nm <- names(df)

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
  # value (e.g. *05udp*), the second (_2 suffix) is the real numeric ID.
  # If the primary fangraphs_id looks non-numeric and a _2 variant exists, swap.
  if ("fangraphs_id_2" %in% names(df)) {
    primary_numeric <- suppressWarnings(sum(!is.na(as.numeric(df$fangraphs_id))))
    alt_numeric <- suppressWarnings(sum(!is.na(as.numeric(df$fangraphs_id_2))))
    if (alt_numeric > primary_numeric) {
      message("  Swapping fangraphs_id with fangraphs_id_2 (primary was encoded)")
      df$fangraphs_id <- df$fangraphs_id_2
    }
  }

  df <- df |>
  mutate(
    fangraphs_id = safe_chr(fangraphs_id),
    mlbid = safe_chr(mlbid),
    player_name_clean = norm_name(player_name),
    team_clean = norm_name(team)
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

  bind_rows(joined_bat, joined_pitch)
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

  tibble(
    games = sum_or_na(coalesce_col(logs, c("g"))),
    pa = sum_or_na(coalesce_col(logs, c("pa"))),
    ab = sum_or_na(coalesce_col(logs, c("ab"))),
    h = sum_or_na(coalesce_col(logs, c("h"))),
    hr = sum_or_na(coalesce_col(logs, c("hr"))),
    so = sum_or_na(coalesce_col(logs, c("so"))),
    bb = sum_or_na(coalesce_col(logs, c("bb"))),
    sb = sum_or_na(coalesce_col(logs, c("sb"))),
    avg = mean_or_na(coalesce_col(logs, c("avg"))),
    obp = mean_or_na(coalesce_col(logs, c("obp"))),
    slg = mean_or_na(coalesce_col(logs, c("slg"))),
    ops = mean_or_na(coalesce_col(logs, c("ops"))),
    iso = mean_or_na(coalesce_col(logs, c("iso"))),
    woba = mean_or_na(coalesce_col(logs, c("w_oba", "woba"))),
    bb_pct = mean_or_na(coalesce_col(logs, c("bb_percent", "bb_pct", "bb%"))),
    k_pct = mean_or_na(coalesce_col(logs, c("k_percent", "k_pct", "k%"))),
    wrc_plus = mean_or_na(coalesce_col(logs, c("w_rc", "wrc_plus", "wrc+", "wrc"))),
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

  tibble(
    games = sum_or_na(coalesce_col(logs, c("g"))),
    gs = sum_or_na(coalesce_col(logs, c("gs"))),
    ip = sum_or_na(coalesce_col(logs, c("ip"))),
    er = sum_or_na(coalesce_col(logs, c("er"))),
    so = sum_or_na(coalesce_col(logs, c("so"))),
    bb = sum_or_na(coalesce_col(logs, c("bb"))),
    hr = sum_or_na(coalesce_col(logs, c("hr"))),
    era = mean_or_na(coalesce_col(logs, c("era"))),
    whip = mean_or_na(coalesce_col(logs, c("whip"))),
    fip = mean_or_na(coalesce_col(logs, c("fip"))),
    xfip = mean_or_na(coalesce_col(logs, c("xfip"))),
    siera = mean_or_na(coalesce_col(logs, c("siera"))),
    k_pct = mean_or_na(coalesce_col(logs, c("k_percent", "k_pct", "k%"))),
    bb_pct = mean_or_na(coalesce_col(logs, c("bb_percent", "bb_pct", "bb%"))),
    k_minus_bb_pct = mean_or_na(coalesce_col(logs, c("k_bb_percent", "k_minus_bb_pct", "k-bb%"))),
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

build_raw_mlb_hitters <- function(players) {
  pool <- players |> filter(level == "MLB", role == "H")
  n_total <- nrow(pool)
  message(sprintf("Building raw MLB hitters: %d players", n_total))
  out <- pool |>
    mutate(row_id = row_number()) |>
    group_split(row_id, .keep = TRUE) |>
    map_dfr(function(p) {
      if (p$row_id[[1]] > 1) Sys.sleep(0.5)
      message(sprintf("  [%d/%d] %s", p$row_id[[1]], n_total, p$player_name[[1]]))
      logs <- safe_fg_batter_logs(p$fangraphs_id[[1]], season_year)
      t14 <- agg_hitter_logs(logs, t14_start, t14_end)
      season <- agg_hitter_logs(logs)

      sc14 <- safe_statcast_batter(p$mlbid[[1]], t14_start, t14_end) |> agg_statcast_hitter()
      sc_season <- safe_statcast_batter(p$mlbid[[1]], paste0(season_year, "-01-01"), t14_end) |> agg_statcast_hitter()

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
    season_xwoba = TRUE,
    season_barrel_pct = TRUE,
    season_hard_hit_pct = TRUE,
    season_bb_minus_k_pct = TRUE,
    season_sb = TRUE,
    season_hr = TRUE,
    season_ops = TRUE,
    season_iso = TRUE,
    season_xba = TRUE,
    season_exit_velocity = TRUE
  ))
}

build_raw_mlb_pitchers <- function(players) {
  pool <- players |> filter(level == "MLB", role == "P")
  n_total <- nrow(pool)
  message(sprintf("Building raw MLB pitchers: %d players", n_total))
  out <- pool |>
    mutate(row_id = row_number()) |>
    group_split(row_id, .keep = TRUE) |>
    map_dfr(function(p) {
      if (p$row_id[[1]] > 1) Sys.sleep(0.5)
      message(sprintf("  [%d/%d] %s", p$row_id[[1]], n_total, p$player_name[[1]]))
      logs <- safe_fg_pitcher_logs(p$fangraphs_id[[1]], season_year)
      t14 <- agg_pitcher_logs(logs, t14_start, t14_end)
      season <- agg_pitcher_logs(logs)

      sc14 <- safe_statcast_pitcher(p$mlbid[[1]], t14_start, t14_end) |> agg_statcast_pitcher()
      sc_season <- safe_statcast_pitcher(p$mlbid[[1]], paste0(season_year, "-01-01"), t14_end) |> agg_statcast_pitcher()

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
        t14_velocity = sc14$velo %||% t14$velo,
        t14_stuff_plus = NA_real_,
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
        season_xfip = season$xfip,
        season_siera = season$siera,
        season_k_pct = season$k_pct,
        season_bb_pct = season$bb_pct,
        season_k_minus_bb_pct = ifelse(is.na(season$k_pct) | is.na(season$bb_pct), NA_real_, season$k_pct - season$bb_pct),
        season_velocity = sc_season$velo %||% season$velo,
        season_stuff_plus = NA_real_,
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
    season_hr_against = FALSE
  ))
}

build_raw_milb_hitters <- function(players) {
  pool <- players |> filter(level == "MiLB", role == "H")
  n_total <- nrow(pool)
  message(sprintf("Building raw MiLB hitters: %d players", n_total))
  out <- pool |>
    mutate(row_id = row_number()) |>
    group_split(row_id, .keep = TRUE) |>
    map_dfr(function(p) {
      if (p$row_id[[1]] > 1) Sys.sleep(0.5)
      message(sprintf("  [%d/%d] %s", p$row_id[[1]], n_total, p$player_name[[1]]))
      logs <- safe_fg_milb_batter_logs(p$fangraphs_id[[1]], season_year)
      t14 <- agg_hitter_logs(logs, t14_start, t14_end)
      season <- agg_hitter_logs(logs)

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
  out <- pool |>
    mutate(row_id = row_number()) |>
    group_split(row_id, .keep = TRUE) |>
    map_dfr(function(p) {
      if (p$row_id[[1]] > 1) Sys.sleep(0.5)
      message(sprintf("  [%d/%d] %s", p$row_id[[1]], n_total, p$player_name[[1]]))
      logs <- safe_fg_milb_pitcher_logs(p$fangraphs_id[[1]], season_year)
      t14 <- agg_pitcher_logs(logs, t14_start, t14_end)
      season <- agg_pitcher_logs(logs)

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
    message("  asset_df is empty, returning empty scores")
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
        wh[["xwoba"]] * season_xwoba_pctile +
        wh[["barrel_pct"]] * season_barrel_pct_pctile +
        wh[["hard_hit_pct"]] * season_hard_hit_pct_pctile +
        wh[["bb_minus_k_pct"]] * season_bb_minus_k_pct_pctile +
        wh[["sb"]] * season_sb_pctile +
        wh[["hr"]] * season_hr_pctile +
        wh[["ops"]] * season_ops_pctile +
        wh[["iso"]] * season_iso_pctile +
        wh[["xba"]] * season_xba_pctile +
        wh[["exit_velocity"]] * season_exit_velocity_pctile
      ),
      trend_score = (
        wht[["xwoba"]] * t14_xwoba_pctile +
        wht[["barrel_pct"]] * t14_barrel_pct_pctile +
        wht[["hard_hit_pct"]] * t14_hard_hit_pct_pctile +
        wht[["bb_minus_k_pct"]] * t14_bb_minus_k_pct_pctile +
        wht[["sb"]] * t14_sb_pctile +
        wht[["hr"]] * t14_hr_pctile +
        wht[["iso"]] * t14_iso_pctile +
        wht[["exit_velocity"]] * t14_exit_velocity_pctile +
        wht[["ops"]] * t14_ops_pctile
      ),
      risk_score = (
        0.30 * percentile_rank(season_k_pct, FALSE) +
        0.25 * abs(t14_xwoba_pctile - season_xwoba_pctile) +
        0.15 * percentile_rank(season_hard_hit_pct, FALSE) +
        0.15 * percentile_rank(season_bb_pct, FALSE) +
        0.15 * abs(t14_ops_pctile - season_ops_pctile)
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
        wp[["k_minus_bb_pct"]] * season_k_minus_bb_pct_pctile +
        wp[["siera"]] * season_siera_pctile +
        wp[["xfip"]] * season_xfip_pctile +
        wp[["swstr_pct"]] * season_swstr_pct_pctile +
        wp[["velocity"]] * season_velocity_pctile +
        wp[["era"]] * season_era_pctile +
        wp[["whip"]] * season_whip_pctile +
        wp[["saves_holds"]] * season_saves_holds_pctile +
        wp[["hard_hit_pct_against"]] * season_hard_hit_pct_against_pctile +
        wp[["hr_against"]] * season_hr_against_pctile
      ),
      trend_score = (
        wpt[["k_minus_bb_pct"]] * t14_k_minus_bb_pct_pctile +
        wpt[["swstr_pct"]] * t14_swstr_pct_pctile +
        wpt[["velocity"]] * t14_velocity_pctile +
        wpt[["xfip"]] * t14_xfip_pctile +
        wpt[["siera"]] * t14_siera_pctile +
        wpt[["era"]] * t14_era_pctile +
        wpt[["whip"]] * t14_whip_pctile +
        wpt[["saves_holds"]] * t14_saves_holds_pctile +
        wpt[["hard_hit_pct_against"]] * t14_hard_hit_pct_against_pctile
      ),
      risk_score = (
        0.30 * percentile_rank(season_bb_pct, TRUE) +
        0.20 * percentile_rank(season_hard_hit_pct_against, TRUE) +
        0.15 * percentile_rank(season_hr_against, TRUE) +
        0.20 * abs(t14_xfip_pctile - season_xfip_pctile) +
        0.15 * ifelse(season_saves_holds > 0 & season_games > 0 & season_innings < 80, 65, 35)
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
        wmh[["wrc_plus"]] * season_wrc_plus_pctile +
        wmh[["bb_minus_k_pct"]] * season_bb_minus_k_pct_pctile +
        wmh[["iso"]] * season_iso_pctile +
        wmh[["age_vs_level"]] * 50 +
        wmh[["obp"]] * season_obp_pctile +
        wmh[["avg"]] * season_avg_pctile +
        wmh[["hr"]] * season_hr_pctile +
        wmh[["steals"]] * season_steals_pctile +
        wmh[["woba"]] * season_woba_pctile +
        wmh[["pa"]] * season_pa_pctile
      ),
      trend_score = (
        wmht[["wrc_plus"]] * t14_wrc_plus_pctile +
        wmht[["iso"]] * t14_iso_pctile +
        wmht[["bb_minus_k_pct"]] * t14_bb_minus_k_pct_pctile +
        wmht[["obp"]] * percentile_rank(t14_obp, TRUE) +
        wmht[["age_vs_level"]] * 50 +
        wmht[["hr"]] * t14_hr_pctile +
        wmht[["steals"]] * t14_steals_pctile +
        wmht[["avg"]] * t14_avg_pctile +
        wmht[["pa"]] * t14_pa_pctile
      ),
      risk_score = (
        0.30 * percentile_rank(season_k_pct, TRUE) +
        0.20 * percentile_rank(season_bb_pct, FALSE) +
        0.20 * percentile_rank(season_wrc_plus, FALSE) +
        0.15 * 50 +
        0.15 * percentile_rank(season_pa, FALSE)
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
        wmp[["k_minus_bb_pct"]] * season_k_minus_bb_pct_pctile +
        wmp[["fip"]] * season_fip_pctile +
        wmp[["xfip"]] * season_xfip_pctile +
        wmp[["siera"]] * season_siera_pctile +
        wmp[["velocity"]] * season_throwing_velocity_pctile +
        wmp[["whip"]] * season_whip_pctile +
        wmp[["earned_runs"]] * percentile_rank(season_earned_runs, FALSE) +
        wmp[["hr"]] * percentile_rank(season_hr, FALSE) +
        wmp[["holds_plus_saves"]] * season_holds_plus_saves_pctile +
        wmp[["placeholder"]] * 50
      ),
      trend_score = (
        wmpt[["k_minus_bb_pct"]] * t14_k_minus_bb_pct_pctile +
        wmpt[["xfip"]] * t14_xfip_pctile +
        wmpt[["siera"]] * t14_siera_pctile +
        wmpt[["velocity"]] * t14_throwing_velocity_pctile +
        wmpt[["fip"]] * t14_fip_pctile +
        wmpt[["whip"]] * t14_whip_pctile +
        wmpt[["earned_runs"]] * percentile_rank(t14_earned_runs, FALSE) +
        wmpt[["hr"]] * percentile_rank(t14_hr, FALSE) +
        wmpt[["placeholder"]] * 50
      ),
      risk_score = (
        0.30 * percentile_rank(season_bb_pct, TRUE) +
        0.20 * percentile_rank(season_hr, TRUE) +
        0.20 * rowMeans(cbind(
          percentile_rank(season_fip, TRUE),
          percentile_rank(season_xfip, TRUE)
        ), na.rm = TRUE) +
        0.15 * 50 +
        0.15 * ifelse(season_holds_plus_saves > 0, 55, 45)
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
    left_join(pool |> select(-player, -team, -mlbid, -fangraphs_id), by = c("player_clean", "team_clean")) |>
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

compute_free_agents <- function(fa_df, raw_hitters, raw_pitchers) {
  if (nrow(fa_df) == 0) {
    message("  fa_df is empty, returning empty free agents")
    return(tibble(name = character(), team = character(), age = numeric(),
                  position = character(), score = numeric()))
  }

  fa_df <- fa_df |> clean_names()

  if (!"player" %in% names(fa_df)) {
    for (cand in c("player_name", "name")) {
      found <- find_col_by_prefix(fa_df, cand)
      if (!is.null(found)) { fa_df <- fa_df |> rename(player = !!sym(found)); break }
    }
  }

  for (col_name in c("team", "position", "level", "age")) {
    if (!col_name %in% names(fa_df)) {
      found <- find_col_by_prefix(fa_df, col_name)
      if (!is.null(found)) {
        fa_df <- fa_df |> rename(!!col_name := !!sym(found))
      } else {
        fa_df[[col_name]] <- if (col_name == "level") "MLB" else NA
      }
    }
  }

  empty_fa_pool <- function() {
    tibble(player = character(), team = character(), age = numeric(), position = character(), score = numeric())
  }

  wh <- WEIGHTS$mlb_h_current
  if (nrow(raw_hitters) == 0) {
    hit_pool <- empty_fa_pool()
  } else {
  hit_pool <- raw_hitters |>
    transmute(
      player = name, team, age, position = "H",
      score = round(
        wh[["xwoba"]] * season_xwoba_pctile +
        wh[["barrel_pct"]] * season_barrel_pct_pctile +
        wh[["hard_hit_pct"]] * season_hard_hit_pct_pctile +
        wh[["bb_minus_k_pct"]] * season_bb_minus_k_pct_pctile +
        wh[["sb"]] * season_sb_pctile +
        wh[["hr"]] * season_hr_pctile +
        wh[["ops"]] * season_ops_pctile +
        wh[["iso"]] * season_iso_pctile +
        wh[["xba"]] * season_xba_pctile +
        wh[["exit_velocity"]] * season_exit_velocity_pctile,
        1
      )
    )

  }

  wp <- WEIGHTS$mlb_p_current
  if (nrow(raw_pitchers) == 0) {
    pitch_pool <- empty_fa_pool()
  } else {
  pitch_pool <- raw_pitchers |>
    transmute(
      player = name, team, age, position = "P",
      score = round(
        wp[["k_minus_bb_pct"]] * season_k_minus_bb_pct_pctile +
        wp[["siera"]] * season_siera_pctile +
        wp[["xfip"]] * season_xfip_pctile +
        wp[["swstr_pct"]] * season_swstr_pct_pctile +
        wp[["velocity"]] * season_velocity_pctile +
        wp[["era"]] * season_era_pctile +
        wp[["whip"]] * season_whip_pctile +
        wp[["saves_holds"]] * season_saves_holds_pctile +
        wp[["hard_hit_pct_against"]] * season_hard_hit_pct_against_pctile +
        wp[["hr_against"]] * season_hr_against_pctile,
        1
      )
    )
  }

  pool <- bind_rows(hit_pool, pitch_pool) |>
    mutate(player_clean = norm_name(player), team_clean = norm_name(team))

  fa_df |>
    filter(level == "MLB" | is.na(level) | level == "") |>
    mutate(player_clean = norm_name(player), team_clean = norm_name(team)) |>
    left_join(pool |> select(-player, -team), by = c("player_clean", "team_clean")) |>
    transmute(
      name = player,
      team = team,
      age = coalesce(age.x, age.y),
      position = coalesce(position.x, position.y),
      score = score
    ) |>
    arrange(desc(score)) |>
    slice_head(n = 20)
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

  raw_hitters <- build_raw_mlb_hitters(test_players)
  raw_pitchers <- build_raw_mlb_pitchers(test_players)
  raw_milb_hitters <- build_raw_milb_hitters(test_players)
  raw_milb_pitchers <- build_raw_milb_pitchers(test_players)

  message("Computing asset scores and free agent rankings...")
  asset_scores <- compute_asset_scores(asset_tab, raw_hitters, raw_pitchers, raw_milb_hitters, raw_milb_pitchers)
  free_agents <- compute_free_agents(fa_tab, raw_hitters, raw_pitchers)
  message(sprintf("  Asset scores: %d rows | Free agents: %d rows", nrow(asset_scores), nrow(free_agents)))

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
  safe_write_sheet(free_agents, "free_agent_rankings")
  message(sprintf("  free_agent_rankings: %d rows", nrow(free_agents)))

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
    free_agent_rows = nrow(free_agents),
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
