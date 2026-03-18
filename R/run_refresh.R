suppressPackageStartupMessages({
  library(baseballr)
  library(googlesheets4)
  library(gargle)
  library(dplyr)
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

sheet_id <- Sys.getenv("GOOGLE_SHEET_ID")
svc_file <- Sys.getenv("GOOGLE_APPLICATION_CREDENTIALS")
refresh_type <- Sys.getenv("REFRESH_TYPE")
if (refresh_type == "") refresh_type <- ifelse(Sys.getenv("GITHUB_EVENT_NAME") == "schedule", "scheduled", "manual")

if (sheet_id == "") stop("GOOGLE_SHEET_ID is missing.")
if (svc_file == "") stop("GOOGLE_APPLICATION_CREDENTIALS is missing.")

gs4_auth(path = svc_file)

safe_read_sheet <- function(tab) {
  tryCatch(
    read_sheet(sheet_id, sheet = tab) |> clean_names(),
    error = function(e) tibble()
  )
}

safe_write_sheet <- function(df, tab) {
  df <- as_tibble(df)
  tryCatch(
    sheet_write(df, ss = sheet_id, sheet = tab),
    error = function(e) {
      try(sheet_add(sheet_id, tab), silent = TRUE)
      sheet_write(df, ss = sheet_id, sheet = tab)
    }
  )
}

safe_num <- function(x) suppressWarnings(as.numeric(x))
safe_chr <- function(x) ifelse(is.na(x), NA_character_, as.character(x))

coalesce_col <- function(df, candidates, default = NA) {
  nm <- names(df)
  hit <- candidates[candidates %in% nm][1]
  if (length(hit) == 0 || is.na(hit)) return(rep(default, nrow(df)))
  df[[hit]]
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

bat_leaders <- safe_fg_bat_leaders(season_year)
pitch_leaders <- safe_fg_pitch_leaders(season_year)

resolve_player_ids <- function(df) {
  df <- df |> clean_names()
  if (!"player_name" %in% names(df) && "player" %in% names(df)) {
    df <- df |> rename(player_name = player)
  }
  if (!"fangraphs_id" %in% names(df)) df$fangraphs_id <- NA
  if (!"mlbid" %in% names(df)) df$mlbid <- NA
  if (!"team" %in% names(df)) df$team <- NA
  if (!"role" %in% names(df)) df$role <- NA
  if (!"level" %in% names(df)) df$level <- NA

  df <- df |>
    mutate(
      fangraphs_id = safe_chr(fangraphs_id),
      mlbid = safe_chr(mlbid),
      player_name_clean = norm_name(player_name),
      team_clean = norm_name(team)
    )

  bat_ref <- bat_leaders |>
    transmute(
      fg_ref = safe_chr(coalesce_col(cur_data(), c("playerid"))),
      mlb_ref = safe_chr(coalesce_col(cur_data(), c("playeridmlb", "playerid_mlb", "mlbid"))),
      name_ref = norm_name(coalesce_col(cur_data(), c("name", "player_name"))),
      team_ref = norm_name(coalesce_col(cur_data(), c("team", "team_name", "teamid"))),
      age_ref = safe_num(coalesce_col(cur_data(), c("age"))),
      pos_ref = safe_chr(coalesce_col(cur_data(), c("pos")))
    )

  pitch_ref <- pitch_leaders |>
    transmute(
      fg_ref = safe_chr(coalesce_col(cur_data(), c("playerid"))),
      mlb_ref = safe_chr(coalesce_col(cur_data(), c("playeridmlb", "playerid_mlb", "mlbid"))),
      name_ref = norm_name(coalesce_col(cur_data(), c("name", "player_name"))),
      team_ref = norm_name(coalesce_col(cur_data(), c("team", "team_name", "teamid"))),
      age_ref = safe_num(coalesce_col(cur_data(), c("age"))),
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
  if (nrow(logs) == 0) return(tibble())
  logs <- logs |>
    mutate(gamedate2 = as.Date(coalesce_col(cur_data(), c("gamedate", "date"))))
  if (!is.null(start_date)) logs <- logs |> filter(gamedate2 >= as.Date(start_date))
  if (!is.null(end_date)) logs <- logs |> filter(gamedate2 <= as.Date(end_date))
  if (nrow(logs) == 0) return(tibble())

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
    woba = mean_or_na(coalesce_col(logs, c("woba"))),
    bb_pct = mean_or_na(coalesce_col(logs, c("bb%"))),
    k_pct = mean_or_na(coalesce_col(logs, c("k%"))),
    wrc_plus = mean_or_na(coalesce_col(logs, c("wrc+"))),
    hard_hit_pct = mean_or_na(coalesce_col(logs, c("hardhit%", "hard%"))),
    barrel_pct = mean_or_na(coalesce_col(logs, c("barrel%", "barrels_per_bbe"))),
    exit_velocity = mean_or_na(coalesce_col(logs, c("ev", "maxev"))),
    age = mean_or_na(coalesce_col(logs, c("age"))),
    team = mode_chr(coalesce_col(logs, c("team"))),
    level = mode_chr(coalesce_col(logs, c("level", "league"))),
    position = mode_chr(coalesce_col(logs, c("pos")))
  )
}

agg_pitcher_logs <- function(logs, start_date = NULL, end_date = NULL) {
  if (nrow(logs) == 0) return(tibble())
  logs <- logs |>
    mutate(gamedate2 = as.Date(coalesce_col(cur_data(), c("gamedate", "date"))))
  if (!is.null(start_date)) logs <- logs |> filter(gamedate2 >= as.Date(start_date))
  if (!is.null(end_date)) logs <- logs |> filter(gamedate2 <= as.Date(end_date))
  if (nrow(logs) == 0) return(tibble())

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
    k_pct = mean_or_na(coalesce_col(logs, c("k%"))),
    bb_pct = mean_or_na(coalesce_col(logs, c("bb%"))),
    k_minus_bb_pct = mean_or_na(coalesce_col(logs, c("k-bb%"))),
    swstr_pct = mean_or_na(coalesce_col(logs, c("swstr%"))),
    hard_hit_pct_against = mean_or_na(coalesce_col(logs, c("hardhit%", "hard%"))),
    barrel_pct_against = mean_or_na(coalesce_col(logs, c("barrel%"))),
    exit_velocity_against = mean_or_na(coalesce_col(logs, c("ev"))),
    velo = mean_or_na(coalesce_col(logs, c("fbv", "vfa"))),
    saves_holds = sum_or_na(coalesce_col(logs, c("sv"))) + sum_or_na(coalesce_col(logs, c("hld"))),
    age = mean_or_na(coalesce_col(logs, c("age"))),
    team = mode_chr(coalesce_col(logs, c("team"))),
    level = mode_chr(coalesce_col(logs, c("level", "league")))
  )
}

build_raw_mlb_hitters <- function(players) {
  out <- players |>
    filter(level == "MLB", role == "H") |>
    mutate(row_id = row_number()) |>
    group_split(row_id, .keep = TRUE) |>
    map_dfr(function(p) {
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
  out <- players |>
    filter(level == "MLB", role == "P") |>
    mutate(row_id = row_number()) |>
    group_split(row_id, .keep = TRUE) |>
    map_dfr(function(p) {
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
  out <- players |>
    filter(level == "MiLB", role == "H") |>
    mutate(row_id = row_number()) |>
    group_split(row_id, .keep = TRUE) |>
    map_dfr(function(p) {
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
  out <- players |>
    filter(level == "MiLB", role == "P") |>
    mutate(row_id = row_number()) |>
    group_split(row_id, .keep = TRUE) |>
    map_dfr(function(p) {
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
  asset_df <- asset_df |> clean_names()
  if (!"player" %in% names(asset_df) && "player_name" %in% names(asset_df)) asset_df <- asset_df |> rename(player = player_name)
  if (!"team" %in% names(asset_df)) asset_df$team <- NA
  if (!"level" %in% names(asset_df)) asset_df$level <- NA
  if (!"role" %in% names(asset_df)) asset_df$role <- NA
  if (!"mlbid" %in% names(asset_df)) asset_df$mlbid <- NA
  if (!"fangraphs_id" %in% names(asset_df)) asset_df$fangraphs_id <- NA

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
        0.14 * season_xwoba_pctile +
        0.14 * season_barrel_pct_pctile +
        0.14 * season_hard_hit_pct_pctile +
        0.14 * season_bb_minus_k_pct_pctile +
        0.14 * season_sb_pctile +
        0.06 * season_hr_pctile +
        0.06 * season_ops_pctile +
        0.06 * season_iso_pctile +
        0.06 * season_xba_pctile +
        0.06 * season_exit_velocity_pctile
      ),
      trend_score = (
        0.20 * t14_xwoba_pctile +
        0.20 * t14_barrel_pct_pctile +
        0.15 * t14_hard_hit_pct_pctile +
        0.15 * t14_bb_minus_k_pct_pctile +
        0.10 * t14_sb_pctile +
        0.05 * t14_hr_pctile +
        0.05 * t14_iso_pctile +
        0.05 * t14_exit_velocity_pctile +
        0.05 * t14_ops_pctile
      ),
      risk_score = (
        0.30 * percentile_rank(season_k_pct, FALSE) +
        0.25 * abs(t14_xwoba_pctile - season_xwoba_pctile) +
        0.15 * percentile_rank(season_hard_hit_pct, FALSE) +
        0.15 * percentile_rank(season_bb_pct, FALSE) +
        0.15 * percentile_rank(season_sb, FALSE)
      ),
      bucket = "MLB_H"
    )

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
        0.14 * season_k_minus_bb_pct_pctile +
        0.14 * season_siera_pctile +
        0.14 * season_xfip_pctile +
        0.14 * season_swstr_pct_pctile +
        0.14 * season_velocity_pctile +
        0.06 * season_era_pctile +
        0.06 * season_whip_pctile +
        0.06 * season_saves_holds_pctile +
        0.06 * season_hard_hit_pct_against_pctile +
        0.06 * season_hr_against_pctile
      ),
      trend_score = (
        0.20 * t14_k_minus_bb_pct_pctile +
        0.20 * t14_swstr_pct_pctile +
        0.15 * t14_velocity_pctile +
        0.15 * t14_xfip_pctile +
        0.10 * t14_siera_pctile +
        0.05 * t14_era_pctile +
        0.05 * t14_whip_pctile +
        0.05 * t14_saves_holds_pctile +
        0.05 * t14_hard_hit_pct_against_pctile
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
        0.14 * season_wrc_plus_pctile +
        0.14 * season_bb_minus_k_pct_pctile +
        0.14 * season_iso_pctile +
        0.14 * 50 +
        0.14 * season_obp_pctile +
        0.06 * season_avg_pctile +
        0.06 * season_hr_pctile +
        0.06 * season_steals_pctile +
        0.06 * season_woba_pctile +
        0.06 * season_pa_pctile
      ),
      trend_score = (
        0.20 * t14_wrc_plus_pctile +
        0.20 * t14_iso_pctile +
        0.20 * t14_bb_minus_k_pct_pctile +
        0.10 * percentile_rank(t14_obp, TRUE) +
        0.10 * 50 +
        0.05 * t14_hr_pctile +
        0.05 * t14_steals_pctile +
        0.05 * t14_avg_pctile +
        0.05 * t14_pa_pctile
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
        0.14 * season_k_minus_bb_pct_pctile +
        0.14 * season_fip_pctile +
        0.14 * season_xfip_pctile +
        0.14 * season_siera_pctile +
        0.14 * season_throwing_velocity_pctile +
        0.06 * season_whip_pctile +
        0.06 * percentile_rank(season_earned_runs, FALSE) +
        0.06 * percentile_rank(season_hr, FALSE) +
        0.06 * season_holds_plus_saves_pctile +
        0.06 * 50
      ),
      trend_score = (
        0.20 * t14_k_minus_bb_pct_pctile +
        0.20 * t14_xfip_pctile +
        0.20 * t14_siera_pctile +
        0.10 * t14_throwing_velocity_pctile +
        0.10 * t14_fip_pctile +
        0.05 * t14_whip_pctile +
        0.05 * percentile_rank(t14_earned_runs, FALSE) +
        0.05 * percentile_rank(t14_hr, FALSE) +
        0.05 * 50
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

  pool <- bind_rows(mlb_h, mlb_p, milb_h, milb_p) |>
    mutate(
      player_clean = norm_name(player),
      team_clean = norm_name(team),
      current_score = round(current_score, 1),
      trend_score = round(trend_score, 1),
      risk_score = round(risk_score, 1)
    )

  out <- asset_df |>
    mutate(
      mlbid = safe_chr(mlbid),
      fangraphs_id = safe_chr(fangraphs_id),
      player_clean = norm_name(player),
      team_clean = norm_name(team)
    ) |>
    left_join(pool, by = c("player_clean", "team_clean")) |>
    mutate(
      prospect_bonus = case_when(level == "MiLB" ~ 0.75, TRUE ~ 0.15),
      future_bonus = case_when(level == "MiLB" ~ 1.20, TRUE ~ 0.30),
      extra_prospect_bump = case_when(level == "MiLB" ~ 0.35, TRUE ~ 0.00),
      current_war = round((current_score / 12) - (risk_score / 150), 2),
      future_war = round((trend_score / 14) + future_bonus - (risk_score / 175), 2),
      dynasty_war = round((current_score / 10) + prospect_bonus - (risk_score / 100), 2),
      dynasty_war_3yr = round(current_war + (future_war * 1.5) + extra_prospect_bump, 2),
      trade_value = round(dynasty_war_3yr * 10, 0)
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
  fa_df <- fa_df |> clean_names()
  if (!"player" %in% names(fa_df) && "player_name" %in% names(fa_df)) fa_df <- fa_df |> rename(player = player_name)
  if (!"team" %in% names(fa_df)) fa_df$team <- NA
  if (!"position" %in% names(fa_df)) fa_df$position <- NA
  if (!"level" %in% names(fa_df)) fa_df$level <- "MLB"

  hit_pool <- raw_hitters |>
    transmute(
      player = name, team, age, position = "H",
      score = round(
        0.14 * season_xwoba_pctile +
        0.14 * season_barrel_pct_pctile +
        0.14 * season_hard_hit_pct_pctile +
        0.14 * season_bb_minus_k_pct_pctile +
        0.14 * season_sb_pctile +
        0.06 * season_hr_pctile +
        0.06 * season_ops_pctile +
        0.06 * season_iso_pctile +
        0.06 * season_xba_pctile +
        0.06 * season_exit_velocity_pctile,
        1
      )
    )

  pitch_pool <- raw_pitchers |>
    transmute(
      player = name, team, age, position = "P",
      score = round(
        0.14 * season_k_minus_bb_pct_pctile +
        0.14 * season_siera_pctile +
        0.14 * season_xfip_pctile +
        0.14 * season_swstr_pct_pctile +
        0.14 * season_velocity_pctile +
        0.06 * season_era_pctile +
        0.06 * season_whip_pctile +
        0.06 * season_saves_holds_pctile +
        0.06 * season_hard_hit_pct_against_pctile +
        0.06 * season_hr_against_pctile,
        1
      )
    )

  pool <- bind_rows(hit_pool, pitch_pool) |>
    mutate(player_clean = norm_name(player), team_clean = norm_name(team))

  fa_df |>
    filter(level == "MLB" | is.na(level) | level == "") |>
    mutate(player_clean = norm_name(player), team_clean = norm_name(team)) |>
    left_join(pool, by = c("player_clean", "team_clean")) |>
    transmute(
      name = player,
      team = team,
      age = age,
      position = coalesce(position.x, position.y),
      score = score
    ) |>
    arrange(desc(score)) |>
    slice_head(n = 20)
}

main <- function() {
  started_at <- with_tz(now("America/Chicago"), "America/Chicago")

  test_tab <- safe_read_sheet("test")
  asset_tab <- safe_read_sheet("asset_database")
  fa_tab <- safe_read_sheet("Free Agent Helper")

  test_players <- resolve_player_ids(test_tab)

  raw_hitters <- build_raw_mlb_hitters(test_players)
  raw_pitchers <- build_raw_mlb_pitchers(test_players)
  raw_milb_hitters <- build_raw_milb_hitters(test_players)
  raw_milb_pitchers <- build_raw_milb_pitchers(test_players)

  asset_scores <- compute_asset_scores(asset_tab, raw_hitters, raw_pitchers, raw_milb_hitters, raw_milb_pitchers)
  free_agents <- compute_free_agents(fa_tab, raw_hitters, raw_pitchers)

  safe_write_sheet(raw_hitters, "raw_hitters")
  safe_write_sheet(raw_pitchers, "raw_pitchers")
  safe_write_sheet(raw_milb_hitters, "raw_milb_hitters")
  safe_write_sheet(raw_milb_pitchers, "raw_milb_pitchers")
  safe_write_sheet(asset_scores, "asset_scores")
  safe_write_sheet(free_agents, "free_agent_rankings")

  finished_at <- with_tz(now("America/Chicago"), "America/Chicago")
  last_update <- tibble(
    refresh_status = "success",
    refresh_type = refresh_type,
    started_at = as.character(started_at),
    finished_at = as.character(finished_at),
    duration_minutes = round(as.numeric(difftime(finished_at, started_at, units = "mins")), 2),
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
