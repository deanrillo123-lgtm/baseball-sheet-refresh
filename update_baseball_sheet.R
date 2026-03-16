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

# -----------------------------
# GOOGLE SHEET URL
# -----------------------------
sheet_url <- "https://docs.google.com/spreadsheets/d/1dxaFxnZnEZV0VbK37PWOJ5QwMgS94QbpxN_A6MCtQC4/edit?gid=456846762#gid=456846762"

# -----------------------------
# GOOGLE AUTH
# -----------------------------
gs4_auth(path = "gs4-auth.json")

# -----------------------------
# DATE LOGIC: BEFORE APRIL 1 = PREVIOUS YEAR
# -----------------------------
today_chicago <- as.Date(with_tz(Sys.time(), tzone = "America/Chicago"))
current_year  <- year(today_chicago)

if (format(today_chicago, "%m-%d") < "04-01") {
  season_year <- current_year - 1
} else {
  season_year <- current_year
}

board_year  <- current_year
cutoff_date <- today_chicago - 14

print(paste("Using season year:", season_year))
print(paste("Using board year:", board_year))
print(paste("Using 14-day cutoff:", cutoff_date))

# =========================================================
# HELPER FUNCTIONS
# =========================================================

safe_col <- function(df, col_name) {
  if (!is.na(col_name) && col_name %in% names(df)) df[[col_name]]
  else rep(NA, nrow(df))
}

safe_num <- function(x) suppressWarnings(parse_number(as.character(x)))
safe_trim <- function(x) trimws(as.character(x))
safe_upper <- function(x) toupper(safe_trim(x))

safe_first_nonblank <- function(x) {
  x <- x[!is.na(x) & x != ""]
  if (length(x) == 0) NA else x[1]
}

safe_last_nonblank <- function(x) {
  x <- x[!is.na(x) & x != ""]
  if (length(x) == 0) NA else x[length(x)]
}

safe_mean <- function(x) {
  if (length(x) == 0 || all(is.na(x))) NA_real_
  else mean(x, na.rm = TRUE)
}

ensure_sheet <- function(ss, sheet_name) {
  if (!(sheet_name %in% sheet_names(ss))) sheet_add(ss, sheet_name)
}

first_existing_col <- function(df, candidates) {
  found <- candidates[candidates %in% names(df)]
  if (length(found) == 0) NA_character_ else found[1]
}

clamp <- function(x, lo = 0, hi = 100) pmax(lo, pmin(hi, x))

# Scoring thresholds (named constants for maintainability)
BREAKOUT_HARDHIT_INCREASE <- 3     # pp rise in HardHit% needed for breakout flag
BREAKOUT_K_DECREASE       <- 2     # pp drop in K% needed for breakout flag
BUY_LOW_XWOBA_DIFF        <- 0.020 # xwOBA - wOBA minimum to flag as Buy-Low
STARTER_BB_RISK_THRESHOLD <- 0.10  # BB% above which a starter is flagged as Risk
RELIEVER_BB_RISK_THRESHOLD<- 0.12  # BB% above which a reliever is flagged as Risk
RELIEVER_STASH_MIN_SV_HLD <- 3     # Min SV+HLD for stash-flag candidate
RELIEVER_STASH_MIN_K_BB   <- 0.10  # Min K-BB% for stash-flag candidate

# Percentile within a vector (0-100). invert=TRUE: lower = higher pct.
calc_percentile <- function(x, invert = FALSE) {
  vals <- as.numeric(x)
  n    <- sum(!is.na(vals))
  if (n < 2) return(rep(NA_real_, length(vals)))
  pct  <- 100 * (rank(vals, na.last = "keep", ties.method = "average") - 0.5) / n
  if (invert) pct <- 100 - pct
  round(pct, 1)
}

# BABIP approx: (H - HR) / (AB - SO - HR)
calc_babip <- function(H, AB, HR, SO) {
  denom <- as.numeric(AB) - as.numeric(SO) - as.numeric(HR)
  h_n   <- as.numeric(H)
  hr_n  <- as.numeric(HR)
  ifelse(!is.na(denom) & denom > 0, (h_n - hr_n) / denom, NA_real_)
}

# Tier label
score_to_tier <- function(score) {
  dplyr::case_when(
    score >= 80 ~ "S",
    score >= 65 ~ "A",
    score >= 50 ~ "B",
    TRUE        ~ "C"
  )
}

# Age vs level benchmarks (average age at each level)
level_age_avg <- c(
  "AAA" = 26.5, "AA" = 24.5, "A+" = 22.5, "HIGH-A" = 22.5,
  "A" = 21.5, "LOW-A" = 21.5, "A-" = 20.5,
  "ROK" = 19.0, "FCL" = 18.5, "DSL" = 18.0, "SS" = 19.5
)

age_vs_level_score <- function(age, level) {
  level_key <- toupper(trimws(as.character(level)))
  avg_age   <- level_age_avg[level_key]
  avg_age   <- ifelse(is.na(avg_age), 24, avg_age)
  age_n     <- suppressWarnings(as.numeric(age))
  age_n     <- ifelse(is.na(age_n), avg_age, age_n)
  clamp(50 + 8 * (avg_age - age_n))
}

# =========================================================
# SCORING FUNCTIONS (0-100)
# =========================================================

score_mlb_hitters <- function(df) {
  if (nrow(df) == 0) return(df)
  df <- df %>%
    mutate(
      pct_xwOBA   = calc_percentile(as.numeric(xwOBA)),
      pct_Barrel  = calc_percentile(as.numeric(Barrel_percent)),
      pct_HardHit = calc_percentile(as.numeric(HardHit_percent)),
      pct_wRCplus = calc_percentile(as.numeric(wRC_plus)),
      pct_ISO     = calc_percentile(as.numeric(ISO)),
      pct_BB      = calc_percentile(as.numeric(BB_percent)),
      pct_K_inv   = calc_percentile(as.numeric(K_percent), invert = TRUE),
      pct_BB_K    = calc_percentile(as.numeric(BB_percent) - as.numeric(K_percent)),
      pct_SB      = calc_percentile(as.numeric(SB)),
      pct_l14_xwOBA   = calc_percentile(as.numeric(last14_xwOBA)),
      pct_l14_HardHit = calc_percentile(as.numeric(last14_HardHit_percent)),
      pct_l14_wOBA    = calc_percentile(as.numeric(last14_wOBA))
    ) %>%
    mutate(
      Season_Score = clamp(
        0.25 * coalesce(pct_xwOBA,   50) +
        0.20 * coalesce(pct_Barrel,  50) +
        0.15 * coalesce(pct_HardHit, 50) +
        0.15 * coalesce(pct_BB_K,    50) +
        0.10 * coalesce(pct_SB,      50) +
        0.15 * coalesce(pct_l14_xwOBA, pct_l14_wOBA, 50)
      ),
      L14_Score = clamp(
        0.40 * coalesce(pct_l14_xwOBA,   50) +
        0.30 * coalesce(pct_l14_HardHit, 50) +
        0.30 * coalesce(pct_l14_wOBA,    50)
      ),
      Final_Score = clamp(0.65 * Season_Score + 0.35 * L14_Score)
    ) %>%
    mutate(
      flag_breakout = (
        !is.na(last14_HardHit_percent) & !is.na(HardHit_percent) &
        (as.numeric(last14_HardHit_percent) - as.numeric(HardHit_percent)) > BREAKOUT_HARDHIT_INCREASE &
        !is.na(last14_K_percent) & !is.na(K_percent) &
        (as.numeric(K_percent) - as.numeric(last14_K_percent)) > BREAKOUT_K_DECREASE
      ),
      flag_buy_low = (
        !is.na(xwOBA) & !is.na(wOBA) &
        (as.numeric(xwOBA) - as.numeric(wOBA)) >= BUY_LOW_XWOBA_DIFF
      ),
      Flags = dplyr::case_when(
        flag_breakout & flag_buy_low ~ "\U1F525 Breakout + \U1F4B0 Buy-Low",
        flag_breakout                ~ "\U1F525 Breakout",
        flag_buy_low                 ~ "\U1F4B0 Buy-Low",
        TRUE                         ~ ""
      )
    ) %>%
    rowwise() %>%
    mutate(Why = {
      parts <- character(0)
      if (!is.na(pct_xwOBA))   parts <- c(parts, sprintf("xwOBA %dth pct",    round(pct_xwOBA)))
      if (!is.na(pct_Barrel))  parts <- c(parts, sprintf("Barrel%% %dth pct", round(pct_Barrel)))
      if (!is.na(pct_HardHit)) parts <- c(parts, sprintf("HardHit %dth pct",  round(pct_HardHit)))
      if (isTRUE(flag_breakout)) {
        hh_s <- round(as.numeric(HardHit_percent), 1)
        hh_l <- round(as.numeric(last14_HardHit_percent), 1)
        k_s  <- round(100 * as.numeric(K_percent), 1)
        k_l  <- round(100 * as.numeric(last14_K_percent), 1)
        parts <- c(parts, sprintf("Rising HardHit (%s%%->%s%% L14)", hh_s, hh_l))
        parts <- c(parts, sprintf("Falling K%% (%s%%->%s%% L14)", k_s, k_l))
      }
      if (isTRUE(flag_buy_low)) {
        parts <- c(parts, sprintf("xwOBA>wOBA (+%.3f)", as.numeric(xwOBA) - as.numeric(wOBA)))
      }
      paste(parts, collapse = " + ")
    }) %>%
    ungroup() %>%
    select(-flag_breakout, -flag_buy_low)
  df
}

score_mlb_pitchers <- function(df) {
  if (nrow(df) == 0) return(df)
  df <- df %>%
    mutate(
      GS_n  = suppressWarnings(as.numeric(GS)),
      G_n   = suppressWarnings(as.numeric(G)),
      IP_n  = suppressWarnings(as.numeric(IP)),
      Role_detected = dplyr::case_when(
        !is.na(GS_n) & !is.na(G_n) & G_n > 0 & (GS_n / G_n) >= 0.5 ~ "Starter",
        !is.na(IP_n) & !is.na(G_n) & G_n > 0 & (IP_n  / G_n) >= 4  ~ "Starter",
        TRUE ~ "Reliever"
      )
    )
  starters  <- df %>% filter(Role_detected == "Starter")
  relievers <- df %>% filter(Role_detected == "Reliever")
  starters  <- score_starters_internal(starters)
  relievers <- score_relievers_internal(relievers)
  bind_rows(starters, relievers) %>% select(-GS_n, -G_n, -IP_n)
}

score_starters_internal <- function(df) {
  if (nrow(df) == 0) return(df)
  df %>%
    mutate(
      pct_K_BB      = calc_percentile(as.numeric(K_BB_percent)),
      pct_CSW       = calc_percentile(as.numeric(CSW)),
      pct_xFIP_inv  = calc_percentile(as.numeric(xFIP),  invert = TRUE),
      pct_SIERA_inv = calc_percentile(as.numeric(SIERA), invert = TRUE),
      pct_IP        = calc_percentile(as.numeric(IP)),
      pct_FBv       = calc_percentile(as.numeric(FBv)),
      pct_l14_K_BB  = calc_percentile(as.numeric(last14_K_BB_percent)),
      pct_l14_xFIP_inv = calc_percentile(as.numeric(last14_xFIP), invert = TRUE)
    ) %>%
    mutate(
      est_score  = clamp((coalesce(pct_xFIP_inv, 50) + coalesce(pct_SIERA_inv, 50)) / 2),
      velo_score = clamp((coalesce(pct_FBv, 50) +
                          clamp(50 + 5 * coalesce(as.numeric(FBv_trend), 0))) / 2),
      Season_Score = clamp(
        0.25 * coalesce(pct_K_BB,  50) +
        0.20 * coalesce(pct_CSW,   50) +
        0.20 * velo_score +
        0.15 * est_score  +
        0.10 * coalesce(pct_IP,    50) +
        0.10 * coalesce(pct_l14_K_BB, 50)
      ),
      L14_Score = clamp(
        0.50 * coalesce(pct_l14_K_BB,    50) +
        0.50 * coalesce(pct_l14_xFIP_inv, 50)
      ),
      Final_Score = clamp(0.65 * Season_Score + 0.35 * L14_Score)
    ) %>%
    mutate(
      flag_breakout = (
        !is.na(FBv_trend) & as.numeric(FBv_trend) > 0.5 &
        !is.na(last14_K_BB_percent) & !is.na(K_BB_percent) &
        as.numeric(last14_K_BB_percent) > as.numeric(K_BB_percent)
      ),
      flag_risk = (!is.na(BB_percent) & as.numeric(BB_percent) > STARTER_BB_RISK_THRESHOLD),
      Flags = dplyr::case_when(
        flag_breakout & flag_risk ~ "\U1F525 Breakout + \u26A0\uFE0F Risk",
        flag_breakout             ~ "\U1F525 Breakout",
        flag_risk                 ~ "\u26A0\uFE0F Risk (BB%>10%)",
        TRUE                      ~ ""
      )
    ) %>%
    rowwise() %>%
    mutate(Why = {
      parts <- character(0)
      if (!is.na(pct_K_BB))    parts <- c(parts, sprintf("K-BB%% %dth pct", round(pct_K_BB)))
      if (!is.na(pct_CSW))     parts <- c(parts, sprintf("CSW %dth pct",    round(pct_CSW)))
      if (!is.na(FBv) && !is.na(last14_FBv))
        parts <- c(parts, sprintf("Velo %.1f->%.1f L14", as.numeric(FBv), as.numeric(last14_FBv)))
      if (isTRUE(flag_breakout)) parts <- c(parts, "Rising velo+K-BB%")
      if (isTRUE(flag_risk))     parts <- c(parts, sprintf("Risk: BB%% %.1f%%", 100 * as.numeric(BB_percent)))
      paste(parts, collapse = " + ")
    }) %>%
    ungroup() %>%
    select(-est_score, -velo_score, -flag_breakout, -flag_risk)
}

score_relievers_internal <- function(df) {
  if (nrow(df) == 0) return(df)
  df %>%
    mutate(
      pct_K_BB      = calc_percentile(as.numeric(K_BB_percent)),
      pct_SwStr     = calc_percentile(as.numeric(SwStr_percent)),
      pct_K         = calc_percentile(as.numeric(K_percent)),
      pct_xFIP_inv  = calc_percentile(as.numeric(xFIP),  invert = TRUE),
      pct_SIERA_inv = calc_percentile(as.numeric(SIERA), invert = TRUE),
      pct_SV_HLD    = calc_percentile(as.numeric(SV_HLD)),
      pct_FBv       = calc_percentile(as.numeric(FBv)),
      pct_l14_K_BB  = calc_percentile(as.numeric(last14_K_BB_percent)),
      SV_HLD_n      = as.numeric(SV_HLD),
      G_n2          = as.numeric(G),
      Leverage_raw  = ifelse(!is.na(SV_HLD_n) & !is.na(G_n2) & G_n2 > 0,
                             SV_HLD_n / G_n2, NA_real_),
      Leverage_Score = dplyr::case_when(
        !is.na(Leverage_raw) & Leverage_raw >= 0.4 ~ "High",
        !is.na(Leverage_raw) & Leverage_raw >= 0.2 ~ "Mid",
        TRUE ~ "Low"
      )
    ) %>%
    mutate(
      dom_score  = clamp((coalesce(pct_K_BB, 50) + coalesce(pct_SwStr, 50) + coalesce(pct_K, 50)) / 3),
      est_score  = clamp((coalesce(pct_xFIP_inv, 50) + coalesce(pct_SIERA_inv, 50)) / 2),
      velo_score = clamp((coalesce(pct_FBv, 50) +
                          clamp(50 + 5 * coalesce(as.numeric(FBv_trend), 0))) / 2),
      Season_Score = clamp(
        0.30 * dom_score +
        0.20 * coalesce(pct_SV_HLD, 50) +
        0.20 * velo_score +
        0.15 * est_score +
        0.15 * coalesce(pct_l14_K_BB, 50)
      ),
      L14_Score = clamp(
        0.60 * coalesce(pct_l14_K_BB, 50) +
        0.40 * clamp(50 + 50 * coalesce(as.numeric(last14_SV_HLD), 0) /
                     pmax(coalesce(as.numeric(G), 1), 1))
      ),
      Final_Score = clamp(0.65 * Season_Score + 0.35 * L14_Score),
      Stash_Score = clamp(
        0.40 * coalesce(pct_SV_HLD, 50) +
        0.30 * coalesce(pct_K_BB, 50) +
        0.30 * coalesce(pct_xFIP_inv, 50)
      )
    ) %>%
    mutate(
      flag_stash = (
        !is.na(last14_SV_HLD) & as.numeric(last14_SV_HLD) > 0 &
        !is.na(K_BB_percent) & as.numeric(K_BB_percent) > RELIEVER_STASH_MIN_K_BB
      ),
      flag_risk = (
        (!is.na(BB_percent) & as.numeric(BB_percent) > RELIEVER_BB_RISK_THRESHOLD) |
        Leverage_Score == "Low"
      ),
      Flags = dplyr::case_when(
        flag_stash & flag_risk ~ "\U1F525 Stash + \u26A0\uFE0F Risk",
        flag_stash             ~ "\U1F525 Stash",
        flag_risk              ~ "\u26A0\uFE0F Risk",
        TRUE                   ~ ""
      )
    ) %>%
    rowwise() %>%
    mutate(Why = {
      parts <- character(0)
      if (!is.na(pct_K_BB))      parts <- c(parts, sprintf("K-BB%% %dth pct",  round(pct_K_BB)))
      if (!is.na(pct_xFIP_inv))  parts <- c(parts, sprintf("xFIP %dth pct",    round(pct_xFIP_inv)))
      if (!is.na(Leverage_Score)) parts <- c(parts, sprintf("Leverage: %s", Leverage_Score))
      if (!is.na(SV_HLD))        parts <- c(parts, sprintf("SV+HLD: %s", SV_HLD))
      if (isTRUE(flag_stash))    parts <- c(parts, "Rising SV+HLD + K-BB%")
      if (isTRUE(flag_risk))     parts <- c(parts, "Risk: low lev or high BB%")
      paste(parts, collapse = " + ")
    }) %>%
    ungroup() %>%
    select(-dom_score, -est_score, -velo_score, -flag_stash, -flag_risk,
           -SV_HLD_n, -G_n2, -Leverage_raw)
}

score_milb_hitters <- function(df) {
  if (nrow(df) == 0) return(df)
  df %>%
    group_by(Level) %>%
    mutate(
      pct_wRCplus  = calc_percentile(as.numeric(wRC_plus)),
      pct_ISO      = calc_percentile(as.numeric(ISO)),
      pct_BB       = calc_percentile(as.numeric(BB_percent)),
      pct_K_inv    = calc_percentile(as.numeric(K_percent), invert = TRUE),
      pct_BB_K     = calc_percentile(as.numeric(BB_percent) - as.numeric(K_percent)),
      pct_l14_wOBA = calc_percentile(as.numeric(last14_wOBA))
    ) %>%
    ungroup() %>%
    mutate(
      age_score      = age_vs_level_score(Age, Level),
      has_statcast   = (!is.na(as.numeric(HardHit_percent)) | !is.na(as.numeric(Barrel_percent))),
      statcast_bonus = ifelse(has_statcast, 5, 0),
      Season_Score = clamp(
        0.25 * coalesce(pct_wRCplus,  50) +
        0.25 * age_score +
        0.20 * coalesce(pct_BB_K,     50) +
        0.20 * coalesce(pct_ISO,      50) +
        0.10 * coalesce(pct_l14_wOBA, 50) +
        statcast_bonus
      ),
      L14_Score   = clamp(coalesce(pct_l14_wOBA, 50)),
      Final_Score = clamp(0.65 * Season_Score + 0.35 * L14_Score)
    ) %>%
    mutate(
      flag_upside = (age_score > 60 & !is.na(pct_wRCplus) & pct_wRCplus >= 75),
      flag_risk   = (age_score < 40 & !is.na(pct_wRCplus) & pct_wRCplus < 40),
      Flags = dplyr::case_when(
        flag_upside & flag_risk ~ "\U1F4C8 Upside + \u26A0\uFE0F Risk",
        flag_upside             ~ "\U1F4C8 Upside",
        flag_risk               ~ "\u26A0\uFE0F Risk (old for level)",
        TRUE                    ~ ""
      )
    ) %>%
    rowwise() %>%
    mutate(Why = {
      parts <- character(0)
      if (!is.na(pct_wRCplus)) parts <- c(parts, sprintf("wRC+ %dth pct",   round(pct_wRCplus)))
      if (!is.na(pct_ISO))     parts <- c(parts, sprintf("ISO %dth pct",    round(pct_ISO)))
      if (!is.na(pct_BB_K))   parts <- c(parts, sprintf("BB-K%% %dth pct", round(pct_BB_K)))
      if (!is.na(age_score))   parts <- c(parts, sprintf("Age/Lvl: %.0f",   age_score))
      if (isTRUE(has_statcast)) parts <- c(parts, "Statcast bonus +5")
      paste(parts, collapse = " + ")
    }) %>%
    ungroup() %>%
    select(-has_statcast, -statcast_bonus, -flag_upside, -flag_risk)
}

score_milb_pitchers <- function(df) {
  if (nrow(df) == 0) return(df)
  df <- df %>%
    mutate(
      IP_per_GS = dplyr::case_when(
        !is.na(GS) & as.numeric(GS) > 0 ~ as.numeric(IP) / as.numeric(GS),
        TRUE ~ NA_real_
      )
    )
  df %>%
    group_by(Level) %>%
    mutate(
      pct_K_BB      = calc_percentile(as.numeric(K_BB_percent)),
      pct_BB_inv    = calc_percentile(as.numeric(BB_percent), invert = TRUE),
      pct_IP_per_GS = calc_percentile(as.numeric(IP_per_GS)),
      pct_l14_K_BB  = calc_percentile(as.numeric(last14_K_BB_percent))
    ) %>%
    ungroup() %>%
    mutate(
      age_score   = age_vs_level_score(Age, Level),
      Season_Score = clamp(
        0.30 * coalesce(pct_K_BB,      50) +
        0.25 * age_score +
        0.15 * coalesce(pct_BB_inv,    50) +
        0.15 * coalesce(pct_IP_per_GS, 50) +
        0.15 * coalesce(pct_l14_K_BB,  50)
      ),
      L14_Score   = clamp(coalesce(pct_l14_K_BB, 50)),
      Final_Score = clamp(0.65 * Season_Score + 0.35 * L14_Score)
    ) %>%
    mutate(
      flag_upside = (
        age_score > 60 &
        !is.na(pct_K_BB) & pct_K_BB >= 70 &
        !is.na(IP_per_GS) & IP_per_GS >= 5
      ),
      flag_reliever = (!is.na(IP_per_GS) & IP_per_GS < 5),
      Flags = dplyr::case_when(
        flag_upside & flag_reliever ~ "\U1F4C8 Upside + \u26A0\uFE0F Reliever profile",
        flag_upside                 ~ "\U1F4C8 Upside",
        flag_reliever               ~ "\u26A0\uFE0F Reliever-only (IP/GS<5)",
        TRUE                        ~ ""
      )
    ) %>%
    rowwise() %>%
    mutate(Why = {
      parts <- character(0)
      if (!is.na(pct_K_BB))    parts <- c(parts, sprintf("K-BB%% %dth pct", round(pct_K_BB)))
      if (!is.na(pct_BB_inv))  parts <- c(parts, sprintf("BB%% %dth pct",   round(pct_BB_inv)))
      if (!is.na(age_score))   parts <- c(parts, sprintf("Age/Lvl: %.0f",   age_score))
      if (!is.na(IP_per_GS))  parts <- c(parts, sprintf("IP/GS: %.1f",     IP_per_GS))
      if (isTRUE(flag_upside)) parts <- c(parts, "Young+K-BB%+starter workload")
      paste(parts, collapse = " + ")
    }) %>%
    ungroup() %>%
    select(-flag_upside, -flag_reliever)
}

# =========================================================
# GAME LOG FETCHERS
# =========================================================

fetch_mlb_hitter_logs <- function(player_id, season_year) {
  for (fn_name in c("fg_batter_game_logs", "fg_player_batter_game_logs")) {
    if (exists(fn_name, mode = "function")) {
      fn <- get(fn_name, mode = "function")
      for (args in list(
        list(playerid = player_id, year = season_year),
        list(playerid = player_id, season = season_year),
        list(playerid = player_id, startseason = season_year, endseason = season_year),
        list(playerid = player_id)
      )) {
        out <- tryCatch(do.call(fn, args), error = function(e) NULL)
        if (!is.null(out) && nrow(out) > 0) return(out)
      }
    }
  }
  NULL
}

fetch_mlb_pitcher_logs <- function(player_id, season_year) {
  for (fn_name in c("fg_pitcher_game_logs", "fg_player_pitcher_game_logs")) {
    if (exists(fn_name, mode = "function")) {
      fn <- get(fn_name, mode = "function")
      for (args in list(
        list(playerid = player_id, year = season_year),
        list(playerid = player_id, season = season_year),
        list(playerid = player_id, startseason = season_year, endseason = season_year),
        list(playerid = player_id)
      )) {
        out <- tryCatch(do.call(fn, args), error = function(e) NULL)
        if (!is.null(out) && nrow(out) > 0) return(out)
      }
    }
  }
  NULL
}

# =========================================================
# FANGRAPHS FV SCRAPER
# =========================================================
scrape_fangraphs_fv <- function(board_year) {
  board_url <- paste0(
    "https://www.fangraphs.com/prospects/the-board/",
    board_year, "-prospect-list?type=0"
  )
  message(paste("Scraping FanGraphs FV from:", board_url))
  page   <- read_html(board_url)
  tables <- page %>% html_elements("table") %>% html_table(fill = TRUE)
  if (length(tables) == 0) { warning("No tables found on FanGraphs Board page."); return(tibble()) }

  board_tbl <- NULL
  for (tbl in tables) {
    nm <- names(tbl)
    if (length(nm) > 0 &&
        any(str_detect(nm, regex("^Name$", ignore_case = TRUE))) &&
        any(str_detect(nm, regex("^Org$",  ignore_case = TRUE))) &&
        any(str_detect(nm, regex("^FV$",   ignore_case = TRUE)))) {
      board_tbl <- tbl; break
    }
  }
  if (is.null(board_tbl)) {
    widths <- purrr::map_int(tables, ncol)
    board_tbl <- tables[[which.max(widths)]]
  }
  board_tbl <- board_tbl %>% janitor::clean_names()

  name_col <- names(board_tbl)[str_detect(names(board_tbl), "^name$|player|prospect")]
  org_col  <- names(board_tbl)[str_detect(names(board_tbl), "^org$|organization")]
  fv_col   <- names(board_tbl)[str_detect(names(board_tbl), "^fv$|future_value")]
  lvl_col  <- names(board_tbl)[str_detect(names(board_tbl), "current_level|level")]

  if (length(name_col) == 0 || length(fv_col) == 0) {
    warning("Could not find Name/FV columns in FanGraphs Board table.")
    return(tibble())
  }
  name_col <- name_col[1]
  org_col  <- if (length(org_col) > 0) org_col[1] else NA_character_
  fv_col   <- fv_col[1]
  lvl_col  <- if (length(lvl_col) > 0) lvl_col[1] else NA_character_

  out <- board_tbl %>%
    transmute(
      fg_name  = safe_trim(.data[[name_col]]),
      fg_org   = if (!is.na(org_col)) safe_trim(.data[[org_col]]) else NA_character_,
      fg_level = if (!is.na(lvl_col)) safe_trim(.data[[lvl_col]]) else NA_character_,
      FV       = safe_trim(.data[[fv_col]])
    ) %>%
    filter(!is.na(fg_name), fg_name != "", !is.na(FV), FV != "") %>%
    mutate(
      Name_clean = safe_upper(fg_name),
      Org_clean  = safe_upper(fg_org)
    ) %>%
    distinct(Name_clean, Org_clean, .keep_all = TRUE)

  message(paste("Scraped", nrow(out), "prospects with FV."))
  out
}

# =========================================================
# READ TEST TAB
# =========================================================
test_df <- read_sheet(sheet_url, sheet = "Test") %>%
  as.data.frame(stringsAsFactors = FALSE)

print("Columns found in Test tab:")
print(names(test_df))

test_df <- test_df %>%
  mutate(
    Player_clean       = safe_trim(Player),
    Role_clean         = toupper(safe_trim(Role)),
    Level_clean        = toupper(safe_trim(Level)),
    Fangraphs_ID_clean = safe_trim(`Fangraphs ID`),
    MiLB_ID_clean      = safe_trim(MiLB_FG_ID)
  )

milb_name_lookup <- test_df %>%
  filter(!is.na(MiLB_ID_clean), MiLB_ID_clean != "") %>%
  distinct(MiLB_ID_clean, Player_clean)

mlb_hit_ids <- test_df %>%
  filter(Level_clean == "MLB", Role_clean == "H",
         !is.na(Fangraphs_ID_clean), Fangraphs_ID_clean != "") %>%
  pull(Fangraphs_ID_clean) %>% unique()

mlb_pitch_ids <- test_df %>%
  filter(Level_clean == "MLB", Role_clean == "P",
         !is.na(Fangraphs_ID_clean), Fangraphs_ID_clean != "") %>%
  pull(Fangraphs_ID_clean) %>% unique()

milb_hit_ids <- test_df %>%
  filter(Level_clean == "MILB", Role_clean == "H",
         !is.na(MiLB_ID_clean), MiLB_ID_clean != "") %>%
  pull(MiLB_ID_clean) %>% unique()

milb_pitch_ids <- test_df %>%
  filter(Level_clean == "MILB", Role_clean == "P",
         !is.na(MiLB_ID_clean), MiLB_ID_clean != "") %>%
  pull(MiLB_ID_clean) %>% unique()

print("MLB hitter IDs found:");  print(mlb_hit_ids)
print("MLB pitcher IDs found:"); print(mlb_pitch_ids)
print("MiLB hitter IDs found:"); print(milb_hit_ids)
print("MiLB pitcher IDs found:"); print(milb_pitch_ids)

# =========================================================
# MLB SEASON LEADERBOARDS
# =========================================================

mlb_hitters_all <- fg_batter_leaders(
  startseason = season_year, endseason = season_year, qual = 0
) %>% rename_with(trimws)

mlb_hitters_out <- mlb_hitters_all %>%
  mutate(
    fangraphs_id    = as.character(safe_col(., "playerid")),
    Name            = if ("PlayerName" %in% names(.)) safe_col(., "PlayerName") else safe_col(., "Name"),
    Team            = safe_col(., "team_name"),
    Age             = safe_col(., "Age"),
    G               = safe_col(., "G"),
    PA              = safe_col(., "PA"),
    AB              = safe_col(., "AB"),
    H_stat          = safe_col(., "H"),
    HR              = safe_col(., "HR"),
    SB              = safe_col(., "SB"),
    SO              = safe_col(., "SO"),
    AVG             = safe_col(., "AVG"),
    OBP             = safe_col(., "OBP"),
    SLG             = safe_col(., "SLG"),
    OPS             = safe_col(., "OPS"),
    ISO             = safe_col(., "ISO"),
    wOBA            = safe_col(., "wOBA"),
    xwOBA           = safe_col(., "xwOBA"),
    xBA             = safe_col(., "xAVG"),
    xSLG            = safe_col(., "xSLG"),
    wRC_plus        = safe_col(., "wRC_plus"),
    BB_percent      = safe_col(., "BB_pct"),
    K_percent       = safe_col(., "K_pct"),
    HardHit_percent = safe_col(., "HardHit_pct"),
    Barrel_percent  = safe_col(., "Barrel_pct"),
    EV              = safe_col(., "EV"),
    Sprint_Speed    = safe_col(., "Sprint_Speed")
  ) %>%
  mutate(
    BABIP = calc_babip(as.numeric(H_stat), as.numeric(AB),
                       as.numeric(HR), as.numeric(SO))
  ) %>%
  select(
    fangraphs_id, Name, Team, Age, G, PA, AB, H_stat, HR, SB, SO,
    AVG, OBP, SLG, OPS, ISO, BABIP,
    wOBA, xwOBA, xBA, xSLG, wRC_plus, BB_percent, K_percent,
    HardHit_percent, Barrel_percent, EV, Sprint_Speed
  ) %>%
  filter(fangraphs_id %in% mlb_hit_ids)

# MLB Pitchers season
mlb_pitchers_all <- fg_pitcher_leaders(
  startseason = season_year, endseason = season_year, qual = 0
) %>% rename_with(trimws)

mlb_pitchers_out <- mlb_pitchers_all %>%
  mutate(
    fangraphs_id    = as.character(safe_col(., "playerid")),
    Name            = if ("PlayerName" %in% names(.)) safe_col(., "PlayerName") else safe_col(., "Name"),
    Team            = safe_col(., "team_name"),
    Age             = safe_col(., "Age"),
    G               = safe_col(., "G"),
    GS              = safe_col(., "GS"),
    IP              = safe_col(., "IP"),
    ERA             = safe_col(., "ERA"),
    xERA            = safe_col(., "xERA"),
    WHIP            = safe_col(., "WHIP"),
    FIP             = safe_col(., "FIP"),
    FIP_minus       = safe_col(., "FIP-"),
    xFIP            = safe_col(., "xFIP"),
    xFIP_minus      = safe_col(., "xFIP-"),
    SIERA           = safe_col(., "SIERA"),
    K_percent       = safe_col(., "K_pct"),
    BB_percent      = safe_col(., "BB_pct"),
    K_BB_percent    = safe_col(., "K-BB_pct"),
    SwStr_percent   = safe_col(., "SwStr_pct"),
    CSW             = safe_col(., first_existing_col(., c("CSW", "CSW_pct", "csw"))),
    HardHit_percent = safe_col(., "HardHit_pct"),
    Barrel_percent  = safe_col(., "Barrel_pct"),
    EV              = safe_col(., "EV"),
    Stuff_plus      = if ("pb_stuff" %in% names(.)) safe_col(., "pb_stuff") else safe_col(., "Stuff+"),
    FBv             = safe_col(., first_existing_col(., c("FBv", "fb_vel", "FA_Vel", "vFA", "FBVelo"))),
    SV              = safe_col(., "SV"),
    HLD             = if ("HLD" %in% names(.)) safe_col(., "HLD")
                      else if ("HD" %in% names(.)) safe_col(., "HD")
                      else rep(NA, nrow(.))
  ) %>%
  mutate(
    SV_num  = safe_num(SV),
    HLD_num = safe_num(HLD),
    SV_HLD  = SV_num + HLD_num
  ) %>%
  select(
    fangraphs_id, Name, Team, Age, G, GS, IP, ERA, xERA, WHIP, FIP, FIP_minus,
    xFIP, xFIP_minus, SIERA, K_percent, BB_percent, K_BB_percent,
    SwStr_percent, CSW, HardHit_percent, Barrel_percent, EV, Stuff_plus,
    FBv, SV, HLD, SV_HLD
  ) %>%
  filter(fangraphs_id %in% mlb_pitch_ids)

# =========================================================
# MLB LAST 14 DAYS FROM GAME LOGS
# =========================================================

# MLB Hitters L14
mlb_hit_logs <- map_dfr(mlb_hit_ids, function(pid) {
  x <- fetch_mlb_hitter_logs(pid, season_year)
  if (is.null(x) || nrow(x) == 0) { message(paste("No MLB hitter log for:", pid)); return(NULL) }
  x$source_fg_id <- as.character(pid); names(x) <- trimws(names(x)); x
})

if (nrow(mlb_hit_logs) > 0) {
  date_col   <- first_existing_col(mlb_hit_logs, c("Date","date","GameDate","gamedate"))
  pa_col     <- first_existing_col(mlb_hit_logs, c("PA"))
  ab_col     <- first_existing_col(mlb_hit_logs, c("AB"))
  h_col      <- first_existing_col(mlb_hit_logs, c("H"))
  hr_col     <- first_existing_col(mlb_hit_logs, c("HR"))
  sb_col     <- first_existing_col(mlb_hit_logs, c("SB"))
  bb_col     <- first_existing_col(mlb_hit_logs, c("BB"))
  so_col     <- first_existing_col(mlb_hit_logs, c("SO","K"))
  obp_col    <- first_existing_col(mlb_hit_logs, c("OBP"))
  slg_col    <- first_existing_col(mlb_hit_logs, c("SLG"))
  ops_col    <- first_existing_col(mlb_hit_logs, c("OPS"))
  iso_col    <- first_existing_col(mlb_hit_logs, c("ISO"))
  woba_col   <- first_existing_col(mlb_hit_logs, c("wOBA"))
  xwoba_col  <- first_existing_col(mlb_hit_logs, c("xwOBA"))
  xba_col    <- first_existing_col(mlb_hit_logs, c("xAVG"))
  xslg_col   <- first_existing_col(mlb_hit_logs, c("xSLG"))
  hh_col     <- first_existing_col(mlb_hit_logs, c("HardHit_pct","HardHit%"))
  barrel_col <- first_existing_col(mlb_hit_logs, c("Barrel_pct","Barrel%"))
  ev_col     <- first_existing_col(mlb_hit_logs, c("EV"))

  mlb_hit_logs <- mlb_hit_logs %>%
    mutate(
      Date2       = as.Date(safe_col(., date_col)),
      PA_num      = safe_num(safe_col(., pa_col)),
      AB_num      = safe_num(safe_col(., ab_col)),
      H_num       = safe_num(safe_col(., h_col)),
      HR_num      = safe_num(safe_col(., hr_col)),
      SB_num      = safe_num(safe_col(., sb_col)),
      BB_num      = safe_num(safe_col(., bb_col)),
      SO_num      = safe_num(safe_col(., so_col)),
      OBP_num     = safe_num(safe_col(., obp_col)),
      SLG_num     = safe_num(safe_col(., slg_col)),
      OPS_num     = safe_num(safe_col(., ops_col)),
      ISO_num     = safe_num(safe_col(., iso_col)),
      wOBA_num    = safe_num(safe_col(., woba_col)),
      xwOBA_num   = safe_num(safe_col(., xwoba_col)),
      xBA_num     = safe_num(safe_col(., xba_col)),
      xSLG_num    = safe_num(safe_col(., xslg_col)),
      HardHit_num = safe_num(safe_col(., hh_col)),
      Barrel_num  = safe_num(safe_col(., barrel_col)),
      EV_num      = safe_num(safe_col(., ev_col))
    )

  mlb_hit_last14 <- mlb_hit_logs %>%
    filter(!is.na(Date2), Date2 >= cutoff_date) %>%
    group_by(source_fg_id) %>%
    summarise(
      last14_G               = n(),
      last14_PA              = sum(PA_num, na.rm = TRUE),
      last14_AB              = sum(AB_num, na.rm = TRUE),
      last14_H               = sum(H_num,  na.rm = TRUE),
      last14_HR              = sum(HR_num, na.rm = TRUE),
      last14_SB              = sum(SB_num, na.rm = TRUE),
      last14_BB              = sum(BB_num, na.rm = TRUE),
      last14_SO              = sum(SO_num, na.rm = TRUE),
      last14_AVG             = ifelse(last14_AB > 0, last14_H / last14_AB, NA_real_),
      last14_OBP             = safe_mean(OBP_num),
      last14_SLG             = safe_mean(SLG_num),
      last14_OPS             = safe_mean(OPS_num),
      last14_ISO             = safe_mean(ISO_num),
      last14_BABIP           = calc_babip(last14_H, last14_AB, last14_HR, last14_SO),
      last14_wOBA            = safe_mean(wOBA_num),
      last14_xwOBA           = safe_mean(xwOBA_num),
      last14_xBA             = safe_mean(xBA_num),
      last14_xSLG            = safe_mean(xSLG_num),
      last14_HardHit_percent = safe_mean(HardHit_num),
      last14_Barrel_percent  = safe_mean(Barrel_num),
      last14_EV              = safe_mean(EV_num),
      last14_BB_percent      = ifelse(last14_PA > 0, last14_BB / last14_PA, NA_real_),
      last14_K_percent       = ifelse(last14_PA > 0, last14_SO / last14_PA, NA_real_),
      .groups = "drop"
    )

  mlb_hitters_out <- mlb_hitters_out %>%
    left_join(mlb_hit_last14, by = c("fangraphs_id" = "source_fg_id"))
} else {
  mlb_hitters_out <- mlb_hitters_out %>%
    mutate(
      last14_G = NA, last14_PA = NA, last14_AB = NA, last14_H = NA,
      last14_HR = NA, last14_SB = NA, last14_BB = NA, last14_SO = NA,
      last14_AVG = NA, last14_OBP = NA, last14_SLG = NA, last14_OPS = NA,
      last14_ISO = NA, last14_BABIP = NA,
      last14_wOBA = NA, last14_xwOBA = NA, last14_xBA = NA, last14_xSLG = NA,
      last14_HardHit_percent = NA, last14_Barrel_percent = NA, last14_EV = NA,
      last14_BB_percent = NA, last14_K_percent = NA
    )
}

# MLB Pitchers L14
mlb_pitch_logs <- map_dfr(mlb_pitch_ids, function(pid) {
  x <- fetch_mlb_pitcher_logs(pid, season_year)
  if (is.null(x) || nrow(x) == 0) { message(paste("No MLB pitcher log for:", pid)); return(NULL) }
  x$source_fg_id <- as.character(pid); names(x) <- trimws(names(x)); x
})

if (nrow(mlb_pitch_logs) > 0) {
  date_col   <- first_existing_col(mlb_pitch_logs, c("Date","date","GameDate","gamedate"))
  ip_col     <- first_existing_col(mlb_pitch_logs, c("IP"))
  er_col     <- first_existing_col(mlb_pitch_logs, c("ER"))
  h_col      <- first_existing_col(mlb_pitch_logs, c("H"))
  hr_col     <- first_existing_col(mlb_pitch_logs, c("HR"))
  bb_col     <- first_existing_col(mlb_pitch_logs, c("BB"))
  so_col     <- first_existing_col(mlb_pitch_logs, c("SO","K"))
  tbf_col    <- first_existing_col(mlb_pitch_logs, c("TBF"))
  xera_col   <- first_existing_col(mlb_pitch_logs, c("xERA"))
  fip_col    <- first_existing_col(mlb_pitch_logs, c("FIP"))
  fipm_col   <- first_existing_col(mlb_pitch_logs, c("FIP-","FIP_minus"))
  xfip_col   <- first_existing_col(mlb_pitch_logs, c("xFIP"))
  xfipm_col  <- first_existing_col(mlb_pitch_logs, c("xFIP-","xFIP_minus"))
  siera_col  <- first_existing_col(mlb_pitch_logs, c("SIERA"))
  kpct_col   <- first_existing_col(mlb_pitch_logs, c("K%","K_pct"))
  bbpct_col  <- first_existing_col(mlb_pitch_logs, c("BB%","BB_pct"))
  kbbpct_col <- first_existing_col(mlb_pitch_logs, c("K-BB%","K-BB_pct"))
  swstr_col  <- first_existing_col(mlb_pitch_logs, c("SwStr%","SwStr_pct"))
  csw_col    <- first_existing_col(mlb_pitch_logs, c("CSW","CSW_pct","csw"))
  hh_col     <- first_existing_col(mlb_pitch_logs, c("HardHit_pct","HardHit%"))
  barrel_col <- first_existing_col(mlb_pitch_logs, c("Barrel_pct","Barrel%"))
  ev_col     <- first_existing_col(mlb_pitch_logs, c("EV"))
  stuff_col  <- first_existing_col(mlb_pitch_logs, c("pb_stuff","Stuff+","Stuff_plus"))
  sv_col     <- first_existing_col(mlb_pitch_logs, c("SV"))
  hld_col    <- first_existing_col(mlb_pitch_logs, c("HLD","HD"))
  fbv_col    <- first_existing_col(mlb_pitch_logs, c("FBv","fb_vel","FA_Vel","vFA","FBVelo"))

  mlb_pitch_logs <- mlb_pitch_logs %>%
    mutate(
      Date2             = as.Date(safe_col(., date_col)),
      IP_num            = safe_num(safe_col(., ip_col)),
      ER_num            = safe_num(safe_col(., er_col)),
      H_num             = safe_num(safe_col(., h_col)),
      HR_num            = safe_num(safe_col(., hr_col)),
      BB_num            = safe_num(safe_col(., bb_col)),
      SO_num            = safe_num(safe_col(., so_col)),
      TBF_num           = safe_num(safe_col(., tbf_col)),
      xERA_num          = safe_num(safe_col(., xera_col)),
      FIP_num           = safe_num(safe_col(., fip_col)),
      FIP_minus_num     = safe_num(safe_col(., fipm_col)),
      xFIP_num          = safe_num(safe_col(., xfip_col)),
      xFIP_minus_num    = safe_num(safe_col(., xfipm_col)),
      SIERA_num         = safe_num(safe_col(., siera_col)),
      K_percent_num     = safe_num(safe_col(., kpct_col)),
      BB_percent_num    = safe_num(safe_col(., bbpct_col)),
      K_BB_percent_num  = safe_num(safe_col(., kbbpct_col)),
      SwStr_percent_num = safe_num(safe_col(., swstr_col)),
      CSW_num           = safe_num(safe_col(., csw_col)),
      HardHit_num       = safe_num(safe_col(., hh_col)),
      Barrel_num        = safe_num(safe_col(., barrel_col)),
      EV_num            = safe_num(safe_col(., ev_col)),
      Stuff_num         = safe_num(safe_col(., stuff_col)),
      SV_num            = safe_num(safe_col(., sv_col)),
      HLD_num           = safe_num(safe_col(., hld_col)),
      FBv_num           = safe_num(safe_col(., fbv_col))
    )

  mlb_pitch_last14 <- mlb_pitch_logs %>%
    filter(!is.na(Date2), Date2 >= cutoff_date) %>%
    group_by(source_fg_id) %>%
    summarise(
      last14_G               = n(),
      last14_IP              = sum(IP_num,  na.rm = TRUE),
      last14_H               = sum(H_num,   na.rm = TRUE),
      last14_ER              = sum(ER_num,  na.rm = TRUE),
      last14_HR              = sum(HR_num,  na.rm = TRUE),
      last14_BB              = sum(BB_num,  na.rm = TRUE),
      last14_SO              = sum(SO_num,  na.rm = TRUE),
      last14_TBF             = sum(TBF_num, na.rm = TRUE),
      last14_ERA             = ifelse(last14_IP > 0, 9 * last14_ER / last14_IP, NA_real_),
      last14_xERA            = safe_mean(xERA_num),
      last14_WHIP            = ifelse(last14_IP > 0, (last14_H + last14_BB) / last14_IP, NA_real_),
      last14_FIP             = safe_mean(FIP_num),
      last14_FIP_minus       = safe_mean(FIP_minus_num),
      last14_xFIP            = safe_mean(xFIP_num),
      last14_xFIP_minus      = safe_mean(xFIP_minus_num),
      last14_SIERA           = safe_mean(SIERA_num),
      last14_K_percent       = ifelse(last14_TBF > 0, last14_SO / last14_TBF, NA_real_),
      last14_BB_percent      = ifelse(last14_TBF > 0, last14_BB / last14_TBF, NA_real_),
      last14_K_BB_percent    = last14_K_percent - last14_BB_percent,
      last14_SwStr_percent   = safe_mean(SwStr_percent_num),
      last14_CSW             = safe_mean(CSW_num),
      last14_HardHit_percent = safe_mean(HardHit_num),
      last14_Barrel_percent  = safe_mean(Barrel_num),
      last14_EV              = safe_mean(EV_num),
      last14_Stuff_plus      = safe_mean(Stuff_num),
      last14_SV              = sum(SV_num,  na.rm = TRUE),
      last14_HLD             = sum(HLD_num, na.rm = TRUE),
      last14_SV_HLD          = sum(SV_num, na.rm = TRUE) + sum(HLD_num, na.rm = TRUE),
      last14_K_per_9         = ifelse(last14_IP > 0, 9 * last14_SO / last14_IP, NA_real_),
      last14_BB_per_9        = ifelse(last14_IP > 0, 9 * last14_BB / last14_IP, NA_real_),
      last14_HR_per_9        = ifelse(last14_IP > 0, 9 * last14_HR / last14_IP, NA_real_),
      last14_FBv             = safe_mean(FBv_num),
      .groups = "drop"
    )

  mlb_pitchers_out <- mlb_pitchers_out %>%
    left_join(mlb_pitch_last14, by = c("fangraphs_id" = "source_fg_id")) %>%
    mutate(
      FBv_trend = ifelse(!is.na(last14_FBv) & !is.na(FBv),
                         as.numeric(last14_FBv) - as.numeric(FBv), NA_real_)
    )
} else {
  mlb_pitchers_out <- mlb_pitchers_out %>%
    mutate(
      last14_G = NA, last14_IP = NA, last14_H = NA, last14_ER = NA,
      last14_HR = NA, last14_BB = NA, last14_SO = NA, last14_TBF = NA,
      last14_ERA = NA, last14_xERA = NA, last14_WHIP = NA,
      last14_FIP = NA, last14_FIP_minus = NA,
      last14_xFIP = NA, last14_xFIP_minus = NA, last14_SIERA = NA,
      last14_K_percent = NA, last14_BB_percent = NA, last14_K_BB_percent = NA,
      last14_SwStr_percent = NA, last14_CSW = NA,
      last14_HardHit_percent = NA, last14_Barrel_percent = NA, last14_EV = NA,
      last14_Stuff_plus = NA, last14_SV = NA, last14_HLD = NA, last14_SV_HLD = NA,
      last14_K_per_9 = NA, last14_BB_per_9 = NA, last14_HR_per_9 = NA,
      last14_FBv = NA, FBv_trend = NA
    )
}

# =========================================================
# MiLB GAME LOGS
# =========================================================

# MiLB Hitters
milb_hit_logs <- map_dfr(milb_hit_ids, function(pid) {
  x <- tryCatch(
    fg_milb_batter_game_logs(playerid = as.character(pid), year = season_year),
    error = function(e) { message(paste("FAILED MiLB hitter", pid, "->", e$message)); NULL }
  )
  if (is.null(x) || nrow(x) == 0) { message(paste("No MiLB hitter data for:", pid)); return(NULL) }
  x$source_milb_id <- as.character(pid); names(x) <- trimws(names(x)); x
})

if (nrow(milb_hit_logs) > 0) {
  name_col_mh  <- first_existing_col(milb_hit_logs, c("Name","PlayerName","player_name","Player","player"))
  team_col_mh  <- first_existing_col(milb_hit_logs, c("Team","Tm","team_name"))
  level_col_mh <- first_existing_col(milb_hit_logs, c("Level","level"))
  age_col_mh   <- first_existing_col(milb_hit_logs, c("Age","age"))
  wrcplus_col  <- first_existing_col(milb_hit_logs, c("wRC_plus","wRC+","wrc_plus"))

  milb_hit_logs <- milb_hit_logs %>%
    mutate(
      source_milb_id  = as.character(source_milb_id),
      player_name_log = safe_trim(safe_col(., name_col_mh)),
      Date2           = as.Date(safe_col(., "Date")),
      PA_num          = safe_num(safe_col(., "PA")),
      AB_num          = safe_num(safe_col(., "AB")),
      H_num           = safe_num(safe_col(., "H")),
      HR_num          = safe_num(safe_col(., "HR")),
      SB_num          = safe_num(safe_col(., "SB")),
      BB_num          = safe_num(safe_col(., "BB")),
      SO_num          = safe_num(safe_col(., "SO")),
      OBP_num         = safe_num(safe_col(., "OBP")),
      SLG_num         = safe_num(safe_col(., "SLG")),
      OPS_num         = safe_num(safe_col(., "OPS")),
      ISO_num         = safe_num(safe_col(., "ISO")),
      wOBA_num        = safe_num(safe_col(., "wOBA")),
      xwOBA_num       = safe_num(safe_col(., "xwOBA")),
      xBA_num         = safe_num(safe_col(., "xAVG")),
      xSLG_num        = safe_num(safe_col(., "xSLG")),
      HardHit_num     = safe_num(safe_col(., "HardHit_pct")),
      Barrel_num      = safe_num(safe_col(., "Barrel_pct")),
      EV_num          = safe_num(safe_col(., "EV")),
      wRC_plus_num    = safe_num(safe_col(., wrcplus_col))
    )

  milb_hitters_out <- milb_hit_logs %>%
    group_by(source_milb_id) %>%
    summarise(
      minor_playerid  = first(source_milb_id),
      Name_from_logs  = safe_last_nonblank(player_name_log),
      Team            = safe_last_nonblank(as.character(safe_col(pick(everything()), team_col_mh))),
      Level           = safe_last_nonblank(as.character(safe_col(pick(everything()), level_col_mh))),
      Age             = safe_last_nonblank(as.character(safe_col(pick(everything()), age_col_mh))),
      G               = n(),
      PA              = sum(PA_num,  na.rm = TRUE),
      AB              = sum(AB_num,  na.rm = TRUE),
      H               = sum(H_num,   na.rm = TRUE),
      HR              = sum(HR_num,  na.rm = TRUE),
      SB              = sum(SB_num,  na.rm = TRUE),
      BB              = sum(BB_num,  na.rm = TRUE),
      SO              = sum(SO_num,  na.rm = TRUE),
      AVG             = ifelse(AB > 0, H / AB, NA_real_),
      OBP             = safe_mean(OBP_num),
      SLG             = safe_mean(SLG_num),
      OPS             = safe_mean(OPS_num),
      ISO             = safe_mean(ISO_num),
      BABIP           = calc_babip(H, AB, HR, SO),
      BB_percent      = ifelse(PA > 0, BB / PA, NA_real_),
      K_percent       = ifelse(PA > 0, SO / PA, NA_real_),
      wOBA            = safe_mean(wOBA_num),
      xwOBA           = safe_mean(xwOBA_num),
      xBA             = safe_mean(xBA_num),
      xSLG            = safe_mean(xSLG_num),
      wRC_plus        = safe_mean(wRC_plus_num),
      HardHit_percent = safe_mean(HardHit_num),
      Barrel_percent  = safe_mean(Barrel_num),
      EV              = safe_mean(EV_num),
      .groups = "drop"
    ) %>%
    left_join(milb_name_lookup, by = c("minor_playerid" = "MiLB_ID_clean")) %>%
    mutate(Name = coalesce(Name_from_logs, Player_clean)) %>%
    select(
      minor_playerid, Name, Team, Level, Age, G, PA, AB, H, HR, SB, BB, SO,
      AVG, OBP, SLG, OPS, ISO, BABIP, BB_percent, K_percent,
      wOBA, xwOBA, xBA, xSLG, wRC_plus, HardHit_percent, Barrel_percent, EV
    )

  milb_hit_last14 <- milb_hit_logs %>%
    filter(!is.na(Date2), Date2 >= cutoff_date) %>%
    group_by(source_milb_id) %>%
    summarise(
      last14_G               = n(),
      last14_PA              = sum(PA_num,  na.rm = TRUE),
      last14_AB              = sum(AB_num,  na.rm = TRUE),
      last14_H               = sum(H_num,   na.rm = TRUE),
      last14_HR              = sum(HR_num,  na.rm = TRUE),
      last14_SB              = sum(SB_num,  na.rm = TRUE),
      last14_BB              = sum(BB_num,  na.rm = TRUE),
      last14_SO              = sum(SO_num,  na.rm = TRUE),
      last14_AVG             = ifelse(last14_AB > 0, last14_H / last14_AB, NA_real_),
      last14_OBP             = safe_mean(OBP_num),
      last14_SLG             = safe_mean(SLG_num),
      last14_OPS             = safe_mean(OPS_num),
      last14_ISO             = safe_mean(ISO_num),
      last14_BABIP           = calc_babip(last14_H, last14_AB, last14_HR, last14_SO),
      last14_wOBA            = safe_mean(wOBA_num),
      last14_xwOBA           = safe_mean(xwOBA_num),
      last14_xBA             = safe_mean(xBA_num),
      last14_xSLG            = safe_mean(xSLG_num),
      last14_wRC_plus        = safe_mean(wRC_plus_num),
      last14_HardHit_percent = safe_mean(HardHit_num),
      last14_Barrel_percent  = safe_mean(Barrel_num),
      last14_EV              = safe_mean(EV_num),
      last14_BB_percent      = ifelse(last14_PA > 0, last14_BB / last14_PA, NA_real_),
      last14_K_percent       = ifelse(last14_PA > 0, last14_SO / last14_PA, NA_real_),
      .groups = "drop"
    )

  milb_hitters_out <- milb_hitters_out %>%
    left_join(milb_hit_last14, by = c("minor_playerid" = "source_milb_id"))
} else {
  milb_hitters_out <- tibble()
}

# MiLB Pitchers
milb_pitch_logs <- map_dfr(milb_pitch_ids, function(pid) {
  message(paste("Trying MiLB pitcher ID:", pid, "for year:", season_year))
  x <- tryCatch(
    fg_milb_pitcher_game_logs(playerid = as.character(pid), year = season_year),
    error = function(e) { message(paste("FAILED MiLB pitcher", pid, "->", e$message)); NULL }
  )
  if (is.null(x) || nrow(x) == 0) { message(paste("No MiLB pitcher data for:", pid)); return(NULL) }
  x$source_milb_id <- as.character(pid); names(x) <- trimws(names(x)); x
})

if (nrow(milb_pitch_logs) > 0) {
  name_col_mp  <- first_existing_col(milb_pitch_logs, c("Name","PlayerName","player_name","Player","player"))
  team_col_mp  <- first_existing_col(milb_pitch_logs, c("Team","Tm","team_name"))
  level_col_mp <- first_existing_col(milb_pitch_logs, c("Level","level"))
  age_col_mp   <- first_existing_col(milb_pitch_logs, c("Age","age"))
  hld_col_mp   <- first_existing_col(milb_pitch_logs, c("HLD","HD"))
  fbv_col_mp   <- first_existing_col(milb_pitch_logs, c("FBv","fb_vel","FA_Vel","vFA","FBVelo","Velo"))
  gs_col_mp    <- first_existing_col(milb_pitch_logs, c("GS"))

  milb_pitch_logs <- milb_pitch_logs %>%
    mutate(
      source_milb_id    = as.character(source_milb_id),
      player_name_log   = safe_trim(safe_col(., name_col_mp)),
      Date2             = as.Date(safe_col(., "Date")),
      IP_num            = safe_num(safe_col(., "IP")),
      TBF_num           = safe_num(safe_col(., "TBF")),
      H_num             = safe_num(safe_col(., "H")),
      ER_num            = safe_num(safe_col(., "ER")),
      HR_num            = safe_num(safe_col(., "HR")),
      BB_num            = safe_num(safe_col(., "BB")),
      SO_num            = safe_num(safe_col(., "SO")),
      ERA_num           = safe_num(safe_col(., "ERA")),
      xERA_num          = safe_num(safe_col(., "xERA")),
      WHIP_num          = safe_num(safe_col(., "WHIP")),
      FIP_num           = safe_num(safe_col(., "FIP")),
      FIP_minus_num     = safe_num(safe_col(., "FIP-")),
      xFIP_num          = safe_num(safe_col(., "xFIP")),
      xFIP_minus_num    = safe_num(safe_col(., "xFIP-")),
      SIERA_num         = safe_num(safe_col(., "SIERA")),
      K_percent_num     = safe_num(safe_col(., "K%")),
      BB_percent_num    = safe_num(safe_col(., "BB%")),
      K_BB_percent_num  = safe_num(safe_col(., "K-BB%")),
      SwStr_percent_num = safe_num(safe_col(., "SwStr%")),
      HardHit_num       = safe_num(safe_col(., "HardHit_pct")),
      Barrel_num        = safe_num(safe_col(., "Barrel_pct")),
      EV_num            = safe_num(safe_col(., "EV")),
      SV_num            = safe_num(safe_col(., "SV")),
      HLD_num           = safe_num(safe_col(., hld_col_mp)),
      FBv_num           = safe_num(safe_col(., fbv_col_mp)),
      GS_num            = safe_num(safe_col(., gs_col_mp))
    )

  milb_pitchers_out <- milb_pitch_logs %>%
    group_by(source_milb_id) %>%
    summarise(
      minor_playerid  = first(source_milb_id),
      Name_from_logs  = safe_last_nonblank(player_name_log),
      Team            = safe_last_nonblank(as.character(safe_col(pick(everything()), team_col_mp))),
      Level           = safe_last_nonblank(as.character(safe_col(pick(everything()), level_col_mp))),
      Age             = safe_last_nonblank(as.character(safe_col(pick(everything()), age_col_mp))),
      G               = n(),
      GS              = sum(GS_num,  na.rm = TRUE),
      IP              = sum(IP_num,  na.rm = TRUE),
      H               = sum(H_num,   na.rm = TRUE),
      ER              = sum(ER_num,  na.rm = TRUE),
      HR              = sum(HR_num,  na.rm = TRUE),
      BB              = sum(BB_num,  na.rm = TRUE),
      SO              = sum(SO_num,  na.rm = TRUE),
      TBF             = sum(TBF_num, na.rm = TRUE),
      ERA             = ifelse(IP > 0, 9 * ER / IP, NA_real_),
      xERA            = safe_mean(xERA_num),
      WHIP            = ifelse(IP > 0, (H + BB) / IP, NA_real_),
      FIP             = safe_mean(FIP_num),
      FIP_minus       = safe_mean(FIP_minus_num),
      xFIP            = safe_mean(xFIP_num),
      xFIP_minus      = safe_mean(xFIP_minus_num),
      SIERA           = safe_mean(SIERA_num),
      K_percent       = ifelse(TBF > 0, SO / TBF, NA_real_),
      BB_percent      = ifelse(TBF > 0, BB / TBF, NA_real_),
      K_BB_percent    = K_percent - BB_percent,
      SwStr_percent   = safe_mean(SwStr_percent_num),
      HardHit_percent = safe_mean(HardHit_num),
      Barrel_percent  = safe_mean(Barrel_num),
      EV              = safe_mean(EV_num),
      FBv             = safe_mean(FBv_num),
      SV              = sum(SV_num,  na.rm = TRUE),
      HLD             = sum(HLD_num, na.rm = TRUE),
      SV_HLD          = sum(SV_num, na.rm = TRUE) + sum(HLD_num, na.rm = TRUE),
      K_per_9         = ifelse(IP > 0, 9 * SO / IP, NA_real_),
      BB_per_9        = ifelse(IP > 0, 9 * BB / IP, NA_real_),
      HR_per_9        = ifelse(IP > 0, 9 * HR / IP, NA_real_),
      .groups = "drop"
    ) %>%
    left_join(milb_name_lookup, by = c("minor_playerid" = "MiLB_ID_clean")) %>%
    mutate(Name = coalesce(Name_from_logs, Player_clean)) %>%
    select(
      minor_playerid, Name, Team, Level, Age, G, GS, IP, H, ER, HR, BB, SO, TBF,
      ERA, xERA, WHIP, FIP, FIP_minus, xFIP, xFIP_minus, SIERA, K_percent,
      BB_percent, K_BB_percent, SwStr_percent, HardHit_percent,
      Barrel_percent, EV, FBv, SV, HLD, SV_HLD, K_per_9, BB_per_9, HR_per_9
    )

  milb_pitch_last14 <- milb_pitch_logs %>%
    filter(!is.na(Date2), Date2 >= cutoff_date) %>%
    group_by(source_milb_id) %>%
    summarise(
      last14_G               = n(),
      last14_IP              = sum(IP_num,  na.rm = TRUE),
      last14_H               = sum(H_num,   na.rm = TRUE),
      last14_ER              = sum(ER_num,  na.rm = TRUE),
      last14_HR              = sum(HR_num,  na.rm = TRUE),
      last14_BB              = sum(BB_num,  na.rm = TRUE),
      last14_SO              = sum(SO_num,  na.rm = TRUE),
      last14_TBF             = sum(TBF_num, na.rm = TRUE),
      last14_ERA             = ifelse(last14_IP > 0, 9 * last14_ER / last14_IP, NA_real_),
      last14_xERA            = safe_mean(xERA_num),
      last14_WHIP            = ifelse(last14_IP > 0, (last14_H + last14_BB) / last14_IP, NA_real_),
      last14_FIP             = safe_mean(FIP_num),
      last14_FIP_minus       = safe_mean(FIP_minus_num),
      last14_xFIP            = safe_mean(xFIP_num),
      last14_xFIP_minus      = safe_mean(xFIP_minus_num),
      last14_SIERA           = safe_mean(SIERA_num),
      last14_K_percent       = ifelse(last14_TBF > 0, last14_SO / last14_TBF, NA_real_),
      last14_BB_percent      = ifelse(last14_TBF > 0, last14_BB / last14_TBF, NA_real_),
      last14_K_BB_percent    = last14_K_percent - last14_BB_percent,
      last14_SwStr_percent   = safe_mean(SwStr_percent_num),
      last14_HardHit_percent = safe_mean(HardHit_num),
      last14_Barrel_percent  = safe_mean(Barrel_num),
      last14_EV              = safe_mean(EV_num),
      last14_FBv             = safe_mean(FBv_num),
      last14_SV              = sum(SV_num,  na.rm = TRUE),
      last14_HLD             = sum(HLD_num, na.rm = TRUE),
      last14_SV_HLD          = sum(SV_num, na.rm = TRUE) + sum(HLD_num, na.rm = TRUE),
      last14_K_per_9         = ifelse(last14_IP > 0, 9 * last14_SO / last14_IP, NA_real_),
      last14_BB_per_9        = ifelse(last14_IP > 0, 9 * last14_BB / last14_IP, NA_real_),
      last14_HR_per_9        = ifelse(last14_IP > 0, 9 * last14_HR / last14_IP, NA_real_),
      .groups = "drop"
    )

  milb_pitchers_out <- milb_pitchers_out %>%
    left_join(milb_pitch_last14, by = c("minor_playerid" = "source_milb_id")) %>%
    mutate(
      FBv_trend = ifelse(!is.na(last14_FBv) & !is.na(FBv),
                         as.numeric(last14_FBv) - as.numeric(FBv), NA_real_)
    )
} else {
  milb_pitchers_out <- tibble()
}

# =========================================================
# APPLY SCORING
# =========================================================

if (nrow(mlb_hitters_out) > 0) {
  mlb_hitters_out <- score_mlb_hitters(mlb_hitters_out)
  mlb_hitters_out <- mlb_hitters_out %>% mutate(Tier = score_to_tier(Final_Score))
  print(paste("MLB hitters scored:", nrow(mlb_hitters_out)))
}

if (nrow(mlb_pitchers_out) > 0) {
  mlb_pitchers_out <- score_mlb_pitchers(mlb_pitchers_out)
  mlb_pitchers_out <- mlb_pitchers_out %>% mutate(Tier = score_to_tier(Final_Score))
  print(paste("MLB pitchers scored:", nrow(mlb_pitchers_out)))
}

if (nrow(milb_hitters_out) > 0) {
  milb_hitters_out <- score_milb_hitters(milb_hitters_out)
  milb_hitters_out <- milb_hitters_out %>% mutate(Tier = score_to_tier(Final_Score))
  print(paste("MiLB hitters scored:", nrow(milb_hitters_out)))
}

if (nrow(milb_pitchers_out) > 0) {
  milb_pitchers_out <- score_milb_pitchers(milb_pitchers_out)
  milb_pitchers_out <- milb_pitchers_out %>% mutate(Tier = score_to_tier(Final_Score))
  print(paste("MiLB pitchers scored:", nrow(milb_pitchers_out)))
}

# =========================================================
# SCRAPE FANGRAPHS FV
# =========================================================
fv_lookup <- tryCatch(
  scrape_fangraphs_fv(board_year),
  error = function(e) { message(paste("FV scrape failed:", e$message)); tibble() }
)
print("FV lookup preview:")
print(head(fv_lookup))

# Join FV to MiLB hitters
if (exists("milb_hitters_out") && nrow(milb_hitters_out) > 0 && nrow(fv_lookup) > 0) {
  milb_hitters_out <- milb_hitters_out %>%
    mutate(Name_clean = safe_upper(Name), Team_clean = safe_upper(Team))
  milb_hitters_out <- milb_hitters_out %>%
    left_join(fv_lookup %>% select(Name_clean, Org_clean, FV),
              by = c("Name_clean" = "Name_clean", "Team_clean" = "Org_clean")) %>%
    left_join(fv_lookup %>% distinct(Name_clean, .keep_all = TRUE) %>%
                select(Name_clean, FV) %>% rename(FV_name_only = FV),
              by = "Name_clean") %>%
    mutate(FV = coalesce(FV, FV_name_only)) %>%
    select(-Name_clean, -Team_clean, -FV_name_only)
  if ("FV" %in% names(milb_hitters_out)) milb_hitters_out <- milb_hitters_out %>% relocate(FV, .after = Name)
}

# Join FV to MiLB pitchers
if (exists("milb_pitchers_out") && nrow(milb_pitchers_out) > 0 && nrow(fv_lookup) > 0) {
  milb_pitchers_out <- milb_pitchers_out %>%
    mutate(Name_clean = safe_upper(Name), Team_clean = safe_upper(Team))
  milb_pitchers_out <- milb_pitchers_out %>%
    left_join(fv_lookup %>% select(Name_clean, Org_clean, FV),
              by = c("Name_clean" = "Name_clean", "Team_clean" = "Org_clean")) %>%
    left_join(fv_lookup %>% distinct(Name_clean, .keep_all = TRUE) %>%
                select(Name_clean, FV) %>% rename(FV_name_only = FV),
              by = "Name_clean") %>%
    mutate(FV = coalesce(FV, FV_name_only)) %>%
    select(-Name_clean, -Team_clean, -FV_name_only)
  if ("FV" %in% names(milb_pitchers_out)) milb_pitchers_out <- milb_pitchers_out %>% relocate(FV, .after = Name)
}

print("Finished scraping and joining FanGraphs FV.")

# =========================================================
# WRITE TO GOOGLE SHEETS
# =========================================================
ensure_sheet(sheet_url, "raw_hitters")
ensure_sheet(sheet_url, "raw_pitchers")
ensure_sheet(sheet_url, "raw_milb_hitters")
ensure_sheet(sheet_url, "raw_milb_pitchers")

range_write(ss = sheet_url, data = mlb_hitters_out,
            sheet = "raw_hitters",  col_names = TRUE, reformat = FALSE)

range_write(ss = sheet_url, data = mlb_pitchers_out,
            sheet = "raw_pitchers", col_names = TRUE, reformat = FALSE)

if (nrow(milb_hitters_out) > 0) {
  range_write(ss = sheet_url, data = milb_hitters_out,
              sheet = "raw_milb_hitters", col_names = TRUE, reformat = FALSE)
}

if (nrow(milb_pitchers_out) > 0) {
  range_write(ss = sheet_url, data = milb_pitchers_out,
              sheet = "raw_milb_pitchers", col_names = TRUE, reformat = FALSE)
}

print("Finished writing all MLB and MiLB data.")
print(paste("Script completed at:", Sys.time()))
