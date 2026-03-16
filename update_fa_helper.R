library(baseballr)
library(dplyr)
library(googlesheets4)
library(lubridate)
library(purrr)
library(readr)
library(tibble)
library(stringr)

# =========================================================
# SETUP
# =========================================================
sheet_url <- "https://docs.google.com/spreadsheets/d/1dxaFxnZnEZV0VbK37PWOJ5QwMgS94QbpxN_A6MCtQC4/edit?gid=456846762#gid=456846762"
gs4_auth(path = "gs4-auth.json")

today_chicago <- as.Date(with_tz(Sys.time(), tzone = "America/Chicago"))
current_year  <- year(today_chicago)
season_year   <- if (format(today_chicago, "%m-%d") < "04-01") current_year - 1 else current_year
cutoff_date   <- today_chicago - 14
updated_at    <- format(today_chicago, "%Y-%m-%d")

print(paste("FA Helper running for season:", season_year))

# =========================================================
# HELPER FUNCTIONS (shared with main script)
# =========================================================
safe_num   <- function(x) suppressWarnings(readr::parse_number(as.character(x)))
safe_trim  <- function(x) trimws(as.character(x))
safe_upper <- function(x) toupper(safe_trim(x))
safe_mean  <- function(x) { if (length(x) == 0 || all(is.na(x))) NA_real_ else mean(x, na.rm = TRUE) }
clamp      <- function(x, lo = 0, hi = 100) pmax(lo, pmin(hi, x))

# Scoring thresholds (named constants for maintainability)
BUY_LOW_XWOBA_DIFF         <- 0.020 # xwOBA - wOBA minimum to flag as Buy-Low
STARTER_BB_RISK_THRESHOLD  <- 0.10  # BB% above which a starter is flagged as Risk
RELIEVER_BB_RISK_THRESHOLD <- 0.12  # BB% above which a reliever is flagged as Risk
RELIEVER_STASH_MIN_SV_HLD  <- 3     # Min SV+HLD for stash-flag candidate
RELIEVER_STASH_MIN_K_BB    <- 0.10  # Min K-BB% for stash-flag candidate

first_existing_col <- function(df, candidates) {
  found <- candidates[candidates %in% names(df)]
  if (length(found) == 0) NA_character_ else found[1]
}

safe_col <- function(df, col_name) {
  if (!is.na(col_name) && col_name %in% names(df)) df[[col_name]]
  else rep(NA, nrow(df))
}

calc_percentile <- function(x, invert = FALSE) {
  vals <- as.numeric(x)
  n    <- sum(!is.na(vals))
  if (n < 2) return(rep(NA_real_, length(vals)))
  pct  <- 100 * (rank(vals, na.last = "keep", ties.method = "average") - 0.5) / n
  if (invert) pct <- 100 - pct
  round(pct, 1)
}

calc_babip <- function(H, AB, HR, SO) {
  denom <- as.numeric(AB) - as.numeric(SO) - as.numeric(HR)
  ifelse(!is.na(denom) & denom > 0, (as.numeric(H) - as.numeric(HR)) / denom, NA_real_)
}

score_to_tier <- function(score) {
  dplyr::case_when(
    score >= 80 ~ "S", score >= 65 ~ "A", score >= 50 ~ "B", TRUE ~ "C"
  )
}

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
# READ FREE AGENT HELPER TAB
# =========================================================
message("Reading Free Agent Helper tab...")
fa_raw <- tryCatch(
  read_sheet(sheet_url, sheet = "free agent helper") %>% as.data.frame(stringsAsFactors = FALSE),
  error = function(e) { stop(paste("Could not read 'free agent helper' tab:", e$message)) }
)

# Expected columns:
#   B = MLB ID, C = FanGraphs ID, N = Ignore (Yes/No), O = Top500 rank list 1, P = Top500 rank list 2
# Adjust based on 0-indexed or 1-indexed column numbering in the sheet.
# read_sheet returns data frame; columns names come from row 1 of the sheet.
message(paste("FA tab columns:", paste(names(fa_raw), collapse=", ")))
message(paste("FA tab rows:", nrow(fa_raw)))

# Determine column positions (B=2, C=3, N=14, O=15, P=16 - 1-indexed)
col_b <- if (ncol(fa_raw) >= 2)  names(fa_raw)[2]  else NULL  # MLB ID
col_c <- if (ncol(fa_raw) >= 3)  names(fa_raw)[3]  else NULL  # FG ID
col_n <- if (ncol(fa_raw) >= 14) names(fa_raw)[14] else NULL  # Ignore flag
col_o <- if (ncol(fa_raw) >= 15) names(fa_raw)[15] else NULL  # Top500 list 1
col_p <- if (ncol(fa_raw) >= 16) names(fa_raw)[16] else NULL  # Top500 list 2

fa_df <- fa_raw %>%
  tibble::rowid_to_column("row_num") %>%
  mutate(
    mlb_id    = if (!is.null(col_b)) safe_trim(.[[col_b]]) else NA_character_,
    fg_id     = if (!is.null(col_c)) safe_trim(.[[col_c]]) else NA_character_,
    ignore    = if (!is.null(col_n)) safe_upper(.[[col_n]]) else NA_character_,
    rank_o    = if (!is.null(col_o)) safe_trim(.[[col_o]]) else NA_character_,
    rank_p    = if (!is.null(col_p)) safe_trim(.[[col_p]]) else NA_character_
  ) %>%
  mutate(
    is_ignore  = (!is.na(ignore) & ignore == "YES"),
    is_prospect = (!is.na(rank_o) & rank_o != "" | !is.na(rank_p) & rank_p != ""),
    has_fg_id  = (!is.na(fg_id) & fg_id != "")
  ) %>%
  filter(!is_ignore, has_fg_id)

message(paste("Active FA rows after filtering:", nrow(fa_df)))
message(paste("  Prospects:", sum(fa_df$is_prospect)))
message(paste("  Non-prospect:", sum(!fa_df$is_prospect)))

# =========================================================
# PULL FULL MLB SEASON LEADERBOARDS (single call each)
# =========================================================
message("Pulling full MLB batter leaderboard...")
all_mlb_batters <- tryCatch(
  fg_batter_leaders(startseason = season_year, endseason = season_year, qual = 0) %>%
    rename_with(trimws),
  error = function(e) { message(paste("MLB batter pull failed:", e$message)); tibble() }
)
message(paste("Total MLB batters:", nrow(all_mlb_batters)))

message("Pulling full MLB pitcher leaderboard...")
all_mlb_pitchers <- tryCatch(
  fg_pitcher_leaders(startseason = season_year, endseason = season_year, qual = 0) %>%
    rename_with(trimws),
  error = function(e) { message(paste("MLB pitcher pull failed:", e$message)); tibble() }
)
message(paste("Total MLB pitchers:", nrow(all_mlb_pitchers)))

# =========================================================
# PROCESS NON-PROSPECT MLB PLAYERS
# =========================================================

process_mlb_batters <- function(fa_ids, all_batters) {
  if (nrow(all_batters) == 0) return(tibble())
  playerid_col <- first_existing_col(all_batters, c("playerid","PlayerID","xMLBAMID"))
  if (is.na(playerid_col)) return(tibble())

  batter_sub <- all_batters %>%
    mutate(.fg_id = as.character(.data[[playerid_col]])) %>%
    filter(.fg_id %in% fa_ids) %>%
    mutate(
      fangraphs_id    = .fg_id,
      Name            = coalesce(safe_col(., "PlayerName"), safe_col(., "Name")),
      Team            = safe_col(., "team_name"),
      Age             = safe_num(safe_col(., "Age")),
      G               = safe_num(safe_col(., "G")),
      PA              = safe_num(safe_col(., "PA")),
      AB              = safe_num(safe_col(., "AB")),
      H_stat          = safe_num(safe_col(., "H")),
      HR              = safe_num(safe_col(., "HR")),
      SB              = safe_num(safe_col(., "SB")),
      SO              = safe_num(safe_col(., "SO")),
      BB              = safe_num(safe_col(., "BB")),
      AVG             = safe_num(safe_col(., "AVG")),
      OBP             = safe_num(safe_col(., "OBP")),
      SLG             = safe_num(safe_col(., "SLG")),
      OPS             = safe_num(safe_col(., "OPS")),
      ISO             = safe_num(safe_col(., "ISO")),
      wOBA            = safe_num(safe_col(., "wOBA")),
      xwOBA           = safe_num(safe_col(., "xwOBA")),
      wRC_plus        = safe_num(safe_col(., "wRC_plus")),
      BB_percent      = safe_num(safe_col(., "BB_pct")),
      K_percent       = safe_num(safe_col(., "K_pct")),
      HardHit_percent = safe_num(safe_col(., "HardHit_pct")),
      Barrel_percent  = safe_num(safe_col(., "Barrel_pct")),
      Sprint_Speed    = safe_num(safe_col(., "Sprint_Speed")),
      BABIP           = calc_babip(H_stat, AB, HR, SO)
    ) %>%
    filter(!is.na(PA), PA >= 10) %>%
    select(fangraphs_id, Name, Team, Age, G, PA, AB, H_stat, HR, SB, SO, BB,
           AVG, OBP, SLG, OPS, ISO, BABIP, wOBA, xwOBA, wRC_plus,
           BB_percent, K_percent, HardHit_percent, Barrel_percent, Sprint_Speed)

  if (nrow(batter_sub) == 0) return(tibble())

  batter_sub %>%
    mutate(
      pct_xwOBA   = calc_percentile(xwOBA),
      pct_Barrel  = calc_percentile(Barrel_percent),
      pct_HardHit = calc_percentile(HardHit_percent),
      pct_BB_K    = calc_percentile(BB_percent - K_percent),
      pct_SB      = calc_percentile(SB),
      pct_wRCplus = calc_percentile(wRC_plus),
      pct_ISO     = calc_percentile(ISO),
      pct_K_inv   = calc_percentile(K_percent, invert = TRUE),
      Season_Score = clamp(
        0.25 * coalesce(pct_xwOBA,   50) +
        0.20 * coalesce(pct_Barrel,  50) +
        0.15 * coalesce(pct_HardHit, 50) +
        0.15 * coalesce(pct_BB_K,    50) +
        0.10 * coalesce(pct_SB,      50) +
        0.15 * coalesce(pct_wRCplus, 50)
      ),
      L14_Score   = 50,
      Final_Score = clamp(0.70 * Season_Score + 0.30 * L14_Score),
      Tier        = score_to_tier(Final_Score),
      Player_Type = "MLB Hitter",
      Level       = "MLB",
      Data_Quality = paste0(PA, " PA")
    ) %>%
    mutate(
      flag_breakout = FALSE,
      flag_buy_low  = (!is.na(xwOBA) & !is.na(wOBA) & (xwOBA - wOBA) >= BUY_LOW_XWOBA_DIFF),
      Key_Flags = dplyr::case_when(
        flag_buy_low  ~ "\U1F4B0 Buy-Low",
        TRUE           ~ ""
      )
    ) %>%
    rowwise() %>%
    mutate(Why = {
      parts <- character(0)
      if (!is.na(pct_xwOBA))   parts <- c(parts, sprintf("xwOBA %dth pct",    round(pct_xwOBA)))
      if (!is.na(pct_Barrel))  parts <- c(parts, sprintf("Barrel%% %dth pct", round(pct_Barrel)))
      if (!is.na(pct_HardHit)) parts <- c(parts, sprintf("HardHit %dth pct",  round(pct_HardHit)))
      if (isTRUE(flag_buy_low)) parts <- c(parts, sprintf("xwOBA>wOBA(+%.3f)", xwOBA - wOBA))      paste(parts, collapse = " + ")
    }) %>%
    ungroup() %>%
    select(fangraphs_id, Name, Team, Level, Player_Type, Age,
           Season_Score, L14_Score, Final_Score, Tier, Key_Flags, Why, Data_Quality)
}

process_mlb_pitchers_fa <- function(fa_ids, all_pitchers) {
  if (nrow(all_pitchers) == 0) return(tibble())
  playerid_col <- first_existing_col(all_pitchers, c("playerid","PlayerID"))
  if (is.na(playerid_col)) return(tibble())

  pitcher_sub <- all_pitchers %>%
    mutate(.fg_id = as.character(.data[[playerid_col]])) %>%
    filter(.fg_id %in% fa_ids) %>%
    mutate(
      fangraphs_id    = .fg_id,
      Name            = coalesce(safe_col(., "PlayerName"), safe_col(., "Name")),
      Team            = safe_col(., "team_name"),
      Age             = safe_num(safe_col(., "Age")),
      G               = safe_num(safe_col(., "G")),
      GS              = safe_num(safe_col(., "GS")),
      IP              = safe_num(safe_col(., "IP")),
      ERA             = safe_num(safe_col(., "ERA")),
      xFIP            = safe_num(safe_col(., "xFIP")),
      SIERA           = safe_num(safe_col(., "SIERA")),
      K_percent       = safe_num(safe_col(., "K_pct")),
      BB_percent      = safe_num(safe_col(., "BB_pct")),
      K_BB_percent    = safe_num(safe_col(., "K-BB_pct")),
      SwStr_percent   = safe_num(safe_col(., "SwStr_pct")),
      CSW             = safe_num(safe_col(., first_existing_col(., c("CSW","CSW_pct","csw")))),
      FBv             = safe_num(safe_col(., first_existing_col(., c("FBv","fb_vel","vFA","FBVelo")))),
      SV_num          = safe_num(safe_col(., "SV")),
      HLD_num         = safe_num(safe_col(., first_existing_col(., c("HLD","HD")))),
      SV_HLD          = SV_num + HLD_num,
      TBF             = safe_num(safe_col(., "TBF"))
    ) %>%
    filter(!is.na(IP), IP >= 1) %>%
    mutate(
      Role_detected = dplyr::case_when(
        !is.na(GS) & !is.na(G) & G > 0 & (GS / G) >= 0.5 ~ "MLB Starter",
        !is.na(IP) & !is.na(G) & G > 0 & (IP / G) >= 4   ~ "MLB Starter",
        TRUE ~ "MLB Reliever"
      )
    )

  if (nrow(pitcher_sub) == 0) return(tibble())

  # Score starters
  starters <- pitcher_sub %>% filter(Role_detected == "MLB Starter") %>%
    mutate(
      pct_K_BB     = calc_percentile(K_BB_percent),
      pct_CSW      = calc_percentile(CSW),
      pct_FBv      = calc_percentile(FBv),
      pct_xFIP_inv = calc_percentile(xFIP, invert = TRUE),
      pct_SIERA_inv= calc_percentile(SIERA, invert = TRUE),
      pct_IP       = calc_percentile(IP),
      Season_Score = clamp(
        0.25 * coalesce(pct_K_BB,     50) +
        0.20 * coalesce(pct_CSW,      50) +
        0.20 * coalesce(pct_FBv,      50) +
        0.15 * (coalesce(pct_xFIP_inv, 50) + coalesce(pct_SIERA_inv, 50)) / 2 +
        0.10 * coalesce(pct_IP,       50) +
        0.10 * 50
      ),
      L14_Score   = 50,
      Final_Score = clamp(0.70 * Season_Score + 0.30 * L14_Score),
      Tier        = score_to_tier(Final_Score),
      Player_Type = "MLB Starter",
      Level       = "MLB",
      Data_Quality = paste0(round(IP, 1), " IP"),
      Key_Flags   = ifelse(!is.na(BB_percent) & BB_percent > STARTER_BB_RISK_THRESHOLD,
                           "\u26A0\uFE0F Risk (BB%>10%)", "")
    ) %>%
    rowwise() %>%
    mutate(Why = {
      parts <- character(0)
      if (!is.na(pct_K_BB))     parts <- c(parts, sprintf("K-BB%% %dth pct", round(pct_K_BB)))
      if (!is.na(pct_xFIP_inv)) parts <- c(parts, sprintf("xFIP %dth pct",    round(pct_xFIP_inv)))
      if (!is.na(FBv))          parts <- c(parts, sprintf("FBv %.1f", FBv))
      paste(parts, collapse = " + ")
    }) %>%
    ungroup() %>%
    select(fangraphs_id, Name, Team, Level, Player_Type, Age,
           Season_Score, L14_Score, Final_Score, Tier, Key_Flags, Why, Data_Quality)

  # Score relievers
  relievers <- pitcher_sub %>% filter(Role_detected == "MLB Reliever") %>%
    mutate(
      pct_K_BB     = calc_percentile(K_BB_percent),
      pct_SwStr    = calc_percentile(SwStr_percent),
      pct_K        = calc_percentile(K_percent),
      pct_FBv      = calc_percentile(FBv),
      pct_xFIP_inv = calc_percentile(xFIP, invert = TRUE),
      pct_SIERA_inv= calc_percentile(SIERA, invert = TRUE),
      pct_SV_HLD   = calc_percentile(SV_HLD),
      Leverage_raw = ifelse(!is.na(SV_HLD) & !is.na(G) & G > 0, SV_HLD / G, NA_real_),
      Leverage_Score = dplyr::case_when(
        !is.na(Leverage_raw) & Leverage_raw >= 0.4 ~ "High",
        !is.na(Leverage_raw) & Leverage_raw >= 0.2 ~ "Mid",
        TRUE ~ "Low"
      ),
      Usage_Trend = "N/A",
      dom_score   = clamp((coalesce(pct_K_BB, 50) + coalesce(pct_SwStr, 50) + coalesce(pct_K, 50)) / 3),
      est_score   = clamp((coalesce(pct_xFIP_inv, 50) + coalesce(pct_SIERA_inv, 50)) / 2),
      Season_Score = clamp(
        0.30 * dom_score +
        0.20 * coalesce(pct_SV_HLD, 50) +
        0.20 * coalesce(pct_FBv,    50) +
        0.15 * est_score +
        0.15 * 50
      ),
      Stash_Score = clamp(
        0.40 * coalesce(pct_SV_HLD, 50) +
        0.30 * coalesce(pct_K_BB,   50) +
        0.30 * coalesce(pct_xFIP_inv, 50)
      ),
      L14_Score   = 50,
      Final_Score = clamp(0.70 * Season_Score + 0.30 * L14_Score),
      Tier        = score_to_tier(Final_Score),
      Player_Type = "MLB Reliever",
      Level       = "MLB",
      Data_Quality = paste0(round(IP, 1), " IP"),
      Key_Flags = dplyr::case_when(
        (!is.na(BB_percent) & BB_percent > RELIEVER_BB_RISK_THRESHOLD) | Leverage_Score == "Low" ~
          paste0("\u26A0\uFE0F Risk | Lev: ", Leverage_Score),
        !is.na(SV_HLD) & SV_HLD >= RELIEVER_STASH_MIN_SV_HLD &
          !is.na(K_BB_percent) & K_BB_percent > RELIEVER_STASH_MIN_K_BB ~
          paste0("\U1F525 Stash | Lev: ", Leverage_Score),
        TRUE ~ paste0("Lev: ", Leverage_Score)
      )
    ) %>%
    rowwise() %>%
    mutate(Why = {
      parts <- character(0)
      if (!is.na(pct_K_BB))      parts <- c(parts, sprintf("K-BB%% %dth pct", round(pct_K_BB)))
      if (!is.na(pct_xFIP_inv))  parts <- c(parts, sprintf("xFIP %dth pct",    round(pct_xFIP_inv)))
      if (!is.na(SV_HLD))        parts <- c(parts, sprintf("SV+HLD: %.0f",     SV_HLD))
      if (!is.na(Stash_Score))   parts <- c(parts, sprintf("Stash: %.0f",      Stash_Score))
      paste(parts, collapse = " + ")
    }) %>%
    ungroup() %>%
    select(fangraphs_id, Name, Team, Level, Player_Type, Age,
           Season_Score, L14_Score, Final_Score, Tier, Key_Flags, Why, Data_Quality)

  bind_rows(starters, relievers)
}

# =========================================================
# PULL MILB PROSPECT DATA
# =========================================================
pull_milb_prospect_batter <- function(fg_id, season_year) {
  tryCatch(
    fg_milb_batter_game_logs(playerid = as.character(fg_id), year = season_year) %>%
      rename_with(trimws),
    error = function(e) { message(paste("MiLB batter fail:", fg_id, e$message)); NULL }
  )
}

pull_milb_prospect_pitcher <- function(fg_id, season_year) {
  tryCatch(
    fg_milb_pitcher_game_logs(playerid = as.character(fg_id), year = season_year) %>%
      rename_with(trimws),
    error = function(e) { message(paste("MiLB pitcher fail:", fg_id, e$message)); NULL }
  )
}

aggregate_milb_batter <- function(logs, fg_id) {
  if (is.null(logs) || nrow(logs) == 0) return(NULL)
  name_col  <- first_existing_col(logs, c("Name","PlayerName","player_name"))
  team_col  <- first_existing_col(logs, c("Team","Tm","team_name"))
  level_col <- first_existing_col(logs, c("Level","level"))
  age_col   <- first_existing_col(logs, c("Age","age"))
  wrcplus_col <- first_existing_col(logs, c("wRC_plus","wRC+","wrc_plus"))
  fbv_col   <- first_existing_col(logs, c("FBv","fb_vel","vFA","FBVelo","Velo"))

  logs %>%
    summarise(
      fangraphs_id    = as.character(fg_id),
      Name            = if (!is.na(name_col)) safe_trim(last(safe_col(pick(everything()), name_col))) else NA_character_,
      Team            = if (!is.na(team_col)) safe_trim(last(safe_col(pick(everything()), team_col))) else NA_character_,
      Level           = if (!is.na(level_col)) safe_trim(last(safe_col(pick(everything()), level_col))) else NA_character_,
      Age             = if (!is.na(age_col)) safe_trim(last(safe_col(pick(everything()), age_col))) else NA_character_,
      G               = n(),
      PA              = sum(safe_num(safe_col(pick(everything()), "PA")), na.rm = TRUE),
      AB              = sum(safe_num(safe_col(pick(everything()), "AB")), na.rm = TRUE),
      H               = sum(safe_num(safe_col(pick(everything()), "H")),  na.rm = TRUE),
      HR              = sum(safe_num(safe_col(pick(everything()), "HR")), na.rm = TRUE),
      SB              = sum(safe_num(safe_col(pick(everything()), "SB")), na.rm = TRUE),
      BB              = sum(safe_num(safe_col(pick(everything()), "BB")), na.rm = TRUE),
      SO              = sum(safe_num(safe_col(pick(everything()), "SO")), na.rm = TRUE),
      wOBA            = safe_mean(safe_num(safe_col(pick(everything()), "wOBA"))),
      ISO             = safe_mean(safe_num(safe_col(pick(everything()), "ISO"))),
      wRC_plus        = if (!is.na(wrcplus_col)) safe_mean(safe_num(safe_col(pick(everything()), wrcplus_col))) else NA_real_,
      HardHit_percent = safe_mean(safe_num(safe_col(pick(everything()), "HardHit_pct"))),
      Barrel_percent  = safe_mean(safe_num(safe_col(pick(everything()), "Barrel_pct"))),
      .groups = "drop"
    ) %>%
    mutate(
      AVG        = ifelse(AB > 0, H / AB, NA_real_),
      BB_percent = ifelse(PA > 0, BB / PA, NA_real_),
      K_percent  = ifelse(PA > 0, SO / PA, NA_real_),
      BABIP      = calc_babip(H, AB, HR, SO)
    )
}

aggregate_milb_pitcher <- function(logs, fg_id) {
  if (is.null(logs) || nrow(logs) == 0) return(NULL)
  name_col  <- first_existing_col(logs, c("Name","PlayerName","player_name"))
  team_col  <- first_existing_col(logs, c("Team","Tm","team_name"))
  level_col <- first_existing_col(logs, c("Level","level"))
  age_col   <- first_existing_col(logs, c("Age","age"))
  fbv_col   <- first_existing_col(logs, c("FBv","fb_vel","vFA","FBVelo","Velo"))
  gs_col    <- first_existing_col(logs, c("GS"))

  logs %>%
    summarise(
      fangraphs_id = as.character(fg_id),
      Name         = if (!is.na(name_col)) safe_trim(last(safe_col(pick(everything()), name_col))) else NA_character_,
      Team         = if (!is.na(team_col)) safe_trim(last(safe_col(pick(everything()), team_col))) else NA_character_,
      Level        = if (!is.na(level_col)) safe_trim(last(safe_col(pick(everything()), level_col))) else NA_character_,
      Age          = if (!is.na(age_col)) safe_trim(last(safe_col(pick(everything()), age_col))) else NA_character_,
      G            = n(),
      GS           = if (!is.na(gs_col)) sum(safe_num(safe_col(pick(everything()), gs_col)), na.rm = TRUE) else 0,
      IP           = sum(safe_num(safe_col(pick(everything()), "IP")),  na.rm = TRUE),
      H            = sum(safe_num(safe_col(pick(everything()), "H")),   na.rm = TRUE),
      ER           = sum(safe_num(safe_col(pick(everything()), "ER")),  na.rm = TRUE),
      HR           = sum(safe_num(safe_col(pick(everything()), "HR")),  na.rm = TRUE),
      BB           = sum(safe_num(safe_col(pick(everything()), "BB")),  na.rm = TRUE),
      SO           = sum(safe_num(safe_col(pick(everything()), "SO")),  na.rm = TRUE),
      TBF          = sum(safe_num(safe_col(pick(everything()), "TBF")), na.rm = TRUE),
      xFIP         = safe_mean(safe_num(safe_col(pick(everything()), "xFIP"))),
      SIERA        = safe_mean(safe_num(safe_col(pick(everything()), "SIERA"))),
      FBv          = if (!is.na(fbv_col)) safe_mean(safe_num(safe_col(pick(everything()), fbv_col))) else NA_real_,
      .groups = "drop"
    ) %>%
    mutate(
      ERA          = ifelse(IP > 0, 9 * ER / IP, NA_real_),
      WHIP         = ifelse(IP > 0, (H + BB) / IP, NA_real_),
      K_percent    = ifelse(TBF > 0, SO / TBF, NA_real_),
      BB_percent   = ifelse(TBF > 0, BB / TBF, NA_real_),
      K_BB_percent = K_percent - BB_percent,
      IP_per_GS    = ifelse(!is.na(GS) & GS > 0, IP / GS, NA_real_)
    )
}

# =========================================================
# IDENTIFY PLAYER TYPES FOR PROSPECTS
# =========================================================
prospect_ids <- fa_df %>% filter(is_prospect) %>% pull(fg_id) %>% unique()
message(paste("Total prospect FG IDs:", length(prospect_ids)))

prospect_batters  <- tibble()
prospect_pitchers <- tibble()

if (length(prospect_ids) > 0) {
  for (pid in prospect_ids) {
    Sys.sleep(0.5)  # be polite to the API
    p_logs <- pull_milb_prospect_pitcher(pid, season_year)
    b_logs <- pull_milb_prospect_batter(pid, season_year)

    has_p_stats <- !is.null(p_logs) && nrow(p_logs) > 0 &&
                   sum(safe_num(safe_col(p_logs, first_existing_col(p_logs, c("IP")))), na.rm = TRUE) >= 1
    has_b_stats <- !is.null(b_logs) && nrow(b_logs) > 0 &&
                   sum(safe_num(safe_col(b_logs, first_existing_col(b_logs, c("PA","AB")))), na.rm = TRUE) >= 1

    if (has_p_stats) {
      agg <- aggregate_milb_pitcher(p_logs, pid)
      if (!is.null(agg)) prospect_pitchers <- bind_rows(prospect_pitchers, agg)
    } else if (has_b_stats) {
      agg <- aggregate_milb_batter(b_logs, pid)
      if (!is.null(agg)) prospect_batters <- bind_rows(prospect_batters, agg)
    } else {
      message(paste("No MiLB stats for prospect:", pid))
    }
  }
}

message(paste("Prospect batters with data:", nrow(prospect_batters)))
message(paste("Prospect pitchers with data:", nrow(prospect_pitchers)))

# =========================================================
# SCORE PROSPECTS
# =========================================================

score_prospect_batters <- function(df) {
  if (nrow(df) == 0) return(tibble())
  df %>%
    group_by(Level) %>%
    mutate(
      pct_wRCplus  = calc_percentile(as.numeric(wRC_plus)),
      pct_wOBA     = calc_percentile(as.numeric(wOBA)),
      pct_ISO      = calc_percentile(as.numeric(ISO)),
      pct_BB_K     = calc_percentile(as.numeric(BB_percent) - as.numeric(K_percent)),
      pct_K_inv    = calc_percentile(as.numeric(K_percent), invert = TRUE)
    ) %>%
    ungroup() %>%
    mutate(
      age_score      = age_vs_level_score(Age, Level),
      has_statcast   = (!is.na(as.numeric(HardHit_percent)) | !is.na(as.numeric(Barrel_percent))),
      statcast_bonus = ifelse(has_statcast, 5, 0),
      base_wrc       = coalesce(pct_wRCplus, pct_wOBA, 50),
      Season_Score   = clamp(
        0.25 * base_wrc +
        0.25 * age_score +
        0.20 * coalesce(pct_BB_K, 50) +
        0.20 * coalesce(pct_ISO,  50) +
        0.10 * 50 +
        statcast_bonus
      ),
      L14_Score   = 50,
      Final_Score = clamp(0.65 * Season_Score + 0.35 * L14_Score),
      Tier        = score_to_tier(Final_Score),
      Player_Type = "Prospect Hitter",
      Data_Quality = paste0(PA, " PA")
    ) %>%
    mutate(
      flag_upside = (age_score > 60 & !is.na(base_wrc) & base_wrc >= 75),
      flag_risk   = (age_score < 40 & !is.na(base_wrc) & base_wrc < 40),
      Key_Flags = dplyr::case_when(
        flag_upside & flag_risk ~ "\U1F4C8 Upside + \u26A0\uFE0F Risk",
        flag_upside             ~ "\U1F4C8 Upside",
        flag_risk               ~ "\u26A0\uFE0F Risk (old for level)",
        TRUE                    ~ ""
      )
    ) %>%
    rowwise() %>%
    mutate(Why = {
      parts <- character(0)
      if (!is.na(base_wrc))  parts <- c(parts, sprintf("wRC+/wOBA %dth pct", round(base_wrc)))
      if (!is.na(pct_ISO))   parts <- c(parts, sprintf("ISO %dth pct",       round(pct_ISO)))
      if (!is.na(age_score)) parts <- c(parts, sprintf("Age/Lvl: %.0f",      age_score))
      if (isTRUE(has_statcast)) parts <- c(parts, "+Statcast")
      paste(parts, collapse = " + ")
    }) %>%
    ungroup() %>%
    select(fangraphs_id, Name, Team, Level, Player_Type, Age,
           Season_Score, L14_Score, Final_Score, Tier, Key_Flags, Why, Data_Quality)
}

score_prospect_pitchers <- function(df) {
  if (nrow(df) == 0) return(tibble())
  df %>%
    group_by(Level) %>%
    mutate(
      pct_K_BB   = calc_percentile(as.numeric(K_BB_percent)),
      pct_BB_inv = calc_percentile(as.numeric(BB_percent), invert = TRUE),
      pct_IP_GS  = calc_percentile(as.numeric(IP_per_GS))
    ) %>%
    ungroup() %>%
    mutate(
      age_score   = age_vs_level_score(Age, Level),
      Season_Score = clamp(
        0.30 * coalesce(pct_K_BB,  50) +
        0.25 * age_score +
        0.15 * coalesce(pct_BB_inv, 50) +
        0.15 * coalesce(pct_IP_GS,  50) +
        0.15 * 50
      ),
      L14_Score   = 50,
      Final_Score = clamp(0.65 * Season_Score + 0.35 * L14_Score),
      Tier        = score_to_tier(Final_Score),
      Player_Type = "Prospect Pitcher",
      Data_Quality = paste0(round(IP, 1), " IP")
    ) %>%
    mutate(
      flag_upside    = (age_score > 60 & !is.na(pct_K_BB) & pct_K_BB >= 70 & !is.na(IP_per_GS) & IP_per_GS >= 5),
      flag_reliever  = (!is.na(IP_per_GS) & IP_per_GS < 5),
      Key_Flags = dplyr::case_when(
        flag_upside & flag_reliever ~ "\U1F4C8 Upside + \u26A0\uFE0F Reliever",
        flag_upside                 ~ "\U1F4C8 Upside",
        flag_reliever               ~ "\u26A0\uFE0F Reliever (IP/GS<5)",
        TRUE                        ~ ""
      )
    ) %>%
    rowwise() %>%
    mutate(Why = {
      parts <- character(0)
      if (!is.na(pct_K_BB))   parts <- c(parts, sprintf("K-BB%% %dth pct",  round(pct_K_BB)))
      if (!is.na(pct_BB_inv)) parts <- c(parts, sprintf("BB%% %dth pct",    round(pct_BB_inv)))
      if (!is.na(age_score))  parts <- c(parts, sprintf("Age/Lvl: %.0f",    age_score))
      if (!is.na(IP_per_GS))  parts <- c(parts, sprintf("IP/GS: %.1f",      IP_per_GS))
      paste(parts, collapse = " + ")
    }) %>%
    ungroup() %>%
    select(fangraphs_id, Name, Team, Level, Player_Type, Age,
           Season_Score, L14_Score, Final_Score, Tier, Key_Flags, Why, Data_Quality)
}

# =========================================================
# PROCESS ALL PLAYER TYPES
# =========================================================

# Non-prospect MLB IDs
non_prospect_ids <- fa_df %>% filter(!is_prospect) %>% pull(fg_id) %>% unique()

# Check which non-prospect IDs are batters vs pitchers
batter_playerids  <- character(0)
pitcher_playerids <- character(0)

if (nrow(all_mlb_batters) > 0) {
  bat_id_col <- first_existing_col(all_mlb_batters, c("playerid","PlayerID"))
  if (!is.na(bat_id_col)) batter_playerids <- as.character(all_mlb_batters[[bat_id_col]])
}
if (nrow(all_mlb_pitchers) > 0) {
  pit_id_col <- first_existing_col(all_mlb_pitchers, c("playerid","PlayerID"))
  if (!is.na(pit_id_col)) pitcher_playerids <- as.character(all_mlb_pitchers[[pit_id_col]])
}

mlb_hitter_fa_ids  <- non_prospect_ids[non_prospect_ids %in% batter_playerids]
mlb_pitcher_fa_ids <- non_prospect_ids[non_prospect_ids %in% pitcher_playerids]
# If in both leaderboards (two-way), include in pitchers only
mlb_hitter_fa_ids <- setdiff(mlb_hitter_fa_ids, mlb_pitcher_fa_ids)

message(paste("MLB hitters to score:", length(mlb_hitter_fa_ids)))
message(paste("MLB pitchers to score:", length(mlb_pitcher_fa_ids)))

scored_mlb_hitters  <- process_mlb_batters(mlb_hitter_fa_ids,  all_mlb_batters)
scored_mlb_pitchers <- process_mlb_pitchers_fa(mlb_pitcher_fa_ids, all_mlb_pitchers)
scored_prospect_hit <- score_prospect_batters(prospect_batters)
scored_prospect_pit <- score_prospect_pitchers(prospect_pitchers)

message(paste("Scored MLB hitters:",    nrow(scored_mlb_hitters)))
message(paste("Scored MLB pitchers:",   nrow(scored_mlb_pitchers)))
message(paste("Scored prospect hit:",   nrow(scored_prospect_hit)))
message(paste("Scored prospect pitch:", nrow(scored_prospect_pit)))

# =========================================================
# COMBINE ALL SCORED PLAYERS
# =========================================================
all_scored <- bind_rows(
  scored_mlb_hitters,
  scored_mlb_pitchers,
  scored_prospect_hit,
  scored_prospect_pit
) %>%
  mutate(Last_Updated = updated_at) %>%
  arrange(Player_Type, desc(Final_Score))

message(paste("Total players scored:", nrow(all_scored)))

# =========================================================
# WRITE SCORES BACK TO FA HELPER TAB STARTING AT COLUMN AG
# =========================================================
# Column AG = column 33
# Build a mapping from fangraphs_id back to row_num in the sheet

output_cols <- c(
  "Player_Type", "Level", "Season_Score", "L14_Score",
  "Final_Score", "Tier", "Key_Flags", "Why", "Data_Quality", "Last_Updated"
)
output_df_base <- all_scored %>% select(fangraphs_id, all_of(output_cols))

# Join back to fa_df to get row positions
fa_with_scores <- fa_df %>%
  left_join(output_df_base, by = c("fg_id" = "fangraphs_id"))

# Prepare output for column AG (position 33 = column AG)
# We write just the score columns for rows that have scores
n_rows      <- nrow(fa_raw)
n_cols_out  <- length(output_cols)
out_matrix  <- as.data.frame(matrix(NA_character_, nrow = n_rows, ncol = n_cols_out))
names(out_matrix) <- output_cols

# Populate scored rows
for (i in seq_len(nrow(fa_with_scores))) {
  row_idx <- fa_with_scores$row_num[i]
  if (!is.na(fa_with_scores$Final_Score[i])) {
    out_matrix[row_idx, ] <- as.character(fa_with_scores[i, output_cols])
  }
}

# Write header row separately
header_df  <- as.data.frame(t(output_cols), stringsAsFactors = FALSE)
names(header_df) <- output_cols

# Build range: AG1 = row 1 header, AG2:onward = data
# We write header + data together starting at AG1
write_df    <- rbind(header_df, out_matrix)

# Write to sheet starting at AG1
# Determine current number of rows in the sheet first
range_write(
  ss        = sheet_url,
  data      = write_df,
  sheet     = "free agent helper",
  range     = "AG1",
  col_names = FALSE,
  reformat  = FALSE
)

message(paste("Wrote FA scores for", nrow(all_scored), "players to column AG+"))
message(paste("FA Helper update completed at:", Sys.time()))
