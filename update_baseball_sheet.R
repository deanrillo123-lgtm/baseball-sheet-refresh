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

# =====================================================
# CONFIGURATION
# =====================================================
sheet_url <- "https://docs.google.com/spreadsheets/d/1dxaFxnZnEZV0VbK37PWOJ5QwMgS94QbpxN_A6MCtQC4/edit?gid=456846762#gid=456846762"
gs4_auth(path = "gs4-auth.json")

# DATE LOGIC (CHICAGO TIME)
today_chicago <- as.Date(with_tz(Sys.time(), tzone = "America/Chicago"))
current_year <- year(today_chicago)
season_year <- if (format(today_chicago, "%m-%d") < "04-01") current_year - 1 else current_year
board_year <- current_year
cutoff_date <- today_chicago - 14

print(paste("Season year:", season_year, "| Board year:", board_year, "| Cutoff:", cutoff_date))

# =====================================================
# HELPER FUNCTIONS
# =====================================================
safe_col <- function(df, col_name) {
  if (!is.na(col_name) && col_name %in% names(df)) df[[col_name]] else rep(NA, nrow(df))
}

safe_num <- function(x) suppressWarnings(parse_number(as.character(x)))
safe_trim <- function(x) trimws(as.character(x))
safe_upper <- function(x) toupper(safe_trim(x))

safe_first_nonblank <- function(x) {
  x <- x[!is.na(x) & x != ""]
  if (length(x) == 0) return(NA) else return(x[1])
}

safe_last_nonblank <- function(x) {
  x <- x[!is.na(x) & x != ""]
  if (length(x) == 0) return(NA) else return(x[length(x)])
}

safe_mean <- function(x) {
  if (length(x) == 0 || all(is.na(x))) return(NA_real_) else return(mean(x, na.rm = TRUE))
}

ensure_sheet <- function(ss, sheet_name) {
  existing_tabs <- sheet_names(ss)
  if (!(sheet_name %in% existing_tabs)) sheet_add(ss, sheet_name)
}

first_existing_col <- function(df, candidates) {
  found <- candidates[candidates %in% names(df)]
  if (length(found) == 0) return(NA_character_) else return(found[1])
}

# PERCENTILE CALCULATION
calculate_percentile <- function(value, reference_vector) {
  if (is.na(value)) return(NA_real_)
  mean(reference_vector <= value, na.rm = TRUE) * 100
}

# ROBUST DATA FETCHERS
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
        if (!is.null(out) && nrow(out) > 0) {
          out$source_fg_id <- as.character(player_id)
          names(out) <- trimws(names(out))
          return(out)
        }
      }
    }
  }
  return(NULL)
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
        if (!is.null(out) && nrow(out) > 0) {
          out$source_fg_id <- as.character(player_id)
          names(out) <- trimws(names(out))
          return(out)
        }
      }
    }
  }
  return(NULL)
}

# SCORING HELPER FUNCTIONS
calculate_volatility_risk <- function(season_score, trend_score) {
  abs(season_score - trend_score)
}

calculate_hitter_risk <- function(pt_risk = 0, volatility = 0, k_risk = 0, role_risk = 0) {
  (pt_risk * 0.30 + volatility * 0.25 + k_risk * 0.25 + role_risk * 0.20)
}

calculate_sp_risk <- function(role_risk = 0, command_risk = 0, volatility = 0, stuff_risk = 0) {
  (role_risk * 0.30 + command_risk * 0.25 + volatility * 0.25 + stuff_risk * 0.20)
}

calculate_rp_risk <- function(role_risk = 0, command_risk = 0, usage_vol = 0, save_context = 0) {
  (role_risk * 0.35 + command_risk * 0.25 + usage_vol * 0.20 + save_context * 0.20)
}

calculate_prospect_hitter_risk <- function(k_risk = 0, age_level_risk = 0, sample_risk = 0, vol = 0) {
  (k_risk * 0.30 + age_level_risk * 0.25 + sample_risk * 0.25 + vol * 0.20)
}

calculate_prospect_pitcher_risk <- function(command_risk = 0, role_risk = 0, age_level_risk = 0, vol = 0) {
  (command_risk * 0.30 + role_risk * 0.25 + age_level_risk * 0.20 + vol * 0.25)
}

# FLAG GENERATION
generate_flags <- function(season_score, trend_score, player_type = "hitter") {
  trend_diff <- trend_score - season_score
  
  trend_flag <- if (trend_diff >= 20) "🔥" 
                else if (trend_diff >= 10) "📈"
                else if (trend_diff <= -20) "❄️"
                else if (trend_diff <= -10) "📉"
                else ""
  
  breakout_flag <- if (trend_score >= 75 && trend_diff >= 12 && season_score < 60) "🔥" else ""
  breakout_watch <- if (trend_score >= 80 && season_score >= 45 && season_score <= 60) "👀" else ""
  
  regression_flag <- if (season_score >= 70 && trend_score <= season_score - 12) "🛑" else ""
  
  list(
    trend_flag = trend_flag,
    breakout_flag = breakout_flag,
    breakout_watch = breakout_watch,
    regression_flag = regression_flag
  )
}

# FANGRAPHS FV SCRAPER
scrape_fangraphs_fv <- function(board_year) {
  board_url <- paste0("https://www.fangraphs.com/prospects/the-board/", board_year, "-prospect-list?type=0")
  message(paste("Scraping FanGraphs FV from:", board_url))
  
  page <- read_html(board_url)
  tables <- page %>% html_elements("table") %>% html_table(fill = TRUE)
  
  if (length(tables) == 0) {
    warning("No tables found on FanGraphs Board page.")
    return(tibble())
  }
  
  board_tbl <- NULL
  for (tbl in tables) {
    nm <- names(tbl)
    if (length(nm) > 0 && 
        any(str_detect(nm, regex("^Name$", ignore_case = TRUE))) &&
        any(str_detect(nm, regex("^Org$", ignore_case = TRUE))) &&
        any(str_detect(nm, regex("^FV$", ignore_case = TRUE)))) {
      board_tbl <- tbl
      break
    }
  }
  
  if (is.null(board_tbl)) {
    widths <- purrr::map_int(tables, ncol)
    board_tbl <- tables[[which.max(widths)]]
  }
  
  board_tbl <- board_tbl %>% janitor::clean_names()
  
  name_col <- names(board_tbl)[str_detect(names(board_tbl), "^name$|player|prospect")][1]
  org_col <- names(board_tbl)[str_detect(names(board_tbl), "^org$|organization")][1]
  fv_col <- names(board_tbl)[str_detect(names(board_tbl), "^fv$|future_value")][1]
  
  if (is.na(name_col) || is.na(fv_col)) {
    warning("Could not find Name/FV columns.")
    return(tibble())
  }
  
  out <- board_tbl %>%
    transmute(
      fg_name = safe_trim(.data[[name_col]]),
      fg_org = if (!is.na(org_col)) safe_trim(.data[[org_col]]) else NA_character_,
      FV = safe_trim(.data[[fv_col]])
    ) %>%
    filter(!is.na(fg_name), fg_name != "", !is.na(FV), FV != "") %>%
    mutate(Name_clean = safe_upper(fg_name), Org_clean = safe_upper(fg_org)) %>%
    distinct(Name_clean, Org_clean, .keep_all = TRUE)
  
  message(paste("Scraped", nrow(out), "prospects with FV."))
  out
}

# =====================================================
# READ TEST TAB & FREE AGENT HELPER TAB
# =====================================================
test_df <- read_sheet(sheet_url, sheet = "Test") %>% as.data.frame(stringsAsFactors = FALSE)
test_df <- test_df %>%
  mutate(
    Player_clean = safe_trim(Player),
    Role_clean = toupper(safe_trim(Role)),
    Level_clean = toupper(safe_trim(Level)),
    Fangraphs_ID_clean = safe_trim(`Fangraphs ID`),
    MiLB_ID_clean = safe_trim(MiLB_FG_ID)
  )

milb_name_lookup <- test_df %>%
  filter(!is.na(MiLB_ID_clean), MiLB_ID_clean != "") %>%
  distinct(MiLB_ID_clean, Player_clean)

# Free Agent Helper Tab (if exists)
fa_helper <- tryCatch({
  read_sheet(sheet_url, sheet = "Free Agent Helper") %>% as.data.frame(stringsAsFactors = FALSE)
}, error = function(e) {
  message("Free Agent Helper tab not found. Continuing with Test tab only.")
  tibble()
})

if (nrow(fa_helper) > 0) {
  fa_helper <- fa_helper %>%
    mutate(
      MLBID_clean = safe_trim(ifelse(ncol(.) >= 2, .[, 2], NA_character_)),
      FG_ID_clean = safe_trim(ifelse(ncol(.) >= 3, .[, 3], NA_character_)),
      Player_Name_clean = safe_trim(ifelse(ncol(.) >= 4, .[, 4], NA_character_)),
      Team_clean = safe_trim(ifelse(ncol(.) >= 5, .[, 5], NA_character_))
    )
}

# =====================================================
# GET IDS FROM TEST TAB
# =====================================================
mlb_hit_ids <- test_df %>%
  filter(Level_clean == "MLB", Role_clean == "H", !is.na(Fangraphs_ID_clean), Fangraphs_ID_clean != "") %>%
  pull(Fangraphs_ID_clean) %>% unique()

mlb_pitch_ids <- test_df %>%
  filter(Level_clean == "MLB", Role_clean == "P", !is.na(Fangraphs_ID_clean), Fangraphs_ID_clean != "") %>%
  pull(Fangraphs_ID_clean) %>% unique()

milb_hit_ids <- test_df %>%
  filter(Level_clean == "MILB", Role_clean == "H", !is.na(MiLB_ID_clean), MiLB_ID_clean != "") %>%
  pull(MiLB_ID_clean) %>% unique()

milb_pitch_ids <- test_df %>%
  filter(Level_clean == "MILB", Role_clean == "P", !is.na(MiLB_ID_clean), MiLB_ID_clean != "") %>%
  pull(MiLB_ID_clean) %>% unique()

# =====================================================
# MLB SEASON DATA - HITTERS
# =====================================================
mlb_hitters_all <- fg_batter_leaders(startseason = season_year, endseason = season_year, qual = 0) %>%
  rename_with(trimws)

mlb_hitters_out <- mlb_hitters_all %>%
  mutate(
    fangraphs_id = as.character(safe_col(., "playerid")),
    Name = if ("PlayerName" %in% names(.)) safe_col(., "PlayerName") else safe_col(., "Name"),
    Team = safe_col(., "team_name"),
    Age = safe_col(., "Age"),
    G = safe_col(., "G"),
    PA = safe_col(., "PA"),
    HR = safe_col(., "HR"),
    SB = safe_col(., "SB"),
    AVG = safe_col(., "AVG"),
    OBP = safe_col(., "OBP"),
    SLG = safe_col(., "SLG"),
    OPS = safe_col(., "OPS"),
    ISO = safe_col(., "ISO"),
    wOBA = safe_col(., "wOBA"),
    xwOBA = safe_col(., "xwOBA"),
    xBA = safe_col(., "xAVG"),
    xSLG = safe_col(., "xSLG"),
    wRC_plus = safe_col(., "wRC+"),
    BB_percent = safe_col(., "BB%"),
    K_percent = safe_col(., "K%"),
    HardHit_percent = safe_col(., "HardHit%"),
    Barrel_percent = safe_col(., "Barrel%"),
    EV = safe_col(., "EV")
  ) %>%
  select(fangraphs_id, Name, Team, Age, G, PA, HR, SB, AVG, OBP, SLG, OPS, ISO,
         wOBA, xwOBA, xBA, xSLG, wRC_plus, BB_percent, K_percent,
         HardHit_percent, Barrel_percent, EV) %>%
  filter(fangraphs_id %in% mlb_hit_ids)

# ADD PERCENTILES FOR MLB HITTERS
for (i in 1:nrow(mlb_hitters_out)) {
  mlb_hitters_out$ISO_Percentile[i] <- calculate_percentile(mlb_hitters_out$ISO[i], mlb_hitters_all$ISO)
  mlb_hitters_out$BB_Percentile[i] <- calculate_percentile(mlb_hitters_out$BB_percent[i], mlb_hitters_all$`BB%`)
  mlb_hitters_out$K_Percentile[i] <- calculate_percentile(mlb_hitters_out$K_percent[i], mlb_hitters_all$`K%`)
  mlb_hitters_out$wOBA_Percentile[i] <- calculate_percentile(mlb_hitters_out$wOBA[i], mlb_hitters_all$wOBA)
  mlb_hitters_out$wRC_Plus_Percentile[i] <- calculate_percentile(mlb_hitters_out$wRC_plus[i], mlb_hitters_all$`wRC+`)
}

# =====================================================
# MLB SEASON DATA - PITCHERS
# =====================================================
mlb_pitchers_all <- fg_pitcher_leaders(startseason = season_year, endseason = season_year, qual = 0) %>%
  rename_with(trimws)

mlb_pitchers_out <- mlb_pitchers_all %>%
  mutate(
    fangraphs_id = as.character(safe_col(., "playerid")),
    Name = if ("PlayerName" %in% names(.)) safe_col(., "PlayerName") else safe_col(., "Name"),
    Team = safe_col(., "team_name"),
    Age = safe_col(., "Age"),
    G = safe_col(., "G"),
    IP = safe_col(., "IP"),
    ERA = safe_col(., "ERA"),
    xERA = safe_col(., "xERA"),
    WHIP = safe_col(., "WHIP"),
    FIP = safe_col(., "FIP"),
    FIP_minus = safe_col(., "FIP-"),
    xFIP = safe_col(., "xFIP"),
    xFIP_minus = safe_col(., "xFIP-"),
    SIERA = safe_col(., "SIERA"),
    K_percent = safe_col(., "K%"),
    BB_percent = safe_col(., "BB%"),
    K_BB_percent = safe_col(., "K-BB%"),
    SwStr_percent = safe_col(., "SwStr%"),
    HardHit_percent = safe_col(., "HardHit%"),
    Barrel_percent = safe_col(., "Barrel%"),
    EV = safe_col(., "EV"),
    Stuff_plus = if ("Stuff+" %in% names(.)) safe_col(., "Stuff+") else rep(NA, nrow(.)),
    SV = safe_col(., "SV"),
    HLD = if ("HLD" %in% names(.)) safe_col(., "HLD") else if ("HD" %in% names(.)) safe_col(., "HD") else rep(NA, nrow(.))
  ) %>%
  mutate(
    SV_num = safe_num(SV),
    HLD_num = safe_num(HLD),
    SV_HLD = SV_num + HLD_num
  ) %>%
  select(fangraphs_id, Name, Team, Age, G, IP, ERA, xERA, WHIP, FIP, FIP_minus,
         xFIP, xFIP_minus, SIERA, K_percent, BB_percent, K_BB_percent,
         SwStr_percent, HardHit_percent, Barrel_percent, EV, Stuff_plus, SV, HLD, SV_HLD) %>%
  filter(fangraphs_id %in% mlb_pitch_ids)

# ADD PERCENTILES FOR MLB PITCHERS (inverted for FIP)
for (i in 1:nrow(mlb_pitchers_out)) {
  mlb_pitchers_out$FIP_Percentile[i] <- 100 - calculate_percentile(mlb_pitchers_out$FIP[i], mlb_pitchers_all$FIP)
  mlb_pitchers_out$K_Percentile[i] <- calculate_percentile(mlb_pitchers_out$K_percent[i], mlb_pitchers_all$`K%`)
  mlb_pitchers_out$BB_Percentile[i] <- calculate_percentile(mlb_pitchers_out$BB_percent[i], mlb_pitchers_all$`BB%`)
  mlb_pitchers_out$Velo_Percentile[i] <- calculate_percentile(mlb_pitchers_out$EV[i], mlb_pitchers_all$EV)
}

# =====================================================
# MLB LAST 14 DAYS - HITTERS
# =====================================================
mlb_hit_logs <- map_dfr(mlb_hit_ids, function(pid) fetch_mlb_hitter_logs(pid, season_year))

if (nrow(mlb_hit_logs) > 0) {
  date_col <- first_existing_col(mlb_hit_logs, c("Date", "date", "GameDate", "gamedate"))
  pa_col <- first_existing_col(mlb_hit_logs, c("PA"))
  ab_col <- first_existing_col(mlb_hit_logs, c("AB"))
  h_col <- first_existing_col(mlb_hit_logs, c("H"))
  hr_col <- first_existing_col(mlb_hit_logs, c("HR"))
  sb_col <- first_existing_col(mlb_hit_logs, c("SB"))
  bb_col <- first_existing_col(mlb_hit_logs, c("BB"))
  so_col <- first_existing_col(mlb_hit_logs, c("SO", "K"))
  iso_col <- first_existing_col(mlb_hit_logs, c("ISO"))
  woba_col <- first_existing_col(mlb_hit_logs, c("wOBA"))
  xwoba_col <- first_existing_col(mlb_hit_logs, c("xwOBA"))
  hh_col <- first_existing_col(mlb_hit_logs, c("HardHit%", "HardHit_pct"))
  barrel_col <- first_existing_col(mlb_hit_logs, c("Barrel%", "Barrel_pct"))
  ev_col <- first_existing_col(mlb_hit_logs, c("EV"))
  
  mlb_hit_logs <- mlb_hit_logs %>%
    mutate(
      Date2 = as.Date(safe_col(., date_col)),
      PA_num = safe_num(safe_col(., pa_col)),
      AB_num = safe_num(safe_col(., ab_col)),
      H_num = safe_num(safe_col(., h_col)),
      HR_num = safe_num(safe_col(., hr_col)),
      SB_num = safe_num(safe_col(., sb_col)),
      BB_num = safe_num(safe_col(., bb_col)),
      SO_num = safe_num(safe_col(., so_col)),
      ISO_num = safe_num(safe_col(., iso_col)),
      wOBA_num = safe_num(safe_col(., woba_col)),
      xwOBA_num = safe_num(safe_col(., xwoba_col)),
      HardHit_num = safe_num(safe_col(., hh_col)),
      Barrel_num = safe_num(safe_col(., barrel_col)),
      EV_num = safe_num(safe_col(., ev_col))
    )
  
  mlb_hit_last14 <- mlb_hit_logs %>%
    filter(!is.na(Date2), Date2 >= cutoff_date) %>%
    group_by(source_fg_id) %>%
    summarise(
      last14_G = n(),
      last14_PA = sum(PA_num, na.rm = TRUE),
      last14_AB = sum(AB_num, na.rm = TRUE),
      last14_H = sum(H_num, na.rm = TRUE),
      last14_HR = sum(HR_num, na.rm = TRUE),
      last14_SB = sum(SB_num, na.rm = TRUE),
      last14_BB = sum(BB_num, na.rm = TRUE),
      last14_SO = sum(SO_num, na.rm = TRUE),
      last14_AVG = ifelse(last14_AB > 0, last14_H / last14_AB, NA_real_),
      last14_ISO = safe_mean(ISO_num),
      last14_wOBA = safe_mean(wOBA_num),
      last14_xwOBA = safe_mean(xwOBA_num),
      last14_HardHit_percent = safe_mean(HardHit_num),
      last14_Barrel_percent = safe_mean(Barrel_num),
      last14_EV = safe_mean(EV_num),
      .groups = "drop"
    )
  
  mlb_hitters_out <- mlb_hitters_out %>%
    left_join(mlb_hit_last14, by = c("fangraphs_id" = "source_fg_id"))
} else {
  mlb_hitters_out <- mlb_hitters_out %>%
    mutate(
      last14_G = NA, last14_PA = NA, last14_AB = NA, last14_H = NA, last14_HR = NA,
      last14_SB = NA, last14_BB = NA, last14_SO = NA, last14_AVG = NA, last14_ISO = NA,
      last14_wOBA = NA, last14_xwOBA = NA, last14_HardHit_percent = NA,
      last14_Barrel_percent = NA, last14_EV = NA
    )
}

# =====================================================
# MLB LAST 14 DAYS - PITCHERS
# =====================================================
mlb_pitch_logs <- map_dfr(mlb_pitch_ids, function(pid) fetch_mlb_pitcher_logs(pid, season_year))

if (nrow(mlb_pitch_logs) > 0) {
  date_col <- first_existing_col(mlb_pitch_logs, c("Date", "date", "GameDate", "gamedate"))
  ip_col <- first_existing_col(mlb_pitch_logs, c("IP"))
  er_col <- first_existing_col(mlb_pitch_logs, c("ER"))
  h_col <- first_existing_col(mlb_pitch_logs, c("H"))
  hr_col <- first_existing_col(mlb_pitch_logs, c("HR"))
  bb_col <- first_existing_col(mlb_pitch_logs, c("BB"))
  so_col <- first_existing_col(mlb_pitch_logs, c("SO", "K"))
  tbf_col <- first_existing_col(mlb_pitch_logs, c("TBF"))
  fip_col <- first_existing_col(mlb_pitch_logs, c("FIP"))
  xfip_col <- first_existing_col(mlb_pitch_logs, c("xFIP"))
  siera_col <- first_existing_col(mlb_pitch_logs, c("SIERA"))
  kpct_col <- first_existing_col(mlb_pitch_logs, c("K%", "K_pct"))
  bbpct_col <- first_existing_col(mlb_pitch_logs, c("BB%", "BB_pct"))
  swstr_col <- first_existing_col(mlb_pitch_logs, c("SwStr%", "SwStr_pct"))
  ev_col <- first_existing_col(mlb_pitch_logs, c("EV"))
  
  mlb_pitch_logs <- mlb_pitch_logs %>%
    mutate(
      Date2 = as.Date(safe_col(., date_col)),
      IP_num = safe_num(safe_col(., ip_col)),
      ER_num = safe_num(safe_col(., er_col)),
      H_num = safe_num(safe_col(., h_col)),
      HR_num = safe_num(safe_col(., hr_col)),
      BB_num = safe_num(safe_col(., bb_col)),
      SO_num = safe_num(safe_col(., so_col)),
      TBF_num = safe_num(safe_col(., tbf_col)),
      FIP_num = safe_num(safe_col(., fip_col)),
      xFIP_num = safe_num(safe_col(., xfip_col)),
      SIERA_num = safe_num(safe_col(., siera_col)),
      K_percent_num = safe_num(safe_col(., kpct_col)),
      BB_percent_num = safe_num(safe_col(., bbpct_col)),
      SwStr_percent_num = safe_num(safe_col(., swstr_col)),
      EV_num = safe_num(safe_col(., ev_col))
    )
  
  mlb_pitch_last14 <- mlb_pitch_logs %>%
    filter(!is.na(Date2), Date2 >= cutoff_date) %>%
    group_by(source_fg_id) %>%
    summarise(
      last14_G = n(),
      last14_IP = sum(IP_num, na.rm = TRUE),
      last14_H = sum(H_num, na.rm = TRUE),
      last14_ER = sum(ER_num, na.rm = TRUE),
      last14_HR = sum(HR_num, na.rm = TRUE),
      last14_BB = sum(BB_num, na.rm = TRUE),
      last14_SO = sum(SO_num, na.rm = TRUE),
      last14_TBF = sum(TBF_num, na.rm = TRUE),
      last14_ERA = ifelse(last14_IP > 0, 9 * last14_ER / last14_IP, NA_real_),
      last14_FIP = safe_mean(FIP_num),
      last14_xFIP = safe_mean(xFIP_num),
      last14_SIERA = safe_mean(SIERA_num),
      last14_K_percent = ifelse(last14_TBF > 0, last14_SO / last14_TBF, NA_real_),
      last14_BB_percent = ifelse(last14_TBF > 0, last14_BB / last14_TBF, NA_real_),
      last14_SwStr_percent = safe_mean(SwStr_percent_num),
      last14_EV = safe_mean(EV_num),
      .groups = "drop"
    )
  
  mlb_pitchers_out <- mlb_pitchers_out %>%
    left_join(mlb_pitch_last14, by = c("fangraphs_id" = "source_fg_id"))
} else {
  mlb_pitchers_out <- mlb_pitchers_out %>%
    mutate(
      last14_G = NA, last14_IP = NA, last14_H = NA, last14_ER = NA, last14_HR = NA,
      last14_BB = NA, last14_SO = NA, last14_TBF = NA, last14_ERA = NA, last14_FIP = NA,
      last14_xFIP = NA, last14_SIERA = NA, last14_K_percent = NA, last14_BB_percent = NA,
      last14_SwStr_percent = NA, last14_EV = NA
    )
}

# =====================================================
# MiLB HITTERS
# =====================================================
milb_hit_logs <- map_dfr(milb_hit_ids, function(pid) {
  tryCatch(
    {x <- fg_milb_batter_game_logs(playerid = as.character(pid), year = season_year)
     if (is.null(x) || nrow(x) == 0) return(NULL)
     x$source_milb_id <- as.character(pid)
     names(x) <- trimws(names(x))
     x},
    error = function(e) NULL
  )
})

if (nrow(milb_hit_logs) > 0) {
  name_col_milb_hit <- first_existing_col(milb_hit_logs, c("Name", "PlayerName", "player_name", "Player"))
  team_col_milb_hit <- first_existing_col(milb_hit_logs, c("Team", "Tm", "team_name"))
  level_col_milb_hit <- first_existing_col(milb_hit_logs, c("Level", "level"))
  
  milb_hit_logs <- milb_hit_logs %>%
    mutate(
      Date2 = as.Date(safe_col(., "Date")),
      PA_num = safe_num(safe_col(., "PA")),
      AB_num = safe_num(safe_col(., "AB")),
      H_num = safe_num(safe_col(., "H")),
      HR_num = safe_num(safe_col(., "HR")),
      SO_num = safe_num(safe_col(., "SO")),
      BB_num = safe_num(safe_col(., "BB")),
      ISO_num = safe_num(safe_col(., "ISO")),
      wOBA_num = safe_num(safe_col(., "wOBA")),
      BB_pct_num = safe_num(safe_col(., "BB%")),
      K_pct_num = safe_num(safe_col(., "K%"))
    )
  
  milb_hitters_out <- milb_hit_logs %>%
    group_by(source_milb_id) %>%
    summarise(
      minor_playerid = first(source_milb_id),
      Name = safe_last_nonblank(safe_col(pick(everything()), name_col_milb_hit)),
      Team = safe_last_nonblank(safe_col(pick(everything()), team_col_milb_hit)),
      Level = safe_last_nonblank(safe_col(pick(everything()), level_col_milb_hit)),
      G = n(),
      PA = sum(PA_num, na.rm = TRUE),
      AB = sum(AB_num, na.rm = TRUE),
      H = sum(H_num, na.rm = TRUE),
      HR = sum(HR_num, na.rm = TRUE),
      SO = sum(SO_num, na.rm = TRUE),
      BB = sum(BB_num, na.rm = TRUE),
      AVG = ifelse(AB > 0, H / AB, NA_real_),
      ISO = safe_mean(ISO_num),
      wOBA = safe_mean(wOBA_num),
      BB_percent = safe_mean(BB_pct_num),
      K_percent = safe_mean(K_pct_num),
      .groups = "drop"
    ) %>%
    left_join(milb_name_lookup, by = c("minor_playerid" = "MiLB_ID_clean")) %>%
    mutate(Name = coalesce(Name, Player_clean)) %>%
    select(-Player_clean)
  
  # ADD PERCENTILES BY LEVEL FOR MiLB HITTERS
  for (level in unique(milb_hitters_out$Level)) {
    level_data <- milb_hitters_out %>% filter(Level == level)
    level_indices <- which(milb_hitters_out$Level == level)
    
    for (idx in level_indices) {
      milb_hitters_out$ISO_Percentile[idx] <- calculate_percentile(milb_hitters_out$ISO[idx], level_data$ISO)
      milb_hitters_out$BB_Percentile[idx] <- calculate_percentile(milb_hitters_out$BB_percent[idx], level_data$BB_percent)
      milb_hitters_out$K_Percentile[idx] <- calculate_percentile(milb_hitters_out$K_percent[idx], level_data$K_percent)
      milb_hitters_out$wOBA_Percentile[idx] <- calculate_percentile(milb_hitters_out$wOBA[idx], level_data$wOBA)
    }
  }
  
  milb_hit_last14 <- milb_hit_logs %>%
    filter(!is.na(Date2), Date2 >= cutoff_date) %>%
    group_by(source_milb_id) %>%
    summarise(
      last14_G = n(),
      last14_PA = sum(PA_num, na.rm = TRUE),
      last14_ISO = safe_mean(ISO_num),
      last14_wOBA = safe_mean(wOBA_num),
      last14_BB_percent = safe_mean(BB_pct_num),
      last14_K_percent = safe_mean(K_pct_num),
      .groups = "drop"
    )
  
  milb_hitters_out <- milb_hitters_out %>%
    left_join(milb_hit_last14, by = c("minor_playerid" = "source_milb_id"))
} else {
  milb_hitters_out <- tibble()
}

# =====================================================
# MiLB PITCHERS
# =====================================================
milb_pitch_logs <- map_dfr(milb_pitch_ids, function(pid) {
  tryCatch(
    {x <- fg_milb_pitcher_game_logs(playerid = as.character(pid), year = season_year)
     if (is.null(x) || nrow(x) == 0) return(NULL)
     x$source_milb_id <- as.character(pid)
     names(x) <- trimws(names(x))
     x},
    error = function(e) NULL
  )
})

if (nrow(milb_pitch_logs) > 0) {
  name_col_milb_pitch <- first_existing_col(milb_pitch_logs, c("Name", "PlayerName", "player_name", "Player"))
  team_col_milb_pitch <- first_existing_col(milb_pitch_logs, c("Team", "Tm", "team_name"))
  level_col_milb_pitch <- first_existing_col(milb_pitch_logs, c("Level", "level"))
  
  milb_pitch_logs <- milb_pitch_logs %>%
    mutate(
      Date2 = as.Date(safe_col(., "Date")),
      IP_num = safe_num(safe_col(., "IP")),
      TBF_num = safe_num(safe_col(., "TBF")),
      SO_num = safe_num(safe_col(., "SO")),
      BB_num = safe_num(safe_col(., "BB")),
      FIP_num = safe_num(safe_col(., "FIP")),
      K_pct_num = safe_num(safe_col(., "K%")),
      BB_pct_num = safe_num(safe_col(., "BB%")),
      EV_num = safe_num(safe_col(., "EV"))
    )
  
  milb_pitchers_out <- milb_pitch_logs %>%
    group_by(source_milb_id) %>%
    summarise(
      minor_playerid = first(source_milb_id),
      Name = safe_last_nonblank(safe_col(pick(everything()), name_col_milb_pitch)),
      Team = safe_last_nonblank(safe_col(pick(everything()), team_col_milb_pitch)),
      Level = safe_last_nonblank(safe_col(pick(everything()), level_col_milb_pitch)),
      G = n(),
      IP = sum(IP_num, na.rm = TRUE),
      TBF = sum(TBF_num, na.rm = TRUE),
      SO = sum(SO_num, na.rm = TRUE),
      BB = sum(BB_num, na.rm = TRUE),
      FIP = safe_mean(FIP_num),
      K_percent = ifelse(TBF > 0, SO / TBF, NA_real_),
      BB_percent = ifelse(TBF > 0, BB / TBF, NA_real_),
      EV = safe_mean(EV_num),
      .groups = "drop"
    ) %>%
    left_join(milb_name_lookup, by = c("minor_playerid" = "MiLB_ID_clean")) %>%
    mutate(Name = coalesce(Name, Player_clean)) %>%
    select(-Player_clean)
  
  # ADD PERCENTILES BY LEVEL FOR MiLB PITCHERS (FIP inverted)
  for (level in unique(milb_pitchers_out$Level)) {
    level_data <- milb_pitchers_out %>% filter(Level == level)
    level_indices <- which(milb_pitchers_out$Level == level)
    
    for (idx in level_indices) {
      milb_pitchers_out$FIP_Percentile[idx] <- 100 - calculate_percentile(milb_pitchers_out$FIP[idx], level_data$FIP)
      milb_pitchers_out$K_Percentile[idx] <- calculate_percentile(milb_pitchers_out$K_percent[idx], level_data$K_percent)
      milb_pitchers_out$BB_Percentile[idx] <- calculate_percentile(milb_pitchers_out$BB_percent[idx], level_data$BB_percent)
      milb_pitchers_out$Velo_Percentile[idx] <- calculate_percentile(milb_pitchers_out$EV[idx], level_data$EV)
    }
  }
  
  milb_pitch_last14 <- milb_pitch_logs %>%
    filter(!is.na(Date2), Date2 >= cutoff_date) %>%
    group_by(source_milb_id) %>%
    summarise(
      last14_G = n(),
      last14_IP = sum(IP_num, na.rm = TRUE),
      last14_FIP = safe_mean(FIP_num),
      last14_K_percent = safe_mean(K_pct_num),
      last14_BB_percent = safe_mean(BB_pct_num),
      last14_EV = safe_mean(EV_num),
      .groups = "drop"
    )
  
  milb_pitchers_out <- milb_pitchers_out %>%
    left_join(milb_pitch_last14, by = c("minor_playerid" = "source_milb_id"))
} else {
  milb_pitchers_out <- tibble()
}

# =====================================================
# FANGRAPHS FV
# =====================================================
fv_lookup <- tryCatch(scrape_fangraphs_fv(board_year), error = function(e) {
  message(paste("FV scrape failed:", e$message))
  tibble()
})

if (nrow(fv_lookup) > 0) {
  if (nrow(milb_hitters_out) > 0) {
    milb_hitters_out <- milb_hitters_out %>%
      mutate(Name_clean = safe_upper(Name), Team_clean = safe_upper(Team)) %>%
      left_join(fv_lookup %>% select(Name_clean, Org_clean, FV), 
                by = c("Name_clean", "Team_clean" = "Org_clean")) %>%
      select(-Name_clean, -Team_clean)
  }
  
  if (nrow(milb_pitchers_out) > 0) {
    milb_pitchers_out <- milb_pitchers_out %>%
      mutate(Name_clean = safe_upper(Name), Team_clean = safe_upper(Team)) %>%
      left_join(fv_lookup %>% select(Name_clean, Org_clean, FV),
                by = c("Name_clean", "Team_clean" = "Org_clean")) %>%
      select(-Name_clean, -Team_clean)
  }
}

# =====================================================
# WRITE RAW SHEETS
# =====================================================
ensure_sheet(sheet_url, "raw_hitters")
ensure_sheet(sheet_url, "raw_pitchers")
ensure_sheet(sheet_url, "raw_milb_hitters")
ensure_sheet(sheet_url, "raw_milb_pitchers")

range_write(ss = sheet_url, data = mlb_hitters_out, sheet = "raw_hitters", col_names = TRUE, reformat = FALSE)
range_write(ss = sheet_url, data = mlb_pitchers_out, sheet = "raw_pitchers", col_names = TRUE, reformat = FALSE)

if (nrow(milb_hitters_out) > 0) {
  range_write(ss = sheet_url, data = milb_hitters_out, sheet = "raw_milb_hitters", col_names = TRUE, reformat = FALSE)
}

if (nrow(milb_pitchers_out) > 0) {
  range_write(ss = sheet_url, data = milb_pitchers_out, sheet = "raw_milb_pitchers", col_names = TRUE, reformat = FALSE)
}

print("✅ Raw sheets written successfully!")

# =====================================================
# SCORING SHEETS (PLACEHOLDER STRUCTURE)
# =====================================================
# This section creates basic scoring structures
# You can expand these with your specific scoring logic

fa_hitters <- tibble(Name = character(), Season_Score = numeric(), Trend_Score = numeric(),
                     Risk_Score = numeric(), Final_Score = numeric(), Trend_Flag = character())

fa_pitchers <- tibble(Name = character(), Season_Score = numeric(), Trend_Score = numeric(),
                      Risk_Score = numeric(), Final_Score = numeric(), Trend_Flag = character())

fa_relievers <- tibble(Name = character(), Season_Score = numeric(), Trend_Score = numeric(),
                       Risk_Score = numeric(), Final_Score = numeric(), Trend_Flag = character())

fa_prospect_hitters <- tibble(Name = character(), Season_Score = numeric(), Trend_Score = numeric(),
                              Risk_Score = numeric(), Upside_Score = numeric(), Final_Score = numeric())

fa_prospect_pitchers <- tibble(Name = character(), Season_Score = numeric(), Trend_Score = numeric(),
                               Risk_Score = numeric(), Upside_Score = numeric(), Final_Score = numeric())

# Rostered versions (same structure)
rostered_hitters <- fa_hitters
rostered_pitchers <- fa_pitchers
rostered_relievers <- fa_relievers
rostered_prospect_hitters <- fa_prospect_hitters
rostered_prospect_pitchers <- fa_prospect_pitchers

print("✅ Script execution completed successfully!")
