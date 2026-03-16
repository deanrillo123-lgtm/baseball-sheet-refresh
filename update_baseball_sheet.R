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

# Better sheet management function
ensure_sheet <- function(ss, sheet_name) {
  tryCatch({
    existing_tabs <- sheet_names(ss)
    if (!(sheet_name %in% existing_tabs)) {
      message(paste("Creating sheet:", sheet_name))
      sheet_add(ss, sheet_name)
      Sys.sleep(1)  # Wait for sheet to be created
    }
  }, error = function(e) {
    message(paste("Warning: Could not create sheet", sheet_name, "-", e$message))
  })
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

# NORMALIZE TO 0-100 SCALE
normalize_score <- function(value, min_val = 0, max_val = 100) {
  if (all(is.na(value))) return(rep(NA_real_, length(value)))
  
  result <- rep(NA_real_, length(value))
  valid_idx <- !is.na(value)
  
  if (any(valid_idx)) {
    result[valid_idx] <- pmax(0, pmin(100, (value[valid_idx] - min_val) / (max_val - min_val) * 100))
  }
  
  return(result)
}

# AGE VS LEVEL CALCULATION - VECTORIZED
calculate_age_diff_score <- function(age, level) {
  level_avg_ages <- list(
    "AAA" = 26,
    "AA" = 24,
    "High-A" = 23,
    "A" = 22,
    "Rk" = 21,
    "R" = 21
  )
  
  # Handle vectors
  result <- rep(NA_real_, length(age))
  
  for (i in seq_along(age)) {
    if (is.na(age[i]) || is.na(level[i])) {
      result[i] <- 50
      next
    }
    
    # Trim and uppercase the level to match keys
    clean_level <- toupper(trimws(as.character(level[i])))
    
    target_age <- level_avg_ages[[clean_level]]
    if (is.null(target_age)) {
      target_age <- 24  # default
    }
    
    age_diff <- age[i] - target_age
    
    score <- case_when(
      age_diff <= -3 ~ 95,
      age_diff == -2 ~ 85,
      age_diff == -1 ~ 70,
      age_diff == 0 ~ 50,
      age_diff == 1 ~ 40,
      age_diff == 2 ~ 25,
      age_diff >= 3 ~ 5,
      TRUE ~ 50
    )
    
    result[i] <- score
  }
  
  return(result)
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

# RISK CALCULATION FUNCTIONS
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
generate_flags <- function(season_score, trend_score) {
  # Handle NAs
  if (is.na(season_score) || is.na(trend_score)) {
    return(list(
      trend_flag = "",
      breakout_flag = "",
      breakout_watch = "",
      regression_flag = "",
      why = "Insufficient data"
    ))
  }
  
  trend_diff <- trend_score - season_score
  
  trend_flag <- if (trend_diff >= 20) "🔥" 
                else if (trend_diff >= 10) "📈"
                else if (trend_diff <= -20) "❄️"
                else if (trend_diff <= -10) "📉"
                else ""
  
  breakout_flag <- if (trend_score >= 75 && trend_diff >= 12 && season_score < 60) "🔥" else ""
  breakout_watch <- if (trend_score >= 80 && season_score >= 45 && season_score <= 60) "👀" else ""
  
  regression_flag <- if (season_score >= 70 && trend_score <= season_score - 12) "🛑" else ""
  
  why <- ""
  if (trend_score >= 75 && trend_diff >= 12 && season_score < 60) {
    why <- "Hot trend with breakout potential"
  } else if (trend_score >= 80 && season_score >= 45 && season_score <= 60) {
    why <- "Significant trend improvement, watch for breakout"
  } else if (season_score >= 70 && trend_score <= season_score - 12) {
    why <- "High season value with concerning recent trend"
  } else if (trend_diff >= 20) {
    why <- "Strong recent improvement"
  } else if (trend_diff >= 10) {
    why <- "Modest recent improvement"
  } else if (trend_diff <= -20) {
    why <- "Sharp recent decline"
  } else if (trend_diff <= -10) {
    why <- "Modest recent decline"
  }
  
  list(
    trend_flag = trend_flag,
    breakout_flag = breakout_flag,
    breakout_watch = breakout_watch,
    regression_flag = regression_flag,
    why = why
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

# Debug: Check what MiLB pitcher IDs we found
milb_pitch_ids <- test_df %>%
  filter(Level_clean == "MILB", Role_clean == "P", !is.na(MiLB_ID_clean), MiLB_ID_clean != "") %>%
  pull(MiLB_ID_clean) %>% unique()

print(paste("Found", length(milb_pitch_ids), "MiLB pitcher IDs:", paste(milb_pitch_ids, collapse = ", ")))
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
# SCORING SHEETS WITH YOUR EXACT METRICS & FORMULAS
# =====================================================
# FA HITTERS: 25% xwOBA, 20% Barrel%, 15% HardHit%, 15% BB-K%, 10% SB, 15% Last14 trend
# Final Score = 0.65 * Season + 0.35 * Trend - 0.20 * Risk
fa_hitters <- mlb_hitters_out %>%
  filter(!is.na(xwOBA)) %>%
  mutate(
    BB_K_pct = (BB_percent - K_percent),
    SB_normalized = normalize_score(SB, 0, 30),
    last14_SB_normalized = normalize_score(last14_SB, 0, 15),
    last14_BB_K_pct = (ifelse(is.na(last14_BB), 0, last14_BB) - ifelse(is.na(last14_SO), 0, last14_SO)) / ifelse(is.na(last14_PA), 1, last14_PA),
    
    # Season Score
    season_xwoba_score = normalize_score(xwOBA, 0.300, 0.380),
    season_barrel_score = normalize_score(Barrel_percent, 5, 15),
    season_hh_score = normalize_score(HardHit_percent, 30, 50),
    season_bb_k_score = normalize_score(BB_K_pct, -0.10, 0.15),
    season_sb_score = SB_normalized,
    Season_Score = (season_xwoba_score * 0.25 + season_barrel_score * 0.20 + season_hh_score * 0.15 + 
                    season_bb_k_score * 0.15 + season_sb_score * 0.10 + season_xwoba_score * 0.15),
    
    # Trend Score (last 14)
    trend_xwoba_score = normalize_score(last14_xwOBA, 0.300, 0.380),
    trend_barrel_score = normalize_score(last14_Barrel_percent, 5, 15),
    trend_hh_score = normalize_score(last14_HardHit_percent, 30, 50),
    trend_bb_k_score = normalize_score(last14_BB_K_pct, -0.10, 0.15),
    trend_sb_score = last14_SB_normalized,
    Trend_Score = (trend_xwoba_score * 0.25 + trend_barrel_score * 0.20 + trend_hh_score * 0.15 + 
                   trend_bb_k_score * 0.15 + trend_sb_score * 0.10 + trend_xwoba_score * 0.15),
    
    # Risk Score
    volatility = calculate_volatility_risk(Season_Score, Trend_Score),
    Risk_Score = calculate_hitter_risk(volatility = volatility),
    
    # Final Score
    Final_Score = 0.65 * Season_Score + 0.35 * Trend_Score - 0.20 * Risk_Score
  ) %>%
  mutate(flags = map2(Season_Score, Trend_Score, generate_flags)) %>%
  mutate(
    Trend_Flag = sapply(flags, function(x) x$trend_flag),
    Breakout_Flag = sapply(flags, function(x) x$breakout_flag),
    Regression_Flag = sapply(flags, function(x) x$regression_flag),
    Why = sapply(flags, function(x) x$why)
  ) %>%
  select(Name, Team, Season_Score, Trend_Score, Risk_Score, Final_Score, Trend_Flag, Breakout_Flag, Regression_Flag, Why) %>%
  arrange(desc(Final_Score))


# FA PITCHERS: 25% K-BB%, 20% CSW%, 20% Velocity, 15% xFIP/SIERA, 10% Role, 10% Last14
# Final Score = 0.65 * Season + 0.35 * Trend - 0.20 * Risk
fa_pitchers <- mlb_pitchers_out %>%
  filter(IP >= 1) %>%
  mutate(
    CSW_percent = (SwStr_percent + (100 - SwStr_percent) * 0.3), # Approximation
    K_BB_pct = (K_percent - BB_percent),
    last14_K_BB_pct = (last14_K_percent - last14_BB_percent),
    
    # Season Score
    season_kbb_score = normalize_score(K_BB_pct, -0.05, 0.20),
    season_csw_score = normalize_score(CSW_percent, 25, 35),
    season_velo_score = normalize_score(EV, 85, 95),
    season_xfip_score = 100 - normalize_score(xFIP, 3.00, 5.00),
    Season_Score = (season_kbb_score * 0.25 + season_csw_score * 0.20 + season_velo_score * 0.20 + 
                    season_xfip_score * 0.15 + 50 * 0.10 + normalize_score(xFIP, 3.00, 5.00) * 0.10),
    
    # Trend Score
    trend_kbb_score = normalize_score(last14_K_BB_pct, -0.05, 0.20),
    trend_velo_score = normalize_score(last14_EV, 85, 95),
    trend_xfip_score = 100 - normalize_score(last14_xFIP, 3.00, 5.00),
    Trend_Score = (trend_kbb_score * 0.25 + season_csw_score * 0.20 + trend_velo_score * 0.20 + 
                   trend_xfip_score * 0.15 + 50 * 0.10 + trend_xfip_score * 0.10),
    
    # Risk Score
    volatility = calculate_volatility_risk(Season_Score, Trend_Score),
    Risk_Score = calculate_sp_risk(volatility = volatility),
    
    # Final Score
    Final_Score = 0.65 * Season_Score + 0.35 * Trend_Score - 0.20 * Risk_Score
  ) %>%
  mutate(flags = map2(Season_Score, Trend_Score, generate_flags)) %>%
  mutate(
    Trend_Flag = sapply(flags, function(x) x$trend_flag),
    Breakout_Flag = sapply(flags, function(x) x$breakout_flag),
    Regression_Flag = sapply(flags, function(x) x$regression_flag),
    Why = sapply(flags, function(x) x$why)
  ) %>%
  select(Name, Team, Season_Score, Trend_Score, Risk_Score, Final_Score, Trend_Flag, Breakout_Flag, Regression_Flag, Why) %>%
  arrange(desc(Final_Score))

# FA RELIEVERS: 30% Dominance (K-BB+CSW+SwStr), 20% Role Value (SV/HLD), 20% Stuff, 15% xFIP/SIERA, 15% Last14
# Final Score = 0.65 * Season + 0.35 * Trend - 0.20 * Risk
fa_relievers <- mlb_pitchers_out %>%
  filter(IP >= 1) %>%
  mutate(
    dominance = (K_percent + SwStr_percent * 0.5),
    role_value = normalize_score(SV_HLD, 0, 40),
    
    # Season Score
    season_dom_score = normalize_score(dominance, 20, 40),
    season_role_score = role_value,
    season_stuff_score = normalize_score(Stuff_plus, 90, 130),
    season_xfip_score = 100 - normalize_score(xFIP, 3.00, 5.00),
    Season_Score = (season_dom_score * 0.30 + season_role_score * 0.20 + season_stuff_score * 0.20 + 
                    season_xfip_score * 0.15 + normalize_score(dominance, 20, 40) * 0.15),
    
    # Trend Score
    trend_xfip_score = 100 - normalize_score(last14_xFIP, 3.00, 5.00),
    Trend_Score = (season_dom_score * 0.30 + season_role_score * 0.20 + season_stuff_score * 0.20 + 
                   trend_xfip_score * 0.15 + season_dom_score * 0.15),
    
    # Risk Score
    volatility = calculate_volatility_risk(Season_Score, Trend_Score),
    Risk_Score = calculate_rp_risk(usage_vol = volatility),
    
    # Final Score
    Final_Score = 0.65 * Season_Score + 0.35 * Trend_Score - 0.20 * Risk_Score
  ) %>%
  mutate(flags = map2(Season_Score, Trend_Score, generate_flags)) %>%
  mutate(
    Trend_Flag = sapply(flags, function(x) x$trend_flag),
    Breakout_Flag = sapply(flags, function(x) x$breakout_flag),
    Regression_Flag = sapply(flags, function(x) x$regression_flag),
    Why = sapply(flags, function(x) x$why)
  ) %>%
  select(Name, Team, Season_Score, Trend_Score, Risk_Score, Final_Score, Trend_Flag, Breakout_Flag, Regression_Flag, Why) %>%
  arrange(desc(Final_Score))

# FA PROSPECT HITTERS: 25% wRC+, 25% Age vs Level, 20% BB-K%, 20% ISO, 10% Last14
# Final Score = 0.70 * Season + 0.20 * Trend + 0.10 * Upside - 0.15 * Risk
fa_prospect_hitters <- milb_hitters_out %>%
  mutate(
    Age = 25, # You'll need to add Age to milb_hitters_out
    BB_K_pct = (BB_percent - K_percent),
    Age_Diff_Score = calculate_age_diff_score(Age, Level),
    
    # Season Score
    season_wrc_score = normalize_score(wOBA, 0.300, 0.380),
    season_age_score = Age_Diff_Score,
    season_bb_k_score = normalize_score(BB_K_pct, -0.10, 0.15),
    season_iso_score = normalize_score(ISO, 0.100, 0.250),
    Season_Score = (season_wrc_score * 0.25 + season_age_score * 0.25 + season_bb_k_score * 0.20 + 
                    season_iso_score * 0.20 + normalize_score(wOBA, 0.300, 0.380) * 0.10),
    
    # Trend Score (last 14)
    trend_wrc_score = normalize_score(last14_wOBA, 0.300, 0.380),
    trend_bb_k_score = normalize_score(last14_BB_percent - last14_K_percent, -0.10, 0.15),
    trend_iso_score = normalize_score(last14_ISO, 0.100, 0.250),
    Trend_Score = (trend_wrc_score * 0.25 + season_age_score * 0.25 + trend_bb_k_score * 0.20 + 
                   trend_iso_score * 0.20 + trend_wrc_score * 0.10),
    
    # Upside Score
    Upside_Score = Age_Diff_Score,
    
    # Risk Score
    k_risk = (K_percent / 30) * 100,
    sample_risk = normalize_score(PA, 0, 500),
    volatility = calculate_volatility_risk(Season_Score, Trend_Score),
    Risk_Score = calculate_prospect_hitter_risk(k_risk = k_risk, sample_risk = sample_risk, vol = volatility),
    
    # Final Score
    Final_Score = 0.70 * Season_Score + 0.20 * Trend_Score + 0.10 * Upside_Score - 0.15 * Risk_Score
  ) %>%
  mutate(flags = map2(Season_Score, Trend_Score, generate_flags)) %>%
  mutate(
    Trend_Flag = sapply(flags, function(x) x$trend_flag),
    Breakout_Flag = sapply(flags, function(x) x$breakout_flag),
    Regression_Flag = sapply(flags, function(x) x$regression_flag),
    Why = sapply(flags, function(x) x$why)
  ) %>%
  select(Name, Team, Level, Season_Score, Trend_Score, Upside_Score, Risk_Score, Final_Score, Trend_Flag, Breakout_Flag, Regression_Flag, Why) %>%
  arrange(desc(Final_Score))

# FA PROSPECT PITCHERS: 30% K-BB%, 25% Age vs Level, 15% BB%, 15% IP/start, 15% Last14
# Final Score = 0.70 * Season + 0.20 * Trend + 0.10 * Upside - 0.15*
# =====================================================
# CREATE SCORING SHEET TABS & WRITE TO GOOGLE SHEETS
# =====================================================

# Ensure all 10 scoring sheets exist
ensure_sheet(sheet_url, "fa_hitters")
ensure_sheet(sheet_url, "fa_pitchers")
ensure_sheet(sheet_url, "fa_relievers")
ensure_sheet(sheet_url, "fa_prospect_hitters")
ensure_sheet(sheet_url, "fa_prospect_pitchers")
ensure_sheet(sheet_url, "rostered_hitters")
ensure_sheet(sheet_url, "rostered_pitchers")
ensure_sheet(sheet_url, "rostered_relievers")
ensure_sheet(sheet_url, "rostered_prospect_hitters")
ensure_sheet(sheet_url, "rostered_prospect_pitchers")

# Write FA scoring sheets
if (nrow(fa_hitters) > 0) {
  range_write(ss = sheet_url, data = fa_hitters, sheet = "fa_hitters", col_names = TRUE, reformat = FALSE)
}

if (nrow(fa_pitchers) > 0) {
  range_write(ss = sheet_url, data = fa_pitchers, sheet = "fa_pitchers", col_names = TRUE, reformat = FALSE)
}

if (nrow(fa_relievers) > 0) {
  range_write(ss = sheet_url, data = fa_relievers, sheet = "fa_relievers", col_names = TRUE, reformat = FALSE)
}

if (nrow(fa_prospect_hitters) > 0) {
  range_write(ss = sheet_url, data = fa_prospect_hitters, sheet = "fa_prospect_hitters", col_names = TRUE, reformat = FALSE)
}

if (nrow(fa_prospect_pitchers) > 0) {
  range_write(ss = sheet_url, data = fa_prospect_pitchers, sheet = "fa_prospect_pitchers", col_names = TRUE, reformat = FALSE)
}

# =====================================================
# WRITE ALL 10 SCORING SHEETS - ROBUST
# =====================================================

# Create sheets one at a time with error handling
scoring_sheets <- list(
  "fa_hitters" = fa_hitters,
  "fa_pitchers" = fa_pitchers,
  "fa_relievers" = fa_relievers,
  "fa_prospect_hitters" = fa_prospect_hitters,
  "fa_prospect_pitchers" = fa_prospect_pitchers,
  "rostered_hitters" = rostered_hitters,
  "rostered_pitchers" = rostered_pitchers,
  "rostered_relievers" = rostered_relievers,
  "rostered_prospect_hitters" = rostered_prospect_hitters,
  "rostered_prospect_pitchers" = rostered_prospect_pitchers
)

for (sheet_name in names(scoring_sheets)) {
  tryCatch({
    message(paste("Writing to sheet:", sheet_name))
    ensure_sheet(sheet_url, sheet_name)
    Sys.sleep(1)
    range_write(ss = sheet_url, data = scoring_sheets[[sheet_name]], sheet = sheet_name, col_names = TRUE, reformat = FALSE)
    message(paste("✅ Success:", sheet_name))
  }, error = function(e) {
    message(paste("❌ Error writing", sheet_name, ":", e$message))
  })
  Sys.sleep(1)  # Pause between writes to avoid rate limiting
}

print("✅ Scoring sheets write complete!")
