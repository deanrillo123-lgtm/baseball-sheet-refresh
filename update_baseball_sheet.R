library(baseballr)
library(dplyr)
library(googlesheets4)
library(httr)
library(jsonlite)
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

# FOR GITHUB ACTIONS LATER, REPLACE ABOVE WITH:
# gs4_auth(path = "gs4-auth.json")

# -----------------------------
# DATE LOGIC
# BEFORE APRIL 1 = PREVIOUS YEAR
# APRIL 1 OR LATER = CURRENT YEAR
# CHICAGO TIME
# -----------------------------
today_chicago <- as.Date(with_tz(Sys.time(), tzone = "America/Chicago"))
current_year <- year(today_chicago)

if (format(today_chicago, "%m-%d") < "04-01") {
  season_year <- current_year - 1
} else {
  season_year <- current_year
}

board_year <- current_year
cutoff_date <- today_chicago - 14

print(paste("Using season year:", season_year))
print(paste("Using board year:", board_year))
print(paste("Using 14-day cutoff:", cutoff_date))

# -----------------------------
# HELPERS
# -----------------------------
safe_col <- function(df, col_name) {
  if (!is.na(col_name) && col_name %in% names(df)) {
    return(df[[col_name]])
  } else {
    return(rep(NA, nrow(df)))
  }
}

safe_num <- function(x) {
  suppressWarnings(parse_number(as.character(x)))
}

safe_trim <- function(x) {
  trimws(as.character(x))
}

safe_upper <- function(x) {
  toupper(safe_trim(x))
}

safe_first_nonblank <- function(x) {
  x <- x[!is.na(x) & x != ""]
  if (length(x) == 0) return(NA)
  x[1]
}

safe_last_nonblank <- function(x) {
  x <- x[!is.na(x) & x != ""]
  if (length(x) == 0) return(NA)
  x[length(x)]
}

safe_mean <- function(x) {
  if (length(x) == 0 || all(is.na(x))) return(NA_real_)
  mean(x, na.rm = TRUE)
}

ensure_sheet <- function(ss, sheet_name) {
  existing_tabs <- sheet_names(ss)
  if (!(sheet_name %in% existing_tabs)) {
    sheet_add(ss, sheet_name)
  }
}

first_existing_col <- function(df, candidates) {
  found <- candidates[candidates %in% names(df)]
  if (length(found) == 0) return(NA_character_)
  found[1]
}

# robust MLB hitter game log fetcher
fetch_mlb_hitter_logs <- function(player_id, season_year) {
  fn_names <- c("fg_batter_game_logs", "fg_player_batter_game_logs")
  
  for (fn_name in fn_names) {
    if (exists(fn_name, mode = "function")) {
      fn <- get(fn_name, mode = "function")
      
      attempts <- list(
        list(playerid = player_id, year = season_year),
        list(playerid = player_id, season = season_year),
        list(playerid = player_id, startseason = season_year, endseason = season_year),
        list(playerid = player_id)
      )
      
      for (args in attempts) {
        out <- tryCatch(
          do.call(fn, args),
          error = function(e) NULL
        )
        if (!is.null(out) && nrow(out) > 0) {
          return(out)
        }
      }
    }
  }
  
  return(NULL)
}

# robust MLB pitcher game log fetcher
fetch_mlb_pitcher_logs <- function(player_id, season_year) {
  fn_names <- c("fg_pitcher_game_logs", "fg_player_pitcher_game_logs")
  
  for (fn_name in fn_names) {
    if (exists(fn_name, mode = "function")) {
      fn <- get(fn_name, mode = "function")
      
      attempts <- list(
        list(playerid = player_id, year = season_year),
        list(playerid = player_id, season = season_year),
        list(playerid = player_id, startseason = season_year, endseason = season_year),
        list(playerid = player_id)
      )
      
      for (args in attempts) {
        out <- tryCatch(
          do.call(fn, args),
          error = function(e) NULL
        )
        if (!is.null(out) && nrow(out) > 0) {
          return(out)
        }
      }
    }
  }
  
  return(NULL)
}

# -----------------------------
# FANGRAPHS FV SCRAPER
# -----------------------------
scrape_fangraphs_fv <- function(board_year) {
  board_url <- paste0(
    "https://www.fangraphs.com/prospects/the-board/",
    board_year,
    "-prospect-list?type=0"
  )

  message(paste("Scraping FanGraphs FV from:", board_url))

  # Shared browser-like headers to avoid being blocked
  browser_headers <- httr::add_headers(
    `User-Agent`      = "Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/120.0.0.0 Safari/537.36",
    `Accept`          = "application/json, text/html, */*",
    `Accept-Language` = "en-US,en;q=0.9",
    `Referer`         = "https://www.fangraphs.com/"
  )

  # Helper: given a data frame, find Name/Org/FV columns and return a tidy tibble.
  extract_fv_cols <- function(df) {
    df <- janitor::clean_names(df)
    nm <- names(df)
    message(paste("  Columns available:", paste(nm, collapse = ", ")))

    name_col <- nm[str_detect(nm, regex("^name$|player|prospect", ignore_case = TRUE))]
    org_col  <- nm[str_detect(nm, regex("^org$|organization|team", ignore_case = TRUE))]
    fv_col   <- nm[str_detect(nm, regex("^fv$|future.?value|grade|rating", ignore_case = TRUE))]

    message(paste("  Name col candidates:", paste(name_col, collapse = ", ")))
    message(paste("  Org  col candidates:", paste(org_col,  collapse = ", ")))
    message(paste("  FV   col candidates:", paste(fv_col,   collapse = ", ")))

    if (length(name_col) == 0) {
      message("  Could not find Name column — skipping this table/result.")
      return(NULL)
    }
    if (length(fv_col) == 0) {
      message("  Could not find FV column — skipping this table/result.")
      return(NULL)
    }

    name_col <- name_col[1]
    org_col  <- if (length(org_col) > 0) org_col[1] else NA_character_
    fv_col   <- fv_col[1]

    out <- df %>%
      transmute(
        fg_name = safe_trim(.data[[name_col]]),
        fg_org  = if (!is.na(org_col)) safe_trim(.data[[org_col]]) else NA_character_,
        FV      = safe_trim(.data[[fv_col]])
      ) %>%
      filter(!is.na(fg_name), fg_name != "", !is.na(FV), FV != "") %>%
      mutate(
        Name_clean = safe_upper(fg_name),
        Org_clean  = safe_upper(fg_org)
      ) %>%
      distinct(Name_clean, Org_clean, .keep_all = TRUE)

    out
  }

  # ------------------------------------------------------------------
  # Attempt 1: FanGraphs JSON API (avoids JavaScript rendering issues)
  # ------------------------------------------------------------------
  message("Attempt 1: FanGraphs JSON API...")
  api_urls <- c(
    paste0("https://www.fangraphs.com/api/prospects/board/0?draft=0&team=0&type=0&pos=all&stats=pit&view=profile&z=", board_year),
    paste0("https://www.fangraphs.com/api/prospects/board/0?draft=0&team=0&type=0&pos=all&view=profile&z=", board_year),
    "https://www.fangraphs.com/api/prospects/board/0?draft=0&team=0&type=0&pos=all&stats=pit&view=profile"
  )

  for (api_url in api_urls) {
    message(paste("  Trying:", api_url))
    api_result <- tryCatch({
      resp <- httr::GET(api_url, browser_headers, httr::timeout(30))
      status <- httr::status_code(resp)
      message(paste("  Status:", status))

      if (status == 200) {
        content_text <- httr::content(resp, as = "text", encoding = "UTF-8")
        message(paste("  Response length:", nchar(content_text), "chars"))

        parsed <- jsonlite::fromJSON(content_text, flatten = TRUE)

        if (is.data.frame(parsed) && nrow(parsed) > 0) {
          message(paste("  API returned", nrow(parsed), "rows (data frame)"))
          parsed
        } else if (is.list(parsed)) {
          # Look for a data frame anywhere in the top-level list
          found_df <- NULL
          for (key in names(parsed)) {
            val <- parsed[[key]]
            if (is.data.frame(val) && nrow(val) > 0) {
              message(paste0("  Found data frame in key '", key, "' with ", nrow(val), " rows"))
              found_df <- val
              break
            }
          }
          found_df
        } else {
          message(paste("  Unexpected API response type:", class(parsed)))
          NULL
        }
      } else {
        NULL
      }
    }, error = function(e) {
      message(paste("  API error:", e$message))
      NULL
    })

    if (!is.null(api_result) && nrow(api_result) > 0) {
      extracted <- extract_fv_cols(api_result)
      if (!is.null(extracted) && nrow(extracted) > 0) {
        message(paste("Scraped", nrow(extracted), "prospects with FV via JSON API."))
        return(extracted)
      }
    }
  }

  # ------------------------------------------------------------------
  # Attempt 2: HTML scraping with browser-like headers
  # ------------------------------------------------------------------
  message("Attempt 2: HTML scraping with browser-like headers...")
  html_result <- tryCatch({
    resp <- httr::GET(board_url, browser_headers, httr::timeout(30))
    status <- httr::status_code(resp)
    message(paste("  HTML response status:", status))

    if (status == 200) {
      content_text <- httr::content(resp, as = "text", encoding = "UTF-8")
      message(paste("  HTML response length:", nchar(content_text), "chars"))

      page   <- read_html(content_text)
      tables <- page %>% html_elements("table") %>% html_table(fill = TRUE)
      message(paste("  HTML tables found:", length(tables)))

      for (i in seq_along(tables)) {
        message(paste("  Table", i, "—", nrow(tables[[i]]), "rows,",
                      "columns:", paste(names(tables[[i]]), collapse = ", ")))
      }
      tables
    } else {
      message(paste("  Non-200 status:", status))
      NULL
    }
  }, error = function(e) {
    message(paste("  HTML scrape error:", e$message))
    NULL
  })

  if (!is.null(html_result) && length(html_result) > 0) {
    # First pass: look for a table that has both Name and FV columns
    board_tbl <- NULL
    for (tbl in html_result) {
      nm <- names(tbl)
      if (
        length(nm) > 0 &&
        any(str_detect(nm, regex("name|player", ignore_case = TRUE))) &&
        any(str_detect(nm, regex("^fv$|future.?value|grade", ignore_case = TRUE)))
      ) {
        board_tbl <- tbl
        message("  Found matching table with Name + FV columns.")
        break
      }
    }

    # Second pass: fall back to the widest table
    if (is.null(board_tbl)) {
      message("  No exact match found — falling back to widest table.")
      widths    <- purrr::map_int(html_result, ncol)
      board_tbl <- html_result[[which.max(widths)]]
    }

    extracted <- extract_fv_cols(board_tbl)
    if (!is.null(extracted) && nrow(extracted) > 0) {
      message(paste("Scraped", nrow(extracted), "prospects with FV via HTML."))
      return(extracted)
    }
  }

  # ------------------------------------------------------------------
  # All attempts failed
  # ------------------------------------------------------------------
  warning(paste(
    "All FanGraphs FV scrape attempts failed for year:", board_year,
    "— FV column will be empty. Review the log messages above for details."
  ))
  tibble()
}

# -----------------------------
# READ TEST TAB
# EXPECTED HEADERS:
# Player | Fangraphs ID | Role | Level | MiLB_FG_ID
# -----------------------------
test_df <- read_sheet(sheet_url, sheet = "Test") %>%
  as.data.frame(stringsAsFactors = FALSE)

print("Columns found in Test tab:")
print(names(test_df))

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

# -----------------------------
# MLB IDS FROM TEST
# -----------------------------
mlb_hit_ids <- test_df %>%
  filter(
    Level_clean == "MLB",
    Role_clean == "H",
    !is.na(Fangraphs_ID_clean),
    Fangraphs_ID_clean != ""
  ) %>%
  pull(Fangraphs_ID_clean) %>%
  unique()

mlb_pitch_ids <- test_df %>%
  filter(
    Level_clean == "MLB",
    Role_clean == "P",
    !is.na(Fangraphs_ID_clean),
    Fangraphs_ID_clean != ""
  ) %>%
  pull(Fangraphs_ID_clean) %>%
  unique()

# -----------------------------
# MiLB IDS FROM TEST
# -----------------------------
milb_hit_ids <- test_df %>%
  filter(
    Level_clean == "MILB",
    Role_clean == "H",
    !is.na(MiLB_ID_clean),
    MiLB_ID_clean != ""
  ) %>%
  pull(MiLB_ID_clean) %>%
  unique()

milb_pitch_ids <- test_df %>%
  filter(
    Level_clean == "MILB",
    Role_clean == "P",
    !is.na(MiLB_ID_clean),
    MiLB_ID_clean != ""
  ) %>%
  pull(MiLB_ID_clean) %>%
  unique()

print("MLB hitter IDs found:")
print(mlb_hit_ids)

print("MLB pitcher IDs found:")
print(mlb_pitch_ids)

print("MiLB hitter IDs found:")
print(milb_hit_ids)

print("MiLB pitcher IDs found:")
print(milb_pitch_ids)

# =========================================================
# MLB SEASON LEADERBOARDS
# =========================================================

# -----------------------------
# MLB SEASON DATA - HITTERS
# -----------------------------
mlb_hitters_all <- fg_batter_leaders(
  startseason = season_year,
  endseason = season_year,
  qual = 0
) %>%
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
    wRC_plus = safe_col(., "wRC_plus"),
    BB_percent = safe_col(., "BB_pct"),
    K_percent = safe_col(., "K_pct"),
    HardHit_percent = safe_col(., "HardHit_pct"),
    Barrel_percent = safe_col(., "Barrel_pct"),
    EV = safe_col(., "EV")
  ) %>%
  select(
    fangraphs_id, Name, Team, Age, G, PA, HR, SB, AVG, OBP, SLG, OPS, ISO,
    wOBA, xwOBA, xBA, xSLG, wRC_plus, BB_percent, K_percent,
    HardHit_percent, Barrel_percent, EV
  ) %>%
  filter(fangraphs_id %in% mlb_hit_ids)

# -----------------------------
# MLB SEASON DATA - PITCHERS
# -----------------------------
mlb_pitchers_all <- fg_pitcher_leaders(
  startseason = season_year,
  endseason = season_year,
  qual = 0
) %>%
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
    K_percent = safe_col(., "K_pct"),
    BB_percent = safe_col(., "BB_pct"),
    K_BB_percent = safe_col(., "K-BB_pct"),
    SwStr_percent = safe_col(., "SwStr_pct"),
    HardHit_percent = safe_col(., "HardHit_pct"),
    Barrel_percent = safe_col(., "Barrel_pct"),
    EV = safe_col(., "EV"),
    Stuff_plus = if ("pb_stuff" %in% names(.)) safe_col(., "pb_stuff") else safe_col(., "Stuff+"),
    SV = safe_col(., "SV"),
    HLD = if ("HLD" %in% names(.)) safe_col(., "HLD") else if ("HD" %in% names(.)) safe_col(., "HD") else rep(NA, nrow(.))
  ) %>%
  mutate(
    SV_num = safe_num(SV),
    HLD_num = safe_num(HLD),
    SV_HLD = SV_num + HLD_num
  ) %>%
  select(
    fangraphs_id, Name, Team, Age, G, IP, ERA, xERA, WHIP, FIP, FIP_minus,
    xFIP, xFIP_minus, SIERA, K_percent, BB_percent, K_BB_percent,
    SwStr_percent, HardHit_percent, Barrel_percent, EV, Stuff_plus,
    SV, HLD, SV_HLD
  ) %>%
  filter(fangraphs_id %in% mlb_pitch_ids)

# =========================================================
# MLB LAST 14 DAYS FROM GAME LOGS
# =========================================================

# -----------------------------
# MLB LAST 14 - HITTERS
# -----------------------------
mlb_hit_logs <- map_dfr(mlb_hit_ids, function(pid) {
  x <- fetch_mlb_hitter_logs(pid, season_year)
  
  if (is.null(x) || nrow(x) == 0) {
    message(paste("No MLB hitter game log data for:", pid))
    return(NULL)
  }
  
  x$source_fg_id <- as.character(pid)
  names(x) <- trimws(names(x))
  x
})

if (nrow(mlb_hit_logs) > 0) {
  date_col <- first_existing_col(mlb_hit_logs, c("Date", "date", "GameDate", "gamedate"))
  pa_col <- first_existing_col(mlb_hit_logs, c("PA"))
  ab_col <- first_existing_col(mlb_hit_logs, c("AB"))
  h_col <- first_existing_col(mlb_hit_logs, c("H"))
  hr_col <- first_existing_col(mlb_hit_logs, c("HR"))
  sb_col <- first_existing_col(mlb_hit_logs, c("SB"))
  bb_col <- first_existing_col(mlb_hit_logs, c("BB"))
  so_col <- first_existing_col(mlb_hit_logs, c("SO", "K"))
  obp_col <- first_existing_col(mlb_hit_logs, c("OBP"))
  slg_col <- first_existing_col(mlb_hit_logs, c("SLG"))
  ops_col <- first_existing_col(mlb_hit_logs, c("OPS"))
  iso_col <- first_existing_col(mlb_hit_logs, c("ISO"))
  woba_col <- first_existing_col(mlb_hit_logs, c("wOBA"))
  xwoba_col <- first_existing_col(mlb_hit_logs, c("xwOBA"))
  xba_col <- first_existing_col(mlb_hit_logs, c("xAVG"))
  xslg_col <- first_existing_col(mlb_hit_logs, c("xSLG"))
  hh_col <- first_existing_col(mlb_hit_logs, c("HardHit_pct", "HardHit%"))
  barrel_col <- first_existing_col(mlb_hit_logs, c("Barrel_pct", "Barrel%"))
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
      OBP_num = safe_num(safe_col(., obp_col)),
      SLG_num = safe_num(safe_col(., slg_col)),
      OPS_num = safe_num(safe_col(., ops_col)),
      ISO_num = safe_num(safe_col(., iso_col)),
      wOBA_num = safe_num(safe_col(., woba_col)),
      xwOBA_num = safe_num(safe_col(., xwoba_col)),
      xBA_num = safe_num(safe_col(., xba_col)),
      xSLG_num = safe_num(safe_col(., xslg_col)),
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
      last14_OBP = safe_mean(OBP_num),
      last14_SLG = safe_mean(SLG_num),
      last14_OPS = safe_mean(OPS_num),
      last14_ISO = safe_mean(ISO_num),
      last14_wOBA = safe_mean(wOBA_num),
      last14_xwOBA = safe_mean(xwOBA_num),
      last14_xBA = safe_mean(xBA_num),
      last14_xSLG = safe_mean(xSLG_num),
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
      last14_G = NA,
      last14_PA = NA,
      last14_AB = NA,
      last14_H = NA,
      last14_HR = NA,
      last14_SB = NA,
      last14_BB = NA,
      last14_SO = NA,
      last14_AVG = NA,
      last14_OBP = NA,
      last14_SLG = NA,
      last14_OPS = NA,
      last14_ISO = NA,
      last14_wOBA = NA,
      last14_xwOBA = NA,
      last14_xBA = NA,
      last14_xSLG = NA,
      last14_HardHit_percent = NA,
      last14_Barrel_percent = NA,
      last14_EV = NA
    )
}

# -----------------------------
# MLB LAST 14 - PITCHERS
# -----------------------------
mlb_pitch_logs <- map_dfr(mlb_pitch_ids, function(pid) {
  x <- fetch_mlb_pitcher_logs(pid, season_year)
  
  if (is.null(x) || nrow(x) == 0) {
    message(paste("No MLB pitcher game log data for:", pid))
    return(NULL)
  }
  
  x$source_fg_id <- as.character(pid)
  names(x) <- trimws(names(x))
  x
})

if (nrow(mlb_pitch_logs) > 0) {
  date_col <- first_existing_col(mlb_pitch_logs, c("Date", "date", "GameDate", "gamedate"))
  ip_col <- first_existing_col(mlb_pitch_logs, c("IP"))
  er_col <- first_existing_col(mlb_pitch_logs, c("ER"))
  h_col <- first_existing_col(mlb_pitch_logs, c("H"))
  hr_col <- first_existing_col(mlb_pitch_logs, c("HR"))
  bb_col <- first_existing_col(mlb_pitch_logs, c("BB"))
  so_col <- first_existing_col(mlb_pitch_logs, c("SO", "K"))
  tbf_col <- first_existing_col(mlb_pitch_logs, c("TBF"))
  era_col <- first_existing_col(mlb_pitch_logs, c("ERA"))
  xera_col <- first_existing_col(mlb_pitch_logs, c("xERA"))
  whip_col <- first_existing_col(mlb_pitch_logs, c("WHIP"))
  fip_col <- first_existing_col(mlb_pitch_logs, c("FIP"))
  fipm_col <- first_existing_col(mlb_pitch_logs, c("FIP-", "FIP_minus"))
  xfip_col <- first_existing_col(mlb_pitch_logs, c("xFIP"))
  xfipm_col <- first_existing_col(mlb_pitch_logs, c("xFIP-", "xFIP_minus"))
  siera_col <- first_existing_col(mlb_pitch_logs, c("SIERA"))
  kpct_col <- first_existing_col(mlb_pitch_logs, c("K%", "K_pct"))
  bbpct_col <- first_existing_col(mlb_pitch_logs, c("BB%", "BB_pct"))
  kbbpct_col <- first_existing_col(mlb_pitch_logs, c("K-BB%", "K-BB_pct"))
  swstr_col <- first_existing_col(mlb_pitch_logs, c("SwStr%", "SwStr_pct"))
  hh_col <- first_existing_col(mlb_pitch_logs, c("HardHit_pct", "HardHit%"))
  barrel_col <- first_existing_col(mlb_pitch_logs, c("Barrel_pct", "Barrel%"))
  ev_col <- first_existing_col(mlb_pitch_logs, c("EV"))
  stuff_col <- first_existing_col(mlb_pitch_logs, c("pb_stuff", "Stuff+", "Stuff_plus"))
  sv_col <- first_existing_col(mlb_pitch_logs, c("SV"))
  hld_col <- first_existing_col(mlb_pitch_logs, c("HLD", "HD"))
  
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
      ERA_num = safe_num(safe_col(., era_col)),
      xERA_num = safe_num(safe_col(., xera_col)),
      WHIP_num = safe_num(safe_col(., whip_col)),
      FIP_num = safe_num(safe_col(., fip_col)),
      FIP_minus_num = safe_num(safe_col(., fipm_col)),
      xFIP_num = safe_num(safe_col(., xfip_col)),
      xFIP_minus_num = safe_num(safe_col(., xfipm_col)),
      SIERA_num = safe_num(safe_col(., siera_col)),
      K_percent_num = safe_num(safe_col(., kpct_col)),
      BB_percent_num = safe_num(safe_col(., bbpct_col)),
      K_BB_percent_num = safe_num(safe_col(., kbbpct_col)),
      SwStr_percent_num = safe_num(safe_col(., swstr_col)),
      HardHit_num = safe_num(safe_col(., hh_col)),
      Barrel_num = safe_num(safe_col(., barrel_col)),
      EV_num = safe_num(safe_col(., ev_col)),
      Stuff_num = safe_num(safe_col(., stuff_col)),
      SV_num = safe_num(safe_col(., sv_col)),
      HLD_num = safe_num(safe_col(., hld_col))
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
      last14_xERA = safe_mean(xERA_num),
      last14_WHIP = ifelse(last14_IP > 0, (last14_H + last14_BB) / last14_IP, NA_real_),
      last14_FIP = safe_mean(FIP_num),
      last14_FIP_minus = safe_mean(FIP_minus_num),
      last14_xFIP = safe_mean(xFIP_num),
      last14_xFIP_minus = safe_mean(xFIP_minus_num),
      last14_SIERA = safe_mean(SIERA_num),
      last14_K_percent = ifelse(last14_TBF > 0, last14_SO / last14_TBF, NA_real_),
      last14_BB_percent = ifelse(last14_TBF > 0, last14_BB / last14_TBF, NA_real_),
      last14_K_BB_percent = last14_K_percent - last14_BB_percent,
      last14_SwStr_percent = safe_mean(SwStr_percent_num),
      last14_HardHit_percent = safe_mean(HardHit_num),
      last14_Barrel_percent = safe_mean(Barrel_num),
      last14_EV = safe_mean(EV_num),
      last14_Stuff_plus = safe_mean(Stuff_num),
      last14_SV = sum(SV_num, na.rm = TRUE),
      last14_HLD = sum(HLD_num, na.rm = TRUE),
      last14_SV_HLD = sum(SV_num, na.rm = TRUE) + sum(HLD_num, na.rm = TRUE),
      last14_K_per_9 = ifelse(last14_IP > 0, 9 * last14_SO / last14_IP, NA_real_),
      last14_BB_per_9 = ifelse(last14_IP > 0, 9 * last14_BB / last14_IP, NA_real_),
      last14_HR_per_9 = ifelse(last14_IP > 0, 9 * last14_HR / last14_IP, NA_real_),
      .groups = "drop"
    )
  
  mlb_pitchers_out <- mlb_pitchers_out %>%
    left_join(mlb_pitch_last14, by = c("fangraphs_id" = "source_fg_id"))
} else {
  mlb_pitchers_out <- mlb_pitchers_out %>%
    mutate(
      last14_G = NA,
      last14_IP = NA,
      last14_H = NA,
      last14_ER = NA,
      last14_HR = NA,
      last14_BB = NA,
      last14_SO = NA,
      last14_TBF = NA,
      last14_ERA = NA,
      last14_xERA = NA,
      last14_WHIP = NA,
      last14_FIP = NA,
      last14_FIP_minus = NA,
      last14_xFIP = NA,
      last14_xFIP_minus = NA,
      last14_SIERA = NA,
      last14_K_percent = NA,
      last14_BB_percent = NA,
      last14_K_BB_percent = NA,
      last14_SwStr_percent = NA,
      last14_HardHit_percent = NA,
      last14_Barrel_percent = NA,
      last14_EV = NA,
      last14_Stuff_plus = NA,
      last14_SV = NA,
      last14_HLD = NA,
      last14_SV_HLD = NA,
      last14_K_per_9 = NA,
      last14_BB_per_9 = NA,
      last14_HR_per_9 = NA
    )
}

# =========================================================
# MiLB GAME LOGS
# =========================================================

# -----------------------------
# MiLB SEASON DATA - HITTERS
# -----------------------------
milb_hit_logs <- map_dfr(milb_hit_ids, function(pid) {
  x <- tryCatch(
    fg_milb_batter_game_logs(playerid = as.character(pid), year = season_year),
    error = function(e) {
      message(paste("FAILED MiLB hitter", pid, "->", e$message))
      NULL
    }
  )
  
  if (is.null(x) || nrow(x) == 0) {
    message(paste("No MiLB hitter data for:", pid))
    return(NULL)
  }
  
  x$source_milb_id <- as.character(pid)
  names(x) <- trimws(names(x))
  x
})

if (nrow(milb_hit_logs) > 0) {
  name_col_milb_hit <- first_existing_col(
    milb_hit_logs,
    c("Name", "PlayerName", "player_name", "Player", "player")
  )
  
  team_col_milb_hit <- first_existing_col(
    milb_hit_logs,
    c("Team", "Tm", "team_name")
  )
  
  level_col_milb_hit <- first_existing_col(
    milb_hit_logs,
    c("Level", "level")
  )
  
  milb_hit_logs <- milb_hit_logs %>%
    mutate(
      source_milb_id = as.character(source_milb_id),
      player_name_log = safe_trim(safe_col(., name_col_milb_hit)),
      Date2 = as.Date(safe_col(., "Date")),
      PA_num = safe_num(safe_col(., "PA")),
      AB_num = safe_num(safe_col(., "AB")),
      H_num = safe_num(safe_col(., "H")),
      HR_num = safe_num(safe_col(., "HR")),
      SB_num = safe_num(safe_col(., "SB")),
      BB_num = safe_num(safe_col(., "BB")),
      SO_num = safe_num(safe_col(., "SO")),
      OBP_num = safe_num(safe_col(., "OBP")),
      SLG_num = safe_num(safe_col(., "SLG")),
      OPS_num = safe_num(safe_col(., "OPS")),
      ISO_num = safe_num(safe_col(., "ISO")),
      wOBA_num = safe_num(safe_col(., "wOBA")),
      xwOBA_num = safe_num(safe_col(., "xwOBA")),
      xBA_num = safe_num(safe_col(., "xAVG")),
      xSLG_num = safe_num(safe_col(., "xSLG")),
      HardHit_num = safe_num(safe_col(., "HardHit_pct")),
      Barrel_num = safe_num(safe_col(., "Barrel_pct")),
      EV_num = safe_num(safe_col(., "EV"))
    )
  
  milb_hitters_out <- milb_hit_logs %>%
    group_by(source_milb_id) %>%
    summarise(
      minor_playerid = first(source_milb_id),
      Name_from_logs = safe_last_nonblank(player_name_log),
      Team = safe_last_nonblank(as.character(safe_col(pick(everything()), team_col_milb_hit))),
      Level = safe_last_nonblank(as.character(safe_col(pick(everything()), level_col_milb_hit))),
      G = n(),
      PA = sum(PA_num, na.rm = TRUE),
      AB = sum(AB_num, na.rm = TRUE),
      H = sum(H_num, na.rm = TRUE),
      HR = sum(HR_num, na.rm = TRUE),
      SB = sum(SB_num, na.rm = TRUE),
      BB = sum(BB_num, na.rm = TRUE),
      SO = sum(SO_num, na.rm = TRUE),
      AVG = ifelse(AB > 0, H / AB, NA_real_),
      OBP = safe_mean(OBP_num),
      SLG = safe_mean(SLG_num),
      OPS = safe_mean(OPS_num),
      ISO = safe_mean(ISO_num),
      BB_percent = ifelse(PA > 0, BB / PA, NA_real_),
      K_percent = ifelse(PA > 0, SO / PA, NA_real_),
      wOBA = safe_mean(wOBA_num),
      xwOBA = safe_mean(xwOBA_num),
      xBA = safe_mean(xBA_num),
      xSLG = safe_mean(xSLG_num),
      HardHit_percent = safe_mean(HardHit_num),
      Barrel_percent = safe_mean(Barrel_num),
      EV = safe_mean(EV_num),
      .groups = "drop"
    ) %>%
    left_join(milb_name_lookup, by = c("minor_playerid" = "MiLB_ID_clean")) %>%
    mutate(
      Name = coalesce(Name_from_logs, Player_clean)
    ) %>%
    select(
      minor_playerid, Name, Team, Level, G, PA, AB, H, HR, SB, BB, SO,
      AVG, OBP, SLG, OPS, ISO, BB_percent, K_percent, wOBA, xwOBA, xBA,
      xSLG, HardHit_percent, Barrel_percent, EV
    )
  
  milb_hit_last14 <- milb_hit_logs %>%
    filter(!is.na(Date2), Date2 >= cutoff_date) %>%
    group_by(source_milb_id) %>%
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
      last14_OBP = safe_mean(OBP_num),
      last14_SLG = safe_mean(SLG_num),
      last14_OPS = safe_mean(OPS_num),
      last14_ISO = safe_mean(ISO_num),
      last14_wOBA = safe_mean(wOBA_num),
      last14_xwOBA = safe_mean(xwOBA_num),
      last14_xBA = safe_mean(xBA_num),
      last14_xSLG = safe_mean(xSLG_num),
      last14_HardHit_percent = safe_mean(HardHit_num),
      last14_Barrel_percent = safe_mean(Barrel_num),
      last14_EV = safe_mean(EV_num),
      .groups = "drop"
    )
  
  milb_hitters_out <- milb_hitters_out %>%
    left_join(milb_hit_last14, by = c("minor_playerid" = "source_milb_id"))
} else {
  milb_hitters_out <- tibble()
}

# -----------------------------
# MiLB SEASON DATA - PITCHERS
# -----------------------------
milb_pitch_logs <- map_dfr(milb_pitch_ids, function(pid) {
  message(paste("Trying MiLB pitcher ID:", pid, "for year:", season_year))
  
  x <- tryCatch(
    fg_milb_pitcher_game_logs(playerid = as.character(pid), year = season_year),
    error = function(e) {
      message(paste("FAILED MiLB pitcher", pid, "->", e$message))
      NULL
    }
  )
  
  if (is.null(x) || nrow(x) == 0) {
    message(paste("No MiLB pitcher data for:", pid))
    return(NULL)
  }
  
  x$source_milb_id <- as.character(pid)
  names(x) <- trimws(names(x))
  x
})

if (nrow(milb_pitch_logs) > 0) {
  hld_col_milb <- first_existing_col(milb_pitch_logs, c("HLD", "HD"))
  
  name_col_milb_pitch <- first_existing_col(
    milb_pitch_logs,
    c("Name", "PlayerName", "player_name", "Player", "player")
  )
  
  team_col_milb_pitch <- first_existing_col(
    milb_pitch_logs,
    c("Team", "Tm", "team_name")
  )
  
  level_col_milb_pitch <- first_existing_col(
    milb_pitch_logs,
    c("Level", "level")
  )
  
  milb_pitch_logs <- milb_pitch_logs %>%
    mutate(
      source_milb_id = as.character(source_milb_id),
      player_name_log = safe_trim(safe_col(., name_col_milb_pitch)),
      Date2 = as.Date(safe_col(., "Date")),
      IP_num = safe_num(safe_col(., "IP")),
      TBF_num = safe_num(safe_col(., "TBF")),
      H_num = safe_num(safe_col(., "H")),
      ER_num = safe_num(safe_col(., "ER")),
      HR_num = safe_num(safe_col(., "HR")),
      BB_num = safe_num(safe_col(., "BB")),
      SO_num = safe_num(safe_col(., "SO")),
      ERA_num = safe_num(safe_col(., "ERA")),
      xERA_num = safe_num(safe_col(., "xERA")),
      WHIP_num = safe_num(safe_col(., "WHIP")),
      FIP_num = safe_num(safe_col(., "FIP")),
      FIP_minus_num = safe_num(safe_col(., "FIP-")),
      xFIP_num = safe_num(safe_col(., "xFIP")),
      xFIP_minus_num = safe_num(safe_col(., "xFIP-")),
      SIERA_num = safe_num(safe_col(., "SIERA")),
      K_percent_num = safe_num(safe_col(., "K%")),
      BB_percent_num = safe_num(safe_col(., "BB%")),
      K_BB_percent_num = safe_num(safe_col(., "K-BB%")),
      SwStr_percent_num = safe_num(safe_col(., "SwStr%")),
      HardHit_num = safe_num(safe_col(., "HardHit_pct")),
      Barrel_num = safe_num(safe_col(., "Barrel_pct")),
      EV_num = safe_num(safe_col(., "EV")),
      SV_num = safe_num(safe_col(., "SV")),
      HLD_num = safe_num(safe_col(., hld_col_milb))
    )
  
  milb_pitchers_out <- milb_pitch_logs %>%
    group_by(source_milb_id) %>%
    summarise(
      minor_playerid = first(source_milb_id),
      Name_from_logs = safe_last_nonblank(player_name_log),
      Team = safe_last_nonblank(as.character(safe_col(pick(everything()), team_col_milb_pitch))),
      Level = safe_last_nonblank(as.character(safe_col(pick(everything()), level_col_milb_pitch))),
      G = n(),
      IP = sum(IP_num, na.rm = TRUE),
      H = sum(H_num, na.rm = TRUE),
      ER = sum(ER_num, na.rm = TRUE),
      HR = sum(HR_num, na.rm = TRUE),
      BB = sum(BB_num, na.rm = TRUE),
      SO = sum(SO_num, na.rm = TRUE),
      TBF = sum(TBF_num, na.rm = TRUE),
      ERA = ifelse(IP > 0, 9 * ER / IP, NA_real_),
      xERA = safe_mean(xERA_num),
      WHIP = ifelse(IP > 0, (H + BB) / IP, NA_real_),
      FIP = safe_mean(FIP_num),
      FIP_minus = safe_mean(FIP_minus_num),
      xFIP = safe_mean(xFIP_num),
      xFIP_minus = safe_mean(xFIP_minus_num),
      SIERA = safe_mean(SIERA_num),
      K_percent = ifelse(TBF > 0, SO / TBF, NA_real_),
      BB_percent = ifelse(TBF > 0, BB / TBF, NA_real_),
      K_BB_percent = K_percent - BB_percent,
      SwStr_percent = safe_mean(SwStr_percent_num),
      HardHit_percent = safe_mean(HardHit_num),
      Barrel_percent = safe_mean(Barrel_num),
      EV = safe_mean(EV_num),
      SV = sum(SV_num, na.rm = TRUE),
      HLD = sum(HLD_num, na.rm = TRUE),
      SV_HLD = sum(SV_num, na.rm = TRUE) + sum(HLD_num, na.rm = TRUE),
      K_per_9 = ifelse(IP > 0, 9 * SO / IP, NA_real_),
      BB_per_9 = ifelse(IP > 0, 9 * BB / IP, NA_real_),
      HR_per_9 = ifelse(IP > 0, 9 * HR / IP, NA_real_),
      .groups = "drop"
    ) %>%
    left_join(milb_name_lookup, by = c("minor_playerid" = "MiLB_ID_clean")) %>%
    mutate(
      Name = coalesce(Name_from_logs, Player_clean)
    ) %>%
    select(
      minor_playerid, Name, Team, Level, G, IP, H, ER, HR, BB, SO, TBF,
      ERA, xERA, WHIP, FIP, FIP_minus, xFIP, xFIP_minus, SIERA, K_percent,
      BB_percent, K_BB_percent, SwStr_percent, HardHit_percent,
      Barrel_percent, EV, SV, HLD, SV_HLD, K_per_9, BB_per_9, HR_per_9
    )
  
  milb_pitch_last14 <- milb_pitch_logs %>%
    filter(!is.na(Date2), Date2 >= cutoff_date) %>%
    group_by(source_milb_id) %>%
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
      last14_xERA = safe_mean(xERA_num),
      last14_WHIP = ifelse(last14_IP > 0, (last14_H + last14_BB) / last14_IP, NA_real_),
      last14_FIP = safe_mean(FIP_num),
      last14_FIP_minus = safe_mean(FIP_minus_num),
      last14_xFIP = safe_mean(xFIP_num),
      last14_xFIP_minus = safe_mean(xFIP_minus_num),
      last14_SIERA = safe_mean(SIERA_num),
      last14_K_percent = ifelse(last14_TBF > 0, last14_SO / last14_TBF, NA_real_),
      last14_BB_percent = ifelse(last14_TBF > 0, last14_BB / last14_TBF, NA_real_),
      last14_K_BB_percent = last14_K_percent - last14_BB_percent,
      last14_SwStr_percent = safe_mean(SwStr_percent_num),
      last14_HardHit_percent = safe_mean(HardHit_num),
      last14_Barrel_percent = safe_mean(Barrel_num),
      last14_EV = safe_mean(EV_num),
      last14_SV = sum(SV_num, na.rm = TRUE),
      last14_HLD = sum(HLD_num, na.rm = TRUE),
      last14_SV_HLD = sum(SV_num, na.rm = TRUE) + sum(HLD_num, na.rm = TRUE),
      last14_K_per_9 = ifelse(last14_IP > 0, 9 * last14_SO / last14_IP, NA_real_),
      last14_BB_per_9 = ifelse(last14_IP > 0, 9 * last14_BB / last14_IP, NA_real_),
      last14_HR_per_9 = ifelse(last14_IP > 0, 9 * last14_HR / last14_IP, NA_real_),
      .groups = "drop"
    )
  
  milb_pitchers_out <- milb_pitchers_out %>%
    left_join(milb_pitch_last14, by = c("minor_playerid" = "source_milb_id"))
} else {
  milb_pitchers_out <- tibble()
}

# =========================================================
# SCRAPE FANGRAPHS FV
# =========================================================
fv_lookup <- tryCatch(
  scrape_fangraphs_fv(board_year),
  error = function(e) {
    message(paste("FV scrape failed:", e$message))
    tibble()
  }
)

print("FV lookup preview:")
print(head(fv_lookup))

# =========================================================
# JOIN FV TO MiLB HITTERS
# =========================================================
if (exists("milb_hitters_out") && nrow(milb_hitters_out) > 0 && nrow(fv_lookup) > 0) {
  milb_hitters_out <- milb_hitters_out %>%
    mutate(
      Name = safe_trim(Name),
      Team = safe_trim(Team),
      Name_clean = safe_upper(Name),
      Team_clean = safe_upper(Team)
    )
  
  fv_hit_lookup_org <- fv_lookup %>%
    select(Name_clean, Org_clean, FV)
  
  fv_hit_lookup_name <- fv_lookup %>%
    distinct(Name_clean, .keep_all = TRUE) %>%
    select(Name_clean, FV)
  
  milb_hitters_out <- milb_hitters_out %>%
    left_join(
      fv_hit_lookup_org,
      by = c("Name_clean" = "Name_clean", "Team_clean" = "Org_clean")
    ) %>%
    left_join(
      fv_hit_lookup_name %>% rename(FV_name_only = FV),
      by = "Name_clean"
    ) %>%
    mutate(
      FV = coalesce(FV, FV_name_only)
    ) %>%
    select(-Name_clean, -Team_clean, -FV_name_only)
  
  if ("FV" %in% names(milb_hitters_out)) {
    milb_hitters_out <- milb_hitters_out %>%
      relocate(FV, .after = Name)
  }
}

# =========================================================
# JOIN FV TO MiLB PITCHERS
# =========================================================
if (exists("milb_pitchers_out") && nrow(milb_pitchers_out) > 0 && nrow(fv_lookup) > 0) {
  milb_pitchers_out <- milb_pitchers_out %>%
    mutate(
      Name = safe_trim(Name),
      Team = safe_trim(Team),
      Name_clean = safe_upper(Name),
      Team_clean = safe_upper(Team)
    )
  
  fv_pitch_lookup_org <- fv_lookup %>%
    select(Name_clean, Org_clean, FV)
  
  fv_pitch_lookup_name <- fv_lookup %>%
    distinct(Name_clean, .keep_all = TRUE) %>%
    select(Name_clean, FV)
  
  milb_pitchers_out <- milb_pitchers_out %>%
    left_join(
      fv_pitch_lookup_org,
      by = c("Name_clean" = "Name_clean", "Team_clean" = "Org_clean")
    ) %>%
    left_join(
      fv_pitch_lookup_name %>% rename(FV_name_only = FV),
      by = "Name_clean"
    ) %>%
    mutate(
      FV = coalesce(FV, FV_name_only)
    ) %>%
    select(-Name_clean, -Team_clean, -FV_name_only)
  
  if ("FV" %in% names(milb_pitchers_out)) {
    milb_pitchers_out <- milb_pitchers_out %>%
      relocate(FV, .after = Name)
  }
}

print("Finished scraping and joining FanGraphs FV.")

# =========================================================
# WRITE TO GOOGLE SHEETS
# =========================================================
ensure_sheet(sheet_url, "raw_hitters")
ensure_sheet(sheet_url, "raw_pitchers")
ensure_sheet(sheet_url, "raw_milb_hitters")
ensure_sheet(sheet_url, "raw_milb_pitchers")

range_write(
  ss = sheet_url,
  data = mlb_hitters_out,
  sheet = "raw_hitters",
  col_names = TRUE,
  reformat = FALSE
)

range_write(
  ss = sheet_url,
  data = mlb_pitchers_out,
  sheet = "raw_pitchers",
  col_names = TRUE,
  reformat = FALSE
)

if (nrow(milb_hitters_out) > 0) {
  range_write(
    ss = sheet_url,
    data = milb_hitters_out,
    sheet = "raw_milb_hitters",
    col_names = TRUE,
    reformat = FALSE
  )
}

if (nrow(milb_pitchers_out) > 0) {
  range_write(
    ss = sheet_url,
    data = milb_pitchers_out,
    sheet = "raw_milb_pitchers",
    col_names = TRUE,
    reformat = FALSE
  )
}

print("Finished writing all MLB and MiLB data with MiLB names and Fangraphs FV added.")
