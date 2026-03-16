# update_baseball_sheet.R

# Load necessary libraries
library(dplyr)
library(tidyr)
library(readr)

# Load data
mlb_hitters <- read_csv('data/mlb_hitters.csv')
mlb_pitchers <- read_csv('data/mlb_pitchers.csv')
milb_hitters <- read_csv('data/milb_hitters.csv')
milb_pitchers <- read_csv('data/milb_pitchers.csv')

# Function to calculate percentile rankings
calculate_percentiles <- function(data, metrics) {
  sapply(metrics, function(metric) {
    percent_rank(data[[metric]])
  })
}

# Percentile rankings for MLB hitters and pitchers
mlb_hitters_percentiles <- calculate_percentiles(mlb_hitters, c('ISO', 'BB%', 'K%', 'wOBA', 'wRC+'))
mlb_pitchers_percentiles <- calculate_percentiles(mlb_pitchers, c('FIP', 'Velo'))

# Process MiLB data and fix levels
milb_hitters <- milb_hitters %>% 
  mutate(Most_Recent_Level = pmap_chr(game_logs, ~ last(na.omit(c(...)))))

# Free Agent Helper scoring
free_agents <- calculate_free_agent_scores(milb_hitters)
rostered_players <- calculate_rostered_scores(mlb_hitters)

# Define scoring functions
calculate_free_agent_scores <- function(data) {
  data %>% 
    mutate(
      Season_Score = Season * 0.65 + Other_Metrics * 0.35,
      Trend_Score = calculate_trend(...),
      Risk_Score = calculate_risk(...),
      Final_Score = Season_Score + Trend_Score - Risk_Score,
      Trend_Flag = ifelse(Trend_Score > threshold, TRUE, FALSE),
      Breakout_Flag = FALSE,
      Regression_Flag = FALSE,
      Why = 'Additional information'
    )
}

# Helper functions
calculate_trend <- function(...) { ... }
calculate_risk <- function(...) { ... }

# Output scores
write_csv(free_agents, 'outputs/free_agents_scores.csv')
write_csv(rostered_players, 'outputs/rostered_players_scores.csv')

# Save all output results
saveRDS(free_agents, 'outputs/free_agents_results.rds')
saveRDS(rostered_players, 'outputs/rostered_results.rds')
