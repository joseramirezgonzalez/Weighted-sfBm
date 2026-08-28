#!/usr/bin/env Rscript

script_path <- sub("^--file=", "", grep("^--file=", commandArgs(FALSE), value = TRUE)[1])
if (is.na(script_path) || !nzchar(script_path)) script_path <- normalizePath("reproduce_supplement_inference.R")
script_dir <- dirname(normalizePath(script_path))
root_dir <- dirname(script_dir)
source(file.path(script_dir, "wsbm_covariance_stable.R"))
source(file.path(script_dir, "wsbm_likelihood.R"))

output_dir <- file.path(root_dir, "reproduced_results_R")
dir.create(output_dir, recursive = TRUE, showWarnings = FALSE)

data_boundary <- read.csv(file.path(root_dir, "data", "sim_data_wsfBm.csv"))$x
data_power <- read.csv(file.path(root_dir, "data", "sim_data_wsfBm_pol.csv"))$x
data_exp <- read.csv(file.path(root_dir, "data", "sim_data_wsfBm_exp.csv"))$x

boundary_times_all <- (1:400) * 10 / 400
power_times_all <- (1:500) * 10 / 500
exp_times_all <- (1:400) * 4 / 400

n_boundary <- 360L
n_power <- 450L
n_exp <- 360L

boundary_times <- boundary_times_all[seq_len(n_boundary)]
power_times <- power_times_all[seq_len(n_power)]
exp_times <- exp_times_all[seq_len(n_exp)]

boundary_data <- data_boundary[seq_len(n_boundary)]
power_data <- data_power[seq_len(n_power)]
exp_data <- data_exp[seq_len(n_exp)]

message("Fitting logarithmic-boundary power family...")
fit_bp <- fit_wsbm(boundary_times, boundary_data, "power",
  starts = rbind(c(-0.0012, 0.9715), c(0, 1)),
  lower = c(-0.5, 0.8), upper = c(0.5, 1.2))
message("Fitting logarithmic-boundary exponential family...")
fit_be <- fit_wsbm(boundary_times, boundary_data, "exponential",
  starts = rbind(c(0.0035, 0.9761), c(0, 1)),
  lower = c(-0.5, 0.8), upper = c(0.5, 1.2))
message("Fitting nonboundary power family...")
fit_pp <- fit_wsbm(power_times, power_data, "power",
  starts = rbind(c(0.498, 1.618), c(0.42, 1.59)),
  lower = c(-0.9, 0.05), upper = c(1.95, 1.95))
message("Fitting nonboundary exponential family...")
fit_ee <- fit_wsbm(exp_times, exp_data, "exponential",
  starts = rbind(c(-0.361, 1.258), c(-0.34, 1.23)),
  lower = c(-0.6, 0.05), upper = c(0.6, 1.95))

message("Computing profile intervals...")
int_bp_a <- profile_interval(fit_bp, "a", c(-0.2, 0.2), c(0.8, 1.2),
  boundary_times, boundary_data, "power")
int_bp_b <- profile_interval(fit_bp, "b", c(0.85, 1.1), c(-0.5, 0.5),
  boundary_times, boundary_data, "power")
int_be_a <- profile_interval(fit_be, "a", c(-0.15, 0.15), c(0.8, 1.2),
  boundary_times, boundary_data, "exponential")
int_be_b <- profile_interval(fit_be, "b", c(0.85, 1.1), c(-0.5, 0.5),
  boundary_times, boundary_data, "exponential")
int_pp_a <- profile_interval(fit_pp, "a", c(0.2, 0.8), c(1.3, 1.9),
  power_times, power_data, "power")
int_pp_b <- profile_interval(fit_pp, "b", c(1.45, 1.78), c(-0.3, 1.2),
  power_times, power_data, "power")
int_ee_a <- profile_interval(fit_ee, "a", c(-0.6, -0.1), c(1.1, 1.5),
  exp_times, exp_data, "exponential")
int_ee_b <- profile_interval(fit_ee, "b", c(1.1, 1.42), c(-0.6, 0.2),
  exp_times, exp_data, "exponential")
fixed_be <- fit_fixed_b1(boundary_times, boundary_data, "exponential", c(-0.2, 0.2))

K_bp <- wsbm_covariance(boundary_times, fit_bp$par[1], fit_bp$par[2], "power")
K_be <- wsbm_covariance(boundary_times, fit_be$par[1], fit_be$par[2], "exponential")
K_K1 <- constant_log_covariance(boundary_times)
K_pp <- wsbm_covariance(power_times, fit_pp$par[1], fit_pp$par[2], "power")
K_ee <- wsbm_covariance(exp_times, fit_ee$par[1], fit_ee$par[2], "exponential")

pred_bp <- conditional_prediction(boundary_times, boundary_times_all[(n_boundary + 1):400],
  boundary_data, fit_bp$par[1], fit_bp$par[2], "power")
pred_be <- conditional_prediction(boundary_times, boundary_times_all[(n_boundary + 1):400],
  boundary_data, fit_be$par[1], fit_be$par[2], "exponential", seed = 20260828L)
pred_K1 <- conditional_prediction(boundary_times, boundary_times_all[(n_boundary + 1):400],
  boundary_data, 0, 1, "power", seed = 20260829L)
pred_pp <- conditional_prediction(power_times, power_times_all[(n_power + 1):500],
  power_data, fit_pp$par[1], fit_pp$par[2], "power", seed = 20260830L)
pred_ee <- conditional_prediction(exp_times, exp_times_all[(n_exp + 1):400],
  exp_data, fit_ee$par[1], fit_ee$par[2], "exponential", seed = 20260831L)

mse <- function(predicted, truth) base::mean((predicted - truth)^2)

make_row <- function(name, family, fit, ia, ib, K, mse_value) {
  diag <- covariance_diagnostics(K)
  data.frame(
    experiment = name,
    family = family,
    a_hat = fit$par[1], b_hat = fit$par[2],
    negative_log_likelihood = fit$nll,
    AIC = fit$AIC,
    a_profile_lower_95 = ia["lower"], a_profile_upper_95 = ia["upper"],
    b_profile_lower_95 = ib["lower"], b_profile_upper_95 = ib["upper"],
    heldout_mse_conditional_mean = mse_value,
    min_eigenvalue = diag["min_eigenvalue"],
    max_eigenvalue = diag["max_eigenvalue"],
    condition_number = diag["condition_number"],
    mean_diagonal = diag["mean_diagonal"],
    row.names = NULL
  )
}

summary_table <- rbind(
  make_row("boundary_power", "power", fit_bp, int_bp_a, int_bp_b, K_bp,
    mse(pred_bp$mean, data_boundary[(n_boundary + 1):400])),
  make_row("boundary_exp", "exponential", fit_be, int_be_a, int_be_b, K_be,
    mse(pred_be$mean, data_boundary[(n_boundary + 1):400])),
  make_row("power_sim", "power", fit_pp, int_pp_a, int_pp_b, K_pp,
    mse(pred_pp$mean, data_power[(n_power + 1):500])),
  make_row("exp_sim", "exponential", fit_ee, int_ee_a, int_ee_b, K_ee,
    mse(pred_ee$mean, data_exp[(n_exp + 1):400]))
)

K1_diag <- covariance_diagnostics(K_K1)
K1_row <- data.frame(
  experiment = "boundary_K1", family = "fixed K1", a_hat = 0, b_hat = 1,
  negative_log_likelihood = gaussian_nll(boundary_data, K_K1),
  AIC = 2 * gaussian_nll(boundary_data, K_K1),
  a_profile_lower_95 = NA, a_profile_upper_95 = NA,
  b_profile_lower_95 = NA, b_profile_upper_95 = NA,
  heldout_mse_conditional_mean = mse(pred_K1$mean, data_boundary[(n_boundary + 1):400]),
  min_eigenvalue = K1_diag["min_eigenvalue"],
  max_eigenvalue = K1_diag["max_eigenvalue"],
  condition_number = K1_diag["condition_number"],
  mean_diagonal = K1_diag["mean_diagonal"],
  row.names = NULL
)
summary_table <- rbind(summary_table, K1_row)
write.csv(summary_table, file.path(output_dir, "corrected_fit_summary_R.csv"), row.names = FALSE)

write.csv(data.frame(
  model = "exponential weight, b fixed at 1",
  a_hat = fixed_be$a_hat,
  negative_log_likelihood = fixed_be$nll,
  a_profile_lower_95 = fixed_be$interval[1],
  a_profile_upper_95 = fixed_be$interval[2],
  cutoff = fixed_be$cutoff
), file.path(output_dir, "fixed_b1_exponential_R.csv"), row.names = FALSE)

write_prediction <- function(filename, times, truth, pred) {
  write.csv(data.frame(time = times, heldout = truth,
    conditional_mean = pred$mean,
    pointwise_lower_95 = pred$lower,
    pointwise_upper_95 = pred$upper),
    file.path(output_dir, filename), row.names = FALSE)
}
write_prediction("boundary_power_prediction_R.csv", boundary_times_all[361:400], data_boundary[361:400], pred_bp)
write_prediction("boundary_exp_prediction_R.csv", boundary_times_all[361:400], data_boundary[361:400], pred_be)
write_prediction("boundary_K1_prediction_R.csv", boundary_times_all[361:400], data_boundary[361:400], pred_K1)
write_prediction("power_sim_prediction_R.csv", power_times_all[451:500], data_power[451:500], pred_pp)
write_prediction("exp_sim_prediction_R.csv", exp_times_all[361:400], data_exp[361:400], pred_ee)

capture.output(sessionInfo(), file = file.path(output_dir, "sessionInfo.txt"))
print(summary_table, digits = 8)
print(fixed_be)
message("Results written to: ", output_dir)
