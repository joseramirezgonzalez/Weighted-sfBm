#!/usr/bin/env Rscript

# Regenerate the corrected profile and prediction figures with base R.
# The likelihood-surface PNG supplied with the manuscript is retained because
# a dense two-dimensional refit is substantially more expensive; all one-
# dimensional profiles and prediction figures are regenerated here.

script_path <- sub("^--file=", "", grep("^--file=", commandArgs(FALSE), value = TRUE)[1])
if (is.na(script_path) || !nzchar(script_path)) script_path <- normalizePath("plot_corrected_results.R")
script_dir <- dirname(normalizePath(script_path))
root_dir <- dirname(script_dir)
source(file.path(script_dir, "wsbm_covariance_stable.R"))
source(file.path(script_dir, "wsbm_likelihood.R"))

result_dir <- file.path(root_dir, "numerical_results")
figure_dir <- file.path(root_dir, "reproduced_figures_R")
dir.create(figure_dir, recursive = TRUE, showWarnings = FALSE)

summary_table <- read.csv(file.path(result_dir, "corrected_fit_summary.csv"),
                          stringsAsFactors = FALSE)
row_for <- function(experiment) {
  ans <- summary_table[summary_table$experiment == experiment, , drop = FALSE]
  if (nrow(ans) != 1L) stop("missing unique summary row: ", experiment)
  ans
}

read_profile <- function(name) {
  read.csv(file.path(result_dir, name), stringsAsFactors = FALSE)
}

profile_ratio <- function(df) {
  # The stored column contains the profiled negative log-likelihood; lower is better.
  exp(min(df$profile_nll) - df$profile_nll)
}

plot_profile <- function(df, mle, truth, lower, upper, xlab, title) {
  ratio <- profile_ratio(df)
  plot(df$fixed_parameter, ratio, type = "l", lwd = 2,
       xlab = xlab, ylab = "Profile likelihood ratio", main = title,
       ylim = c(0, 1.04))
  abline(v = truth, lty = 2, lwd = 1.5)
  abline(v = mle, lty = 1, lwd = 1.5)
  abline(v = c(lower, upper), lty = 3, lwd = 1.5)
  legend("topright", legend = c("Profile likelihood ratio", "Generating value",
                                 "MLE", "95% profile limits"),
         lty = c(1, 2, 1, 3), lwd = c(2, 1.5, 1.5, 1.5), cex = 0.72,
         bty = "n")
}

prediction_panel <- function(times_observed, observed, times_future, truth, pred,
                             title, max_paths = 200L) {
  yrange <- range(c(observed, truth, pred$lower, pred$upper), finite = TRUE)
  plot(times_observed, observed, type = "l", lwd = 1.5,
       xlim = range(c(times_observed, times_future)), ylim = yrange,
       xlab = expression(t), ylab = "Process value", main = title)
  polygon(c(times_future, rev(times_future)),
          c(pred$lower, rev(pred$upper)), border = NA,
          col = grDevices::adjustcolor("lightblue", alpha.f = 0.45))
  count <- min(as.integer(max_paths), nrow(pred$simulations))
  if (count > 0L) {
    for (i in seq_len(count)) {
      lines(times_future, pred$simulations[i, ],
            col = grDevices::adjustcolor("gray55", alpha.f = 0.18), lwd = 0.5)
    }
  }
  lines(times_observed, observed, lwd = 1.5)
  lines(times_future, truth, lty = 2, lwd = 1.5)
  lines(times_future, pred$mean, lwd = 2)
  legend("topleft", legend = c("Observed trajectory", "Held-out trajectory",
                                "95% pointwise prediction band", "Conditional mean"),
         lty = c(1, 2, NA, 1), lwd = c(1.5, 1.5, NA, 2),
         pch = c(NA, NA, 15, NA), pt.cex = c(NA, NA, 1.6, NA),
         cex = 0.72, bty = "n")
}

nsim <- suppressWarnings(as.integer(Sys.getenv("NSIM", "1000")))
if (!is.finite(nsim) || nsim < 1L) nsim <- 1000L

# Boundary data and fits.
boundary_all <- read.csv(file.path(root_dir, "data", "sim_data_wsfBm.csv"))$x
boundary_times_all <- (1:400) * 10 / 400
n_boundary <- 360L
boundary_times <- boundary_times_all[seq_len(n_boundary)]
boundary_data <- boundary_all[seq_len(n_boundary)]
boundary_future <- boundary_times_all[(n_boundary + 1):400]
boundary_truth <- boundary_all[(n_boundary + 1):400]

bp <- row_for("boundary_power")
be <- row_for("boundary_exp")
bk <- row_for("boundary_K1")

bp_pred <- conditional_prediction(boundary_times, boundary_future, boundary_data,
                                  bp$a_hat, bp$b_hat, "power", nsim = nsim,
                                  seed = 20260827L)
be_pred <- conditional_prediction(boundary_times, boundary_future, boundary_data,
                                  be$a_hat, be$b_hat, "exponential", nsim = nsim,
                                  seed = 20260828L)
bk_pred <- conditional_prediction(boundary_times, boundary_future, boundary_data,
                                  0, 1, "power", nsim = nsim,
                                  seed = 20260829L)

png(file.path(figure_dir, "profile_power_boundary_R.png"),
    width = 1800, height = 760, res = 170)
par(mfrow = c(1, 2), mar = c(4.4, 4.4, 3, 1.2))
plot_profile(read_profile("boundary_power_a.csv"), bp$a_hat, 0,
             bp$a_profile_lower_95, bp$a_profile_upper_95,
             expression(a), "(a) Profile in a")
plot_profile(read_profile("boundary_power_b.csv"), bp$b_hat, 1,
             bp$b_profile_lower_95, bp$b_profile_upper_95,
             expression(b), "(b) Profile in b")
dev.off()

fixed_exp <- read.csv(file.path(result_dir, "fixed_b1_exponential_profile.csv"))
png(file.path(figure_dir, "profile_exp_boundary_R.png"),
    width = 1800, height = 1180, res = 170)
layout(matrix(c(1, 3, 2, 3), 2, 2, byrow = TRUE), widths = c(1, 1.2))
par(mar = c(4.4, 4.4, 3, 1.2))
plot_profile(read_profile("boundary_exp_b.csv"), be$b_hat, 1,
             be$b_profile_lower_95, be$b_profile_upper_95,
             expression(b), "(a) Profile in b")
plot_profile(read_profile("boundary_exp_a.csv"), be$a_hat, 0,
             be$a_profile_lower_95, be$a_profile_upper_95,
             expression(a), "(b) Unrestricted profile in a")
plot_profile(read_profile("fixed_b1_exp_a.csv"), fixed_exp$a_hat, 0,
             fixed_exp$a_profile_lower_95, fixed_exp$a_profile_upper_95,
             expression(a), "(c) Profile in a with b=1")
dev.off()

png(file.path(figure_dir, "predictions_boundary_R.png"),
    width = 1800, height = 1700, res = 170)
par(mfrow = c(3, 1), mar = c(4.2, 4.4, 3, 1.2))
prediction_panel(boundary_times, boundary_data, boundary_future, boundary_truth,
                 bk_pred, "(a) Logarithmic boundary covariance")
prediction_panel(boundary_times, boundary_data, boundary_future, boundary_truth,
                 bp_pred, "(b) Fitted power-weight family")
prediction_panel(boundary_times, boundary_data, boundary_future, boundary_truth,
                 be_pred, "(c) Fitted exponential-weight family")
dev.off()

# Nonboundary power experiment.
power_all <- read.csv(file.path(root_dir, "data", "sim_data_wsfBm_pol.csv"))$x
power_times_all <- (1:500) * 10 / 500
n_power <- 450L
power_times <- power_times_all[seq_len(n_power)]
power_future <- power_times_all[(n_power + 1):500]
pp <- row_for("power_sim")
pp_pred <- conditional_prediction(power_times, power_future, power_all[1:n_power],
                                  pp$a_hat, pp$b_hat, "power", nsim = nsim,
                                  seed = 20260830L)

png(file.path(figure_dir, "inference_power_R.png"),
    width = 1800, height = 1250, res = 170)
layout(matrix(c(1, 2, 3, 3), 2, 2, byrow = TRUE))
par(mar = c(4.4, 4.4, 3, 1.2))
plot_profile(read_profile("power_sim_a.csv"), pp$a_hat, 0.42,
             pp$a_profile_lower_95, pp$a_profile_upper_95,
             expression(a), "(a) Profile in a")
plot_profile(read_profile("power_sim_b.csv"), pp$b_hat, 1.59,
             pp$b_profile_lower_95, pp$b_profile_upper_95,
             expression(b), "(b) Profile in b")
prediction_panel(power_times, power_all[1:n_power], power_future,
                 power_all[(n_power + 1):500], pp_pred,
                 "(c) Held-out prediction")
dev.off()

# Nonboundary exponential experiment.
exp_all <- read.csv(file.path(root_dir, "data", "sim_data_wsfBm_exp.csv"))$x
exp_times_all <- (1:400) * 4 / 400
n_exp <- 360L
exp_times <- exp_times_all[seq_len(n_exp)]
exp_future <- exp_times_all[(n_exp + 1):400]
ee <- row_for("exp_sim")
ee_pred <- conditional_prediction(exp_times, exp_future, exp_all[1:n_exp],
                                  ee$a_hat, ee$b_hat, "exponential", nsim = nsim,
                                  seed = 20260831L)

png(file.path(figure_dir, "inference_exponential_R.png"),
    width = 1800, height = 1250, res = 170)
layout(matrix(c(1, 2, 3, 3), 2, 2, byrow = TRUE))
par(mar = c(4.4, 4.4, 3, 1.2))
plot_profile(read_profile("exp_sim_a.csv"), ee$a_hat, -0.34,
             ee$a_profile_lower_95, ee$a_profile_upper_95,
             expression(a), "(a) Profile in a")
plot_profile(read_profile("exp_sim_b.csv"), ee$b_hat, 1.23,
             ee$b_profile_lower_95, ee$b_profile_upper_95,
             expression(b), "(b) Profile in b")
prediction_panel(exp_times, exp_all[1:n_exp], exp_future,
                 exp_all[(n_exp + 1):400], ee_pred,
                 "(c) Held-out prediction")
dev.off()

message("Corrected R figures written to: ", figure_dir)
