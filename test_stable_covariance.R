#!/usr/bin/env Rscript
script_path <- sub("^--file=", "", grep("^--file=", commandArgs(FALSE), value = TRUE)[1])
if (is.na(script_path) || !nzchar(script_path)) script_path <- normalizePath("test_stable_covariance.R")
test_dir <- dirname(normalizePath(script_path))
r_dir <- dirname(test_dir)
root_dir <- dirname(r_dir)
source(file.path(r_dir, "wsbm_covariance_stable.R"))
source(file.path(r_dir, "wsbm_likelihood.R"))

assert_close <- function(x, y, tol, message) {
  error <- max(abs(x - y))
  if (!is.finite(error) || error > tol) stop(message, "; max error = ", format(error, digits = 8))
}

# 1. The two weight families coincide at a=0.
times <- seq(0.05, 1, length.out = 20)
for (b in c(0.4, 1, 1.4)) {
  Kp <- wsbm_covariance(times, 0, b, "power")
  Ke <- wsbm_covariance(times, 0, b, "exponential")
  assert_close(Kp, Ke, 2e-8, paste("family mismatch at b=", b))
}

# 2. Stable logarithmic power evaluation remains positive definite for a<0.
Kneg <- power_covariance_log(times, -0.2)
if (min(eigen(Kneg, symmetric = TRUE, only.values = TRUE)$values) <= 0) {
  stop("negative-a logarithmic power covariance is not positive definite")
}

# 3. The matched boundary formula agrees with independent stabilized quadrature.
small_times <- seq(0.1, 1.5, length.out = 9)
for (family in c("power", "exponential")) {
  a <- if (family == "power") -0.1 else 0.02
  for (b in c(0.9995, 1, 1.0005)) {
    Km <- wsbm_covariance(small_times, a, b, family, "matched")
    Kq <- wsbm_covariance(small_times, a, b, family, "quadrature",
      quadrature_order = 192L)
    assert_close(Km, Kq, 2e-6,
      paste("matched/quadrature mismatch for", family, "at b=", b))
  }
}

# 4. Likelihoods are finite and continuous through the logarithmic boundary.
data <- seq_along(times) / 100
for (family in c("power", "exponential")) {
  values <- vapply(c(0.9999, 1, 1.0001), function(b) {
    gaussian_nll(data, wsbm_covariance(times, 0.01, b, family))
  }, numeric(1))
  if (any(!is.finite(values)) || max(abs(diff(values))) > 1) {
    stop("likelihood discontinuity detected for ", family)
  }
}

# 5. Prediction uses Cholesky solves and returns correctly ordered bands.
pred <- conditional_prediction(times[1:15], times[16:20], data[1:15],
  0, 1, "power", nsim = 200L, seed = 123L)
stopifnot(length(pred$mean) == 5L,
          all(pred$lower <= pred$upper),
          all(is.finite(pred$mean)))

# 6. The nominal 95% profile cutoff is the standard chi-square value.
stopifnot(abs(qchisq(0.95, 1) - 3.84145882069412) < 1e-12)

# Optional slow regression test on the supplied boundary data.
if (identical(Sys.getenv("RUN_SLOW_TESTS"), "1")) {
  y <- read.csv(file.path(root_dir, "data", "sim_data_wsfBm.csv"))$x[1:360]
  tt <- (1:360) * 10 / 400
  fixed <- fit_fixed_b1(tt, y, "exponential", c(-0.2, 0.2))
  if (abs(fixed$a_hat - 0.0176526) > 5e-4) {
    stop("fixed-b=1 MLE regression failed: ", fixed$a_hat)
  }
  assert_close(fixed$interval, c(-0.0094807, 0.0465762), 8e-4,
    "fixed-b=1 profile interval regression failed")
}

cat("All stable covariance tests passed.\n")
