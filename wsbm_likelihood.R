# Gaussian likelihood, profile likelihood, and prediction utilities.
# Source wsbm_covariance_stable.R before using this file.

safe_chol <- function(K, jitter_rel = 1e-12, max_tries = 9L) {
  K <- (K + t(K)) / 2
  scale <- mean(diag(K))
  if (!is.finite(scale) || scale <= 0) stop("invalid covariance diagonal")
  jitter <- 0
  last_error <- NULL
  for (k in 0:(max_tries - 1L)) {
    attempt <- tryCatch(chol(K + diag(jitter, nrow(K))), error = identity)
    if (!inherits(attempt, "error")) {
      return(list(R = attempt, jitter = jitter, covariance = K))
    }
    last_error <- attempt
    jitter <- if (k == 0L) jitter_rel * scale else 10 * jitter
  }
  stop(conditionMessage(last_error))
}

chol_solve <- function(R, rhs) {
  backsolve(R, forwardsolve(t(R), rhs))
}

gaussian_nll <- function(data, K, return_details = FALSE) {
  data <- as.numeric(data)
  if (length(data) != nrow(K)) stop("data and covariance dimensions disagree")
  cc <- safe_chol(K)
  alpha <- chol_solve(cc$R, data)
  logdet <- 2 * sum(log(diag(cc$R)))
  value <- 0.5 * (length(data) * log(2 * pi) + logdet + sum(data * alpha))
  if (return_details) return(list(nll = value, jitter = cc$jitter, R = cc$R))
  value
}

wsbm_nll <- function(theta, times, data, family,
                     boundary_method = "matched") {
  a <- theta[1]
  b <- theta[2]
  if (!is.finite(a) || !is.finite(b)) return(.Machine$double.xmax / 100)
  if (family == "power" && a <= -1) return(.Machine$double.xmax / 100)
  if (b < 0 || b > 2) return(.Machine$double.xmax / 100)
  tryCatch({
    K <- wsbm_covariance(times, a, b, family, boundary_method)
    value <- gaussian_nll(data, K)
    if (is.finite(value)) value else .Machine$double.xmax / 100
  }, error = function(e) .Machine$double.xmax / 100)
}

fit_wsbm <- function(times, data, family = c("power", "exponential"),
                     starts = NULL,
                     lower = NULL,
                     upper = NULL,
                     boundary_method = "matched") {
  family <- match.arg(family)
  if (is.null(lower)) lower <- if (family == "power") c(-0.95, 0) else c(-0.75, 0)
  if (is.null(upper)) upper <- if (family == "power") c(2, 2) else c(0.75, 2)
  if (is.null(starts)) starts <- rbind(c(0, 1), (lower + upper) / 2)
  starts <- as.matrix(starts)
  objective <- function(par) wsbm_nll(par, times, data, family, boundary_method)

  fits <- vector("list", nrow(starts))
  for (i in seq_len(nrow(starts))) {
    start <- pmin(pmax(starts[i, ], lower), upper)
    fits[[i]] <- optim(start, objective, method = "L-BFGS-B",
      lower = lower, upper = upper,
      control = list(factr = 1e7, pgtol = 1e-7, maxit = 500L))
  }
  values <- vapply(fits, function(x) x$value, numeric(1))
  best <- fits[[which.min(values)]]
  list(par = best$par, nll = best$value, convergence = best$convergence,
       message = best$message, all_fits = fits,
       AIC = 4 + 2 * best$value, family = family)
}

profile_nll <- function(fixed_value, fixed = c("a", "b"),
                        times, data, family, nuisance_interval,
                        boundary_method = "matched", tol = 2e-6) {
  fixed <- match.arg(fixed)
  objective <- function(nuisance) {
    theta <- if (fixed == "a") c(fixed_value, nuisance) else c(nuisance, fixed_value)
    wsbm_nll(theta, times, data, family, boundary_method)
  }
  oo <- optimize(objective, nuisance_interval, tol = tol)
  c(nll = oo$objective, nuisance_hat = oo$minimum)
}

profile_interval <- function(fit, fixed = c("a", "b"),
                             fixed_interval, nuisance_interval,
                             times, data, family,
                             level = 0.95,
                             boundary_method = "matched") {
  fixed <- match.arg(fixed)
  index <- if (fixed == "a") 1L else 2L
  mle <- fit$par[index]
  cutoff <- qchisq(level, df = 1)
  cache <- new.env(parent = emptyenv())
  prof <- function(x) {
    key <- sprintf("%.12g", x)
    if (!exists(key, envir = cache, inherits = FALSE)) {
      assign(key, profile_nll(x, fixed, times, data, family,
        nuisance_interval, boundary_method), envir = cache)
    }
    get(key, envir = cache)[["nll"]]
  }
  root_fun <- function(x) 2 * (prof(x) - fit$nll) - cutoff
  left <- uniroot(root_fun, c(fixed_interval[1], mle), tol = 2e-7)$root
  right <- uniroot(root_fun, c(mle, fixed_interval[2]), tol = 2e-7)$root
  c(lower = left, upper = right, cutoff = cutoff)
}

fit_fixed_b1 <- function(times, data, family = c("power", "exponential"),
                         a_interval, level = 0.95) {
  family <- match.arg(family)
  objective <- function(a) {
    K <- wsbm_covariance(times, a, 1, family)
    gaussian_nll(data, K)
  }
  fit <- optimize(objective, a_interval, tol = 1e-9)
  cutoff <- qchisq(level, 1)
  root_fun <- function(a) 2 * (objective(a) - fit$objective) - cutoff
  left <- uniroot(root_fun, c(a_interval[1], fit$minimum), tol = 1e-9)$root
  right <- uniroot(root_fun, c(fit$minimum, a_interval[2]), tol = 1e-9)$root
  list(a_hat = fit$minimum, nll = fit$objective,
       interval = c(left, right), cutoff = cutoff)
}

covariance_diagnostics <- function(K) {
  values <- eigen((K + t(K)) / 2, symmetric = TRUE, only.values = TRUE)$values
  c(min_eigenvalue = min(values), max_eigenvalue = max(values),
    condition_number = max(values) / min(values),
    mean_diagonal = mean(diag(K)))
}

conditional_prediction <- function(times_observed, times_future, data,
                                   a, b, family,
                                   nsim = 1000L, seed = 20260827L,
                                   boundary_method = "matched") {
  times_observed <- as.numeric(times_observed)
  times_future <- as.numeric(times_future)
  data <- as.numeric(data)
  nsim <- as.integer(nsim)
  if (!length(times_observed) || !length(times_future)) {
    stop("observed and future time grids must both be non-empty")
  }
  if (length(data) != length(times_observed)) {
    stop("data length must equal the observed-grid length")
  }
  if (any(!is.finite(times_observed)) || any(!is.finite(times_future)) ||
      any(diff(times_observed) <= 0) || any(diff(times_future) <= 0)) {
    stop("time grids must be finite and strictly increasing")
  }
  if (min(times_future) <= max(times_observed)) {
    stop("future times must be strictly later than the observed times")
  }
  if (!is.finite(nsim) || nsim < 1L) stop("nsim must be a positive integer")

  all_times <- c(times_observed, times_future)
  K <- wsbm_covariance(all_times, a, b, family, boundary_method)
  n <- length(times_observed)
  K11 <- K[seq_len(n), seq_len(n), drop = FALSE]
  K12 <- K[seq_len(n), (n + 1):nrow(K), drop = FALSE]
  K21 <- t(K12)
  K22 <- K[(n + 1):nrow(K), (n + 1):nrow(K), drop = FALSE]
  cc <- safe_chol(K11)
  alpha <- chol_solve(cc$R, as.numeric(data))
  mean_future <- as.numeric(K21 %*% alpha)
  solve12 <- chol_solve(cc$R, K12)
  covariance_future <- (K22 - K21 %*% solve12)
  covariance_future <- (covariance_future + t(covariance_future)) / 2

  ee <- eigen(covariance_future, symmetric = TRUE)
  spectral_tol <- 1e-10 * max(1, max(abs(ee$values)))
  if (min(ee$values) < -spectral_tol) {
    stop("conditional covariance is not positive semidefinite; minimum eigenvalue = ",
         format(min(ee$values), digits = 8))
  }
  values <- pmax(ee$values, 0)
  set.seed(seed)
  Z <- matrix(rnorm(nsim * length(times_future)), nsim, length(times_future))
  transform <- ee$vectors %*% diag(sqrt(values), nrow = length(values))
  simulations <- sweep(Z %*% t(transform), 2, mean_future, "+")
  lower <- apply(simulations, 2, quantile, probs = 0.025, names = FALSE)
  upper <- apply(simulations, 2, quantile, probs = 0.975, names = FALSE)
  list(mean = mean_future, covariance = covariance_future,
       simulations = simulations, lower = lower, upper = upper,
       training_jitter = cc$jitter)
}
