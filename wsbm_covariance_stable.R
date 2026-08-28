# Stable covariance evaluation for weighted sub-fractional Brownian motion.
#
# This file replaces the numerically fragile covariance functions in the
# historical script.  It does not install packages as a side effect.
# All functions are vectorized unless explicitly documented otherwise.

.ws_preserve_dim <- function(value, template) {
  dim(value) <- dim(template)
  value
}

xlogx <- function(x) {
  out <- x * 0
  idx <- is.finite(x) & x > 0
  out[idx] <- x[idx] * log(x[idx])
  out
}

z2logz <- function(x) {
  out <- x * 0
  idx <- is.finite(x) & x > 0
  out[idx] <- x[idx]^2 * log(x[idx])
  out
}

q_b_stable <- function(x, y, b, boundary_tol = 1e-13) {
  stopifnot(length(b) == 1L, is.finite(b))
  if (abs(b - 1) <= boundary_tol) {
    return(xlogx(x + y) - xlogx(x) - xlogx(y))
  }
  if (abs(b) <= boundary_tol) {
    return(1.0 * (x > 0 & y > 0))
  }
  if (abs(b - 2) <= boundary_tol) {
    return(2 * x * y)
  }

  delta <- b - 1
  if (abs(delta) < 0.15) {
    z_delta <- function(z) {
      out <- z * 0
      idx <- z > 0
      out[idx] <- z[idx] * expm1(delta * log(z[idx]))
      out
    }
    return(-(z_delta(x) + z_delta(y) - z_delta(x + y)) / delta)
  }
  (x^b + y^b - (x + y)^b) / (1 - b)
}

constant_log_covariance <- function(times) {
  times <- as.numeric(times)
  s <- outer(times, rep(1, length(times)))
  t <- t(s)
  0.25 * (z2logz(s + t) + z2logz(abs(s - t))) -
    0.5 * (z2logz(s) + z2logz(t))
}

H_power_stable <- function(x, a, tol = 2e-14, max_terms = 2000L) {
  if (!is.finite(a) || a <= -1) stop("a must be finite and greater than -1")
  template <- x
  x <- as.numeric(x)
  out <- numeric(length(x))
  out[x <= 0] <- 0
  h1 <- beta(a + 1, 2) * (digamma(2) - digamma(a + 3))
  out[x >= 1] <- h1
  mid <- which(x > 0 & x < 1)
  if (!length(mid)) return(.ws_preserve_dim(out, template))

  xm <- x[mid]
  values <- numeric(length(xm))
  low <- which(xm <= 0.88)
  if (length(low)) {
    xl <- xm[low]
    total <- -xl^(a + 2) / (a + 2)
    power <- xl^(a + 3)
    for (n in 2:max_terms) {
      term <- power / (n * (n - 1) * (a + n + 1))
      total <- total + term
      if (n > 20 && max(abs(term)) <= tol * max(1, max(abs(total)))) break
      power <- power * xl
    }
    values[low] <- total
  }

  high <- setdiff(seq_along(xm), low)
  if (length(high)) {
    xh <- xm[high]
    h <- 1 - xh
    logh <- log(h)
    tail <- numeric(length(h))
    coefficient <- 1
    hpower <- h^2
    for (k in 0:(max_terms - 1L)) {
      d <- k + 2
      term <- coefficient * hpower * (logh / d - 1 / d^2)
      tail <- tail + term
      if (k > 12 && max(abs(term)) <= tol * max(1, max(abs(tail)))) break
      coefficient <- coefficient * (k - a) / (k + 1)
      hpower <- hpower * h
    }
    values[high] <- h1 - tail
  }
  out[mid] <- values
  .ws_preserve_dim(out, template)
}

power_covariance_log <- function(times, a) {
  times <- as.numeric(times)
  if (a <= -1) stop("a must be greater than -1")
  n <- length(times)
  s <- outer(times, rep(1, n))
  t <- t(s)
  m <- pmin(s, t)
  M <- pmax(s, t)
  K <- matrix(0, n, n)
  idx <- which(m > 0)
  if (!length(idx)) return(K)

  mv <- m[idx]
  Mv <- M[idx]
  x1 <- 2 * mv / (Mv + mv)
  x2 <- mv / Mv
  B1 <- beta(a + 1, 2)

  termA <- 2^(-a - 1) * (Mv + mv)^(a + 2) *
    (log(Mv + mv) * B1 * pbeta(x1, a + 1, 2) + H_power_stable(x1, a))
  termB <- Mv^(a + 2) *
    (log(Mv) * B1 * pbeta(x2, a + 1, 2) + H_power_stable(x2, a))
  termC <- mv^(a + 2) *
    (log(mv) * B1 + beta(a + 1, 2) * (digamma(2) - digamma(a + 3)))
  K[idx] <- termA - termB - termC
  (K + t(K)) / 2
}

power_covariance_closed <- function(times, a, b) {
  times <- as.numeric(times)
  if (a <= -1) stop("a must be greater than -1")
  if (abs(b - 1) <= 1e-14) return(power_covariance_log(times, a))
  if (b <= -1) stop("b must be greater than -1")

  n <- length(times)
  s <- outer(times, rep(1, n))
  t <- t(s)
  m <- pmin(s, t)
  M <- pmax(s, t)
  K <- matrix(0, n, n)
  idx <- which(m > 0)
  if (!length(idx)) return(K)

  mv <- m[idx]
  Mv <- M[idx]
  p <- a + 1
  q <- b + 1
  exponent <- a + b + 1
  B <- beta(p, q)
  x2 <- mv / Mv
  x3 <- 2 * mv / (Mv + mv)
  term1 <- mv^exponent * B
  term2 <- Mv^exponent * B * pbeta(x2, p, q)
  term3 <- 2^(-a - 1) * (Mv + mv)^exponent * B * pbeta(x3, p, q)
  K[idx] <- (term1 + term2 - term3) / (1 - b)
  (K + t(K)) / 2
}

J_exp_series <- function(c, m, a, b, tol = 2e-14, max_terms = 120L) {
  if (b <= -1) stop("b must be greater than -1")
  template <- c
  c <- as.numeric(c)
  m <- as.numeric(m)
  out <- numeric(length(c))
  idx <- which(m > 0 & c > 0)
  if (!length(idx)) return(.ws_preserve_dim(out, template))

  cv <- c[idx]
  mv <- pmin(m[idx], cv)
  x <- mv / cv
  base <- cv^(b + 1)
  coefficient <- rep(1, length(cv))
  total <- base * beta(1, b + 1) * pbeta(x, 1, b + 1)
  for (k in 1:max_terms) {
    coefficient <- coefficient * (a * cv) / k
    term <- base * coefficient * beta(k + 1, b + 1) * pbeta(x, k + 1, b + 1)
    total <- total + term
    if (k > 12 && max(abs(term)) <= tol * max(1, max(abs(total)))) break
  }
  out[idx] <- total
  .ws_preserve_dim(out, template)
}

primitive_ylog <- function(y, p) {
  template <- y
  y <- as.numeric(y)
  out <- numeric(length(y))
  idx <- which(y > 0)
  pp <- p + 1
  out[idx] <- y[idx]^pp * (log(y[idx]) / pp - 1 / pp^2)
  .ws_preserve_dim(out, template)
}

I_k_clog <- function(c, m, k) {
  total <- c * 0
  lower <- c - m
  for (j in 0:k) {
    total <- total + (-1)^j * choose(k, j) * c^(k - j) *
      (primitive_ylog(c, j + 1) - primitive_ylog(lower, j + 1))
  }
  total
}

L_exp_series <- function(c, m, a, tol = 5e-14, max_terms = 70L) {
  total <- c * 0
  coefficient <- 1
  for (k in 0:(max_terms - 1L)) {
    if (k > 0) coefficient <- coefficient * a / k
    term <- coefficient * I_k_clog(c, m, k)
    total <- total + term
    if (k > 8 && max(abs(term)) <= tol * max(1, max(abs(total)))) break
  }
  total
}

Phi_exp_analytic <- function(y, a) {
  if (abs(a) < 1e-12) stop("Phi_exp_analytic must not be used at a=0")
  if (!requireNamespace("expint", quietly = TRUE)) {
    stop("Package 'expint' is required for the analytic large-|a| branch")
  }
  template <- y
  y <- as.numeric(y)
  out <- numeric(length(y))
  idx <- which(y > 0)
  out[idx] <- (expint::expint_Ei(-a * y[idx]) -
    exp(-a * y[idx]) * ((a * y[idx] + 1) * log(y[idx]) + 1)) / a^2
  out[y <= 0] <- (-digamma(1) + log(abs(a)) - 1) / a^2
  .ws_preserve_dim(out, template)
}

L_exp_direct <- function(c, m, a, rel.tol = 1e-10) {
  template <- c
  c <- as.numeric(c)
  m <- as.numeric(m)
  out <- numeric(length(c))
  idx <- which(m > 0)
  if (length(idx)) {
    out[idx] <- vapply(idx, function(i) {
      integrate(function(r) {
        z <- c[i] - r
        exp(a * r) * xlogx(z)
      }, lower = 0, upper = m[i], rel.tol = rel.tol,
      subdivisions = 500L, stop.on.error = TRUE)$value
    }, numeric(1))
  }
  .ws_preserve_dim(out, template)
}

L_exp_stable <- function(c, m, a) {
  if (max(abs(a) * abs(c)) <= 0.8) return(L_exp_series(c, m, a))
  if (requireNamespace("expint", quietly = TRUE)) {
    return(exp(a * c) * (Phi_exp_analytic(c, a) - Phi_exp_analytic(c - m, a)))
  }
  L_exp_direct(c, m, a)
}

# Cache the exact power-series basis
#   K_a^{(2)}(s,t) = sum_{k>=0} a^k/k! K_k^{(1)}(s,t),
# which follows by expanding exp(a u).  This makes repeated likelihood
# evaluations near a=0 much faster and avoids the subtraction in Phi_a.
.exp_log_basis_cache <- new.env(parent = emptyenv())

clear_wsbm_covariance_cache <- function() {
  rm(list = ls(envir = .exp_log_basis_cache, all.names = TRUE),
     envir = .exp_log_basis_cache)
  invisible(NULL)
}

.exp_log_basis_key <- function(times, order) {
  paste0(order, ":", paste(sprintf("%.17g", as.numeric(times)), collapse = ","))
}

exp_log_basis <- function(times, order = 36L) {
  order <- as.integer(order)
  key <- .exp_log_basis_key(times, order)
  if (exists(key, envir = .exp_log_basis_cache, inherits = FALSE)) {
    return(get(key, envir = .exp_log_basis_cache, inherits = FALSE))
  }
  basis <- lapply(0:order, function(k) power_covariance_log(times, k))
  assign(key, basis, envir = .exp_log_basis_cache)
  basis
}

exp_log_from_basis <- function(a, basis) {
  K <- matrix(0, nrow(basis[[1L]]), ncol(basis[[1L]]))
  coefficient <- 1
  for (k in seq_along(basis)) {
    if (k > 1L) coefficient <- coefficient * a / (k - 1L)
    K <- K + coefficient * basis[[k]]
  }
  (K + t(K)) / 2
}

exponential_covariance_log_integral <- function(times, a) {
  times <- as.numeric(times)
  n <- length(times)
  s <- outer(times, rep(1, n))
  t <- t(s)
  m <- pmin(s, t)
  c <- (s + t) / 2
  K <- 2 * L_exp_stable(c, m, a) +
    2 * log(2) * J_exp_series(c, m, a, 1) -
    L_exp_stable(s, m, a) - L_exp_stable(t, m, a)
  (K + t(K)) / 2
}

exponential_covariance_log <- function(times, a) {
  times <- as.numeric(times)
  scale <- if (length(times)) max(times) else 0
  # With |a|max(t)<=1.8, 36 Taylor terms are far below double-precision
  # error.  Outside this region use the integral/analytic implementation.
  if (abs(a) * scale <= 1.8) {
    return(exp_log_from_basis(a, exp_log_basis(times, 36L)))
  }
  exponential_covariance_log_integral(times, a)
}

exponential_covariance_closed <- function(times, a, b) {
  if (abs(b - 1) <= 1e-14) return(exponential_covariance_log(times, a))
  times <- as.numeric(times)
  n <- length(times)
  s <- outer(times, rep(1, n))
  t <- t(s)
  m <- pmin(s, t)
  K <- (J_exp_series(s, m, a, b) + J_exp_series(t, m, a, b) -
    2^b * J_exp_series((s + t) / 2, m, a, b)) / (1 - b)
  (K + t(K)) / 2
}

gauss_legendre <- local({
  cache <- new.env(parent = emptyenv())
  function(n = 128L) {
    key <- as.character(as.integer(n))
    if (exists(key, envir = cache, inherits = FALSE)) return(get(key, envir = cache))
    n <- as.integer(n)
    if (n < 2L) stop("quadrature order must be at least 2")
    i <- seq_len(n - 1L)
    off <- i / sqrt(4 * i^2 - 1)
    J <- matrix(0, n, n)
    J[cbind(i, i + 1L)] <- off
    J[cbind(i + 1L, i)] <- off
    ee <- eigen(J, symmetric = TRUE)
    ord <- order(ee$values)
    nodes <- (ee$values[ord] + 1) / 2
    weights <- (2 * ee$vectors[1, ord]^2) / 2
    ans <- list(nodes = nodes, weights = weights)
    assign(key, ans, envir = cache)
    ans
  }
})

boundary_covariance_quadrature <- function(times, a, b, family = c("power", "exponential"),
                                           order = 128L) {
  family <- match.arg(family)
  if (family == "power" && a <= -1) stop("a must be greater than -1")
  times <- as.numeric(times)
  n <- length(times)
  gl <- gauss_legendre(order)
  x <- gl$nodes
  w <- gl$weights
  K <- matrix(0, n, n)
  for (i in seq_len(n)) {
    for (j in seq_len(i)) {
      s <- times[i]
      t <- times[j]
      m <- min(s, t)
      if (m == 0) {
        value <- 0
      } else if (family == "power") {
        # u=m*x^(1/(a+1)) absorbs the possible power singularity exactly.
        u <- m * x^(1 / (a + 1))
        value <- m^(a + 1) / (a + 1) *
          sum(w * q_b_stable(s - u, t - u, b))
      } else {
        u <- m * x
        value <- m * sum(w * exp(a * u) * q_b_stable(s - u, t - u, b))
      }
      K[i, j] <- value
      K[j, i] <- value
    }
  }
  (K + t(K)) / 2
}

matched_boundary_covariance <- function(times, a, b, family, width = 1e-3) {
  delta <- b - 1
  log_fun <- if (family == "power") power_covariance_log else exponential_covariance_log
  closed_fun <- if (family == "power") power_covariance_closed else exponential_covariance_closed
  if (abs(delta) >= width) return(closed_fun(times, a, b))
  K0 <- log_fun(times, a)
  Kp <- closed_fun(times, a, 1 + width)
  Km <- closed_fun(times, a, 1 - width)
  d1 <- (Kp - Km) / (2 * width)
  d2 <- (Kp - 2 * K0 + Km) / width^2
  K <- K0 + delta * d1 + 0.5 * delta^2 * d2
  (K + t(K)) / 2
}

wsbm_covariance <- function(times, a, b,
                            family = c("power", "exponential"),
                            boundary_method = c("matched", "quadrature"),
                            boundary_width = 1e-3,
                            quadrature_order = 128L) {
  family <- match.arg(family)
  boundary_method <- match.arg(boundary_method)
  if (any(!is.finite(times)) || any(times < 0)) stop("times must be finite and non-negative")
  if (!is.finite(a) || !is.finite(b)) stop("parameters must be finite")
  if (family == "power" && a <= -1) stop("power exponent a must be greater than -1")
  if (b < 0 || b > 2) stop("this inference implementation restricts b to [0,2]")

  if (abs(b - 1) <= 1e-14) {
    return(if (family == "power") power_covariance_log(times, a)
           else exponential_covariance_log(times, a))
  }
  if (abs(b - 1) < boundary_width) {
    if (boundary_method == "quadrature") {
      return(boundary_covariance_quadrature(times, a, b, family, quadrature_order))
    }
    return(matched_boundary_covariance(times, a, b, family, boundary_width))
  }
  if (family == "power") power_covariance_closed(times, a, b)
  else exponential_covariance_closed(times, a, b)
}

covariance_function <- function(s, t, a, b, c = 0,
                                boundary_method = "matched") {
  family <- if (identical(as.integer(c), 0L)) "power" else "exponential"
  K <- wsbm_covariance(base::c(s, t), a, b, family, boundary_method)
  K[1, 2]
}

cov_wfbm <- function(time, a, b, c = 0, boundary_method = "matched") {
  family <- if (identical(as.integer(c), 0L)) "power" else "exponential"
  wsbm_covariance(time, a, b, family, boundary_method)
}
