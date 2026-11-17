#for github


# =============================================================================
#  Stochastic volatility with jumps in the Duffie-Pan-Singleton framework:
#  Heston, SVJ and SVJJ calibrated to SPX options on 13 November 2019
#  Financial Engineering, Group 5
#
#  ONE file, SEVEN self-contained parts. Run top to bottom (about 5-8 min the
#  first time; afterwards calibrations and the Monte Carlo study are read
#  from output/*.rds).
#
#    PART 0  Setup
#    PART 1  Data: load, dividend yield + discount curve, filters,
#            arbitrage checks, implied vols, train/test split
#    PART 2  Pricing and calibration tools (Riccati solver, Carr-Madan,
#            Levenberg-Marquardt)
#    PART 3  The DPS model: ONE transform for SVJJ; SVJ and Heston as
#            restrictions; unit checks
#    PART 4  Numerical illustrations: branch cut, pricer accuracy,
#            Monte Carlo validation, what each component does
#    PART 5  Calibration of Heston, SVJ and SVJJ (nested)
#    PART 6  Comparison and analysis
#
#  Packages: readxl, ggplot2, minpack.lm
#    install.packages(c("readxl", "ggplot2", "minpack.lm"))
# =============================================================================


# #############################################################################
# PART 0  SETUP
# #############################################################################

suppressPackageStartupMessages({
  library(readxl)       # read the Excel file
  library(ggplot2)      # figures
  library(minpack.lm)   # Levenberg-Marquardt least squares (nls.lm)
})

DATA_FILE <- "Data20191113.xlsx"   # must be in the working directory
OUT_DIR   <- "output"
FIG_DIR   <- file.path(OUT_DIR, "figures")
dir.create(FIG_DIR, recursive = TRUE, showWarnings = FALSE)

USE_CACHE <- TRUE   # TRUE: reuse saved calibrations in output/ if they exist
set.seed(2019)

# Run `expr` and save the result, or read it back if it was saved earlier
cached <- function(name, expr) {
  f <- file.path(OUT_DIR, paste0(name, ".rds"))
  if (USE_CACHE && file.exists(f)) return(readRDS(f))
  val <- expr
  saveRDS(val, f)
  val
}

save_fig <- function(plot, name, width = 8, height = 5) {
  ggsave(file.path(FIG_DIR, paste0(name, ".pdf")), plot, width = width, height = height)
  ggsave(file.path(FIG_DIR, paste0(name, ".png")), plot, width = width, height = height, dpi = 200)
}
theme_set(theme_bw(base_size = 11))


# #############################################################################
# PART 1  DATA
#
#   1.1 Black-Scholes and implied volatility (needed to build the surface)
#   1.2 Load the SPX options
#   1.3 Dividend yield and discount curve from put-call parity
#   1.4 Filters
#   1.5 Static-arbitrage checks
#   1.6 Implied volatility surface and its features
#   1.7 Train / test split
#
# CONVENTION used everywhere in this file
#   Forward:      F_T = S_0 exp((r_T - q) T),   discount factor D_T = exp(-r_T T)
#   Moneyness:    k = log(K / F_T)              (log-forward-moneyness)
#   Prices:       "normalised" = price / (D_T F_T)
#   Char. fcts:   of X_T = log(S_T / F_T), so the martingale condition is
#                 phi(-i) = 1 for every model.
# #############################################################################

# -----------------------------------------------------------------------------
# 1.1 Black-Scholes (normalised, forward form) and implied volatility
# -----------------------------------------------------------------------------

# Normalised Black-Scholes price: price / (D * F).
#   k   = log(K/F),  s = sigma * sqrt(tau)  (total volatility),  cp = "C" / "P"
bs_norm <- function(k, s, cp) {
  d1 <- (-k + 0.5 * s^2) / s
  d2 <- d1 - s
  call <- pnorm(d1) - exp(k) * pnorm(d2)
  put  <- exp(k) * pnorm(-d2) - pnorm(-d1)
  is_call <- rep_len(cp == "C", length(call))
  ifelse(is_call, call, put)
}

# Normalised Black-Scholes vega with respect to sigma: dPrice/dsigma / (D * F)
bs_vega_norm <- function(k, sigma, tau) {
  s  <- sigma * sqrt(tau)
  d1 <- (-k + 0.5 * s^2) / s
  dnorm(d1) * sqrt(tau)
}

# Implied volatility by vectorised bisection (slow but cannot fail).
#   price_norm = price / (D * F). Returns NA where the price violates the
#   no-arbitrage bounds (below intrinsic value or above the upper bound).
implied_vol <- function(price_norm, k, tau, cp, lo = 1e-4, hi = 5, n_iter = 60) {
  n   <- length(price_norm)
  lo  <- rep(lo, n); hi <- rep(hi, n)
  sq  <- sqrt(tau)
  bad <- !is.finite(price_norm) |
         price_norm <= bs_norm(k, lo * sq, cp) |
         price_norm >= bs_norm(k, hi * sq, cp)
  for (j in seq_len(n_iter)) {
    mid  <- 0.5 * (lo + hi)
    high <- bs_norm(k, mid * sq, cp) > price_norm
    high[is.na(high)] <- FALSE
    hi[high]  <- mid[high]
    lo[!high] <- mid[!high]
  }
  iv <- 0.5 * (lo + hi)
  iv[bad] <- NA_real_
  iv
}


# -----------------------------------------------------------------------------
# 1.2 Load the SPX options
# -----------------------------------------------------------------------------
cat("\n================ PART 1: DATA ================\n")

S0 <- suppressMessages(
  as.numeric(read_excel(DATA_FILE, sheet = 1, range = "G3", col_names = FALSE)[[1]]))
raw <- suppressMessages(
  as.data.frame(read_excel(DATA_FILE, sheet = 1, skip = 5, guess_max = 10000)))

opt <- data.frame(
  exdate = as.Date(raw$exdate),
  tau    = as.numeric(as.Date(raw$exdate) - as.Date(raw$date)) / 365,
  K      = raw$Strike,
  cp     = raw$cp_flag,
  bid    = raw$best_bid,
  ask    = raw$best_offer,
  volume = raw$volume,
  oi     = raw$open_interest,
  stringsAsFactors = FALSE)
opt$mid <- 0.5 * (opt$bid + opt$ask)
cat(sprintf("S0 = %.2f, %d quotes, %d maturities (%.2f to %.2f years)\n",
            S0, nrow(opt), length(unique(opt$tau)), min(opt$tau), max(opt$tau)))

# -----------------------------------------------------------------------------
# 1.3 Dividend yield and discount curve (Kokholm's note)
#
#   Choose n call/put pairs on each side of ATM for every maturity and minimise
#     sum_i sum_j [ P(T_i,K_j) - ( C(T_i,K_j) + K_j e^{-r_i T_i} - S0 e^{-q T_i} ) ]^2
#   over ONE dividend yield q and one spot rate r_i per maturity.
# -----------------------------------------------------------------------------
N_PAIRS <- 5    # pairs on each side of ATM

calls <- opt[opt$cp == "C", c("tau", "K", "mid", "bid")]
puts  <- opt[opt$cp == "P", c("tau", "K", "mid", "bid")]
pairs <- merge(calls, puts, by = c("tau", "K"), suffixes = c(".c", ".p"))
pairs <- pairs[pairs$bid.c > 0 & pairs$bid.p > 0, ]

pcp <- do.call(rbind, lapply(split(pairs, pairs$tau), function(x) {
  below <- x[x$K <  S0, ]; below <- below[order(-below$K), ][seq_len(N_PAIRS), ]
  above <- x[x$K >= S0, ]; above <- above[order(above$K), ][seq_len(N_PAIRS), ]
  rbind(below, above)
}))
taus <- sort(unique(pcp$tau))
mat  <- match(pcp$tau, taus)

pcp_objective <- function(par) {          # par = (q, r_1, ..., r_m)
  q <- par[1]; r <- par[-1][mat]
  sum((pcp$mid.p - (pcp$mid.c + pcp$K * exp(-r * pcp$tau) - S0 * exp(-q * pcp$tau)))^2)
}
pcp_fit <- optim(c(0.02, rep(0.02, length(taus))), pcp_objective, method = "BFGS",
                 control = list(reltol = 1e-14, maxit = 2000))
q_div <- pcp_fit$par[1]
curve <- data.frame(tau = taus, r = pcp_fit$par[-1])
curve$D   <- exp(-curve$r * curve$tau)
curve$Fwd <- S0 * exp((curve$r - q_div) * curve$tau)
curve$exdate <- sort(unique(opt$exdate))
pcp$resid <- pcp$mid.p - (pcp$mid.c + pcp$K * exp(-curve$r[mat] * pcp$tau) -
                            S0 * exp(-q_div * pcp$tau))
curve$max_abs_pcp_resid <- as.numeric(tapply(abs(pcp$resid), pcp$tau, max))

cat(sprintf("Implied dividend yield q = %.4f\n", q_div))
print(format(curve[, c("exdate", "tau", "r", "D", "Fwd", "max_abs_pcp_resid")], digits = 5),
      row.names = FALSE)
write.csv(curve, file.path(OUT_DIR, "discount_curve.csv"), row.names = FALSE)

i <- match(opt$tau, curve$tau)
opt$r <- curve$r[i]; opt$D <- curve$D[i]; opt$Fwd <- curve$Fwd[i]
opt$k <- log(opt$K / opt$Fwd)

# -----------------------------------------------------------------------------
# 1.4 Filters
#   (i)   bid > 0
#   (ii)  out-of-the-money only: puts with K < F, calls with K >= F
#   (iii) mid price at least MIN_MID (tick-size noise dominates below that)
#   (iv)  relative bid-ask spread at most MAX_REL_SPREAD
#   (v)   implied volatility exists
# -----------------------------------------------------------------------------
MIN_MID        <- 0.50
MAX_REL_SPREAD <- 0.50

n_log <- c(raw = nrow(opt))
opt <- opt[opt$bid > 0, ];                                       n_log["bid > 0"] <- nrow(opt)
opt <- opt[(opt$cp == "P" & opt$K < opt$Fwd) |
           (opt$cp == "C" & opt$K >= opt$Fwd), ];                n_log["OTM only"] <- nrow(opt)
opt <- opt[opt$mid >= MIN_MID, ];                                n_log["mid >= min"] <- nrow(opt)
opt <- opt[(opt$ask - opt$bid) / opt$mid <= MAX_REL_SPREAD, ];   n_log["spread"] <- nrow(opt)

opt$price_norm <- opt$mid / (opt$D * opt$Fwd)
opt$iv         <- implied_vol(opt$price_norm, opt$k, opt$tau, opt$cp)
opt <- opt[!is.na(opt$iv), ];                                    n_log["IV exists"] <- nrow(opt)

# -----------------------------------------------------------------------------
# 1.5 Static-arbitrage checks (Carr and Madan, 2005)
#
#   All OTM quotes are converted to (normalised) call prices c(K) with put-call
#   parity. For each maturity, with strikes sorted, absence of arbitrage needs
#     (a) call spreads:   -1/F <= dc/dK <= 0     (monotone, slope bounded)
#     (b) butterflies:    dc/dK increasing in K  (convexity)
#   and across maturities
#     (c) calendar:       total variance w = iv^2 * tau non-decreasing in tau
#                         at fixed log-forward-moneyness k.
#
#   The conditions are checked twice:
#     * at MID prices: violations here are reported but not removed, because a
#       mid price is not tradable and small violations are tick-size noise;
#     * at TRADABLE prices (buy at the ask, sell at the bid): a violation here
#       is a real arbitrage. Such quotes are removed, worst offender first.
# -----------------------------------------------------------------------------
opt$call_norm <- ifelse(opt$cp == "C", opt$price_norm, opt$price_norm + 1 - exp(opt$k))
opt$half_norm <- 0.5 * (opt$ask - opt$bid) / (opt$D * opt$Fwd)   # half spread
opt <- opt[order(opt$tau, opt$K), ]

# Size of the violation attributed to each quote of ONE maturity (sorted by K).
#   tradable = FALSE: mid prices.   tradable = TRUE: buy at ask, sell at bid.
strike_violation <- function(x, tradable) {
  n <- nrow(x); v <- numeric(n)
  if (n < 3) return(v)
  h    <- if (tradable) x$half_norm else 0
  buy  <- x$call_norm + h                 # price paid
  sell <- x$call_norm - h                 # price received
  dK   <- diff(x$K)
  # (a) call spread: buy low strike, sell high strike must cost >= 0 ...
  v[-1] <- v[-1] + pmax(sell[-1] - buy[-n], 0)
  #     ... and at most dK/F: sell low strike, buy high strike, receive <= dK/F
  v[-1] <- v[-1] + pmax(sell[-n] - buy[-1] - dK / x$Fwd[1], 0)
  # (b) butterfly: buy the wings, sell the body, cost must be >= 0
  i   <- 2:(n - 1)
  lam <- (x$K[i + 1] - x$K[i]) / (x$K[i + 1] - x$K[i - 1])
  v[i] <- v[i] + pmax(sell[i] - lam * buy[i - 1] - (1 - lam) * buy[i + 1], 0)
  v
}

n_mid_violations <- sum(unlist(lapply(split(opt, opt$tau), function(x)
  strike_violation(x, tradable = FALSE) > 1e-12)))

n_removed_strike <- 0
opt <- do.call(rbind, lapply(split(opt, opt$tau), function(x) {
  repeat {
    v <- strike_violation(x, tradable = TRUE)
    if (max(v) <= 1e-12) break
    x <- x[-which.max(v), ]
    n_removed_strike <<- n_removed_strike + 1
  }
  x
}))
n_log["call spread / butterfly"] <- nrow(opt)

# calendar check: compare each maturity with the previous one at the same k
opt$w <- opt$iv^2 * opt$tau
opt$calendar_violation <- FALSE
tau_list <- sort(unique(opt$tau))
for (j in seq_along(tau_list)[-1]) {
  cur  <- opt$tau == tau_list[j]
  prev <- opt[opt$tau == tau_list[j - 1], ]
  w_prev <- approx(prev$k, prev$w, xout = opt$k[cur], rule = 1)$y   # NA outside range
  opt$calendar_violation[cur] <- !is.na(w_prev) & opt$w[cur] < w_prev
}
n_calendar <- sum(opt$calendar_violation)
opt <- opt[!opt$calendar_violation, ];                           n_log["calendar"] <- nrow(opt)

opt$vega_norm <- bs_vega_norm(opt$k, opt$iv, opt$tau)
rownames(opt) <- NULL

cat("\nQuotes remaining after each filter:\n")
print(data.frame(step = names(n_log), quotes = as.integer(n_log)), row.names = FALSE)
cat(sprintf(paste0("Arbitrage: %d quotes violate call-spread/butterfly conditions at mid prices,\n",
                   "           %d of them outside the bid-ask spread (removed); %d calendar violations\n"),
            n_mid_violations, n_removed_strike, n_calendar))
write.csv(data.frame(step = names(n_log), quotes = as.integer(n_log)),
          file.path(OUT_DIR, "filter_log.csv"), row.names = FALSE)

# -----------------------------------------------------------------------------
# 1.6 Implied volatility surface and its features
# -----------------------------------------------------------------------------
opt$mat_label <- factor(sprintf("%s (T=%.2f)", format(opt$exdate, "%b %Y"), opt$tau),
                        levels = unique(sprintf("%s (T=%.2f)", format(opt$exdate, "%b %Y"), opt$tau)))

p_surface <- ggplot(opt, aes(k, 100 * iv, colour = tau, group = tau)) +
  geom_line() + geom_point(size = 0.6) +
  scale_colour_viridis_c(name = "Maturity (years)", trans = "sqrt") +
  labs(x = "Log-forward-moneyness  k = log(K/F)", y = "Implied volatility (%)",
       title = "SPX implied volatility smiles, 13 November 2019")
save_fig(p_surface, "fig01_iv_smiles")

# Features per maturity, read off the smile by linear interpolation:
#   ATM level  IV(0),
#   ATM skew   [IV(h) - IV(-h)] / (2h)            (central difference),
#   curvature  [IV(h) - 2 IV(0) + IV(-h)] / h^2,
# with h = SKEW_H. The same definition is applied to the models in PART 7.
SKEW_H <- 0.02
features <- do.call(rbind, lapply(split(opt, opt$tau), function(x) {
  iv <- approx(x$k, x$iv, xout = c(-SKEW_H, 0, SKEW_H))$y
  data.frame(exdate = x$exdate[1], tau = x$tau[1], n_quotes = nrow(x),
             k_min = min(x$k), k_max = max(x$k),
             atm_iv = iv[2], atm_skew = (iv[3] - iv[1]) / (2 * SKEW_H),
             atm_curv = (iv[3] - 2 * iv[2] + iv[1]) / SKEW_H^2)
}))
rownames(features) <- NULL
cat("\nSurface features per maturity:\n")
print(format(features, digits = 3), row.names = FALSE)
write.csv(features, file.path(OUT_DIR, "surface_features.csv"), row.names = FALSE)

p_feat <- ggplot(features, aes(tau, atm_skew)) + geom_line() + geom_point() +
  labs(x = "Maturity (years)", y = "ATM skew  dIV/dk at k = 0",
       title = "Term structure of the ATM skew")
save_fig(p_feat, "fig02_atm_skew_term_structure", 6, 4)

p_atm <- ggplot(features, aes(tau, 100 * atm_iv)) + geom_line() + geom_point() +
  labs(x = "Maturity (years)", y = "ATM implied volatility (%)",
       title = "Term structure of ATM implied volatility")
save_fig(p_atm, "fig03_atm_term_structure", 6, 4)

# -----------------------------------------------------------------------------
# 1.7 Train / test split
#
#   Two kinds of out-of-sample quotes, so that both dimensions are tested:
#     "test_maturity": two ENTIRE maturities are held out. The models never see
#                      them; this tests the term-structure the model implies.
#     "test_strike"  : 20% of the quotes in the remaining maturities, drawn at
#                      random within each maturity; tests the smile shape.
#   The shortest and the longest maturity always stay in the training set,
#   because the short end is where the research question lives and we do not
#   want to extrapolate in maturity.
# -----------------------------------------------------------------------------
HOLDOUT_EXDATES <- as.Date(c("2020-01-17", "2020-09-18"))
TEST_FRACTION   <- 0.20

opt$sample <- "train"
opt$sample[opt$exdate %in% HOLDOUT_EXDATES] <- "test_maturity"
for (t in unique(opt$tau[opt$sample == "train"])) {
  idx <- which(opt$tau == t)
  opt$sample[sample(idx, round(TEST_FRACTION * length(idx)))] <- "test_strike"
}
train <- opt[opt$sample == "train", ]
cat("\nSample sizes:\n"); print(table(opt$sample))
print(table(format(opt$exdate), opt$sample))
saveRDS(opt, file.path(OUT_DIR, "options_clean.rds"))
write.csv(opt, file.path(OUT_DIR, "options_clean.csv"), row.names = FALSE)


# #############################################################################
# PART 2  PRICING AND CALIBRATION TOOLS (shared by all three specifications)
#
#   2.1 Gauss-Legendre quadrature
#   2.2 The Riccati solver ("the machine")
#   2.3 Carr-Madan pricer
#   2.4 Calibration engine
#   2.5 Evaluation helpers
# #############################################################################

# -----------------------------------------------------------------------------
# 2.1 Gauss-Legendre quadrature (Golub-Welsch, no extra package needed)
# -----------------------------------------------------------------------------

# Nodes and weights on [-1, 1]
gauss_legendre <- function(n) {
  i <- seq_len(n - 1)
  b <- i / sqrt(4 * i^2 - 1)
  J <- matrix(0, n, n)
  J[cbind(i, i + 1)] <- b
  J[cbind(i + 1, i)] <- b
  e <- eigen(J, symmetric = TRUE)
  o <- order(e$values)
  list(x = e$values[o], w = 2 * e$vectors[1, o]^2)
}

GL16 <- gauss_legendre(16)

# Composite rule: n_panels panels of equal width on [0, upper], 16 nodes each
composite_gl <- function(upper, n_panels) {
  h    <- upper / n_panels
  left <- (seq_len(n_panels) - 1) * h
  list(v = as.vector(outer(0.5 * h * (GL16$x + 1), left, "+")),
       w = rep(0.5 * h * GL16$w, times = n_panels))
}

# -----------------------------------------------------------------------------
# 2.2 The machine: closed-form solution of the Riccati equation
#
#       B'(tau) = a + b B + c B^2,      B(0) = 0
#
#    with constant complex coefficients. Returns B(tau) and int_0^tau B(s) ds,
#    plus the intermediate quantities (d, g, B_minus, exp(-d tau)) that the
#    SVJJ model needs. Written in the "little Heston trap" form (exp(-d tau)
#    decays), so the complex logarithm never crosses its branch cut.
#
#    Heston / SVJ / SVJJ:  a = -(u^2 + iu)/2,  b = rho*eta*iu - kappa,  c = eta^2/2
# -----------------------------------------------------------------------------
riccati <- function(a, b, c, tau) {
  d   <- sqrt(b^2 - 4 * a * c)          # principal root, Re(d) >= 0
  Bm  <- (-b - d) / (2 * c)             # B_minus (root the solution tends to)
  Bp  <- (-b + d) / (2 * c)             # B_plus
  g   <- Bm / Bp
  e   <- exp(-d * tau)
  B   <- Bm * (1 - e) / (1 - g * e)
  # int_0^tau B ds = B_minus*tau - (1/c) * log((1 - g e^{-d tau}) / (1 - g))
  intB <- Bm * tau - log((1 - g * e) / (1 - g)) / c
  list(B = B, intB = intB, d = d, g = g, Bm = Bm, e = e)
}

# -----------------------------------------------------------------------------
# 2.3 Carr-Madan pricer
#
#    C(k) / (D F) = exp(-alpha k)/pi * int_0^inf Re[ exp(-ivk) psi(v) ] dv,
#    psi(v) = phi(v - (alpha+1) i) / (alpha^2 + alpha - v^2 + i (2 alpha + 1) v)
#
#    The integral is computed by composite Gauss-Legendre quadrature. The
#    upper limit is chosen adaptively from the decay of |phi|, because short
#    maturities need a much longer integration range than long ones.
# -----------------------------------------------------------------------------
CM_ALPHA <- 1.25     # damping parameter
CM_TOL   <- 1e-9     # truncation tolerance (in units of the forward)
CM_PANEL <- 10       # panel width in v (16 nodes per panel)

# Normalised OTM option prices for ONE maturity.
#   cf : function(u, tau, p) -> characteristic function of log(S_T/F_T)
#   Returns NULL if the parameter set is not admissible for pricing
#   (moment E[S^(alpha+1)] infinite, or a numerical failure).
cm_prices <- function(cf, p, tau, k, cp, alpha = CM_ALPHA) {
  # moment condition: phi(-(alpha+1) i) = E[(S_T/F)^(alpha+1)] must be finite
  m <- cf(complex(real = 0, imaginary = -(alpha + 1)), tau, p)
  if (!is.finite(Re(m)) || !is.finite(Im(m)) || Re(m) <= 0 || Re(m) > 1e8) return(NULL)

  # adaptive upper limit: first point where the tail bound |phi|/v is negligible
  cand <- 25 * 2^(0:8)                                   # 25, 50, ..., 6400
  mag  <- Mod(cf(complex(real = cand, imaginary = -(alpha + 1)), tau, p)) / cand
  if (any(!is.finite(mag))) return(NULL)
  ok    <- which(mag < CM_TOL)
  upper <- if (length(ok)) cand[ok[1]] else max(cand)

  q   <- composite_gl(upper, ceiling(upper / CM_PANEL))
  u   <- complex(real = q$v, imaginary = -(alpha + 1))
  psi <- cf(u, tau, p) / (alpha^2 + alpha - q$v^2 + 1i * (2 * alpha + 1) * q$v)
  if (any(!is.finite(Re(psi))) || any(!is.finite(Im(psi)))) return(NULL)

  # sum over nodes for all strikes at once: Re[ sum_j w_j psi_j exp(-i v_j k) ]
  integral <- Re(colSums((q$w * psi) * exp(-1i * outer(q$v, k))))
  call <- exp(-alpha * k) / pi * integral
  ifelse(cp == "C", call, call - 1 + exp(k))             # put-call parity
}

# Normalised prices for a whole data set (data frame with tau, k, cp).
# Returns NULL if any maturity fails.
price_surface <- function(cf, p, dat) {
  out <- numeric(nrow(dat))
  for (idx in split(seq_len(nrow(dat)), dat$tau)) {
    pr <- cm_prices(cf, p, dat$tau[idx[1]], dat$k[idx], dat$cp[idx])
    if (is.null(pr)) return(NULL)
    out[idx] <- pr
  }
  out
}

# -----------------------------------------------------------------------------
# 2.4 Calibration engine
#
#    Objective: sum of squared VEGA-WEIGHTED price errors,
#        e_i = (P_model,i - P_market,i) / vega_market,i
#    To first order e_i equals the implied-volatility error, so we minimise
#    (approximately) the IV RMSE without inverting Black-Scholes inside the
#    optimiser. The exact IV errors are computed afterwards for reporting.
#
#    Optimiser: Levenberg-Marquardt with box constraints (minpack.lm::nls.lm),
#    started from several starting points; the best local optimum is kept.
#
#    A model is described by a list:
#      name, cf, par_names, lower, upper, starts (list of start vectors)
# -----------------------------------------------------------------------------
PENALTY <- 1    # residual (in vol units) returned for inadmissible parameters

calib_residuals <- function(p, model, dat) {
  pr <- price_surface(model$cf, p, dat)
  if (is.null(pr)) return(rep(PENALTY, nrow(dat)))
  r <- (pr - dat$price_norm) / dat$vega_norm
  r[!is.finite(r)] <- PENALTY
  pmax(pmin(r, PENALTY), -PENALTY)
}

calibrate <- function(model, dat, maxiter = 150, verbose = TRUE) {
  counter <- new.env(); counter$n <- 0
  fn <- function(p) { counter$n <- counter$n + 1; calib_residuals(p, model, dat) }

  t0   <- proc.time()[["elapsed"]]
  runs <- list()
  for (s in seq_along(model$starts)) {
    start <- pmin(pmax(model$starts[[s]], model$lower), model$upper)
    t1    <- proc.time()[["elapsed"]]
    n1    <- counter$n
    fit   <- tryCatch(
      nls.lm(par = start, lower = model$lower, upper = model$upper, fn = fn,
             control = nls.lm.control(maxiter = maxiter, ftol = 1e-10, ptol = 1e-10)),
      error = function(e) NULL)
    if (is.null(fit)) next
    runs[[length(runs) + 1]] <- list(
      start = start, par = fit$par, sse = fit$deviance,
      rmse  = sqrt(fit$deviance / nrow(dat)),
      time  = proc.time()[["elapsed"]] - t1, n_eval = counter$n - n1,
      iter  = fit$niter)
    if (verbose)
      cat(sprintf("  [%s] start %d/%d: approx. IV-RMSE = %.4f vol pts  (%d evals, %.1fs)\n",
                  model$name, s, length(model$starts),
                  100 * runs[[length(runs)]]$rmse, counter$n - n1,
                  runs[[length(runs)]]$time))
  }
  best <- runs[[which.min(vapply(runs, function(r) r$sse, 0))]]
  par  <- setNames(best$par, model$par_names)
  list(name = model$name, par = par, n_par = length(par),
       sse = best$sse, runs = runs,
       time_total = proc.time()[["elapsed"]] - t0, n_eval_total = counter$n,
       time_best = best$time, n_eval_best = best$n_eval)
}

# -----------------------------------------------------------------------------
# 2.5 Evaluation
# -----------------------------------------------------------------------------

# Adds model price, model implied vol and IV error (in vol points) to dat
evaluate_model <- function(model, p, dat) {
  pr <- price_surface(model$cf, p, dat)
  if (is.null(pr)) stop("pricing failed at the supplied parameters")
  out <- dat
  out$model      <- model$name
  out$model_norm <- pr
  out$model_px   <- pr * dat$D * dat$Fwd
  out$model_iv   <- implied_vol(pr, dat$k, dat$tau, dat$cp)
  out$iv_err     <- 100 * (out$model_iv - out$iv)          # vol points
  out
}

rmse <- function(x) sqrt(mean(x^2, na.rm = TRUE))

# Seconds per evaluation of the full price surface (for the speed comparison)
time_surface <- function(model, p, dat, reps = 20) {
  t <- system.time(for (i in seq_len(reps)) price_surface(model$cf, p, dat))[["elapsed"]]
  t / reps
}

# Small helper for the unit checks printed by the model scripts
check <- function(label, ok) {
  cat(sprintf("  %-62s %s\n", label, if (isTRUE(ok)) "PASS" else "FAIL"))
  invisible(isTRUE(ok))
}

# Classical RK4 solution of the Riccati system, used only to verify the
# closed forms:  B' = a + b B + c B^2,  A' = extra(B)   (complex valued)
riccati_rk4 <- function(a, b, c, tau, extra = function(B) 0 * B, n = 4000) {
  h <- tau / n; B <- 0 + 0i; A <- 0 + 0i
  f <- function(B) a + b * B + c * B^2
  for (i in seq_len(n)) {
    k1 <- f(B); k2 <- f(B + 0.5 * h * k1); k3 <- f(B + 0.5 * h * k2); k4 <- f(B + h * k3)
    Bn <- B + h / 6 * (k1 + 2 * k2 + 2 * k3 + k4)
    # Simpson for A' = extra(B), using the midpoint B from the RK stages
    Bmid <- B + 0.5 * h * (k1 + k2) / 2
    A <- A + h / 6 * (extra(B) + 4 * extra(Bmid) + extra(Bn))
    B <- Bn
  }
  list(A = A, B = B)
}




# #############################################################################
# PART 3  THE DUFFIE-PAN-SINGLETON MODEL (SVJJ) AND ITS RESTRICTIONS
#
#   General model (SVJJ, Duffie, Pan and Singleton 2000):
#     dX = -(lambda*mubar + V/2) dt + sqrt(V) dW1 + Z^s dN,     X = log(S/F)
#     dV = kappa (theta - V) dt + eta sqrt(V) dW2 + Z^v dN,     dW1 dW2 = rho dt
#     N     Poisson with intensity lambda (one counter: the jumps are simultaneous)
#     Z^v ~ Exp(mean mu_v),   Z^s | Z^v ~ N(mu_s + rho_J Z^v, sigma_s^2)
#     mubar = E[exp(Z^s)] - 1 = exp(mu_s + sigma_s^2/2) / (1 - rho_J mu_v) - 1
#
#   Restrictions used in the report:
#     SVJ    (Bates 1996):  mu_v = 0, rho_J = 0     (jumps in price only)
#     Heston (1993):        lambda = 0              (no jumps)
#
#   ONE characteristic function is derived and coded: the general SVJJ one.
#   SVJ and Heston are obtained by fixing parameters, exactly as in the report.
#
#   Full parameter vector (always in this order):
#     (kappa, theta, eta, rho, v0, lambda, mu_s, sigma_s, mu_v, rho_J)
# #############################################################################
cat("\n================ PART 3: DPS MODEL ================\n")

DPS_PAR <- c("kappa", "theta", "eta", "rho", "v0", "lambda", "mu_s", "sigma_s",
             "mu_v", "rho_J")

# ---- 3.1 the transform for the general case ----------------------------------
#   phi(u) = E[exp(iu X_T)] = exp(A(tau) + B(tau) v0), where
#     B solves the Heston Riccati equation  B' = a + bB + cB^2,  B(0) = 0,
#       a = -(u^2 + iu)/2,  b = rho*eta*iu - kappa,  c = eta^2/2,
#     A' = kappa*theta*B - lambda*iu*mubar + lambda*( theta_J(u, B) - 1 ),
#       theta_J(u, B) = E[exp(iu Z^s + B Z^v)]
#                     = exp(iu mu_s - sigma_s^2 u^2/2) / (1 - mu_v (B + iu rho_J)).
#   Integrating A' in closed form:
#     A = kappa*theta*int B - lambda*tau*(1 + iu*mubar)
#         + lambda * exp(iu mu_s - sigma_s^2 u^2/2) * I(tau),
#     I(tau) = int_0^tau ds / (c0 - mu_v B(s)),      c0 = 1 - iu rho_J mu_v
#            = tau/m + mu_v B_- (1-g) / (d m n) * log( (m + n e^{-d tau}) / (m + n) ),
#     m = c0 - mu_v B_-,   n = mu_v B_- - c0 g.
#   With mu_v = 0: I = tau and the SVJ transform follows.
#   With lambda = 0: the jump terms vanish and the Heston transform follows.
dps_I <- function(R, c0, mu_v, tau) {
  m <- c0 - mu_v * R$Bm
  n <- mu_v * R$Bm - c0 * R$g
  I <- tau / m + mu_v * R$Bm * (1 - R$g) / (R$d * m * n) * log((m + n * R$e) / (m + n))
  # removable 0/0 when n -> 0 (e.g. at u = -i): use the limit
  small <- Mod(n) < 1e-10 * Mod(m)
  if (any(small))
    I[small] <- (tau / m + mu_v * R$Bm * (1 - R$g) * (R$e - 1) / (R$d * m^2))[small]
  I
}

cf_dps <- function(u, tau, p) {
  kappa <- p[1]; theta <- p[2]; eta <- p[3]; rho <- p[4]; v0 <- p[5]
  lambda <- p[6]; mu_s <- p[7]; sigma_s <- p[8]; mu_v <- p[9]; rho_J <- p[10]
  R <- riccati(a = -0.5 * (u^2 + 1i * u), b = rho * eta * 1i * u - kappa,
               c = 0.5 * eta^2, tau = tau)
  A <- kappa * theta * R$intB
  if (lambda > 0) {
    mubar <- exp(mu_s + 0.5 * sigma_s^2) / (1 - rho_J * mu_v) - 1
    I     <- if (mu_v > 0) dps_I(R, 1 - 1i * u * rho_J * mu_v, mu_v, tau) else tau
    A     <- A - lambda * tau * (1 + 1i * u * mubar) +
             lambda * exp(1i * u * mu_s - 0.5 * sigma_s^2 * u^2) * I
  }
  exp(A + R$B * v0)
}

# ---- 3.2 the three specifications as restrictions ----------------------------
# A specification = the free parameters + fixed values for the rest. Its
# characteristic function is cf_dps evaluated at the completed vector.
DPS_FIXED <- c(kappa = NA, theta = NA, eta = NA, rho = NA, v0 = NA,
               lambda = 0, mu_s = 0, sigma_s = 0.1, mu_v = 0, rho_J = 0)

dps_spec <- function(name, free, lower, upper, starts = list()) {
  full <- DPS_FIXED
  list(name = name, par_names = free, lower = lower, upper = upper, starts = starts,
       full = function(p) { f <- full; f[free] <- p; unname(f) },
       cf   = function(u, tau, p) { f <- full; f[free] <- p; cf_dps(u, tau, unname(f)) })
}

SV_LOWER  <- c(0.01, 1e-4, 0.01, -0.999, 1e-4);  SV_UPPER  <- c(20, 1, 5, 0.5, 1)
PJ_LOWER  <- c(0, -1.0, 1e-3);                   PJ_UPPER  <- c(10, 0.5, 1)    # lambda, mu_s, sigma_s
VJ_LOWER  <- c(0, -10);                          VJ_UPPER  <- c(0.5, 0.4)      # mu_v, rho_J

heston <- dps_spec("Heston", DPS_PAR[1:5],  SV_LOWER, SV_UPPER)
svj    <- dps_spec("SVJ",    DPS_PAR[1:8],  c(SV_LOWER, PJ_LOWER), c(SV_UPPER, PJ_UPPER))
svjj   <- dps_spec("SVJJ",   DPS_PAR,       c(SV_LOWER, PJ_LOWER, VJ_LOWER),
                                            c(SV_UPPER, PJ_UPPER, VJ_UPPER))

# ---- 3.3 unit checks ---------------------------------------------------------
cat("Checks:\n")
local({
  p   <- c(2, 0.04, 0.5, -0.7, 0.03, 0.6, -0.1, 0.12, 0.05, -0.4); tau <- 2.1
  u   <- c(0.3, 2, 15, 60) + 0i
  check("phi(0) = 1", abs(cf_dps(0i, tau, p) - 1) < 1e-12)
  check("martingale: phi(-i) = 1 (removable 0/0 handled)", abs(cf_dps(-1i, tau, p) - 1) < 1e-12)

  # general closed form against a numerical solution of the ODE system,
  # for real u and for the complex u used by Carr-Madan
  for (shift in c(0, -(CM_ALPHA + 1))) {
    uc  <- complex(real = c(0.3, 2, 15, 60), imaginary = shift)
    num <- sapply(uc, function(ui) {
      mubar <- exp(p[7] + 0.5 * p[8]^2) / (1 - p[10] * p[9]) - 1
      extra <- function(B) p[1] * p[2] * B - p[6] * 1i * ui * mubar +
        p[6] * (exp(1i * ui * p[7] - 0.5 * p[8]^2 * ui^2) /
                  (1 - p[9] * (B + 1i * ui * p[10])) - 1)
      s <- riccati_rk4(-0.5 * (ui^2 + 1i * ui), p[4] * p[3] * 1i * ui - p[1], 0.5 * p[3]^2,
                       tau, extra = extra)
      exp(s$A + s$B * p[5]) })
    check(sprintf("closed form = numerical ODE solution, Im(u) = %.2f", shift),
          max(Mod(num - cf_dps(uc, tau, p)) / Mod(num)) < 1e-7)
  }

  # restrictions: mu_v -> 0 continuously approaches SVJ, lambda -> 0 approaches Heston
  p_svj <- p; p_svj[9:10] <- 0
  p_eps <- p; p_eps[9] <- 1e-9
  check("SVJJ with mu_v -> 0 converges to SVJ",
        max(Mod(cf_dps(u, tau, p_eps) - cf_dps(u, tau, p_svj))) < 1e-7)
  p_h <- p; p_h[6] <- 0; p_eps <- p; p_eps[6] <- 1e-10
  check("SVJJ with lambda -> 0 converges to Heston",
        max(Mod(cf_dps(u, tau, p_eps) - cf_dps(u, tau, p_h))) < 1e-8)

  # Black-Scholes limit: lambda = 0, eta -> 0, v0 = theta
  k <- seq(-0.4, 0.2, 0.1); cp <- ifelse(k < 0, "P", "C")
  pr <- cm_prices(heston$cf, c(1, 0.04, 1e-4, 0, 0.04), 0.5, k, cp)
  check("Heston with eta -> 0 gives Black-Scholes prices",
        max(abs(pr - bs_norm(k, 0.2 * sqrt(0.5), cp))) < 1e-7)

  # Merton limit: SVJ with eta -> 0, v0 = theta. Merton's series formula.
  lam <- 0.6; mu <- -0.1; sg <- 0.12; s2 <- 0.04; t <- 0.5
  mubar  <- exp(mu + 0.5 * sg^2) - 1
  merton <- rowSums(sapply(0:60, function(n) {
    v_n <- sqrt(s2 * t + n * sg^2)
    m_n <- -lam * mubar * t + n * (mu + 0.5 * sg^2)
    dpois(n, lam * t) * exp(m_n) * bs_norm(k - m_n, v_n, "C") }))
  merton <- ifelse(cp == "C", merton, merton - 1 + exp(k))
  pr <- cm_prices(svj$cf, c(1, s2, 1e-4, 0, s2, lam, mu, sg), t, k, cp)
  check("SVJ with eta -> 0 gives Merton jump-diffusion prices", max(abs(pr - merton)) < 1e-7)

  uu <- seq(0, 200, by = 0.05) + 0i
  ph <- cf_dps(uu, tau, c(1, 0.05, 1.5, -0.9, 0.02, 1, -0.1, 0.1, 0.2, -1))
  check("phi continuous in u at T = 2.1 (no branch-cut jumps)", max(Mod(diff(ph))) < 0.05)
})


# #############################################################################
# PART 4  NUMERICAL ILLUSTRATIONS (illustrative parameters, no data used)
#
#   4.1 Why the "little Heston trap" form of the transform is needed
#   4.2 Accuracy of the Carr-Madan pricer: damping alpha and truncation
#   4.3 Monte Carlo validation of the transform, for all three specifications
#   4.4 What each extra piece does to the smile and to the skew term structure
# #############################################################################
cat("\n================ PART 4: NUMERICAL ILLUSTRATIONS ================\n")

# One illustrative SVJJ parameter set, of the size found for SPX in the
# literature. Feller condition 2*kappa*theta/eta^2 = 0.67 < 1 (violated, as it
# usually is for calibrated parameters), which also tests the MC scheme.
P_ILL <- c(kappa = 3, theta = 0.04, eta = 0.6, rho = -0.8, v0 = 0.02,
           lambda = 0.8, mu_s = -0.05, sigma_s = 0.08, mu_v = 0.05, rho_J = -0.5)
P_ILL_SVJ    <- P_ILL; P_ILL_SVJ[c("mu_v", "rho_J")] <- 0
P_ILL_HESTON <- P_ILL; P_ILL_HESTON["lambda"] <- 0
ILL_SETS <- list(Heston = P_ILL_HESTON, SVJ = P_ILL_SVJ, SVJJ = P_ILL)

spec_colours <- c(Heston = "#1b9e77", SVJ = "#d95f02", SVJJ = "#7570b3")

# Temporarily change the pricer's quadrature settings
with_cm <- function(tol, panel, expr) {
  old <- c(CM_TOL, CM_PANEL)
  CM_TOL <<- tol; CM_PANEL <<- panel
  on.exit({ CM_TOL <<- old[1]; CM_PANEL <<- old[2] })
  expr
}
# log-moneyness grid that scales with maturity: k = z * 0.2 * sqrt(tau)
k_grid <- function(tau, z = seq(-4, 1.5, by = 0.25)) z * 0.2 * sqrt(tau)

# ---- 4.1 the branch cut ------------------------------------------------------
# Heston's original formula uses g = B_+/B_- and exp(+d tau). The complex log in
# the A-term then crosses its branch cut for long maturities and large eta, and
# phi jumps. The formulation in riccati() (Albrecher et al., 2007) does not.
local({
  p <- c(kappa = 1, theta = 0.05, eta = 1.5, rho = -0.9, v0 = 0.02); tau <- 5
  u <- seq(0.01, 30, by = 0.01) + 0i
  a <- -0.5 * (u^2 + 1i * u); b <- p[["rho"]] * p[["eta"]] * 1i * u - p[["kappa"]]
  c <- 0.5 * p[["eta"]]^2
  d <- sqrt(b^2 - 4 * a * c); Bp <- (-b + d) / (2 * c); G <- (-b + d) / (-b - d)
  e <- exp(d * tau)
  orig <- exp(p[["kappa"]] * p[["theta"]] * (Bp * tau - log((1 - G * e) / (1 - G)) / c) +
              Bp * (1 - e) / (1 - G * e) * p[["v0"]])
  trap <- heston$cf(u, tau, unname(p))
  df <- rbind(data.frame(u = Re(u), re = Re(orig), form = "Original Heston (1993) form"),
              data.frame(u = Re(u), re = Re(trap), form = "Form used here (Albrecher et al., 2007)"))
  g <- ggplot(df, aes(u, re, colour = form)) + geom_line() +
    scale_colour_manual(values = c("#b2182b", "black"), name = NULL) +
    labs(x = "u", y = expression(Re~phi(u)),
         title = "Heston characteristic function, T = 5, eta = 1.5: the branch-cut jump") +
    theme(legend.position = "bottom")
  save_fig(g, "fig_n1_branch_cut", 7.5, 4)
  cat(sprintf("4.1 Largest jump in phi between grid points: original %.3f, used here %.5f\n",
              max(Mod(diff(orig))), max(Mod(diff(trap)))))
})

# ---- 4.2 pricer accuracy -----------------------------------------------------
# Reference prices: very fine quadrature and very long integration range.
# Errors are reported in implied-vol points, the unit used in the calibration.
pricer_accuracy <- local({
  taus <- c(0.1, 1, 2.1)
  ref <- lapply(taus, function(t) {
    k <- k_grid(t); cp <- ifelse(k < 0, "P", "C")
    pr <- with_cm(1e-15, 2, cm_prices(svjj$cf, P_ILL, t, k, cp))
    list(k = k, cp = cp, iv = implied_vol(pr, k, t, cp))
  })
  # the reference does not depend on alpha: check it against alpha = 0.75
  ref2 <- sapply(seq_along(taus), function(j) {
    r <- ref[[j]]; pr <- with_cm(1e-15, 2, cm_prices(svjj$cf, P_ILL, taus[j], r$k, r$cp, alpha = 0.75))
    max(abs(implied_vol(pr, r$k, taus[j], r$cp) - r$iv)) })
  cat(sprintf("4.2 Reference prices with alpha = 1.25 vs 0.75: max IV difference %.1e vol pts\n",
              100 * max(ref2)))

  grid <- expand.grid(alpha = c(0.25, 0.5, 0.75, 1, 1.25, 1.5, 2, 3, 5),
                      tol = c(1e-5, 1e-7, 1e-9, 1e-11), tau = taus)
  grid$max_iv_err <- NA; grid$n_nodes <- NA
  for (i in seq_len(nrow(grid))) {
    j <- match(grid$tau[i], taus); r <- ref[[j]]
    pr <- with_cm(grid$tol[i], CM_PANEL,
                  cm_prices(svjj$cf, P_ILL, grid$tau[i], r$k, r$cp, alpha = grid$alpha[i]))
    if (is.null(pr)) next
    grid$max_iv_err[i] <- 100 * max(abs(implied_vol(pr, r$k, grid$tau[i], r$cp) - r$iv), na.rm = TRUE)
  }
  grid
})
write.csv(pricer_accuracy, file.path(OUT_DIR, "table_pricer_accuracy.csv"), row.names = FALSE)
g <- ggplot(pricer_accuracy[!is.na(pricer_accuracy$max_iv_err), ],
            aes(alpha, pmax(max_iv_err, 1e-9), colour = factor(tol))) +
  geom_line() + geom_point(size = 1) + facet_wrap(~ paste("T =", tau)) +
  scale_y_log10() + scale_x_log10(breaks = c(0.25, 0.5, 1, 2, 5)) +
  geom_vline(xintercept = CM_ALPHA, linetype = 2, colour = "grey50") +
  labs(x = expression("Damping parameter "*alpha), y = "Max IV error (vol points, log scale)",
       colour = "Truncation\ntolerance",
       title = "Carr-Madan pricer: accuracy against damping and truncation (SVJJ)")
save_fig(g, "fig_n2_pricer_accuracy", 9, 4)
cat("    Max IV error (vol pts) at the settings used, alpha = 1.25, tol = 1e-9:\n")
print(pricer_accuracy[pricer_accuracy$alpha == CM_ALPHA & pricer_accuracy$tol == CM_TOL,
                      c("tau", "max_iv_err")], row.names = FALSE)

# ---- 4.3 Monte Carlo validation ----------------------------------------------
# Euler scheme with full truncation for V (Lord, Koekkoek and van Dijk, 2010)
# and EXACT simulation of the jumps in each step: given N jumps in a step,
#   sum Z^v ~ Gamma(N, scale mu_v),   sum Z^s | sum Z^v ~ N(N mu_s + rho_J sum Z^v, N sigma_s^2).
# The log-price step is an exact martingale given V at the start of the step,
# so E[S_T/F_T] = 1 holds in the simulation, not only in the limit.
# Antithetic normals; standard errors are computed over antithetic pairs.
simulate_dps <- function(p, tau, n_pairs, steps_per_year = 500) {
  kappa <- p[1]; theta <- p[2]; eta <- p[3]; rho <- p[4]; v0 <- p[5]
  lambda <- p[6]; mu_s <- p[7]; sigma_s <- p[8]; mu_v <- p[9]; rho_J <- p[10]
  n  <- 2 * n_pairs
  ns <- max(100, ceiling(steps_per_year * tau)); dt <- tau / ns
  mubar <- exp(mu_s + 0.5 * sigma_s^2) / (1 - rho_J * mu_v) - 1
  X <- numeric(n); V <- rep(v0, n)
  for (s in seq_len(ns)) {
    z1 <- rnorm(n_pairs); z2 <- rnorm(n_pairs)
    z1 <- c(z1, -z1); z2 <- c(z2, -z2)
    Vp <- pmax(V, 0)
    X  <- X - (0.5 * Vp + lambda * mubar) * dt + sqrt(Vp * dt) * z1
    V  <- V + kappa * (theta - Vp) * dt +
          eta * sqrt(Vp * dt) * (rho * z1 + sqrt(1 - rho^2) * z2)
    if (lambda > 0) {
      N <- rpois(n, lambda * dt); j <- which(N > 0)
      if (length(j)) {
        Zv <- if (mu_v > 0) rgamma(length(j), shape = N[j], scale = mu_v) else 0
        X[j] <- X[j] + rnorm(length(j), N[j] * mu_s + rho_J * Zv, sqrt(N[j]) * sigma_s)
        V[j] <- V[j] + Zv
      }
    }
  }
  X
}

mc_validation <- cached("mc_validation", local({
  set.seed(42)
  out <- list()
  for (m in names(ILL_SETS)) for (t in c(0.1, 0.5, 1)) {
    p  <- unname(ILL_SETS[[m]])
    k  <- k_grid(t, z = c(-3, -2, -1, -0.5, 0, 0.5, 1)); cp <- ifelse(k < 0, "P", "C")
    X  <- simulate_dps(p, t, n_pairs = 100000)
    h  <- length(X) / 2
    pay <- sapply(seq_along(k), function(i)
      if (cp[i] == "C") pmax(exp(X) - exp(k[i]), 0) else pmax(exp(k[i]) - exp(X), 0))
    pair <- 0.5 * (pay[1:h, , drop = FALSE] + pay[(h + 1):(2 * h), , drop = FALSE])
    mc <- colMeans(pair); se <- apply(pair, 2, sd) / sqrt(h)
    ff <- cm_prices(svjj$cf, p, t, k, cp)
    out[[length(out) + 1]] <- data.frame(
      model = m, tau = t, k = k, cp = cp, fourier = ff, mc = mc, se = se,
      z_score = (mc - ff) / se,
      iv_fourier = implied_vol(ff, k, t, cp), iv_mc = implied_vol(mc, k, t, cp),
      iv_lo = implied_vol(mc - 1.96 * se, k, t, cp), iv_hi = implied_vol(mc + 1.96 * se, k, t, cp),
      martingale = mean(exp(X)))
  }
  do.call(rbind, out)
}))
mc_validation$model <- factor(mc_validation$model, levels = names(ILL_SETS))
write.csv(mc_validation, file.path(OUT_DIR, "table_mc_validation.csv"), row.names = FALSE)
cat("4.3 Monte Carlo vs Fourier (200,000 paths per maturity):\n")
print(aggregate(cbind(max_abs_z = abs(z_score), max_iv_diff_volpts = 100 * abs(iv_mc - iv_fourier),
                      martingale_minus_1 = martingale - 1) ~ model + tau, mc_validation, max),
      digits = 3, row.names = FALSE)

g <- ggplot(mc_validation, aes(k, 100 * iv_fourier)) +
  geom_line(aes(colour = model)) +
  geom_errorbar(aes(ymin = 100 * iv_lo, ymax = 100 * iv_hi), width = 0) +
  geom_point(aes(y = 100 * iv_mc), size = 1) +
  facet_grid(model ~ paste("T =", tau), scales = "free_x") +
  scale_colour_manual(values = spec_colours, guide = "none") +
  labs(x = "Log-forward-moneyness k", y = "Implied volatility (%)",
       title = "Fourier prices (lines) against Monte Carlo with 95% intervals (points)")
save_fig(g, "fig_n3_mc_validation", 9, 6.5)

# ---- 4.4 what each extra piece does ------------------------------------------
# Start from Heston, add price jumps (SVJ), then variance jumps (SVJJ). To
# compare shapes and not levels, theta and v0 are lowered so that the expected
# annual variance from all sources stays (approximately) the same:
#   price jumps add  lambda * E[(Z^s)^2],
#   variance jumps raise the long-run mean of V by lambda * mu_v / kappa.
jump_var <- function(p) with(as.list(p),
  lambda * (sigma_s^2 + mu_s^2 + 2 * mu_s * rho_J * mu_v + 2 * rho_J^2 * mu_v^2))
matched <- lapply(ILL_SETS, function(p) {
  J <- jump_var(p); p["v0"] <- P_ILL[["v0"]] - J
  p["theta"] <- P_ILL[["theta"]] - J - p[["lambda"]] * p[["mu_v"]] / p[["kappa"]]
  p })
cat("4.4 Variance-matched parameter sets (theta, v0):\n")
print(round(sapply(matched, function(p) p[c("theta", "v0")]), 4))

smile_df <- do.call(rbind, lapply(names(matched), function(m) do.call(rbind, lapply(c(0.1, 1),
  function(t) {
    k <- k_grid(t, z = seq(-3, 1.5, by = 0.1)); cp <- ifelse(k < 0, "P", "C")
    pr <- cm_prices(svjj$cf, unname(matched[[m]]), t, k, cp)
    data.frame(model = m, tau = t, k = k, iv = implied_vol(pr, k, t, cp)) }))))
smile_df$model <- factor(smile_df$model, levels = names(matched))
g1 <- ggplot(smile_df, aes(k, 100 * iv, colour = model)) + geom_line(linewidth = 0.7) +
  facet_wrap(~ paste("T =", tau), scales = "free") +
  scale_colour_manual(values = spec_colours, name = NULL) +
  labs(x = "Log-forward-moneyness k", y = "Implied volatility (%)",
       title = "Adding price jumps, then variance jumps (variance-matched)")
save_fig(g1, "fig_n4_smiles_by_component", 9, 4)

skew_ill <- do.call(rbind, lapply(names(matched), function(m) {
  tg <- exp(seq(log(1 / 52), log(3), length.out = 40))
  data.frame(model = m, tau = tg, skew = sapply(tg, function(t) {
    pr <- cm_prices(svjj$cf, unname(matched[[m]]), t, c(-SKEW_H, SKEW_H), c("P", "C"))
    iv <- implied_vol(pr, c(-SKEW_H, SKEW_H), t, c("P", "C")); (iv[2] - iv[1]) / (2 * SKEW_H) })) }))
skew_ill$model <- factor(skew_ill$model, levels = names(matched))
g2 <- ggplot(skew_ill, aes(tau, skew, colour = model)) + geom_line(linewidth = 0.7) +
  scale_x_log10(breaks = c(0.02, 0.05, 0.1, 0.25, 0.5, 1, 2)) +
  scale_colour_manual(values = spec_colours, name = NULL) +
  labs(x = "Maturity (years, log scale)", y = "ATM skew  dIV/dk at k = 0",
       title = "ATM skew term structure by component (variance-matched)")
save_fig(g2, "fig_n5_skew_by_component", 7.5, 4.5)


# #############################################################################
# PART 5  CALIBRATION TO THE SPX SURFACE
#
#   The three specifications are calibrated in order of size. Because they are
#   nested, each one starts (among other points) from the previous optimum with
#   the extra parameters set close to their restricted values, so the in-sample
#   fit cannot get worse when a component is added.
#
#   5.1 Heston   5.2 SVJ   5.3 SVJJ   5.4 Heston on sub-surfaces (distortion)
#   5.5 Evaluation of all three on every quote
# #############################################################################
cat("\n================ PART 5: CALIBRATION ================\n")

# ---- 5.1 Heston ----------------------------------------------------------------
heston$starts <- list(c(2.0, 0.04, 0.5, -0.7, 0.02),
                      c(5.0, 0.03, 1.0, -0.8, 0.015),
                      c(0.5, 0.08, 0.3, -0.6, 0.02))
fit_heston <- cached("fit_heston", calibrate(heston, train))
print(round(fit_heston$par, 4))
cat(sprintf("Feller ratio 2*kappa*theta/eta^2 = %.3f\n",
            2 * fit_heston$par[["kappa"]] * fit_heston$par[["theta"]] / fit_heston$par[["eta"]]^2))

# ---- 5.2 SVJ -------------------------------------------------------------------
svj$starts <- list(c(fit_heston$par, 0.10, -0.10, 0.10),     # Heston optimum + small jumps
                   c(2.0, 0.03, 0.3, -0.7, 0.012, 0.5, -0.08, 0.08),
                   c(1.0, 0.04, 0.4, -0.8, 0.010, 1.5, -0.04, 0.05),
                   c(3.0, 0.03, 0.6, -0.6, 0.012, 0.2, -0.20, 0.15))
fit_svj <- cached("fit_svj", calibrate(svj, train))
print(round(fit_svj$par, 4))

# ---- 5.3 SVJJ ------------------------------------------------------------------
svjj$starts <- list(c(fit_svj$par, 0.005,  0.0),             # SVJ optimum + tiny variance jumps
                    c(fit_svj$par, 0.050, -0.4),
                    c(2.0, 0.02, 0.3, -0.7, 0.012, 0.5, -0.05, 0.08, 0.03, -0.5),
                    c(4.0, 0.03, 0.6, -0.6, 0.010, 0.2, -0.10, 0.10, 0.10, -1.0),
                    c(3.0, 0.02, 0.5, -0.9, 0.012, 1.0,  0.00, 0.05, 0.08, -0.7),
                    c(1.5, 0.03, 0.4, -0.8, 0.012, 0.3, -0.10, 0.10, 0.05, -2.0))
fit_svjj <- cached("fit_svjj", calibrate(svjj, train))
print(round(fit_svjj$par, 4))

# Distinct local optima found by the multi-start (identification of SVJJ)
svjj_optima <- do.call(rbind, lapply(fit_svjj$runs, function(r)
  c(rmse_volpts = 100 * r$rmse, setNames(r$par, DPS_PAR))))
cat("SVJJ optimum from each starting point:\n"); print(round(svjj_optima, 4))
write.csv(svjj_optima, file.path(OUT_DIR, "table_svjj_local_optima.csv"), row.names = FALSE)

# ---- 5.4 Heston on sub-surfaces ------------------------------------------------
# If Heston were correctly specified, the parameters fitted to the short end
# and to the long end would agree with each other and with the full fit.
SHORT_MAX <- 0.30   # "short" = maturities up to this many years
LONG_MIN  <- 0.90   # "long"  = maturities from this many years
heston_sub <- function(d, start) {
  m <- heston; m$starts <- c(list(start), heston$starts[1:2]); calibrate(m, d)
}
fit_heston_short <- cached("fit_heston_short",
                           heston_sub(train[train$tau <= SHORT_MAX, ], fit_heston$par))
fit_heston_long  <- cached("fit_heston_long",
                           heston_sub(train[train$tau >= LONG_MIN, ], fit_heston$par))

# ---- 5.5 evaluation on all quotes ------------------------------------------------
res_heston <- evaluate_model(heston, fit_heston$par, opt)
res_svj    <- evaluate_model(svj,    fit_svj$par,    opt)
res_svjj   <- evaluate_model(svjj,   fit_svjj$par,   opt)
for (r in list(res_heston, res_svj, res_svjj)) {
  cat(r$model[1], ": "); print(round(tapply(r$iv_err, r$sample, rmse), 3))
}
# #############################################################################
# PART 6  COMPARISON AND ANALYSIS
#
#   6.1 Collect results
#   6.2 Overall fit, in and out of sample, and calibration speed
#   6.3 Calibrated parameters
#   6.4 Where do the models fail? Errors by maturity and by moneyness
#   6.5 Heatmaps of implied-vol errors (maturity x moneyness)
#   6.6 Fitted smiles
#   6.7 What does each extra piece buy?
#   6.8 The mechanism: model-implied ATM skew term structure
#   6.9 Parameter distortion in Heston
# #############################################################################
cat("\n================ PART 6: COMPARISON ================\n")

# ---- 6.1 collect -------------------------------------------------------------
MODELS <- list(Heston = heston, SVJ = svj, SVJJ = svjj)
FITS   <- list(Heston = fit_heston, SVJ = fit_svj, SVJJ = fit_svjj)
model_levels <- names(MODELS)

res <- rbind(res_heston, res_svj, res_svjj)
res$model <- factor(res$model, levels = model_levels)
res$mny_bucket <- cut(res$k, breaks = c(-Inf, -0.40, -0.20, -0.10, -0.05, 0, 0.05, Inf),
                      labels = c("< -0.40", "-0.40..-0.20", "-0.20..-0.10", "-0.10..-0.05",
                                 "-0.05..0", "0..0.05", "> 0.05"))
res$mat_short <- factor(sprintf("%.2f", res$tau), levels = sprintf("%.2f", sort(unique(res$tau))))
write.csv(res, file.path(OUT_DIR, "results_all_quotes.csv"), row.names = FALSE)
cat(sprintf("Quotes where a model IV could not be computed: %d\n", sum(is.na(res$iv_err))))

model_colours <- spec_colours

# ---- 6.2 overall fit and speed -----------------------------------------------
# IV-RMSE in volatility points. "sec_per_surface" is the time for one
# evaluation of all training prices; "time_best_start" is the time of the
# single optimiser run that found the optimum.
summary_tab <- do.call(rbind, lapply(model_levels, function(m) {
  r <- res[res$model == m, ]; f <- FITS[[m]]
  data.frame(model = m, n_par = f$n_par,
             rmse_train         = rmse(r$iv_err[r$sample == "train"]),
             rmse_test_strike   = rmse(r$iv_err[r$sample == "test_strike"]),
             rmse_test_maturity = rmse(r$iv_err[r$sample == "test_maturity"]),
             mae_all            = mean(abs(r$iv_err), na.rm = TRUE),
             bias_all           = mean(r$iv_err, na.rm = TRUE),
             n_starts           = length(f$runs),
             time_total_sec     = f$time_total, n_eval_total = f$n_eval_total,
             time_best_start    = f$time_best,  n_eval_best  = f$n_eval_best,
             sec_per_surface    = time_surface(MODELS[[m]], f$par, train))
}))
cat("\nFit (IV-RMSE in vol points) and calibration speed:\n")
print(format(summary_tab, digits = 3), row.names = FALSE)
write.csv(summary_tab, file.path(OUT_DIR, "table_summary.csv"), row.names = FALSE)

# ---- 6.3 parameters ----------------------------------------------------------
par_tab <- do.call(rbind, lapply(model_levels, function(m)
  data.frame(model = m, parameter = names(FITS[[m]]$par), value = unname(FITS[[m]]$par),
             lower = MODELS[[m]]$lower, upper = MODELS[[m]]$upper)))
par_tab$at_bound <- with(par_tab, abs(value - lower) < 1e-6 * (1 + abs(lower)) |
                                  abs(value - upper) < 1e-6 * (1 + abs(upper)))
cat("\nCalibrated parameters:\n"); print(format(par_tab, digits = 4), row.names = FALSE)
write.csv(par_tab, file.path(OUT_DIR, "table_parameters.csv"), row.names = FALSE)

# ---- 6.4 errors by maturity and by moneyness ---------------------------------
by_mat <- aggregate(iv_err ~ model + tau + exdate, res, rmse)
by_mat$holdout <- by_mat$exdate %in% HOLDOUT_EXDATES
cat("\nIV-RMSE by maturity (vol points):\n")
print(round(tapply(res$iv_err, list(sprintf("%.2f", res$tau), res$model), rmse), 3))
write.csv(reshape(by_mat[, c("model", "tau", "iv_err")], idvar = "tau", timevar = "model",
                  direction = "wide"), file.path(OUT_DIR, "table_rmse_by_maturity.csv"),
          row.names = FALSE)

p_mat <- ggplot(by_mat, aes(tau, iv_err, colour = model)) +
  geom_line() + geom_point(aes(shape = holdout), size = 2) +
  scale_colour_manual(values = model_colours, name = NULL) +
  scale_shape_manual(values = c(`FALSE` = 16, `TRUE` = 1), labels = c("in training set", "held-out maturity"),
                     name = NULL) +
  scale_x_continuous(trans = "sqrt", breaks = c(0.1, 0.25, 0.5, 1, 1.5, 2)) +
  labs(x = "Maturity (years, square-root scale)", y = "IV-RMSE (vol points)",
       title = "Implied-volatility error by maturity")
save_fig(p_mat, "fig04_rmse_by_maturity", 7.5, 4.5)

by_mny <- aggregate(iv_err ~ model + mny_bucket, res, rmse)
cat("\nIV-RMSE by moneyness bucket (vol points):\n")
print(round(tapply(res$iv_err, list(res$mny_bucket, res$model), rmse), 3))
write.csv(reshape(by_mny, idvar = "mny_bucket", timevar = "model", direction = "wide"),
          file.path(OUT_DIR, "table_rmse_by_moneyness.csv"), row.names = FALSE)

p_mny <- ggplot(by_mny, aes(mny_bucket, iv_err, fill = model)) +
  geom_col(position = "dodge") +
  scale_fill_manual(values = model_colours, name = NULL) +
  labs(x = "Log-forward-moneyness k", y = "IV-RMSE (vol points)",
       title = "Implied-volatility error by moneyness")
save_fig(p_mny, "fig05_rmse_by_moneyness", 7.5, 4.5)

# ---- 6.5 heatmaps: maturity x moneyness --------------------------------------
heat <- aggregate(iv_err ~ model + mat_short + mny_bucket, res,
                  function(e) c(bias = mean(e), rmse = rmse(e), n = length(e)))
heat <- cbind(heat[, 1:3], as.data.frame(heat$iv_err))

lim <- max(abs(heat$bias))
p_heat_bias <- ggplot(heat, aes(mny_bucket, mat_short, fill = bias)) +
  geom_tile(colour = "white") +
  geom_text(aes(label = sprintf("%.1f", bias)), size = 2.3) +
  facet_wrap(~model, nrow = 1) +
  scale_fill_gradient2(low = "#2166ac", mid = "white", high = "#b2182b", midpoint = 0,
                       limits = c(-lim, lim), name = "Mean IV error\n(model - market,\nvol points)") +
  labs(x = "Log-forward-moneyness k", y = "Maturity (years)",
       title = "Mean implied-volatility error by maturity and moneyness") +
  theme(axis.text.x = element_text(angle = 60, hjust = 1), panel.grid = element_blank())
save_fig(p_heat_bias, "fig06_heatmap_bias", 12, 5)

p_heat_rmse <- ggplot(heat, aes(mny_bucket, mat_short, fill = rmse)) +
  geom_tile(colour = "white") +
  geom_text(aes(label = sprintf("%.1f", rmse)), size = 2.3) +
  facet_wrap(~model, nrow = 1) +
  scale_fill_gradient(low = "white", high = "#b2182b", name = "IV-RMSE\n(vol points)") +
  labs(x = "Log-forward-moneyness k", y = "Maturity (years)",
       title = "Implied-volatility RMSE by maturity and moneyness") +
  theme(axis.text.x = element_text(angle = 60, hjust = 1), panel.grid = element_blank())
save_fig(p_heat_rmse, "fig07_heatmap_rmse", 12, 5)
write.csv(heat, file.path(OUT_DIR, "table_heatmap.csv"), row.names = FALSE)

# ---- 6.6 fitted smiles -------------------------------------------------------
mkt <- res[res$model == "Heston", ]
p_smiles <- ggplot() +
  geom_point(data = mkt, aes(k, 100 * iv), size = 0.5, colour = "grey35") +
  geom_line(data = res, aes(k, 100 * model_iv, colour = model), linewidth = 0.45) +
  facet_wrap(~mat_label, scales = "free", ncol = 4) +
  scale_colour_manual(values = model_colours, name = NULL) +
  labs(x = "Log-forward-moneyness k", y = "Implied volatility (%)",
       title = "Market smiles (points) and calibrated models (lines)") +
  theme(legend.position = "bottom")
save_fig(p_smiles, "fig08_fitted_smiles", 12, 8)

# the two shortest maturities, zoomed in around the money
short2 <- sort(unique(res$tau))[1:2]
p_short <- ggplot() +
  geom_point(data = mkt[mkt$tau %in% short2 & mkt$k > -0.25, ], aes(k, 100 * iv),
             size = 0.8, colour = "grey35") +
  geom_line(data = res[res$tau %in% short2 & res$k > -0.25, ],
            aes(k, 100 * model_iv, colour = model), linewidth = 0.6) +
  facet_wrap(~mat_label, scales = "free") +
  scale_colour_manual(values = model_colours, name = NULL) +
  labs(x = "Log-forward-moneyness k", y = "Implied volatility (%)",
       title = "The short end of the surface") + theme(legend.position = "bottom")
save_fig(p_short, "fig09_short_end_smiles", 9, 4.5)

# ---- 6.7 what does each extra piece buy? -------------------------------------
res$mat_group <- cut(res$tau, c(0, SHORT_MAX, LONG_MIN, Inf), right = FALSE,
                     labels = c(sprintf("short (T < %.2f)", SHORT_MAX), "medium",
                                sprintf("long (T >= %.2f)", LONG_MIN)))
res$wing <- cut(res$k, c(-Inf, -0.10, 0.0, Inf),
                labels = c("OTM puts (k < -0.10)", "near-ATM puts", "OTM calls"))
buy <- tapply(res$iv_err, list(paste(res$mat_group, "|", res$wing), res$model), rmse)
buy <- cbind(buy,
             `SVJ vs Heston (%)`  = 100 * (buy[, "SVJ"]  / buy[, "Heston"] - 1),
             `SVJJ vs SVJ (%)`    = 100 * (buy[, "SVJJ"] / buy[, "SVJ"]    - 1),
             `SVJJ vs Heston (%)` = 100 * (buy[, "SVJJ"] / buy[, "Heston"] - 1))
cat("\nIV-RMSE by region, and the change from each extension:\n"); print(round(buy, 3))
write.csv(buy, file.path(OUT_DIR, "table_what_each_piece_buys.csv"))

grp <- aggregate(iv_err ~ model + mat_group + wing, res, rmse)
p_buy <- ggplot(grp, aes(wing, iv_err, fill = model)) + geom_col(position = "dodge") +
  facet_wrap(~mat_group) + scale_fill_manual(values = model_colours, name = NULL) +
  labs(x = NULL, y = "IV-RMSE (vol points)", title = "Where each model gains or loses") +
  theme(axis.text.x = element_text(angle = 25, hjust = 1), legend.position = "bottom")
save_fig(p_buy, "fig10_what_each_piece_buys", 9, 4.5)

# ---- 6.8 the mechanism: model-implied ATM skew term structure -----------------
# ATM skew by central differences with h = SKEW_H, exactly as for the market
# in PART 1.6, on a fine maturity grid that also goes below the shortest
# traded maturity.
atm_skew_model <- function(model, p, tau_grid, h = SKEW_H) {
  sapply(tau_grid, function(t) {
    pr <- cm_prices(model$cf, p, t, c(-h, h), c("P", "C"))
    iv <- implied_vol(pr, c(-h, h), t, c("P", "C"))
    (iv[2] - iv[1]) / (2 * h)
  })
}
tau_grid <- exp(seq(log(1 / 52), log(2.2), length.out = 40))
skew_tab <- do.call(rbind, lapply(model_levels, function(m)
  data.frame(model = m, tau = tau_grid,
             skew = atm_skew_model(MODELS[[m]], FITS[[m]]$par, tau_grid))))
skew_tab$model <- factor(skew_tab$model, levels = model_levels)

p_skew <- ggplot() +
  geom_line(data = skew_tab, aes(tau, skew, colour = model), linewidth = 0.7) +
  geom_point(data = features, aes(tau, atm_skew), size = 2) +
  scale_colour_manual(values = model_colours, name = NULL) +
  scale_x_continuous(trans = "log10", breaks = c(0.02, 0.05, 0.1, 0.25, 0.5, 1, 2)) +
  labs(x = "Maturity (years, log scale)", y = "ATM skew  dIV/dk at k = 0",
       title = "ATM skew term structure: market (points) and calibrated models (lines)")
save_fig(p_skew, "fig11_atm_skew_models", 7.5, 4.5)
write.csv(skew_tab, file.path(OUT_DIR, "table_model_atm_skew.csv"), row.names = FALSE)

# ---- 6.9 parameter distortion in Heston --------------------------------------
# (i) Heston calibrated to all / only short / only long maturities.
# (ii) The same five diffusion parameters inside SVJ and SVJJ.
distortion <- rbind(
  `Heston (all maturities)` = fit_heston$par,
  `Heston (short only)`     = fit_heston_short$par,
  `Heston (long only)`      = fit_heston_long$par,
  `SVJ diffusion part`      = fit_svj$par[1:5],
  `SVJJ diffusion part`     = fit_svjj$par[1:5])
distortion <- cbind(distortion,
  feller   = 2 * distortion[, "kappa"] * distortion[, "theta"] / distortion[, "eta"]^2,
  vol0     = sqrt(distortion[, "v0"]),
  vol_long = sqrt(distortion[, "theta"]))
cat("\nParameter distortion in Heston:\n"); print(round(distortion, 4))
write.csv(distortion, file.path(OUT_DIR, "table_heston_distortion.csv"))

# (iii) Cross-errors: how well does the Heston fitted on one end price the other?
cross <- sapply(list(all = fit_heston, short = fit_heston_short, long = fit_heston_long),
  function(f) {
    r <- evaluate_model(heston, f$par, opt)
    c(short = rmse(r$iv_err[r$tau <= SHORT_MAX]), long = rmse(r$iv_err[r$tau >= LONG_MIN]),
      all = rmse(r$iv_err))
  })
cat("\nHeston IV-RMSE (rows: evaluated on; columns: calibrated on):\n"); print(round(cross, 3))
write.csv(cross, file.path(OUT_DIR, "table_heston_cross_errors.csv"))

# (iv) Jump contribution to variance in SVJ / SVJJ (annualised, under Q)
jump_var <- c(
  SVJ  = unname(fit_svj$par["lambda"] * (fit_svj$par["mu_s"]^2 + fit_svj$par["sigma_s"]^2)),
  SVJJ = with(as.list(fit_svjj$par),      # E[(Z^s)^2] with Z^s | Z^v normal, Z^v exponential
              lambda * (sigma_s^2 + mu_s^2 + 2 * mu_s * rho_J * mu_v + 2 * rho_J^2 * mu_v^2)))
cat("\nAnnualised variance from price jumps:\n"); print(round(jump_var, 5))

cat("\nDone. Tables are in '", OUT_DIR, "', figures in '", FIG_DIR, "'.\n", sep = "")
