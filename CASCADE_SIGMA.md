# sigma(n) derived as a smoothed multiplicative cascade — and it
# SATURATES (2026-08-13)

## The decomposition (exact per transition)

ln R(child) = m + delta with m the contribution-share-weighted parent
mean; Var[ln R] propagates as sigma^2_{n+1} = g_n sigma^2_n + v_n +
2cov_n.  Measured (cascade_sigma.py, exact DP):

  n->n+1   g_n     v_n    2cov_n   s_loc^2
  3->4    1.091*  0.392   +0.207    0.144      (*early transient)
  4->5    0.909   0.294   +0.176    0.131
  5->6    0.834   0.304   +0.209    0.115
  6->7    0.850   0.269   +0.288    0.101
  7->8    0.889   0.243   +0.318    0.089

Stable constants from n = 4 on: g ~ 0.86, v ~ 0.29, 2cov ~ +0.22.

HOLDOUT VALIDATION: constants fitted on 4->5..6->7 predict
sigma(8) = 1.555 vs measured 1.587 — **2.0% error**.  The sigma
dynamics is a measured-constant AR(1) cascade; the tilt law's one
dynamical input is now itself derived from the R-recursion's
structure, up to the two constants (g, v).

## The two mechanisms, identified

1. SMOOTHING g < 1: multi-parent aggregation averages parent log-
   weights — the SAME class aggregation that drives anti-decoherence
   and record accretion also tames the spread.  The coherent channel
   self-regularizes.
2. INJECTION v: the increment variance is NOT mainly local branching
   (s_loc^2 = 0.09-0.14 and falling) — it is dominated by
   heterogeneous aggregation gain (the spread of ln N_eff-like
   path-multiplicity accrual across classes).  Variance is injected
   by how unevenly geometries accumulate histories, not by the law's
   per-parent rho-spread.

## The consequence: the lognormal spread SATURATES

With g < 1 the cascade has a fixed point

    sigma*^2 = (v + 2cov)/(1 - g) ~ 3.8,   sigma* ~ 1.95,

(vs 1.59 at n = 8): NOT runaway multifractality.  If the constants
persist, every tilt exponent inherits saturation: overlap growth
gamma_A slows and freezes, the anti-KPZ exponent ratios stabilize,
and the covariant measure's deviation from classical statistics
approaches a FIXED lognormal profile — an asymptotically
scale-invariant statistical phase (consistent with, and explaining,
the geometric d_eff plateau seen independently at n <= 60).

Falsifiable continuation: sampled sigma at n = 9-12 should follow
sigma^2_{n+1} = 0.86 sigma^2_n + 0.51 (e.g. sigma(12) ~ 1.75),
and overlap growth curves c(A, n) should visibly decelerate.

## Honest scope

- Constants drift slowly (v falling ~10%/step, 2cov rising); the
  fixed point 3.8 assumes persistence — stated as extrapolation, with
  the trend caveat.  The 3->4 transition is transient (g > 1).
- Share-weighted decomposition is one canonical choice; the variance
  identity is exact for it.
- Remaining analytic step, sharply posed: derive g (one minus an
  average inverse parent-participation) and v (aggregation-gain
  variance) from the double-conservation + max-entropy structure.
  These are now finite, well-defined targets.

## The completed pyramid

  double conservation + action phases
    -> phase telescoping (Lean)  -> coherent measure = R^2, phase-free
    -> record accretion (Lean)   -> facts accrete
    -> tilt family (measured law: f_R^2 = f_count * f_Q)
    -> sigma-cascade (this note: g = 0.86, v = 0.29, 2% holdout)
    -> saturating lognormal phase (sigma* ~ 1.95)

Every statistical exponent measured this arc now traces to two
measured cascade constants and their two identified mechanisms.
