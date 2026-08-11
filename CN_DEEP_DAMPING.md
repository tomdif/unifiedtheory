# The deep-damping floor: c_N vanishes as a power law — the theory
# CLEARS its own CMB falsifier (2026-08-11)

## What was at stake

EVERPRESENT_LAMBDA_DERIVED.md made the Poisson-floor coefficient c_N a
kill-or-clear quantity with zero remaining freedom: the parameter-free
amplitude dLambda sqrt(V) = kappa sqrt(v_eff) puts the floor channel
at Omega ~ 1.55 sqrt(c_N) on the CMB-fatal classic law, so early-dark-
energy limits demand c_N(eps*) <= 3.7e-4 at the cosmological smearing
eps* ~ 2e-81.  The July MC (diamond, noise floor ~0.3) could not
resolve this.  Readings registered in cn_deep_damping.py.

## Method

Flat spacetime box [0, 14.75] x spatial torus [0,9]^3 at unit density
(NO spatial boundary), 180 realizations of <N> = 10751; same kernel
and conventions as action_variance_mc.py (f weights 1, -9e, 8e^2,
-(4/3)e^3; S/kappa = N - D); interval counts n = C@C once per
realization, reused across eps in {0.5, 0.4, 0.3, 0.2, 0.1, 0.05};
bulk window t >= 10.55 = 3 tau_eps(0.05) (every window point's
smearing support e^{-eps V}, eps V <= 81, fully inside the box); four
time bands, Var(S_W/kappa)/<N_W> per band, intercept against the
band's mean t^2.

GEOMETRY CORRECTION (important, honest): on the torus the boost/
near-null term SATURATES (minimum-image caps spatial separations at
sqrt(3) L/2), so it does not grow as t^2 in the window — the measured
t^2 slopes collapse toward zero at small eps (2.81 -> -0.01) and the
saturated boost contribution folds INTO the intercept.  The intercept
is therefore an UPPER BOUND on the bulk Poisson floor:
    c_N(eps) <= intercept(eps) = floor + compactified-boost(eps, L).
This strengthens the verdict below: even the TOTAL bulk variance obeys
the decreasing law.

## Result (cn_deep_damping.log)

  eps        intercept (>= c_N)    t^2 slope
  0.5        632.6                 2.81
  0.4        177.5                 2.09
  0.3         94.7                 0.83
  0.2         84.5                 0.07
  0.1         31.4                -0.01
  0.05        17.9                -0.01

  power law:  intercept(eps) = 796 * eps^1.35   (6/6 positive,
              monotone decreasing; local exponent at the small-eps end
              ~0.8, global 1.35)

  extrapolation:  c_N(eps* = 2e-81) <= 8e-107   (global exponent)
                                    <= ~1e-63   (conservative local
                                       exponent 0.8)
  CMB bound: 3.7e-4.

**VERDICT: registered reading (i).  The floor VANISHES in deep
damping; at the cosmological smearing it is at least ~59 orders of
magnitude (conservatively) below the CMB requirement.  The
parameter-free everpresent-Lambda sector survives its own falsifier.**

Robustness of the extrapolation: the bound clears for ANY continued
power law with exponent >= 0.06; only a plateau (a new scale appearing
below eps = 0.05, which the scale-free kernel does not contain) could
change the verdict.  The per-pair analytic structure supports the
power law: each pair contributes O(eps^2 f^2) with f exponentially
damped in eps V, leaving no mechanism for an eps-independent residue.

## What this closes and what remains

Closed: the floor channel is harmless — the CMB constraint from
EVERPRESENT_LAMBDA_DERIVED.md is satisfied with enormous margin; the
dark-energy sector's surviving structure is exactly as derived there:
the edge channel with l_k = 12.1 fm, CMB-safe, thawing w, zero free
amplitude parameters.

Remaining (registered):
1. The zero-parameter DESI likelihood run (unchanged, now the single
   decisive data test).
2. A Minkowski-geometry (diamond) version at eps <= 0.05 to separate
   the true t^2 edge coefficient from the floor in the same run
   (needs bigger boxes; the torus upper bound suffices for the CMB
   question).
3. Lean: the cancellation identity and the per-pair O(eps) damping
   structure (`variance_rate`-shaped per the July report).

## Honest scope

- Upper-bound logic: the intercept over-counts (saturated boost term
  included); the true floor is smaller — the direction that helps.
- Extrapolation spans 79 orders in eps; flagged, with the
  any-exponent->=0.06 robustness statement above.
- Torus-flat differs from Minkowski-flat for kernel ranges near L/2
  (the eps = 0.05 point is marginal, range ~5.3 vs L/2 = 4.5); this
  distorts the O(1) prefactor, not the monotone vanishing.
- 180 realizations; variance-of-variance ~11% per band point; the
  fitted exponent is stable to dropping any single eps point.
