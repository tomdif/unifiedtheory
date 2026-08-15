# Emergent-4D: the comprehensive negative (2026-08-15)

The flagship physics question — does the quantized (pi/4) causal-set
law's dimension flow up toward 4 — is now answered across ALL three
accessible probes.  It does not, at any scale reachable without MCMC.

## Probe 1 — bare Myrheim-Meyer (ordering-fraction) dimension
`deep_dimension_ideals.py`, exact ideal-lattice sampler, two-limb
120-bit masks, n = 80, ideal counts to 5.5M, 0 infeasible parents to
depth 79.
  d_eff: 2.27 (n=5) -> 1.71 (60) -> 1.69 (70) -> 1.67 (80),
  monotone slow DECLINE (slope -0.0023/element; 1/n-asymptote ~1.58).
No upturn.  Bulk sits in the CDT UV band but flows DOWN.

## Probe 2 — spectral dimension d_s(sigma)
`deep_dimension_ideals.py` spectral section, n = 80 final causets,
lazy random walk on the Hasse graph.
  d_s: 2.74 (sigma=2) -> 2.22 (4) -> 1.74 (6) -> 1.40 (8) -> ...
  MONOTONE FALL to the finite-size floor (P_return -> 1/N by
  sigma ~ 10-20).  NO intermediate-scale rise toward 4.
Resolvable window sigma <= ~8-10 at N = 80; an IR plateau, if it
exists, lives beyond the finite-size cutoff.

## Probe 3 — coarse-grained (RG) dimension: STRUCTURALLY VOID
`dimension_rg_flow.py` (built, then diagnosed void).  The
Myrheim-Meyer / ordering-fraction dimension is THINNING-INVARIANT:
under random-deletion coarse-graining each surviving pair keeps its
relation status, so E[r_coarse] = r of the fine causet, and d_MM is
coarse-graining invariant BY CONSTRUCTION.  The naive "coarse vs
native-at-matched-size" test therefore only re-reads the r(n) growth
curve (the smoke test's -4.8 sigma "DOWN" is exactly this artifact,
not physics).  This reproduces the caveat already registered in the
2026-08-12 IR-flow note: the r-chart cannot see RG flow.  A valid
coarse-graining probe must use a NON-thinning-invariant observable
(spectral d_s, interval-dimension d_int at matched height) — i.e.
Probe 2, which is finite-size-limited.

## Verdict
Emergent 4D does NOT appear in the bare dimension (declines to
~1.67), the spectral dimension (falls monotonically, no rise), or
via MM coarse-graining (structurally blind).  The quantized law is a
UV ~1.7-dimensional theory at every accessible scale — firmly inside
the CDT/asymptotic-safety UV band (d_s = 1.80 +- 0.25) but with no
IR growth signal.

The ONLY surviving route is a genuine large-N IR window: the
spectral d_s intermediate plateau requires N in the hundreds so that
sigma_max (set by P_return > 2/N) opens a decade before the
finite-size floor.  That is an MCMC-over-growth-paths computation
(the exact ideal sampler caps near n ~ 80-90 by ideal count), not
more of the same.  Registered as the single open flagship item; the
accessible-scale question is closed negative.
