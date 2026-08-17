# Maxent-law solver audit (2026-08-16): nondeterminism found, fixed,
# and a systematic bias corrected

## Discovery
The turnover computation's class counts differed across otherwise
identical runs (level 6: 171 / 176 / 180; level 9: 115,317 vs
116,381).  Traced to make_law: (a) LP restart directions drew from
the GLOBAL seeded rng, so the member depended on process history;
(b) the max-entropy stage ran a SINGLE SLSQP start on a nonconvex
sphere-slice and landed in different near-optima.

## Measured impact (n=8, balanced system (1,-3,2) phi=0.625pi)
  - Cross-run spread of tex_mu(8): std 0.0044, RANGE 0.011 -
    LARGER than the +-0.008 turnover decision threshold.
  - Flickering classes carry real mass (mu up to ~1e-2).
  - Sanity that fell out free: on fully-labeled histories
    tex_mu == tex_P exactly (single path per labeled history =>
    |A|^2 = P): coherence lives ONLY in class aggregation.

## Fix: law_ellipsoid.py (make_law_ell)
Parametrize the feasible set {A y = b, y^T M y = 1, y >= 0} exactly:
null space of A gives an ellipsoid section of dim K-2; sample it
densely with a PER-KEY deterministic generator; polish each start
with SLSQP; keep best entropy (raw feasible starts scored too -
SLSQP reports failure at pinned solutions).  Orthant-safe LP-vertex
bisection starts kept as backup.  Convergence in NSTART:
    NSTART=8:  tex_mu(8) = 0.2869436
    NSTART=16: tex_mu(8) = 0.2870921   (+1.5e-4)
    NSTART=48: tex_mu(8) = 0.2871467   (+5.5e-5)
Geometric convergence; NSTART=16 adopted (residual ~1e-4, well
below decision thresholds).  Reproducibility: exact (zero spread
across rng-history perturbations).  Cost: ~60ms per distinct gap
system; ~1.4k distinct systems at n<=8.

## Corrections forced on prior readings
1. OLD LAW BIASED LOW: best-of-4 old member gave tex_mu(8)=0.2675,
   best-of-10 0.2725, converged value 0.2871 - the old solver sat
   ~0.02 BELOW the true maxent member.  All prior tex numbers from
   the reference ladder (0.250 -> 0.264 -> 0.276 -> 0.2857) carry
   this bias.
2. DECELERATION READING RETRACTED: the "+0.0139/+0.0120/+0.0100
   decelerating" pattern differed by ~0.002 per step - within the
   old cross-run noise (0.0044) and far within the old systematic
   bias (0.02).  It was never significant.  The corrected ladder
   n=8..11 is being recomputed in one internally-consistent run
   with the converged deterministic law (turnover_check2.py v3).
3. Direction note: the true maxent member has HIGHER texture than
   the old-solver members at n=8 - if this persists across n, the
   entropy problem is WORSE than reported, firming the gate-1
   verdict; but the increments decide, not the level.
4. selection_and_action.py's in-place make_law was also patched
   (deterministic per-key seeds + multi-start best-of) as a
   stopgap; make_law_ell supersedes it for all decision-grade runs.

## Scope of contamination (honest inventory)
Any prior result whose OBSERVABLE depended on the maxent member's
fine structure at ~1e-2 resolution: the coherent-measure ladder,
balance-point scan (r_mu 0.5060 vs 0.5014 - margin 0.005, now
suspect), texture-targeted scan champion values.  NOT contaminated:
Lean theorems (exact), feasibility walls (binary, margins large),
expansion-law fits (xfe member, different stage), no-gos (exact
linear algebra), composite-bridge geometry (uses sampled growth,
not member fine structure at 1e-2), k=3 additivity, phase
covariance/octant results (exact integer structure).
