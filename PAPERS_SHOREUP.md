# Shoring the three papers to submission grade (2026-08-13)

Consolidation of the shore-up computations for P1 (fact stability),
P2 (statistical phase), P3 (Lambda exclusion).

## P1 — "Fact stability selects Born-normalized growth"

PRIOR-ART SWEEP (PRIOR_ART_P1.md): novelty claim SUPPORTED.  The
literature's Complex Sequential Growth (Surya-Zalel 2003.11311, Zalel
covtree, Martin-Sorkin complex percolation) is coherent-only
(sum a = 1); its covariance program attacks measure-extension
(bounded variation), not the law.  Barandes' unistochastic theorems
are adjacent (Born-completeness of unitary rows) but never impose
both normalizations on the same transition data and have no
causal-set contact.  No prior bi-normalized growth law, no prior
record-stability selection postulate, no prior phase-quantization
result of our form was found.  Referee risk register drafted with
answers.  STATUS: content 100%; remaining work is writing.

## P2 — "Statistical phase of a parameter-free quantum growth law"

(a) CASCADE VALIDATED AT n = 9, OUT OF SAMPLE (p2_cascade_n9.log;
level 9 built exactly: 183231 classes, matching the known count):
  - V1: sigma(9) predicted 1.640 (constants frozen from the committed
    4->7 fit) vs measured 1.680 - 2.4% error, second consecutive
    out-of-sample hit.
  - V2: transition 8->9 constants g = 0.909, v = 0.219, 2cov = +0.312
    (committed: 0.864/0.289/+0.224).  Slow drift continues (v down,
    cov up, g up); the injection SUM v + 2cov is stable (0.531 vs
    0.513).  Paper statement: AR(1) cascade with slowly drifting
    constants, predictive at the 2-3% level per step; saturation
    stated as the g < 1 consequence with the drift caveat.
  - V3: overlap deceleration CONFIRMED for all five stem events
    (ln-c increments shrink monotonically, e.g. stem2
    -0.243 -> -0.073), as saturation predicts; the has_post overlap
    still grows with roughly flat increments at n <= 9 - deceleration
    not yet visible for the rare-side event; stated honestly.
(b) SELECTION ROBUSTNESS (tilt_gapvariant.log): the gap-grouped
    max-entropy variant reproduces the tilt law with T2 residual mean
    +0.074 - IDENTICAL to the class-variant mean.  The tilt structure
    is selection-independent within the measured band.
(c) SECOND-ENGINE CHECK - honest limitation (p2_tilt_4d.log): the 4D
    bracket law at phi4 has support 4/28 classes at n = 7/8
    (deterministic-fan onset; branching begins at n = 6), too thin
    for tilt statistics at exact-DP depths.  The engine-robustness
    axis is INCONCLUSIVE-BY-DEPTH and the paper's tilt claims are
    scoped to the 2D engine, with the 4D check listed as future work
    (needs n >> 10).
STATUS: 100% within its (now explicitly scoped) claims; remaining
work is writing.

## P3 — everpresent-Lambda exclusion note

ROBUSTNESS APPENDIX (p3_robustness.log), subdominant-envelope bound
with Omega_m AND h profiled (fixing the committed scan's held-Om
caveat):
  R1 baseline (profiled):      A_2sig = 0.0286  ->  l_k >= 35.0 fm
  R2 BAO-only (no CMB):        no 2-sigma crossing to A = 0.30
                               (bound driven by the CMB-BAO
                               consistency, stated)
  R3 no-Lya:                   A_2sig = 0.0293  ->  l_k >= 34.7 fm
  R4 h-grid halved:            A_2sig = 0.0249  ->  l_k >= 36.7 fm
The profiled bound STRENGTHENS the committed l_k >= 27 fm to
l_k >= 35 fm and is stable to dropping Lya and to grid refinement;
BAO-only is honestly reported as non-constraining at this amplitude
range.  The exclusion itself (stochastic min Delta-chi2 = +41,
deterministic +971) was never in question.  Headline updated:
l_k(grav) >= 35 fm (2 sigma, DESI DR2 + Planck distances, profiled).
STATUS: 100%; remaining work is writing (and optionally SN, which
can only strengthen).

## Residual writing checklist (no computation)

P1: introduction + related-work section from PRIOR_ART_P1.md;
    theorem statements exported from the four Lean modules; numerics
    section from born_records_test / factstab_probe logs.
P2: methods (ideal-lattice sampler), results (exponent table, tilt,
    cascade, plateau), scoped-claims section.
P3: model recap (Planck cancellation), pipeline validation, exclusion,
    bound, robustness appendix table above.
