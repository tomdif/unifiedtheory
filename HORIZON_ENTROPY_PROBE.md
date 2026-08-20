# Finite Horizon Relative-Entropy Probe

Date: 2026-08-19

Script: `horizon_entropy_probe.py`

## Setup

The finite horizon cut is the current maximal antichain of a growing causal set.
For a candidate next-birth precursor downset `D`, define

```text
J(D)      = number of current horizon elements hit by D
DeltaA(D) = 1 - J(D)
```

`DeltaA` is the exact one-birth change in horizon size: the new event becomes
maximal and every maximal element inside `D` ceases to be maximal.

The excitation is the exponential source tilt of the baseline birth law:

```text
q_lambda(D) = p(D) exp(lambda J(D)) / Z(lambda)
```

## Exact Finite Identity

For this finite exponential family, the breakthrough identity is

```text
d/dlambda KL(q_lambda || p) = lambda Var_q[J]
d/dlambda E_q[DeltaA]       = - Var_q[J]
```

Therefore

```text
d/dlambda KL(q_lambda || p)
  = -lambda d/dlambda E_q[DeltaA].
```

This is the finite causal-growth analogue of the Dorau-Much/Jacobson statement
that relative entropy controls horizon focusing.  It is now formalized in Lean
as `finiteEntropyFocusing_birthLaw_deriv_identity`.

Small-source consequence:

```text
E_q[DeltaA] - E_p[DeltaA] ~= -2 KL(q_lambda || p) / lambda.
```

## Run

Command:

```bash
python3 horizon_entropy_probe.py --n 22 --paths 24 --burn 5 --starts 8 --lambdas 0.025,0.05,0.10
```

Result:

```text
sampled 408 parent transitions from 24/24 paths

lambda=0.025
  mean KL                    2.928995e-04
  mean Var_p[J]              9.246310e-01
  mean area shift           -2.335314e-02
  mean response ratio        0.996802
  max exact-id residual      0.000e+00
  mean gap/action shift     -2.898343e-02
  mean precursor-size shift  4.888528e-02
  mean corr_p(J,gap)        -0.068871

lambda=0.050
  mean KL                    1.187115e-03
  mean area shift           -4.717329e-02
  mean response ratio        0.993716
  mean gap/action shift     -5.910976e-02

lambda=0.100
  mean KL                    4.868461e-03
  mean area shift           -9.616037e-02
  mean response ratio        0.987884
  mean gap/action shift     -1.226595e-01

cross-parent coupling at lambda=0.025:
  corr(Var_p[J], gap_shift)  = -0.829711
  corr(Var_p[J], area_shift) = -0.999954
```

## Verdict

The finite entropy-to-focusing identity is exact, not merely numerical.  The
small-source approximation is already within about 0.3 percent at `lambda=0.025`
and about 1.2 percent at `lambda=0.10`.

The action/gap sector is not just the same observable in disguise:
`corr_p(J,gap)` is weak on average.  But across parent states, the entropy
susceptibility `Var_p[J]` strongly predicts the source-induced gap/action shift.
That is the useful bridge signal: horizon relative entropy has an exact finite
focusing law and a nontrivial coupling to the existing action observable.

Next target: replace the simple frontier-hit source `J` by a local interval or
BDG stress source and test whether the same KL/focusing identity survives with
the quantitative Hauptvermutung curvature estimator.

## Source Scan

Script: `horizon_source_scan.py`

Command:

```bash
python3 horizon_source_scan.py --n 22 --paths 24 --burn 5 --starts 8 --lam 0.05 --mixes 0.25,0.5,1.0,2.0
```

The existing 2D gap convention decomposes as

```text
gap(D) = 1 - (2 shell_0(D) - 4 shell_1(D) + 2 shell_2(D)).
```

Every horizon element hit by `D` is a shell-0 element, so the boundary part of
the BDG bracket is exactly

```text
boundary_bdg(D) = 2 J(D).
```

Run result:

```text
parents=408, lambda=0.05
max gap reconstruction error = 0

source              corr(J,S)  area_slope  gap_slope   area_shift      gap_shift
J                    1.000000  -0.893758  -0.443083  -4.567297e-02  -2.275695e-02
boundary_bdg         1.000000  -0.893758  -0.443083  -4.567297e-02  -2.275695e-02
interior_bdg        -0.166387   0.088707  -7.641308   4.404470e-03  -3.805627e-01
gap                 -0.068871   0.158709   7.911155   7.775477e-03   3.962618e-01
-gap                 0.068871  -0.158709  -7.911155  -8.090986e-03  -3.944982e-01
size                 0.742664  -0.699277  -0.397512  -3.516968e-02  -2.027589e-02
h0                   0.298081  -0.355882  -5.689365  -1.784824e-02  -2.870330e-01
h2                   0.323263  -0.306273  -4.379157  -1.558734e-02  -2.228166e-01

J_plus_negGap_0.25   0.975108  -0.873026  -2.073582  -4.464598e-02  -1.041166e-01
J_plus_negGap_0.5    0.908295  -0.819676  -3.522664  -4.190239e-02  -1.764349e-01
J_plus_negGap_1.0    0.715312  -0.673684  -5.636247  -3.435332e-02  -2.821131e-01
J_plus_negGap_2.0    0.450433  -0.472626  -7.174804  -2.402421e-02  -3.585587e-01
```

Interpretation:

* The full gap/action observable is mostly an interior signal at this scale.  A
  tilt by `gap` anti-focuses; a tilt by `-gap` focuses only weakly.
* The exact entropy-focusing source is the boundary BDG component `2J`, not the
  full gap.
* Mixed sources are promising.  `J + 0.25*(-gap)` retains about 98 percent of
  the horizon-focusing slope while increasing the action response by roughly
  4.5x relative to pure `J`.  `J + 0.5*(-gap)` retains about 92 percent of the
  focusing slope and gives roughly 7.8x the action response.

Updated target: formalize a two-channel finite source,

```text
S_a = standardized(J) + a standardized(-gap),
```

as the discrete analogue of "horizon energy flux + bulk stress."  Then replace
`gap` by a genuinely local BDG/curvature estimator and rerun the same scan.

## Pareto Scan

Script: `horizon_mix_pareto.py`

Command:

```bash
python3 horizon_mix_pareto.py --n 22 --paths 24 --burn 5 --starts 8 --amin 0 --amax 2.5 --step 0.05 --report-step 0.25 --thresholds 0.98,0.95,0.90
```

Result:

```text
pure J slopes: area=-0.893758, gap=-0.443083

a       area_slope   gap_slope    corrJ   focus_ret  gap_gain
0.00    -0.893758   -0.443083   1.0000    1.0000     1.000
0.25    -0.873026   -2.073582   0.9751    0.9768     4.680
0.50    -0.819676   -3.522664   0.9083    0.9171     7.950
0.75    -0.748445   -4.719373   0.8156    0.8374    10.651
1.00    -0.673684   -5.636247   0.7153    0.7538    12.721

Best with focus_ret >= 0.98:
  a=0.200, area_slope=-0.880230, gap_slope=-1.758848,
  corrJ=0.9839, focus_ret=0.9849, gap_gain=3.970

Best with focus_ret >= 0.95:
  a=0.350, area_slope=-0.854794, gap_slope=-2.680092,
  corrJ=0.9526, focus_ret=0.9564, gap_gain=6.049

Best with focus_ret >= 0.90:
  a=0.550, area_slope=-0.806382, gap_slope=-3.783567,
  corrJ=0.8913, focus_ret=0.9022, gap_gain=8.539
```

Current best working coefficient depends on how much focusing we require:

* strict: `a = 0.20`;
* balanced: `a = 0.35`;
* aggressive action coupling: `a = 0.55`.

The next cleaner test is to replace `std(-gap)` by its component orthogonal to
`std(J)` parent-by-parent.  That isolates the genuine bulk/action channel from
the exact horizon entropy channel.

## Orthogonal Bulk Channel

Command:

```bash
python3 horizon_mix_pareto.py --n 22 --paths 24 --burn 5 --starts 8 --amin 0 --amax 2.5 --step 0.05 --report-step 0.25 --thresholds 0.98,0.95,0.90 --orthogonal
```

Here the source is

```text
S_a = std(std(J) + a residual(std(-gap) | std(J))).
```

This removes the parentwise horizon component from the action channel before
mixing.

Result:

```text
pure J slopes: area=-0.893758, gap=-0.443083

a       area_slope   gap_slope    corrJ   focus_ret  gap_gain
0.00    -0.893758   -0.443083   1.0000    1.0000     1.000
0.25    -0.867073   -2.188585   0.9701    0.9701     4.939
0.50    -0.799402   -3.639246   0.8944    0.8944     8.213
0.75    -0.715007   -4.705328   0.8000    0.8000    10.620

Best with focus_ret >= 0.98:
  a=0.200, area_slope=-0.876402, gap_slope=-1.856602,
  corrJ=0.9806, focus_ret=0.9806, gap_gain=4.190

Best with focus_ret >= 0.95:
  a=0.300, area_slope=-0.856065, gap_slope=-2.508081,
  corrJ=0.9578, focus_ret=0.9578, gap_gain=5.661

Best with focus_ret >= 0.90:
  a=0.450, area_slope=-0.815038, gap_slope=-3.379790,
  corrJ=0.9119, focus_ret=0.9119, gap_gain=7.628
```

This is the cleaner candidate than the unprojected mixture.  The added action
response survives after removing the horizon-hit component, so the two-channel
signal is not just double-counting `J`.

Current registered source:

```text
S_* = std(std(J) + 0.20 residual(std(-gap) | std(J))).
```

This keeps about 98 percent of the exact horizon-focusing slope while giving
about 4.2x the gap/action response of pure `J`.

Robustness check:

```text
orthogonal scan, 98 percent focus-retention coefficient

n=18: a=0.20, focus_ret=0.9806, gap_gain=4.750
n=20: a=0.20, focus_ret=0.9806, gap_gain=4.779
n=22: a=0.20, focus_ret=0.9806, gap_gain=4.190

orthogonal scan, 95 percent focus-retention coefficient

n=18: a=0.30, focus_ret=0.9578, gap_gain=6.480
n=20: a=0.30, focus_ret=0.9578, gap_gain=6.523
n=22: a=0.30, focus_ret=0.9578, gap_gain=5.661
```

The coefficient is stable over the tested depth range.  The gap-gain drift is
moderate, but the focusing-retention geometry is essentially fixed because the
orthogonal construction controls the source angle directly.

Formalization:

`UnifiedTheory/Audit/KFCausalCSpecFiniteHorizonSource.lean` proves the scalar
core, the finite linear-response identity, and the exact finite
exponential-tilt derivative identity:

```text
focusRetention(a)^2 = 1 / (1 + a^2)
focusRetention(1/5)^2 = 25 / 26
mixedSlope(gapJ,gapBulk,1/5)
  = focusRetention(1/5) * (gapJ + gapBulk/5)

Cov(c - J, J) = -Var(J)
linearTiltResponse(source=J, observable=c-J) = -Var(J)
area_shift_linear = -2 KL_quadratic / lambda

Z(lambda) = sum_i p_i exp(lambda J_i)
E_lambda[X] = sum_i p_i exp(lambda J_i) X_i / Z(lambda)
KL_lambda = lambda E_lambda[J] - log Z(lambda)

d/dlambda E_lambda[c-J] = -Var_lambda[J]
d/dlambda KL_lambda = lambda Var_lambda[J]
d/dlambda KL_lambda = -lambda d/dlambda E_lambda[c-J]
```

So the observed depth-stability of `a = 0.20` is not a numerical accident.  It
is the exact geometry of a normalized orthogonal two-channel source.

The follow-up finite control theorem is now in
`UnifiedTheory/Audit/KFCausalCSpecHorizonOrthogonalDefect.lean`, with the
research note
[`HORIZON_ORTHOGONAL_DEFECT.md`](HORIZON_ORTHOGONAL_DEFECT.md).  It proves the
general covariance projection

```text
G_perp = G - Cov(G,J)/Var(J) * J
```

is the unique residual with `Cov(G_perp,J) = 0`, and that any combined source

```text
thetaH * J + thetaD * G_perp
```

has first-order horizon-area response exactly `-thetaH * Var(J)`, independent
of `thetaD`.  This upgrades the orthogonal bulk-channel scan from a numerical
source-angle observation to a reusable finite theorem.

The deeper follow-up is the second central response.  The same Lean file proves

```text
quadraticResponse(S, c - J) = -Cov(J, centered(S)^2).
```

So a projected residual has zero linear area response, but it can still leak
through `Cov(J, centered(S)^2)`.  The new script
`horizon_second_order_leakage.py` measures this obstruction.  On a modest
sample:

```text
python3 horizon_second_order_leakage.py --n 18 --paths 8 --burn 5 --starts 8 --coeffs 0.20,0.30,0.45

residual first_area = 2.23e-17
residual quad_area  = -6.11e-02
residual leakage    =  6.11e-02
quad+leak           =  4.97e-18
```

The residual is first-order clean, but not automatically second-order clean.
On this sample its second central area response has the focusing sign.  The
next optimization target is therefore sharper: keep `Cov(S,J)=0`, control or
tune `Cov(J,centered(S)^2)`, and maximize the Hauptvermutung-defect response.

The null-cone scan then tests two-channel defect mixtures:

```text
PYTHONDONTWRITEBYTECODE=1 python3 horizon_leakage_nullcone_scan.py --n 20 --paths 12 --burn 5 --starts 8 --tmin -2 --tmax 2 --step 0.05 --top 8
```

Representative low-leakage candidates:

```text
residual(-gap) + 0.003 residual(h2):  leakage = -6.54e-05, gap_slope = -7.459
residual(-gap) - 0.750 residual(h1): leakage =  1.89e-04, gap_slope = -7.191
```

This supports the null-cone idea at the sample-mean level.  It does not yet
select a stable physical channel; the best compensator changes with sample and
depth, so the next test is a refinement-stability scan.

Refinement-stability check:

```text
PYTHONDONTWRITEBYTECODE=1 python3 horizon_nullcone_stability.py --depths 18,20 --seeds 53,157 --paths 8 --burn 5 --starts 8 --tmin -2 --tmax 2 --step 0.10
```

Tracked pairs keep small leakage and large gap response, but the coefficient
drifts:

```text
-gap+h2:   mean|leak| = 1.33e-03, mean|gap| = 5.55, std(t) = 0.49
-gap+h0:   mean|leak| = 2.30e-03, mean|gap| = 6.82, std(t) = 0.31
h1+size:   mean|leak| = 5.66e-03, mean|gap| = 6.66, std(t) = 0.19
```

A broad multi-channel search did not improve this decisively:

```text
PYTHONDONTWRITEBYTECODE=1 python3 horizon_multichannel_nullcone_search.py --n 20 --paths 8 --burn 5 --starts 8 --directions 600 --top 8
```

Its best high-score directions were still almost pair-like.  The working
lesson is that the theorem is useful, but the proxy channels are not yet the
right invariant physical basis.

The next pass adds
`horizon_hauptvermutung_channels.py`, which computes one-birth proxies for the
certificate fields directly: local interval-dimension errors, relation-fraction
bias, interval-profile spread, count-window irregularity, and resolved-interval
mass.  Running the same null-cone machinery with `--basis hv` gives stronger
physical evidence but the same caveat:

```text
0.924 residual(-gap) + 0.381 residual(hv_big_interval_count):
  leakage  = -1.94e-03
  gap_slope = -7.875
```

Across the small `n=18,20`, two-seed check, HV channels keep large gap response
with leakage around `1e-3` to `5e-3`, but the coefficient still drifts.  The
correct next target is therefore a basis built from actual certificate errors
`countWindow`, `curvatureBias`, and `pairConsistency`, not just local interval
proxies.

That target is now implemented by `horizon_certificate_channels.py`.  With
`--basis cert`, the strongest small-sample lead is:

```text
cert_pairConsistency + 3.5035 residual(-gap):
  leakage  =  2.98e-05
  gap_slope = -7.652
```

The certificate-basis stability check then picks out
`cert_target4Distortion + residual(-gap)` as the best tracked low-leakage
candidate:

```text
mean|leak| = 4.90e-04
mean|gap|  = 7.66
```

The coefficient still drifts, so this is not yet a growth certificate.  It is,
however, the first search result expressed directly in the same error-channel
language as the quantitative Hauptvermutung bridge.

The Lean follow-up now turns that empirical target into a precise finite
interface.  A `ProtectedCertificateErrorSource` supplies a finite source `S`
with:

```text
Cov(S,J) = 0
Cov(J, centered(S)^2) = 0
linearResponse(S, certificateError) <= -descentRate
```

Lean proves that such a source has zero first-order horizon-area response,
zero finite second central horizon-area response, and negative
certificate-error response when `descentRate > 0`.  The refinement interface
allows the second-order leakage to tend to zero instead of vanishing at each
finite stage, and proves the second central area response tends to zero.
The theorem
`twoResidualChannel_protected_certificate_error_source_bridge` specializes this
to the residualized two-channel mixtures used by the null-cone scans.
The newer
`ProtectedHauptvermutungDistortionSource.preserves_horizon_and_descends_distortion`
specializes the certificate error further to the actual displayed
Hauptvermutung distortion observable
`(countWindow + curvatureBias + countWindow*curvatureBias)*scale
  + pairConsistency/2`.
The latest descent theorem adds the finite update gate:
`protected_distortion_step_decreases_with_remainder` proves the displayed
distortion strictly decreases when the finite remainder is below half the
protected descent margin, and
`ProtectedHauptvermutungDistortionDescent.distortion_tendsto_zero_of_geometric_bound`
records the geometric-contraction route to zero distortion.
The combined sequence theorem
`ProtectedHauptvermutungDistortionDescent.horizon_protection_and_distortion_tendsto_zero`
adds that the same descent sequence keeps the horizon response zero through
second order at every finite stage.

The original finite horizon-entropy theorem is stronger than a fit to the probe
output: for any normalized nonnegative finite birth law, the full
exponential-family KL derivative is exactly `-lambda` times the derivative of
expected one-birth horizon area.  This is the discrete algebraic core of the
Dorau-Much/Jacobson focusing step.  What remains outside the proof is the
analytic AQFT theorem identifying continuum Araki relative entropy with the
weighted null-energy flux.

Lean theorem names:

```text
hasDerivAt_expTiltExpectation
hasDerivAt_expTiltAreaExpectation
hasDerivAt_expTiltKL
finiteEntropyFocusing_deriv_identity
finiteEntropyFocusing_breakthrough
finiteEntropyFocusing_birthLaw_deriv_identity
```

## Finite Growth Kernel Bridge

The same Lean file now proves the finite normalization step for causal growth.
For a fixed parent state, a raw one-step kernel only needs nonnegative
transition weights and positive total weight:

```text
weight_i >= 0
sum_i weight_i > 0
--------------------------------
p_i = weight_i / sum_j weight_j
sum_i p_i = 1
```

It also proves that an exponential source tilt preserves the birth-law
conditions:

```text
q_lambda(i) = p_i exp(lambda J_i) / Z(lambda)
q_lambda(i) >= 0
sum_i q_lambda(i) = 1
```

Lean theorem names:

```text
FiniteCausalGrowthKernel.produces_birthLaw
FiniteCausalGrowthKernel.source_tilt_produces_birthLaw
FiniteCausalGrowthKernel.kernel_entropyFocusing_deriv_identity
FiniteCausalGrowthSystem.producesRequiredBirthLaws
FiniteCausalGrowthSystem.sourceTiltProducesRequiredBirthLaws
FiniteCausalGrowthSystem.entropyFocusing_at_parent
```

This closes the finite part of the bridge
`causalGrowthProducesRequiredBirthLaws`: any finite admissible-precursor
growth rule with nonnegative raw rates and nonzero total rate supplies exactly
the birth-law hypotheses required by the entropy-focusing theorem.  The
parent-indexed system theorem says this holds at every parent state, and the
entropy-focusing identity can be applied parent-by-parent.  The remaining part
is not normalization algebra; it is the physical classification of the
admissible precursor set and transition weights for the intended causal-growth
dynamics.

## Entropy-Flux Limit Bridge

New bridge file:

```text
UnifiedTheory/Audit/KFCausalCSpecEntropyFluxLimit.lean
```

This file starts closing the remaining continuum gap.  It proves that a scaled
finite horizon source converges to a continuum null/Araki flux whenever the
source admits an explicit vanishing error budget.

Core pattern:

```text
J_rho_scaled = J_rho / rho^p
J_rho = rho^p * (W + residual_rho)
residual_rho -> 0
--------------------------------
J_rho_scaled -> W
```

RSS/Poisson error-control form:

```text
|finiteScaledFlux_n - W| <= (epsilon_n + b_n + epsilon_n*b_n) * S
epsilon_n -> 0
b_n -> 0
--------------------------------
finiteScaledFlux_n -> W
```

Important theorem names:

```text
flat_rindler_scaledFlux_converges
finiteEntropySource_converges_to_ArakiFlux_of_errorControl
finiteEntropySource_converges_of_rssPoissonError
HorizonHitSourceEstimator.finiteScaledFlux_converges_to_continuumFlux
HorizonHitSourceEstimator.closes_ArakiFlux_bridge
entropyFluxLimitBridge_closes_first_field
```

The bridge now has a concrete physical horizon-cell interface.  A finite
refinement level `n` has density `rho_n`, a horizon-hit count in each cell, a
nonnegative cell weight, a continuum cell-flux target, and a vanishing per-cell
error estimate:

```text
|scaledHorizonSource(rho_n, p, hitCount_n(i)) - continuumCellFlux(i)|
  <= cellError_n(i)

cellError_n(i) -> 0
--------------------------------
sum_i weight_i * scaledHorizonSource_n(i)
  -> sum_i weight_i * continuumCellFlux(i)
```

If the weighted continuum cell flux is identified with the Araki null flux, the
proved theorem `HorizonHitSourceEstimator.closes_ArakiFlux_bridge` closes the
same `finiteEntropySourceConvergesToArakiFlux` slot.  The remaining work has
therefore narrowed from "make the finite source converge" to "prove the
per-cell vanishing error estimates for the actual causal-growth horizon
estimator."

Related Dorau-Much bridge:

`UnifiedTheory/Audit/KFCausalCSpecArakiHorizonRelativeEntropy.lean` proves the
scalar constant chain from the paper once its analytic horizon inputs are
exposed as named target propositions:

```text
S_rel = -2*pi*W
delta A = alpha/(2*pi) * S_rel
delta A = -R
S_rel = delta A/4
--------------------------------
R = 8*pi*W
```

The theorem
`bekensteinHawking_raychaudhuri_flux_balance_eight_pi` is the direct proved
version of that chain for nonzero excitations.  The same file also proves that
the null trace term drops, so this null-null balance supplies the equilibrium
input needed by the repository's existing Einstein-equation theorem.

## Path-Level Tilt

Script: `horizon_tilt_paths.py`

Command:

```bash
python3 horizon_tilt_paths.py --n 22 --paths 24 --starts 8 --a 0.20 --lambdas=-0.10,0.00,0.10 --seed 20260819 --paired
```

This applies the registered source at every birth:

```text
q_lambda(D) proportional to p(D) exp(lambda S_*(D)).
```

Paired mode uses the same quantile sequence for baseline and tilted paths.

Result:

```text
N=22, paths=24, paired=True

lambda   frontier      r        height   rank_w    action      KL       N0       N1       N2
-0.100      4.833     0.5492    6.208    5.500    14.917    0.0959    2.104    1.301    0.636
+0.000      4.625     0.5595    6.125    5.917    15.750    0.0000    2.078    1.307    0.655
+0.100      4.375     0.5853    6.708    5.292     4.583    0.1108    2.095    1.225    0.729

paired shifts vs baseline:

lambda   dFrontier      dr        dHeight    dAction     dN0       dN1       dN2
-0.100   +0.208±0.225  -0.0103±0.0058  +0.083±0.133   -0.833±6.443  +0.027±0.045  -0.006±0.046  -0.019±0.045
+0.100   -0.250±0.193  +0.0258±0.0078  +0.583±0.180  -11.167±8.098  +0.017±0.041  -0.081±0.067  +0.074±0.034
```

Local interval dimension:

```text
lambda   d_all    d_k~4    d_k~8
-0.100    2.374    2.388    2.324
+0.000    2.353    2.401    2.201
+0.100    2.231    2.243    2.208

paired local-dimension shifts:

-0.100: dAll +0.021±0.058, d4 -0.013±0.069, d8 +0.137±0.056
+0.100: dAll -0.122±0.044, d4 -0.158±0.053, d8 +0.004±0.036
```

Interpretation:

The one-step source survives path composition.  Positive source tilt decreases
the final frontier size, increases ordering fraction and height, and shifts the
UV interval census toward larger `N2`.  The action shift has the right sign but
needs larger samples; at this sample size it is still noisy.

This is a stress/focusing deformation, not a manifold-likeness improvement by
itself: increasing `r` and height moves the causet more chainlike.  That is
consistent with positive null energy focusing.  The local interval-dimension
diagnostic confirms it: positive tilt lowers `d_all` and small-interval `d4`.
So `S_*` is now best read as a finite stress/focusing source, not as a
dimension-raising source.
