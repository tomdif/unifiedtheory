# Horizon-Orthogonal Least-Defect Growth

Date: 2026-08-20

Lean files:

```text
UnifiedTheory/Audit/KFCausalCSpecHorizonOrthogonalDefect.lean
UnifiedTheory/Audit/KFCausalCSpecBridgeDefectObservable.lean
```

Context paper:

Philipp Dorau and Albert Much, "From Quantum Relative Entropy to the
Semiclassical Einstein Equations," arXiv:2510.24491v3 [hep-th],
Phys. Rev. Lett. 136, 091602 (2026), DOI: 10.1103/lmq8-nsty,
arXiv DOI: 10.48550/arXiv.2510.24491.

## New Idea

The horizon-hit source `J` is the exact finite focusing channel.  A generic
geometry or Hauptvermutung-defect source `G` can accidentally contain a
horizon component, so mixing `G` into the growth law can double-count the same
entropy channel.

The new rule is:

```text
G_perp = G - Cov(G,J)/Var(J) * J
S(thetaH,thetaD) = thetaH * J + thetaD * G_perp
```

Use `J` only for horizon entropy focusing, and use `G_perp` for independent
defect repair.

## What Is Proved

For any finite normalized birth law with `Var(J) != 0`, Lean proves:

```text
Cov(G_perp,J) = 0
```

and therefore:

```text
linearResponse(S(thetaH,thetaD), c - J) = -thetaH * Var(J).
```

The defect-repair coefficient `thetaD` drops out exactly at first order.
This is not a fitted numerical fact; it is finite covariance algebra.

The formal theorem also proves uniqueness of the projection coefficient:
`Cov(G - aJ,J) = 0` forces

```text
a = Cov(G,J)/Var(J).
```

So the residual used above is the unique covariance projection that removes
first-order horizon contamination.

## Deeper Result: Second-Order Leakage

Looking one order deeper, first-order orthogonality is not the end of the
story.  Lean now defines the finite second central response numerator

```text
quadraticResponse(S, X) = Cov(X, centered(S)^2)
```

and proves the exact horizon-area formula

```text
quadraticResponse(S, c - J) = -Cov(J, centered(S)^2).
```

For an already horizon-orthogonal source `S`, the first-order area response is
zero, and the remaining second-order obstruction is precisely

```text
horizonSecondOrderLeakage(J,S) = Cov(J, centered(S)^2).
```

Therefore a stronger protected defect source must satisfy two conditions:

```text
Cov(S,J) = 0
Cov(J, centered(S)^2) = 0
```

The first condition removes linear horizon contamination.  The second removes
quadratic horizon leakage.

The theorem also polarizes this leakage into a quadratic form.  For two
first-order-clean defect channels `A` and `B`,

```text
Leak(aA + bB)
  = a^2 Leak(A,A) + 2ab Leak(A,B) + b^2 Leak(B,B).
```

So the second-order breakthrough target is a leakage null cone: find two or
more Hauptvermutung-repair directions that are individually orthogonal to `J`
and choose coefficients that make this quadratic form vanish.  Lean proves
that any such mixture has zero first-order area response and zero finite
second central area response.

The file also proves a certificate version of this null-cone statement: if the
mixture descends a named certificate-error observable, then horizon protection
and certificate descent hold simultaneously.  A residual-channel specialization
applies after projecting two raw defect observables off the horizon source.

The newest concrete specialization applies this same finite control layer to
the private-marker bridge poset.  The global order incidence recovers edge
transport, which lets Lean define a bridge-census defect directly from the
shifted continuation profile.  The canonical transport has defect zero, every
noncanonical transport has positive defect, and the recovered incidence
relation identifies the transported atom.  The pair-consistency-only displayed
Hauptvermutung distortion proxy is then proved equal to this defect, so the
canonical residual-gradient and corrected-source bridge now descend an
order-derived CSpec target rather than only an abstract certificate error.
A finite population version proves the summed bridge-census distortion is
nonnegative and vanishes exactly when every candidate transport is the
order-recovered one.  The aggregate `physicalHauptvermutungDistortion` then
adds count-window, curvature-bias, and spectral-locality defects; under
nonnegative component hypotheses, total zero forces every component to vanish
and the transport candidate family to be canonical.  The bridge component is a
strict minimizer inside that aggregate, and `PhysicalGrowthSuppliesRepairSource`
packages the horizon-protected half-remainder contraction gate that the actual
physical growth law must instantiate.  `PhysicalGrowthRepairRefinement` records
that gate across a refinement sequence and proves every certified finite step
has zero first-order and second central horizon-area response while satisfying
`D_{n+1} < D_n`.  Under a geometric majorant `D_n <= D_0*q^n`,
`0 <= q < 1`, it also proves `D_n -> 0`.  The step-factor version derives
that majorant from `D_{n+1} <= q * D_n`; the relative-margin version derives
that step factor from `(1 - q)*D_n <= step_n*descentRate_n/2`; the
descent-budget version packages the same condition as
`2*(1 - q)*D_n <= step_n*descentRate_n`; the rate-floor version derives that
budget from `rateFloor_n*D_n <= descentRate_n` and
`2*(1 - q) <= step_n*rateFloor_n`; the uniform version derives convergence
with `q = 1 - stepFloor*gamma/2` from `gamma*D_n <= descentRate_n`,
`stepFloor <= step_n`, and `0 < stepFloor*gamma <= 2`, reducing the next
physical target to that uniform package for the actual growth law, or to the
nonuniform product-decay replacement `Product_{k<n} q_k -> 0` for variable
factors `q_n = 1 - step_n*rateFloor_n/2`.  The newest uniform-bound bridge
derives that product decay from `0 <= q_n <= qBound < 1`.  The newest
gain-window gate derives this bound from `0 < beta`,
`beta <= step_n*rateFloor_n`, and `step_n*rateFloor_n <= 2`.  The newest
physical-total version discharges the external `D_n >= 0` side condition when
`D_n` is exactly the displayed physical aggregate with nonnegative component
observables.  The newest local-descent version replaces the global
`rateFloor_n*D_n <= descentRate_n` assumption with finite per-cell descent
certificates whose sum is `descentRate_n`.  The newest uniform local-rate
version derives convergence from those local certificates together with
`gamma <= rateFloor_n`, `stepFloor <= step_n`, and
`0 < stepFloor*gamma <= 2`.  The newest source-local version identifies those
certificates with the actual source's per-cell negative first-order response
contributions and proves they sum to `-linearResponse(S_n, D_n)`.  The newest
centered-source floor gate derives those cellwise bounds from
`rateFloor_n <= -w_{n,i}*centered(S_n)_i`.  The newest weighted anti-alignment
gate splits that into nonnegative weights, a weighted rate floor, and
`alignment_{n,i} <= -centered(S_n)_i`.  The newest uniform weighted-alignment
gate derives the weighted rate floor from uniform lower bounds on sampling
weight and anti-alignment amplitude.  The newest rate-floor-free gate replaces
`rateFloor_n` with the direct uniform bound
`gamma <= weightFloor*alignmentFloor`.  The newest direct centered-source
floor gate removes the auxiliary alignment observable and proves the same
theorem from `gamma <= weightFloor*sourceFloor`,
`weightFloor <= w_{n,i}`, and
`sourceFloor <= -centered(S_n)_i`.  The newest gamma-free product gate sets
the rate constant to `weightFloor*sourceFloor` itself and only requires
`0 < stepFloor*(weightFloor*sourceFloor) <= 2`.  The newest positive-floor
gate derives that strict positivity from
`0 < stepFloor`, `0 < weightFloor`, and `0 < sourceFloor`.  The newest
clipped-rate gate removes the product upper-bound side condition by using the
effective rate `min (weightFloor*sourceFloor) (1/stepFloor)`, so the stability
product is automatically at most `1`.  The newest stagewise clipped-rate gate
removes global uniformity at this layer and proves convergence from positive
stage-dependent weight/source floors plus decay of the corresponding clipped
contraction-factor product.  The newest clipped-gain gate derives that decay
from a uniform positive lower bound
`beta <= step_n*min(weightFloor_n*sourceFloor_n, 1/step_n)`.  The newest
unclipped-gain gate derives that clipped bound from `beta <= 1` and
`beta <= step_n*(weightFloor_n*sourceFloor_n)`.

## Lean Names

```text
rawDefect_eq_projection_plus_residual
covariance_horizonOrthogonalResidual_self
horizonProjectionCoeff_unique
orthogonal_source_area_response_zero
quadraticResponse_finiteAreaChange_eq_neg_leakage
orthogonal_source_secondOrder_area_obstruction
orthogonal_source_firstAndSecondOrder_area_zero
horizonSecondOrderLeakage_linear_combination
twoChannel_firstAndSecondOrder_area_zero
twoChannel_protected_certificate_error_source_bridge
twoChannel_certificate_error_response_negative
twoResidualChannel_protected_certificate_error_source_bridge
horizonOrthogonalResidual_area_response_zero
horizonOrthogonalResidual_secondOrder_area_obstruction
horizonOrthogonalResidual_firstAndSecondOrder_area_zero
combined_orthogonal_area_response
combined_horizonOrthogonal_area_response
HorizonOrthogonalDefectCertificate.residual_orthogonal
HorizonOrthogonalDefectCertificate.residual_secondOrder_area_obstruction
HorizonOrthogonalDefectCertificate.residual_firstAndSecondOrder_area_zero
HorizonOrthogonalDefectCertificate.leastDefectSource_preserves_horizon_focusing
HorizonOrthogonalDefectCertificate.leastDefectSource_secondOrder_area_obstruction
ProtectedCertificateErrorSource.preserves_horizon_through_secondOrder
ProtectedCertificateErrorSource.certificate_error_response_negative
ProtectedCertificateErrorSource.protected_certificate_error_source_bridge
ProtectedCertificateErrorRefinement.first_area_response_zero
ProtectedCertificateErrorRefinement.quadratic_area_response_tendsto_zero
ProtectedCertificateErrorRefinement.certificate_error_response_negative
linearResponse_neg_source
horizonSecondOrderLeakage_neg_source
horizonOrthogonalResidual_linearResponse_rawDefect
canonicalHorizonInvisibleDescentSource_orthogonal
canonicalHorizonInvisibleDescentSource_response_rawDefect
canonicalHorizonInvisibleDescentSource_strictly_descends_rawDefect
canonicalHorizonInvisibleDescentSource_area_response_zero
canonicalHorizonInvisibleDescentSource_secondOrder_area_obstruction
canonicalHorizonInvisibleDescentSource_protected_certificate_bridge
correctedCanonicalHorizonInvisibleDescentSource_orthogonal
correctedCanonicalHorizonInvisibleDescentSource_response_rawDefect
correctedCanonicalHorizonInvisibleDescentSource_descends_rawDefect
correctedCanonicalHorizonInvisibleDescentSource_protected_bridge
bridgeCensusDefect_canonical_zero
bridgeCensusDefect_pos_of_ne
bridgeCensusDefect_eq_zero_iff
bridgeCensusDefect_zero_and_orderRecovered
cSpecBridgeHauptvermutungDistortion_eq_defect
cSpecBridgeHauptvermutungDistortion_zero_iff
cSpecBridgeTotalDistortion_eq_zero_iff
cSpecBridgeTotalDistortion_pos_iff_candidate_ne_canonical
cSpecBridgeTotalDistortion_canonical_min
cSpecBridgeTotalDistortion_strict_min_of_ne
cSpecBridgeTotalDistortion_zero_orderRecovered
cSpecBridge_canonicalSource_descends_distortion
cSpecBridge_canonicalSource_area_response_zero
cSpecBridge_correctedSource_protected_bridge
physicalHauptvermutungTotalDistortion_eq_zero_iff
physicalHauptvermutungTotalDistortion_strict_transport_min_of_ne
physicalHauptvermutungTotalDistortion_pos_of_transport_ne_canonical
physicalGrowthSuppliesRepairSource_protected_and_contracts
physicalGrowthSuppliesRepairSource_step_factor_of_relative_margin
physicalGrowthSuppliesRepairSource_step_factor_of_descent_budget
physicalGrowthSuppliesRepairSource_descent_budget_of_rate_floor
physicalGrowthSuppliesRepairSource_step_factor_of_rate_floor
physicalGrowthRepairRefinement_protected_and_contracts
physicalGrowthRepairRefinement_horizon_protection_and_total_tendsto_zero
physicalGrowthRepairRefinement_step_factor_of_relative_margin
physicalGrowthRepairRefinement_step_factor_of_descent_budget
physicalGrowthRepairRefinement_descent_budget_of_rate_floor
physicalGrowthRepairRefinement_step_factor_of_rate_floor
physicalGrowthRepairRefinement_step_factor_of_variable_rate_floor
physicalGrowthRepairRefinement_step_factor_of_explicit_variable_rate_floor
physicalGrowthRepairRefinement_step_factor_of_uniform_rate_floor
physicalGrowthRepairRefinement_product_bound_of_step_factors
physicalGrowthRepairRefinement_product_bound_of_factor_le
physicalGrowthRepairRefinement_total_tendsto_zero_of_product_bound
physicalGrowthRepairRefinement_product_majorant_tendsto_zero_of_factor_le
physicalGrowthRepairRefinement_total_tendsto_zero_of_variable_step_factor_product
physicalGrowthRepairRefinement_total_tendsto_zero_of_variable_step_factor_uniform_bound
physicalGrowthRepairRefinement_horizon_protection_and_total_tendsto_zero_of_step_factor
physicalGrowthRepairRefinement_horizon_protection_and_total_tendsto_zero_of_variable_step_factor_product
physicalGrowthRepairRefinement_horizon_protection_and_total_tendsto_zero_of_variable_step_factor_uniform_bound
physicalGrowthRepairRefinement_horizon_protection_and_total_tendsto_zero_of_relative_margin
physicalGrowthRepairRefinement_horizon_protection_and_total_tendsto_zero_of_descent_budget
physicalGrowthRepairRefinement_horizon_protection_and_total_tendsto_zero_of_rate_floor
physicalGrowthRepairRefinement_horizon_protection_and_total_tendsto_zero_of_uniform_rate_floor
physicalGrowthRepairRefinement_horizon_protection_and_total_tendsto_zero_of_explicit_uniform_rate_floor
physicalGrowthRepairRefinement_horizon_protection_and_total_tendsto_zero_of_variable_rate_floor_product
physicalGrowthRepairRefinement_horizon_protection_and_total_tendsto_zero_of_explicit_variable_rate_floor_product
physicalGrowthRepairRefinement_horizon_protection_and_total_tendsto_zero_of_explicit_variable_rate_floor_uniform_bound
physicalGrowthRepairRefinement_explicit_factor_bounds_of_gain_floor
physicalGrowthRepairRefinement_horizon_protection_and_total_tendsto_zero_of_variable_gain_floor
physicalHauptvermutungTotalDistortion_sequence_nonneg
physicalGrowthRepairRefinement_horizon_protection_and_total_tendsto_zero_of_physical_total_variable_gain_floor
physicalHauptvermutungTotalDistortion_rate_floor_of_local_descent
physicalGrowthRepairRefinement_horizon_protection_and_total_tendsto_zero_of_local_physical_variable_gain_floor
physicalHauptvermutungTotalDistortion_uniform_rate_floor_of_local_descent
physicalGrowthRepairRefinement_horizon_protection_and_total_tendsto_zero_of_local_physical_uniform_rate_floor
localLinearDescentContribution
sum_localLinearDescentContribution_eq_neg_linearResponse
physicalHauptvermutungTotalDistortion_uniform_rate_floor_of_source_local_response
physicalGrowthRepairRefinement_horizon_protection_and_total_tendsto_zero_of_source_local_physical_uniform_rate_floor
physicalHauptvermutungDistortion_source_local_response_of_centered_source_floor
physicalGrowthRepairRefinement_horizon_protection_and_total_tendsto_zero_of_centered_source_floor
centeredSource_floor_of_weighted_anti_alignment
physicalGrowthRepairRefinement_horizon_protection_and_total_tendsto_zero_of_weighted_anti_alignment
weighted_floor_of_uniform_weight_alignment
physicalGrowthRepairRefinement_horizon_protection_and_total_tendsto_zero_of_uniform_weighted_anti_alignment
centeredSource_gamma_floor_of_uniform_weighted_alignment
centeredSource_gamma_floor_of_uniform_centered_source_floor
centeredSource_rate_floor_of_stagewise_centered_source_floor
physicalHauptvermutungTotalDistortion_rate_floor_of_centered_source_floor
physicalHauptvermutungTotalDistortion_uniform_rate_of_source_local_response
physicalHauptvermutungTotalDistortion_uniform_rate_of_centered_source_floor
physicalGrowthRepairRefinement_horizon_protection_and_total_tendsto_zero_of_uniform_weight_alignment_floor
physicalGrowthRepairRefinement_horizon_protection_and_total_tendsto_zero_of_uniform_centered_source_floor
physicalGrowthRepairRefinement_horizon_protection_and_total_tendsto_zero_of_uniform_centered_source_product_floor
physicalGrowthRepairRefinement_horizon_protection_and_total_tendsto_zero_of_positive_uniform_centered_source_product_floor
physicalGrowthRepairRefinement_horizon_protection_and_total_tendsto_zero_of_positive_uniform_centered_source_clipped_rate_floor
physicalGrowthRepairRefinement_horizon_protection_and_total_tendsto_zero_of_stagewise_centered_source_clipped_rate_product
physicalGrowthRepairRefinement_horizon_protection_and_total_tendsto_zero_of_stagewise_centered_source_clipped_gain_floor
physicalGrowthRepairRefinement_horizon_protection_and_total_tendsto_zero_of_stagewise_centered_source_unclipped_gain_floor
linearResponse_orientTowardObservable_eq_neg_abs
covariance_orientTowardObservable_horizon
horizonSecondOrderLeakage_orientTowardObservable
oriented_response_negative_of_nonzero
linearResponse_hauptvermutungDistortionObservable
componentResponses_descend_hauptvermutungDistortionObservable
ProtectedHauptvermutungDistortionSource.preserves_horizon_and_descends_distortion
ProtectedHauptvermutungDistortionSource.distortion_response_negative
ProtectedHauptvermutungDistortionSource.distortion_response_expands
orientedProtectedHauptvermutungDistortionSource_descentRate_positive
orientedProtectedHauptvermutungDistortionSource_bridge
componentResponses_protected_distortion_bridge
protected_distortion_step_decreases_with_remainder
protected_distortion_step_strictly_decreases
distortion_geometric_majorant_tendsto_zero
ProtectedHauptvermutungDistortionDescent.step_decreases
ProtectedHauptvermutungDistortionDescent.step_strictly_decreases
ProtectedHauptvermutungDistortionDescent.distortion_tendsto_zero_of_geometric_bound
ProtectedHauptvermutungDistortionDescent.step_preserves_horizon_through_secondOrder
ProtectedHauptvermutungDistortionDescent.first_area_response_zero
ProtectedHauptvermutungDistortionDescent.quadratic_area_response_tendsto_zero
ProtectedHauptvermutungDistortionDescent.horizon_protection_and_distortion_tendsto_zero
```

## Why This Matters

The previous horizon probe found that an orthogonalized bulk/action channel
keeps nearly all of the horizon-focusing slope while adding a much stronger
gap/action response.  This file proves the exact first-order mechanism behind
that observation.

In physics terms: the growth law can have a protected entropy/focusing knob
and an independent geometry-repair knob.  If the second knob is projected
orthogonally to the horizon source, it does not renormalize the Dorau--Much
entropy-to-area channel at first order.

This does not prove full continuum quantum gravity.  It gives a sharper target
for the remaining physical dynamics: construct the actual causal-growth defect
source `G`, project it to `G_perp`, and prove that the resulting tilted growth
law improves the Hauptvermutung/continuum certificate while preserving the
horizon flux bridge.

## Next Experiment

Replace the current proxy `std(-gap)` in the horizon-mix scan by a direct
Hauptvermutung-defect observable:

```text
G = local chart distortion gradient
  + curvature-volume bias gradient
  + pairwise chart-consistency gradient
```

Then use the proved projection:

```text
G_perp = G - Cov(G,J)/Var(J) * J
```

and scan the finite growth tilt

```text
S = thetaH * J + thetaD * G_perp.
```

The success criterion is now clean:

```text
horizon area response stays fixed by thetaH
Hauptvermutung distortion decreases with thetaD
```

That is the concrete path from the Dorau--Much horizon entropy bridge toward a
causal-growth law that repairs continuum geometry without spoiling the
first-order horizon focusing channel.

## Leakage Probe

Script:

```bash
python3 horizon_second_order_leakage.py --n 18 --paths 8 --burn 5 --starts 8 --coeffs 0.20,0.30,0.45
```

Sample result:

```text
source        first_area        quad_area        leakage       quad+leak   gap_slope  focus_ret
residual       2.23e-17         -6.11e-02        6.11e-02      4.97e-18   -6.808     -0.0000
J+aR a=0.20   -8.25e-01         -6.57e-01        6.57e-01      9.07e-18   -1.354      0.9806
J+aR a=0.30   -8.06e-01         -6.46e-01        6.46e-01      7.57e-18   -1.975      0.9578
J+aR a=0.45   -7.67e-01         -6.13e-01        6.13e-01      9.47e-18   -2.812      0.9119
```

The `quad+leak` column is the numerical check of the Lean identity
`quadraticResponse(S,c-J) = -horizonSecondOrderLeakage(J,S)`.  On this sample,
the projected residual has no first-order area response but a small negative
second central area response.  That suggests a stronger search target: among
Hauptvermutung-repair sources, minimize or tune the leakage term while keeping
the gap/distortion response large.

## Null-Cone Scan

Script:

```bash
PYTHONDONTWRITEBYTECODE=1 python3 horizon_leakage_nullcone_scan.py --n 20 --paths 12 --burn 5 --starts 8 --tmin -2 --tmax 2 --step 0.05 --top 8
```

This scans residualized channels

```text
-gap, interior_bdg, h0, h1, h2, size
```

where each channel is first projected off `J`.  For each pair it estimates the
mean leakage quadratic form and evaluates both grid coefficients and the
quadratic roots.

Sample result:

```text
Top by score:

pair             t       first_area    quad_area    leakage      quad+leak   gap_slope
-gap+h2          0.003   1.01e-17      6.54e-05    -6.54e-05     4.75e-18   -7.459
-gap+h1         -0.750   6.88e-18     -1.89e-04     1.89e-04    -4.17e-18   -7.191
h0+h2            1.000   1.18e-17     -3.48e-04     3.48e-04     3.61e-18   -5.825
```

Interpretation:

* the first-order area response is still numerically zero;
* the identity `quad_area + leakage = 0` holds to floating precision;
* sample-mean leakage can be tuned close to zero while retaining a large
  defect/gap response;
* the best compensating channel is sample-dependent at this size, so this is a
  search lead, not a physical certificate.

The concrete next target is now narrower: find a stable physical
Hauptvermutung-defect basis whose leakage quadratic form has a robust null
direction in the refinement limit, not just on finite sampled parents.

## Stability And Multi-Channel Checks

Stability command:

```bash
PYTHONDONTWRITEBYTECODE=1 python3 horizon_nullcone_stability.py --depths 18,20 --seeds 53,157 --paths 8 --burn 5 --starts 8 --tmin -2 --tmax 2 --step 0.10
```

Result:

```text
Tracked pair stability:
pair       mean|leak|   mean|gap|   mean t   std t
-gap+h2     1.33e-03    5.55e+00   -0.480   0.488
-gap+h1     5.08e-03    6.63e+00    1.623   1.973
-gap+h0     2.30e-03    6.82e+00    0.311   0.307
h0+h2       1.01e-03    4.55e+00    0.679   0.812
h1+size     5.66e-03    6.66e+00   -0.079   0.191
```

Interpretation: the existence of low-leakage directions is stable, but the
best pair and coefficient are not stable at this sample size.

Multi-channel command:

```bash
PYTHONDONTWRITEBYTECODE=1 python3 horizon_multichannel_nullcone_search.py --n 20 --paths 8 --burn 5 --starts 8 --directions 600 --top 8
```

Best score on that run:

```text
+0.993 residual(-gap) + 0.120 residual(h2):
  leakage  = -1.67e-03
  gap_slope = -7.388
```

The multi-channel random search did not reveal a clearly better stable
high-dimensional direction.  Its best high-gap results were still effectively
pair-like.  That suggests the next serious basis should be physical rather
than broad: use channels tied directly to Hauptvermutung certificate defects
instead of generic shell-count proxies.

## Hauptvermutung-Basis Probe

The next scan replaces generic shell proxies with finite one-birth proxies for
the physical-growth certificate fields:

```text
hv_dim4_err            local interval-dimension error against d=4
hv_dim2_err            local interval-dimension error against d=2
hv_rel4_abs            relation-fraction bias against the 4D calibration
hv_rel2_abs            relation-fraction bias against the 2D calibration
hv_dim_spread          local interval-profile spread
hv_logk_spread         count-window / scale-window irregularity
hv_interval_mass       number of resolved local intervals
hv_big_interval_count  number of k>=8 local intervals
```

Implementation:

```text
horizon_hauptvermutung_channels.py
```

Small HV-basis scan:

```bash
PYTHONDONTWRITEBYTECODE=1 python3 horizon_leakage_nullcone_scan.py --basis hv --n 18 --paths 4 --burn 5 --starts 8 --tmin -2 --tmax 2 --step 0.10 --top 8
```

Representative high-score candidates:

```text
hv_dim_spread + 4.467 residual(-gap):
  leakage  = -1.44e-03
  gap_slope = -7.759

hv_logk_spread - 4.705 residual(-gap):
  leakage  = -2.81e-03
  gap_slope =  7.776

hv_big_interval_count - 5.247 residual(-gap):
  leakage  = -4.35e-03
  gap_slope =  8.297
```

HV stability command:

```bash
PYTHONDONTWRITEBYTECODE=1 python3 horizon_nullcone_stability.py --basis hv --depths 18,20 --seeds 53,157 --paths 4 --burn 5 --starts 8 --tmin -2 --tmax 2 --step 0.10 --track hv_dim_spread:-gap,hv_logk_spread:-gap,hv_big_interval_count:-gap,hv_dim2_err:-gap,hv_rel2_abs:-gap
```

Tracked HV-pair averages:

```text
hv_dim_spread + -gap:           mean|leak|=2.41e-03, mean|gap|=7.81, std(t)=4.07
hv_logk_spread + -gap:          mean|leak|=3.76e-03, mean|gap|=7.95, std(t)=1.28
hv_dim2_err + -gap:             mean|leak|=4.51e-03, mean|gap|=7.23, std(t)=2.64
hv_rel2_abs + -gap:             mean|leak|=1.52e-03, mean|gap|=6.96, std(t)=2.52
```

HV multi-channel command:

```bash
PYTHONDONTWRITEBYTECODE=1 python3 horizon_multichannel_nullcone_search.py --basis hv --n 20 --paths 4 --burn 5 --starts 8 --directions 600 --top 8
```

Best high-score output:

```text
0.924 residual(-gap) + 0.381 residual(hv_big_interval_count):
  leakage  = -1.94e-03
  gap_slope = -7.875
```

Interpretation: the null-cone mechanism survives when the defect basis is
moved closer to the Hauptvermutung certificate fields.  However, the
coefficient still moves substantially across seeds and depths.  The likely
missing ingredient is not more random directions; it is a better invariant
physical basis, probably built from the actual certificate errors
`countWindow`, `curvatureBias`, and `pairConsistency` rather than these
one-birth interval proxies.

## Certificate-Error Basis

The next pass implements one-birth proxy estimators named after the actual
certificate errors:

```text
horizon_certificate_channels.py

cert_countWindow
cert_curvatureBias
cert_pairConsistency
cert_distortionBound
cert_scaledDistortionBound
cert_target4Distortion
cert_target2Distortion
```

The finite proxy bound is modeled on the Lean certificate formula:

```text
distortion ~= countWindow + curvatureBias + countWindow*curvatureBias
              + pairConsistency/2.
```

Small certificate-basis scan:

```bash
PYTHONDONTWRITEBYTECODE=1 python3 horizon_leakage_nullcone_scan.py --basis cert --n 18 --paths 4 --burn 5 --starts 8 --tmin -2 --tmax 2 --step 0.10 --top 8
```

Best sample lead:

```text
cert_pairConsistency + 3.5035 residual(-gap):
  first_area =  1.77e-17
  leakage    =  2.98e-05
  gap_slope  = -7.652
```

This is the strongest single-run null-cone candidate so far: it uses a named
certificate proxy, keeps first-order horizon response zero, almost cancels the
second central leakage, and retains a large gap/action response.

Certificate-basis stability:

```bash
PYTHONDONTWRITEBYTECODE=1 python3 horizon_nullcone_stability.py --basis cert --depths 18,20 --seeds 53,157 --paths 4 --burn 5 --starts 8 --tmin -2 --tmax 2 --step 0.10
```

Tracked averages:

```text
cert_target4Distortion + -gap:
  mean|leak| = 4.90e-04
  mean|gap|  = 7.66
  std(t)     = 3.29

cert_pairConsistency + -gap:
  mean|leak| = 1.46e-03
  mean|gap|  = 7.71
  std(t)     = 3.27

cert_curvatureBias + -gap:
  mean|leak| = 2.08e-03
  mean|gap|  = 7.50
  std(t)     = 2.77
```

Certificate multi-channel search:

```bash
PYTHONDONTWRITEBYTECODE=1 python3 horizon_multichannel_nullcone_search.py --basis cert --n 20 --paths 4 --burn 5 --starts 8 --directions 600 --top 8
```

Representative output:

```text
0.885 residual(-gap) + 0.466 residual(cert_target2Distortion):
  leakage  = -8.88e-04
  gap_slope = -7.612

-0.862 residual(-gap) + 0.507 residual(cert_target4Distortion):
  leakage  =  7.03e-04
  gap_slope =  7.049

mixed certificate/action direction:
  leakage  =  4.90e-04
  gap_slope =  7.311
```

Interpretation: moving from shell proxies to named certificate-error proxies
improves the conceptual match and gives the best low-leak/high-gap candidates
so far.  The coefficient drift remains; this is evidence for the shape of the
certificate source, not a finished physical-growth certificate.

## Formal Certificate-Source Interface

The formal target suggested by the certificate-basis scan is now stated in
Lean.  A `ProtectedCertificateErrorSource` packages one finite parent-state
source with:

```text
Cov(S,J) = 0
Cov(J, centered(S)^2) = 0
linearResponse(S, certificateError) <= -descentRate
```

Lean proves that those three hypotheses imply the combined bridge statement:

```text
linearResponse(S, c - J) = 0
quadraticResponse(S, c - J) = 0
linearResponse(S, certificateError) <= -descentRate
```

If `descentRate > 0`, the certificate-error response is strictly negative.
This is the clean finite formulation of the breakthrough target: a growth
source can repair a Hauptvermutung certificate while preserving the
Dorau--Much horizon channel through the finite second central response.

The residualized two-channel scan has its own checked bridge theorem:

```text
twoResidualChannel_protected_certificate_error_source_bridge
```

It says that two raw defect observables can first be projected to residuals;
if their residual mixture lies on the leakage null cone and descends the named
certificate error, then the same finite horizon/certificate bridge follows.
This is the theorem-level version of scanning mixtures like
`cert_pairConsistency + residual(-gap)`.

## Hauptvermutung Distortion Observable

The generic certificate-error interface is now specialized to the actual
quantitative-Hauptvermutung distortion formula used by the physical bridge:

```text
Dist = (countWindow + curvatureBias + countWindow*curvatureBias) * scale
       + pairConsistency/2.
```

Lean defines the corresponding one-birth observable and proves its response
decomposition:

```text
linearResponse(S, Dist)
  = scale * (linearResponse(S, countWindow)
             + linearResponse(S, curvatureBias)
             + linearResponse(S, countWindow*curvatureBias))
    + linearResponse(S, pairConsistency)/2.
```

The new `ProtectedHauptvermutungDistortionSource` theorem says: if a source is
first-order horizon-orthogonal, has zero second-order horizon leakage, and
descends this whole distortion observable, then it preserves the Dorau--Much
horizon channel through second order while improving the actual displayed
Hauptvermutung distortion bound.  This is stronger than the previous generic
interface because the certificate error is no longer abstract.

## Local Orientation

The descent-gate probe showed that the useful source should be allowed to
choose a sign at each parent state.  Lean now proves that this local sign
choice is algebraically safe.  Define

```text
orientTowardObservable(w,S,X) =
  if linearResponse(w,S,X) <= 0 then S else -S.
```

Then Lean proves:

```text
linearResponse(orientTowardObservable(w,S,X), X)
  = -abs(linearResponse(w,S,X)).
```

So any nonzero raw response becomes a strict descent direction.  The same sign
orientation preserves horizon orthogonality and second-order leakage:

```text
Cov(orient(S), J) = 0         if Cov(S,J) = 0
Leak(J, orient(S)) = Leak(J,S)
```

Consequently an oriented raw source whose leakage is zero becomes a
`ProtectedHauptvermutungDistortionSource` with descent rate equal to the
absolute raw distortion response.  This is the formal version of the
`--local-sign` gate probe.

The latest corollary packages the locally oriented source directly:

```text
orientedProtectedHauptvermutungDistortionSource_bridge
```

It is the finite theorem behind the current new-physics lead in
[`HORIZON_INVISIBLE_GEOMETRIC_RELAXATION.md`](HORIZON_INVISIBLE_GEOMETRIC_RELAXATION.md):
a state-dependent geometry-repair channel can descend the displayed
Hauptvermutung distortion observable while staying invisible to the
Dorau--Much horizon-area response through second order.

## Canonical Residual Attack

The current attack removes one arbitrary choice.  For a certificate observable
`G`, define the canonical repair direction

```text
S_can = -horizonOrthogonalResidual(w,J,G).
```

Lean proves:

```text
linearResponse(S_can,G)
  = -variance(horizonOrthogonalResidual(w,J,G)).
```

Thus, when the residual variance is positive, the canonical source strictly
descends `G` and has zero first-order horizon-area response.  Lean also proves
that its remaining second central area response is exactly the residual
gradient's second-order horizon leakage.  If that leakage vanishes, the
canonical source is a fully protected finite certificate descent source.

Key theorem names:

```text
canonicalHorizonInvisibleDescentSource_response_rawDefect
canonicalHorizonInvisibleDescentSource_area_response_zero
canonicalHorizonInvisibleDescentSource_secondOrder_area_obstruction
canonicalHorizonInvisibleDescentSource_protected_certificate_bridge
correctedCanonicalHorizonInvisibleDescentSource_protected_bridge
```

Numerically, the pure canonical source
`residual(cert_scaledDistortionBound)` descends
`cert_scaledDistortionBound` on 35/35 sampled seed-53 parents and passes the
half-remainder gate through step `0.050`, but has nonzero mean leakage
`4.77e-01`.  Adding the null-cone correction
`3.5 residual(-gap)` reduces sample-mean leakage to `-7.41e-04`; with local
orientation the corrected source descends 35/35 seed-53 parents and 33/33
seed-157 parents, passing the gate through step `0.050` on both samples.
The same corrected source also passes a deeper `n=20`, `paths=2` check on
both seed 53 and seed 157, descending 20/20 parents in each sample.

The follow-up script

```text
horizon_corrected_canonical_scan.py
```

estimates the leakage-null coefficient directly.  On the higher-statistics
`n=18`, `paths=4` check, seeds 53 and 157 give coefficient magnitudes
`3.67279` and `3.55183`, with mean absolute leakage `3.15e-3`.  On the lower
`paths=2`, `depths=18,20` scan the root is noisier, but the local gate still
passes all small-step rows.  The next mathematical target is coefficient
stability: prove that the null-cone correction magnitude converges, or replace
`-gap` with an invariant corrector whose root is stable by construction.

Corrector comparison adds an important simplification.  Under the scan's
standardize-and-residualize convention, `-gap` and `interior_bdg` give
identical statistics: both are just the interior BDG corrector after constants
and horizon-boundary terms are projected away.  On `n=18`, `paths=4`, both have
mean `|t| = 3.61231`, mean absolute leakage `3.15e-3`, and pass rate `0.985714`
at step `0.050`.  Lean now proves the quotient behind this observation:
constants and horizon-parallel terms leave the centered residual's first-order
response and second-order horizon leakage unchanged, and the corrected
canonical source inherits that same corrector-gauge invariance.  The stronger
polynomial theorem preserves zeros of the leakage null cone itself, so the
estimated coefficient root is independent of the chosen constant/horizon
representative.  The full protected bridge now transfers across that quotient:
the cone condition, descent margin, horizon protection, and raw-defect descent
hold for every equivalent corrector representative.  The `size` corrector
passes the gate but has worse leakage.

## Descent Dynamics

The file now also formalizes the finite dynamical step needed to turn
one-step descent into a refinement program.  Suppose a protected source updates
the displayed distortion error by a first-order term plus a finite remainder:

```text
D_next <= D_old + step * linearResponse(S, Dist) + remainder.
```

If the remainder is controlled by half of the protected descent margin,

```text
remainder <= step * descentRate / 2,
```

Lean proves:

```text
D_next <= D_old - step * descentRate / 2.
```

With `step > 0` and `descentRate > 0`, this is a strict decrease.  The
refinement package `ProtectedHauptvermutungDistortionDescent` records such a
step at every scale.  A separate geometric-majorant theorem proves that if the
nonnegative displayed distortion errors are bounded by

```text
D_n <= D_0 * q^n,    0 <= q < 1,
```

then `D_n -> 0`.

This does not prove that the actual causal-growth dynamics has such a
uniform contraction.  It proves the exact finite checklist: construct the
protected source, prove the half-remainder bound, and prove a geometric
majorant or another convergence estimate for the displayed distortion.

The sequence-level theorem now combines the two sides:

```text
ProtectedHauptvermutungDistortionDescent
  .horizon_protection_and_distortion_tendsto_zero
```

Under the same geometric distortion majorant, Lean proves both:

```text
linearResponse(S_n, c_n - J_n) = 0       for every n
quadraticResponse(S_n, c_n - J_n) = 0    for every n
D_n -> 0
```

So the finite endpoint is no longer just a local descent rule.  It is a checked
refinement template: every certified step leaves the Dorau--Much horizon
channel protected through second order, while the displayed Hauptvermutung
distortion tends to zero.

## Descent Gate Probe

The script

```text
horizon_distortion_descent_gate.py
```

tests the finite half-remainder gate on the certificate-basis candidate

```text
residual(cert_pairConsistency) + 3.5035 residual(-gap)
```

against the displayed distortion target `cert_scaledDistortionBound`.

Global orientation command:

```bash
PYTHONDONTWRITEBYTECODE=1 python3 horizon_distortion_descent_gate.py --n 18 --paths 4 --burn 5 --starts 8 --seed 53 --steps 0.005,0.01,0.02,0.05
```

Global result:

```text
parents = 35
descent_positive_frac = 28/35 = 0.800
mean target_response  = -6.35e-01
step 0.005: pass=0.800, strict=0.800, mean_gate_ratio=0.016
step 0.010: pass=0.800, strict=0.800, mean_gate_ratio=0.033
step 0.020: pass=0.771, strict=0.800, mean_gate_ratio=0.066
step 0.050: pass=0.743, strict=0.771, mean_gate_ratio=0.163
```

The global fixed direction has the right average sign and a small mean
remainder, but it is not yet a uniform certificate because 7 of 35 sampled
parents point the wrong way for the distortion target.

Local orientation command:

```bash
PYTHONDONTWRITEBYTECODE=1 python3 horizon_distortion_descent_gate.py --n 18 --paths 4 --burn 5 --starts 8 --seed 53 --steps 0.005,0.01,0.02,0.05 --local-sign
```

Local result:

```text
parents = 35
descent_positive_frac = 35/35 = 1.000
mean target_response  = -8.00e-01
step 0.005: pass=1.000, strict=1.000, mean_gate_ratio=0.015
step 0.010: pass=1.000, strict=1.000, mean_gate_ratio=0.030
step 0.020: pass=0.971, strict=1.000, mean_gate_ratio=0.060
step 0.050: pass=0.943, strict=0.971, mean_gate_ratio=0.150
```

This is much closer to the formal theorem.  The protected descent package
allows the source to vary with the finite parent state, so local orientation is
the right finite model for the next physical certificate.  The remaining
empirical target is now precise: find an invariant rule for choosing that
state-dependent sign/coefficient, then prove its half-remainder gate uniformly
under refinement.

The file also defines `ProtectedCertificateErrorRefinement`.  In this
refinement version, first-order horizon contamination vanishes at every finite
stage, while the second-order leakage only has to tend to zero:

```text
Cov(S_n,J_n) = 0
Cov(J_n, centered(S_n)^2) -> 0
```

Lean proves:

```text
linearResponse(S_n, c_n - J_n) = 0       for every n
quadraticResponse(S_n, c_n - J_n) -> 0   as n -> infinity
```

This is now the exact theorem template the numerics must fill.  The remaining
unproved physical step is to derive such an `S_n` from the actual causal-growth
dynamics and prove stable descent of the named certificate errors
`countWindow`, `curvatureBias`, and `pairConsistency`.
