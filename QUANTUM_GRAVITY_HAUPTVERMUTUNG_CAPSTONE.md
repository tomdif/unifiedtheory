# Quantum Gravity / Hauptvermutung Capstone

Date: 2026-08-19

Lean file:

```text
UnifiedTheory/Audit/KFCausalCSpecQuantumGravityHauptvermutungCapstone.lean
```

First bridge file:

```text
UnifiedTheory/Audit/KFCausalCSpecEntropyFluxLimit.lean
```

## What Is Proved

The capstone proves the strongest honest package currently available in the
repo:

```text
finite_kp_quantum_gravity_core
exact_finite_entropy_focusing
dorau_much_eight_pi_null_balance
conformal_rss_small_diamond_certificate
quantitative_hauptvermutung_global_mean
full_continuum_qg_bridge_complete_iff
```

In plain terms:

* finite K/P quantum-gravity algebra is proved: Born nonnegativity,
  interference, finite-sum UV boundedness, and CPT invariance;
* finite causal-growth entropy focusing is exact:

```text
d/dlambda KL_lambda
  = -lambda * d/dlambda E_lambda[c - J]
```

* the Dorau-Much scalar chain gives the fixed `8*pi` null-balance once the
  analytic horizon inputs are supplied;
* the conformally-flat RSS/Gibbons-Solodukhin small-diamond volume certificate
  is available with explicit constants;
* the quantitative Hauptvermutung mean-gluing theorem gives a global
  approximate isometry with explicit distortion:

```text
distortion <= (epsilon + b + epsilon*b) * S + kappa_d/2.
```

* horizon-orthogonal least-defect growth separates the first-order horizon
  entropy channel from independent geometry/Hauptvermutung defect repair.

## What Is Not Proved

This is not an unconditional proof of nonperturbative continuum quantum
gravity.  The file makes the remaining bridge explicit as
`FullContinuumQGBridge`.

The remaining fields are:

```text
finiteEntropySourceConvergesToArakiFlux
causalGrowthProducesRequiredBirthLaws
quantitativeHauptvermutungAppliesToPhysicalGrowth
diffeomorphismInvariantObservablesConstructed
infraredGRAndQFTRecovered
```

So the current status is:

```text
finite causal-set entropy focusing: proved
finite causal-growth birth-law normalization: proved
finite K/P quantum algebra: proved
physical-growth Hauptvermutung certificate interface: proved
diffeomorphism/label-invariant quotient observables: proved
finite horizon-orthogonal defect projection: proved
quantitative Hauptvermutung under displayed hypotheses: proved
Dorau-Much 8*pi scalar bridge under analytic horizon inputs: proved
full continuum quantum gravity: reduced to the named bridge fields
```

## First Bridge Step Added

`KFCausalCSpecEntropyFluxLimit.lean` follows the next-step plan:

```text
scaled horizon source       J_rho / rho^p
flat Rindler decomposition  J_rho = rho^p (W + residual_rho)
RSS/Poisson error budget     (epsilon + b + epsilon*b) S
error -> 0                  finite source -> continuum null flux
```

Key theorem names:

```text
flat_rindler_scaledFlux_converges
finiteEntropySource_converges_to_ArakiFlux_of_errorControl
finiteEntropySource_converges_of_rssPoissonError
HorizonHitSourceEstimator.finiteScaledFlux_converges_to_continuumFlux
HorizonHitSourceEstimator.closes_ArakiFlux_bridge
FiniteBirthLaw.partition_pos
entropyFluxLimitBridge_closes_first_field
```

This closes the formal slot for:

```text
finiteEntropySourceConvergesToArakiFlux
```

provided the geometric/analytic estimates instantiate the displayed error
control.

The bridge now also has a concrete physical horizon-cell estimator.  It proves
that weighted finite horizon-hit counts converge to the weighted continuum
null-flux target when each cell has a vanishing error bound.  If that continuum
target is identified with the Araki flux, the theorem
`HorizonHitSourceEstimator.closes_ArakiFlux_bridge` closes the first
`FullContinuumQGBridge` field.  The next mathematical job is therefore the
physical one: prove those per-cell horizon-hit estimates for the causal-growth
law rather than merely postulating the aggregate flux limit.

## Second Finite Bridge Step Added

`KFCausalCSpecFiniteHorizonSource.lean` now includes a finite one-step growth
kernel interface:

```text
weight_i >= 0
sum_i weight_i > 0
p_i = weight_i / sum_j weight_j
```

Key theorem names:

```text
FiniteCausalGrowthKernel.produces_birthLaw
FiniteCausalGrowthKernel.source_tilt_produces_birthLaw
FiniteCausalGrowthKernel.kernel_entropyFocusing_deriv_identity
FiniteCausalGrowthSystem.producesRequiredBirthLaws
FiniteCausalGrowthSystem.sourceTiltProducesRequiredBirthLaws
FiniteCausalGrowthSystem.entropyFocusing_at_parent
```

This proves the finite algebraic part of:

```text
causalGrowthProducesRequiredBirthLaws
```

There is also a parent-indexed system theorem, so the entropy-focusing identity
applies at every parent state of any finite system satisfying those kernel
hypotheses.  The still-open part is the physical dynamics theorem: identify the
actual admissible precursor family and show its transition weights satisfy the
finite kernel hypotheses at each parent state.

## Third Bridge Step Added

`KFCausalCSpecHauptvermutungPhysicalBridge.lean` packages the quantitative
Hauptvermutung hypotheses into a physical-growth certificate:

```text
local chart count windows
curvature-volume bias bounds
pairwise chart consistency
density and positivity conditions
--------------------------------
global arithmetic-mean map is an approximate isometry
```

Key theorem names:

```text
PhysicalGrowthHauptvermutungCertificate.applies_quantitative_hauptvermutung
PhysicalGrowthHauptvermutungCertificate.distortionBound_tendsto_zero
PhysicalGrowthHauptvermutungCertificate.certificate_distortionBound_tendsto_zero
```

This closes the formal certificate version of:

```text
quantitativeHauptvermutungAppliesToPhysicalGrowth
```

It also proves the limit statement: if the counting window, curvature bias, and
chart-pair consistency all vanish along a refinement sequence with fixed scale,
then the displayed global distortion bound tends to zero.  The still-open part
is again physical rather than algebraic: produce these certificates from the
actual causal-growth dynamics.

## Fourth Bridge Step Added

`KFCausalCSpecDiffeomorphismInvariantObservables.lean` proves the quotient
construction for physical observables:

```text
x ~ y  implies  O(x) = O(y)
--------------------------------
O descends to an observable on State / ~
```

Key theorem names:

```text
quotientObservable_mk
pair_invariant
finiteSignature_invariant
InvariantObservableFamily.constructs_diffeomorphismInvariantObservables
InvariantObservableFamily.finiteSignature_constructs
```

This proves the formal construction behind:

```text
diffeomorphismInvariantObservablesConstructed
```

The still-open physical part is selecting the actual invariant observable family
that separates the continuum sectors we care about.  The quotient construction
itself is now checked.

## Fifth Finite Control Step Added

`KFCausalCSpecHorizonOrthogonalDefect.lean` formalizes the new
horizon-orthogonal least-defect source:

```text
G_perp = G - Cov(G,J)/Var(J) * J
S(thetaH,thetaD) = thetaH * J + thetaD * G_perp
```

For any normalized finite birth law with `Var(J) != 0`, Lean proves:

```text
Cov(G_perp,J) = 0
linearResponse(S(thetaH,thetaD), c - J) = -thetaH * Var(J)
```

So the defect-repair coefficient `thetaD` does not change the first-order
horizon-focusing law.  The file also proves uniqueness: if
`Cov(G - aJ,J) = 0`, then `a = Cov(G,J)/Var(J)`.

The same file now looks one order deeper.  It defines the finite second central
response numerator

```text
quadraticResponse(S,X) = Cov(X, centered(S)^2)
```

and proves the exact leakage identity:

```text
quadraticResponse(S, c - J) = -Cov(J, centered(S)^2).
```

Thus first-order projection is not the full protection criterion.  A residual
defect source is protected through this second central response only when its
squared centered amplitude is also horizon-balanced.

The leakage term is also proved to be a quadratic form on defect directions:

```text
Leak(aA + bB)
  = a^2 Leak(A,A) + 2ab Leak(A,B) + b^2 Leak(B,B).
```

This turns second-order protection into a finite null-cone problem.  If two
defect channels are first-order orthogonal to `J` and their coefficients lie on
the leakage null cone, Lean proves the mixture has zero first-order area
response and zero finite second central area response.

`horizon_leakage_nullcone_scan.py` tests this numerically on residualized
finite defect channels.  On a modest `n=20`, `paths=12` sample, combinations
such as `residual(-gap) + 0.003 residual(h2)` and
`residual(-gap) - 0.75 residual(h1)` reduce sample-mean leakage to about
`1e-4` while keeping gap response near `7`.  The coefficient is not yet stable
enough to be a physical certificate; it is a sharper search target for the
actual Hauptvermutung-defect basis.

`horizon_nullcone_stability.py` repeats the scan across depths and seeds.  On
the current small check (`n=18,20`, seeds `53,157`) low-leakage directions
persist, but the best pair and coefficient drift.  A broader random
multi-channel search in `horizon_multichannel_nullcone_search.py` also lands
mostly on pair-like directions.  The current evidence therefore supports the
finite null-cone mechanism, but the physical channel basis is still the open
problem.

The follow-up `horizon_hauptvermutung_channels.py` adds one-birth proxies for
the actual certificate fields: interval-dimension error, relation-fraction
bias, interval-profile spread, scale-window irregularity, and resolved-interval
mass.  With `--basis hv`, the null-cone search still finds low-leakage,
high-gap directions such as
`0.924 residual(-gap) + 0.381 residual(hv_big_interval_count)` with leakage
about `2e-3` and gap response about `7.9` on the small `n=20`, `paths=4`
sample.  The coefficient still drifts, so this is evidence for the mechanism,
not a physical-growth Hauptvermutung certificate.

The next pass adds `horizon_certificate_channels.py`, whose channels are named
after the actual bridge fields: `cert_countWindow`, `cert_curvatureBias`,
`cert_pairConsistency`, and finite proxy distortion bounds.  This produces the
strongest low-leak/high-gap lead so far:

```text
cert_pairConsistency + 3.5035 residual(-gap):
  leakage  =  2.98e-05
  gap_slope = -7.652
```

Across the small `n=18,20`, two-seed stability run,
`cert_target4Distortion + residual(-gap)` has mean absolute leakage below
`5e-4` with mean gap response about `7.66`, though its coefficient still
drifts.  This is now the main empirical target for the formal
certificate-source interface.

That interface is now checked in Lean.  A `ProtectedCertificateErrorSource`
packages a finite source `S`, horizon source `J`, and named certificate-error
observable with:

```text
Cov(S,J) = 0
Cov(J, centered(S)^2) = 0
linearResponse(S, certificateError) <= -descentRate
```

Lean proves that such a source preserves the finite horizon-area response
through second order and descends the certificate error.  If
`descentRate > 0`, the certificate-error response is strictly negative.  The
refinement version weakens exact second-order cancellation to leakage tending
to zero, and proves the second central horizon-area response tends to zero.
The residualized two-channel theorem directly covers the null-cone scans:
after two raw defect observables are projected off the horizon source, a
leakage-null mixture that descends a named certificate error satisfies the same
finite horizon/certificate bridge.

The same Lean file now specializes the abstract certificate error to the actual
quantitative-Hauptvermutung distortion observable:

```text
Dist = (countWindow + curvatureBias + countWindow*curvatureBias) * scale
       + pairConsistency/2.
```

It proves the first-order response decomposition into the count-window,
curvature-bias, mixed count-curvature, and pair-consistency channels, and then
packages a `ProtectedHauptvermutungDistortionSource`: horizon-protected descent
of this aggregate distortion observable implies simultaneous horizon
protection and improvement of the displayed Hauptvermutung distortion bound.

The latest finite descent layer adds the Taylor-remainder gate.  If a protected
source updates the displayed distortion by

```text
D_next <= D_old + step * linearResponse(S, Dist) + remainder
```

and the finite remainder is at most half the descent margin,

```text
remainder <= step * descentRate / 2,
```

Lean proves `D_next <= D_old - step*descentRate/2`, with strict decrease when
`step > 0` and `descentRate > 0`.  A refinement package records this at every
scale, and a geometric-majorant theorem proves `D_n -> 0` from
`D_n <= D_0*q^n` with `0 <= q < 1`.

The sequence-level bridge combines this with horizon protection: under the
same geometric distortion majorant, Lean proves every finite step has zero
first-order and zero second central horizon-area response, while the displayed
Hauptvermutung distortion tends to zero.

`horizon_distortion_descent_gate.py` now tests the finite half-remainder gate
on the certificate-basis candidate
`residual(cert_pairConsistency) + 3.5035 residual(-gap)`.  On the small
`n=18`, `paths=4`, seed-53 sample, the global fixed orientation descends the
displayed distortion target on 28/35 parents and passes the half-remainder gate
for 80% of parents at steps `0.005` and `0.010`.  With local per-parent
orientation, descent is positive on 35/35 parents and the gate passes on all
parents at steps `0.005` and `0.010`.  This supports the state-dependent source
form of the Lean descent package, but it is still empirical, not a uniform
refinement certificate.

Lean now formalizes that local orientation rule.  `orientTowardObservable`
flips a source exactly when its first-order distortion response is positive,
and proves the oriented response is `-|response|`.  The sign flip preserves
horizon orthogonality and second-order leakage, so a nonzero response gives a
positive protected descent rate without damaging the Dorau--Much horizon
channel.

This is now recorded as the current new-physics lead:
[`HORIZON_INVISIBLE_GEOMETRIC_RELAXATION.md`](HORIZON_INVISIBLE_GEOMETRIC_RELAXATION.md).
The finite mechanism is a horizon-invisible geometric relaxation channel: a
parent-local defect source can descend the displayed Hauptvermutung distortion
observable while leaving the Dorau--Much horizon-area response zero through
second order.  It remains a finite mechanism until the source and uniform
remainder bound are derived from the physical causal-growth dynamics.

The latest attack identifies a canonical source instead of an ad hoc one:
take the displayed distortion observable itself, project it off the horizon
source, and move down the residual.  Lean proves this canonical
`canonicalHorizonInvisibleDescentSource` has zero first-order horizon response
and descends its defining observable with response
`-variance(horizonOrthogonalResidual(w,J,G))`.  The second-order obstruction is
also isolated exactly as the residual gradient's horizon leakage.  Numerically,
the pure canonical source descends 35/35 seed-53 parents, and the null-cone
corrected source `residual(cert_scaledDistortionBound) + 3.5 residual(-gap)`
passes the local half-remainder gate through step `0.050` on both seed-53
and seed-157 samples.  Lean now packages this correction as
`correctedCanonicalHorizonInvisibleDescentSource_protected_bridge`: if the
corrected source lies on the leakage null cone and retains enough
residual-gradient margin, it is a protected finite certificate bridge.  The
same `t=3.5` correction also passes a deeper `n=20`, `paths=2` gate check on
both seed 53 and seed 157.

`horizon_corrected_canonical_scan.py` now estimates the leakage-null
coefficient directly.  On the `n=18`, `paths=4` check, the two seed roots have
stable magnitude (`3.67279`, `3.55183`) and mean absolute leakage `3.15e-3`.
At lower `paths=2` statistics across depths `18,20`, the root is noisier, but
the local descent gate mostly remains open.  The next finite target is
coefficient-magnitude stability under refinement, or an invariant replacement
for the current `-gap` corrector.

Corrector comparison shows that the apparent `-gap` corrector is really the
interior BDG channel after residualization: `-gap` and `interior_bdg` have
identical `n=18`, `paths=4` statistics, while `size` has worse leakage.  This
narrows the physical source target from a whole action-gap proxy to the
interior action channel with the horizon boundary part projected out.  The
finite Lean file now proves the algebra behind this quotient: adding constants
and horizon-parallel terms to a corrector does not change the centered
residual's first-order response or second-order horizon leakage, and the
corrected canonical source inherits the same invariance.  It now also proves
that zeros of the leakage null-cone quadratic survive the same replacement, so
the coefficient root is a quotient-level object rather than a representative
artifact.  The full protected corrected-source bridge now transfers across
that quotient, including the cone hypothesis, descent margin, horizon
protection, and raw-defect descent.

The newest concrete target is now order-derived.
`KFCausalCSpecBridgeDefectObservable.lean` uses the private-marker bridge
poset and the CSpec census recovery theorem to define a bridge-census defect
from global order incidence:

```text
bridgeCensusDefect(e,tau)
  = 18 - permScore(bridgeProfile(e), shiftedBridgeProfile(e), tau).
```

Lean proves the canonical transport has zero defect, every noncanonical
transport has positive defect, and the order incidence recovers the transported
atom.  It then identifies the pair-consistency part of the displayed
Hauptvermutung distortion proxy with this defect and specializes the
canonical/corrected horizon-invisible source bridge to that concrete CSpec
observable.  The finite population version proves the total bridge-census
distortion is nonnegative, that the canonical order-recovered candidate family
is a zero minimizer, and that total zero forces every candidate transport to
be the order-recovered one.

The first explicit gap-closing interface is now recorded in
[`TOE_COMPLETION_PLAN.md`](TOE_COMPLETION_PLAN.md).  In Lean, the aggregate
`physicalHauptvermutungDistortion` combines count-window, curvature-bias,
spectral-locality, and bridge-census transport defects.  Under nonnegative
component hypotheses, total zero means every component is zero and the
transport candidate family is canonical.  The bridge component is also a
strict minimizer inside this aggregate: changing only the transport candidate
away from the order-recovered family strictly increases total aggregate
distortion.  The companion interface `PhysicalGrowthSuppliesRepairSource`
packages the next required physical theorem shape: a horizon-protected repair
source with aggregate descent and a half-remainder bound strictly contracts
the aggregate distortion.  The refinement wrapper
`PhysicalGrowthRepairRefinement` records this source certificate at every
finite stage and proves stepwise horizon protection together with
`D_{n+1} < D_n`.  With an additional geometric majorant
`D_n <= D_0*q^n`, `0 <= q < 1`, the same wrapper proves aggregate convergence
`D_n -> 0`.  The newest step-factor version derives that majorant from
`D_{n+1} <= q * D_n`, and the newest relative-margin version derives that
factor from `(1 - q)*D_n <= step_n*descentRate_n/2`.  The newest
descent-budget version packages the same condition as
`2*(1 - q)*D_n <= step_n*descentRate_n`.  The newest rate-floor version derives
that budget from `rateFloor_n*D_n <= descentRate_n` and
`2*(1 - q) <= step_n*rateFloor_n`.  The newest uniform version derives
convergence with `q = 1 - stepFloor*gamma/2` from
`gamma*D_n <= descentRate_n`, `stepFloor <= step_n`, and
`0 < stepFloor*gamma <= 2`.  The next proof target is to derive this uniform
package, or the now-formal product-decay replacement
`Product_{k<n} q_k -> 0`, from the physical causal-growth law.  The explicit
variable-rate-floor specialization uses
`q_n = 1 - step_n*rateFloor_n/2`; the newest uniform-bound bridge derives
product decay from `0 <= q_n <= qBound < 1`.  The newest gain-window gate
derives this bound from `0 < beta`, `beta <= step_n*rateFloor_n`, and
`step_n*rateFloor_n <= 2`.  The newest physical-total version discharges the
external `D_n >= 0` side condition when `D_n` is exactly the displayed physical
aggregate with nonnegative component observables.  The newest local-descent
version replaces the global `rateFloor_n*D_n <= descentRate_n` assumption with
finite per-cell descent certificates whose sum is `descentRate_n`.  The newest
uniform local-rate version derives convergence from those local certificates
together with `gamma <= rateFloor_n`, `stepFloor <= step_n`, and
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
`beta <= step_n*(weightFloor_n*sourceFloor_n)`.  The newest component-gain
gate derives that ordinary gain floor from separate lower bounds on step size,
weight-floor amplitude, and centered-source-floor amplitude.  The newest
positive component-floor gate removes the auxiliary `beta` by setting
`beta = min 1 (stepFloor*(weightBase*sourceBase))`, so positive component
floors themselves imply the protected convergence theorem.  The newest direct
uniform component-floor gate removes the auxiliary stagewise floor sequences
and asks only for positive uniform lower bounds on `step_n`, `w_{n,i}`, and
`-centered(S_n)_i`.  The newest certificate theorem packages those floors
with the physical-total identity, nonnegative components, descent identity,
and refinement data as `PhysicalHauptvermutungConvergenceCertificate`, then
proves protected convergence from that single certificate.  The newest
exact-recovery theorem shows that if every noncanonical bridge candidate stays
at least `epsilon > 0` above zero distortion, then the certificate forces
eventual equality with the canonical CSpec bridge candidate.  The newest
bridge-defect-floor theorem derives that uniform gap from the local bridge
penalty itself:
`epsilon <= bridgeCensusDefect(edge_{n,i}, candidate_{n,i})` at every wrong
local transport.  The newest parameter-free recovery theorem proves the bridge
census has fixed wrong-transport floor `18`, so the convergence certificate
alone forces eventual canonical CSpec bridge recovery.  The newest operational
recovery corollaries then prove eventual zero bridge total and eventual
order-incidence recovery of the candidate transport.  The newest residual-split
theorems then prove that the post-recovery aggregate is exactly the
count/curvature/spectral base distortion, that this base and each finite local
component tend to zero, and that a fixed positive residual gap forces eventual
exact zero total.  Those hypotheses are now packaged as
`PhysicalHauptvermutungExactRecoveryCertificate`, which proves horizon
protection plus eventual full operational recovery and gives a finite threshold
after which `PhysicalHauptvermutungRecoveredStage` holds.  The newest
observable-zero corollary expands that threshold into total, physical-total,
base, bridge, residual, canonical-transport, and incidence recovery facts.

Key theorem names:

```text
rawDefect_eq_projection_plus_residual
covariance_horizonOrthogonalResidual_self
horizonProjectionCoeff_unique
horizonProjectionCoeff_add_horizon
horizonProjectionCoeff_add_const
horizonOrthogonalResidual_add_const_horizon
horizonSecondOrderCrossLeakage_horizonOrthogonalResidual_gauge
horizonSecondOrderLeakageQuadratic_correctorGauge
horizonSecondOrderLeakageQuadratic_correctorGauge_zero
linearResponse_horizonOrthogonalResidual_add_const_horizon
horizonSecondOrderLeakage_horizonOrthogonalResidual_add_const_horizon
orthogonal_source_area_response_zero
quadraticResponse_finiteAreaChange_eq_neg_leakage
orthogonal_source_secondOrder_area_obstruction
orthogonal_source_firstAndSecondOrder_area_zero
horizonSecondOrderLeakage_linear_combination
twoChannel_firstAndSecondOrder_area_zero
twoChannel_protected_certificate_error_source_bridge
twoResidualChannel_protected_certificate_error_source_bridge
combined_orthogonal_area_response
combined_horizonOrthogonal_area_response
HorizonOrthogonalDefectCertificate.leastDefectSource_preserves_horizon_focusing
HorizonOrthogonalDefectCertificate.leastDefectSource_secondOrder_area_obstruction
ProtectedCertificateErrorSource.protected_certificate_error_source_bridge
ProtectedCertificateErrorSource.certificate_error_response_negative
ProtectedCertificateErrorRefinement.quadratic_area_response_tendsto_zero
linearResponse_orientTowardObservable_eq_neg_abs
horizonSecondOrderLeakage_orientTowardObservable
oriented_response_negative_of_nonzero
horizonOrthogonalResidual_linearResponse_rawDefect
canonicalHorizonInvisibleDescentSource_response_rawDefect
canonicalHorizonInvisibleDescentSource_area_response_zero
canonicalHorizonInvisibleDescentSource_secondOrder_area_obstruction
canonicalHorizonInvisibleDescentSource_protected_certificate_bridge
correctedCanonicalHorizonInvisibleDescentSource_response_correctorGauge
correctedCanonicalHorizonInvisibleDescentSource_leakage_correctorGauge
correctedCanonicalHorizonInvisibleDescentSource_quadraticResponse_correctorGauge
correctedCanonicalHorizonInvisibleDescentSource_cone_correctorGauge
correctedCanonicalHorizonInvisibleDescentSource_margin_correctorGauge
correctedCanonicalHorizonInvisibleDescentSource_response_rawDefect
correctedCanonicalHorizonInvisibleDescentSource_descends_rawDefect
correctedCanonicalHorizonInvisibleDescentSource_protected_bridge
correctedCanonicalHorizonInvisibleDescentSource_protected_bridge_correctorGauge
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
physicalHauptvermutungBaseDistortion_eq_zero_iff
physicalHauptvermutungTotalDistortion_eq_zero_iff
physicalHauptvermutungTotalDistortion_strict_transport_min_of_ne
physicalHauptvermutungTotalDistortion_pos_of_transport_ne_canonical
physicalGrowthSuppliesRepairSource_contracts
physicalGrowthSuppliesRepairSource_strictly_contracts
physicalGrowthSuppliesRepairSource_step_factor_of_relative_margin
physicalGrowthSuppliesRepairSource_step_factor_of_descent_budget
physicalGrowthSuppliesRepairSource_descent_budget_of_rate_floor
physicalGrowthSuppliesRepairSource_step_factor_of_rate_floor
physicalGrowthSuppliesRepairSource_protected_and_contracts
physicalGrowthRepairRefinement_step_contracts
physicalGrowthRepairRefinement_step_strictly_contracts
physicalGrowthRepairRefinement_protected_and_contracts
physicalGrowthRepairRefinement_total_tendsto_zero_of_geometric_bound
physicalGrowthRepairRefinement_horizon_protection_and_total_tendsto_zero
physicalGrowthRepairRefinement_step_factor_of_relative_margin
physicalGrowthRepairRefinement_step_factor_of_descent_budget
physicalGrowthRepairRefinement_descent_budget_of_rate_floor
physicalGrowthRepairRefinement_step_factor_of_rate_floor
physicalGrowthRepairRefinement_step_factor_of_variable_rate_floor
physicalGrowthRepairRefinement_step_factor_of_explicit_variable_rate_floor
physicalGrowthRepairRefinement_step_factor_of_uniform_rate_floor
physicalGrowthRepairRefinement_geometric_bound_of_step_factor
physicalGrowthRepairRefinement_total_tendsto_zero_of_step_factor
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
physicalGrowthRepairRefinement_horizon_protection_and_total_tendsto_zero_of_positive_uniform_direct_rate_floor
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
physicalGrowthRepairRefinement_horizon_protection_and_total_tendsto_zero_of_stagewise_centered_source_component_gain_floor
physicalGrowthRepairRefinement_horizon_protection_and_total_tendsto_zero_of_positive_stagewise_centered_source_component_floors
physicalGrowthRepairRefinement_horizon_protection_and_total_tendsto_zero_of_positive_uniform_centered_source_component_floors
PhysicalHauptvermutungConvergenceCertificate
physicalHauptvermutungConvergenceCertificate_horizon_protection_and_total_tendsto_zero
physicalHauptvermutungConvergenceCertificate_eventually_canonical_of_uniform_gap
bridgeCensusDefect_wrong_floor
physicalHauptvermutungTotalDistortion_gap_of_bridge_defect_floor
physicalHauptvermutungConvergenceCertificate_eventually_canonical_of_bridge_defect_floor
physicalHauptvermutungConvergenceCertificate_eventually_canonical
physicalHauptvermutungConvergenceCertificate_eventually_bridge_total_zero
physicalHauptvermutungConvergenceCertificate_eventually_orderRecovered
physicalHauptvermutungConvergenceCertificate_eventually_total_eq_base
physicalHauptvermutungConvergenceCertificate_base_tendsto_zero
physicalHauptvermutungConvergenceCertificate_countWindow_tendsto_zero
physicalHauptvermutungConvergenceCertificate_curvatureBias_tendsto_zero
physicalHauptvermutungConvergenceCertificate_spectralLocality_tendsto_zero
physicalHauptvermutungConvergenceCertificate_eventually_exact_zero_of_residual_gap
PhysicalHauptvermutungExactRecoveryCertificate
PhysicalHauptvermutungRecoveredStage
PhysicalHauptvermutungRecoveredStage.candidate_eq_canonical
PhysicalHauptvermutungRecoveredStage.candidate_transport
PhysicalHauptvermutungRecoveredStage.physical_total_distortion_zero
PhysicalHauptvermutungRecoveredStage.residuals_zero
PhysicalHauptvermutungRecoveredStage.base_distortion_zero
PhysicalHauptvermutungRecoveredStage.rssPoissonError_zero
physicalHauptvermutungExactRecoveryCertificate_eventually_exact_zero
physicalHauptvermutungExactRecoveryCertificate_eventually_local_distortion_zero
physicalHauptvermutungExactRecoveryCertificate_eventually_full_operational_recovery
physicalHauptvermutungExactRecoveryCertificate_eventually_recoveredStage
physicalHauptvermutungExactRecoveryCertificate_exists_recovered_after
physicalHauptvermutungExactRecoveryCertificate_exists_observable_zero_after
physicalHauptvermutungExactRecoveryCertificate_eventually_rssPoissonError_zero
physicalHauptvermutungExactRecoveryCertificate_exists_rssPoissonError_zero_after
RecoveredStageBDGAsymptoticInterface
RecoveredStageBDGAsymptoticInterface.eventually_recoveredStage
RecoveredStageBDGAsymptoticInterface.eventually_rssPoissonError_zero
RecoveredStageBDGAsymptoticInterface.bdg_dalembertian_tendsto
RecoveredStageBDGAsymptoticInterface.rssPoissonError_zero_and_bdg_dalembertian_tendsto
RecoveredStageBDGAsymptoticInterface.standard_bdg_dalembertian_tendsto
RecoveredStageBDGAsymptoticInterface.rssPoissonError_zero_and_standard_bdg_dalembertian_tendsto
BDGProfileSequenceAsymptotics
BDGProfileSequenceAsymptotics.layer_asymptotics
RecoveredStageBDGProfileSequenceInterface
RecoveredStageBDGProfileSequenceInterface.toAsymptoticInterface
RecoveredStageBDGProfileSequenceInterface.eventually_recoveredStage
RecoveredStageBDGProfileSequenceInterface.profile_bdg_dalembertian_tendsto
RecoveredStageBDGProfileSequenceInterface.rssPoissonError_zero_and_profile_bdg_dalembertian_tendsto
RecoveredStageBDGProfileSequenceInterface.rssPoissonError_zero_and_standard_profile_bdg_dalembertian_tendsto
BDG4DOperatorProfileData
BDG4DOperatorProfileData.tendsto
BDG4DOperatorProfileData.sampled_tendsto
BDG4DOperatorProfileData.sequenceAsymptotics
BDG4DOperatorProfileData.sequenceAsymptotics_layer_asymptotics
RecoveredStageBDG4DOperatorInterface
RecoveredStageBDG4DOperatorInterface.toProfileSequenceInterface
RecoveredStageBDG4DOperatorInterface.eventually_recoveredStage
RecoveredStageBDG4DOperatorInterface.operator_tendsto
RecoveredStageBDG4DOperatorInterface.rssPoissonError_zero_and_operator_tendsto
RecoveredStageBDG4DOperatorInterface.recoveredStage_and_operator_tendsto
RecoveredStageExactCSpecSequence.eventually_recoveredStage
RecoveredStageExactCSpecSequence.eventually_rssPoissonError_zero
RecoveredStageExactCSpecSequence.exists_rssPoissonError_zero_after
RecoveredStageBDG4DChartInterface.toOperatorInterface
RecoveredStageBDG4DChartInterface.rssPoissonError_zero_and_chart_operator_tendsto
RecoveredStageBDG4DChartInterface.recoveredStage_and_chart_operator_tendsto
RecoveredStageBDG4DPhysicalChartInterface.toChartInterface
RecoveredStageBDG4DPhysicalChartInterface.applies_quantitative_hauptvermutung_at
RecoveredStageBDG4DPhysicalChartInterface.distortionBound_tendsto_zero
RecoveredStageBDG4DPhysicalChartInterface.rssPoissonError_zero_chart_operator_tendsto_and_distortionBound_tendsto_zero
RecoveredStageBDG4DPhysicalChartInterface.recoveredStage_chart_operator_tendsto_and_distortionBound_tendsto_zero
physicalHauptvermutungExactRecoveryCertificate_horizon_protection_and_eventually_full_recovery
physicalHauptvermutungExactRecoveryCertificate_horizon_protection_and_recovered_after
linearResponse_hauptvermutungDistortionObservable
ProtectedHauptvermutungDistortionSource.preserves_horizon_and_descends_distortion
ProtectedHauptvermutungDistortionSource.distortion_response_expands
orientedProtectedHauptvermutungDistortionSource_descentRate_positive
orientedProtectedHauptvermutungDistortionSource_bridge
componentResponses_protected_distortion_bridge
protected_distortion_step_decreases_with_remainder
protected_distortion_step_strictly_decreases
ProtectedHauptvermutungDistortionDescent.step_decreases
ProtectedHauptvermutungDistortionDescent.distortion_tendsto_zero_of_geometric_bound
ProtectedHauptvermutungDistortionDescent.step_preserves_horizon_through_secondOrder
ProtectedHauptvermutungDistortionDescent.quadratic_area_response_tendsto_zero
ProtectedHauptvermutungDistortionDescent.horizon_protection_and_distortion_tendsto_zero
```

This is a finite control theorem, not a continuum completion.  Its role is to
make the next physical task sharper: construct the actual causal-growth
Hauptvermutung-defect source, project it off the horizon source, and prove the
protected certificate-source hypotheses from the physical dynamics.
The newest direct aggregate-rate theorem further sharpens that task: deriving a
positive aggregate descent rate and positive step floor is enough for protected
convergence, while pointwise centered-source floors are one possible derivation
route rather than a required logical endpoint.
The recovered-stage BDG interface sharpens Gate 4 in the same way: exact finite
recovery now feeds the BDG assembler once the physical law supplies the
per-layer interval-volume/RNC asymptotics.
The profile-sequence adapter removes a technical mismatch there: the existing
4D BDG profile limits may be proved over a real density parameter and then
sampled along the recovered-stage sequence.
The concrete 4D operator wrapper now supplies that real profile source from the
already-proved reduced 4D BDG operator theorem, leaving the physical-law task of
constructing its support, regularity, and cone-bound data from recovered charts.
The recovered 4D operator interface then combines that data with exact finite
recovery to obtain zero finite horizon error and the sampled 4D operator limit
in one theorem.
The local-chart supplier interface now sharpens the remaining physical task:
`RecoveredStageBDG4DChartInterface` separates exact finite CSpec recovery from
`RecoveredStageBDG4DChartData`, whose fields are the recovered local chart map,
density sequence, sampled point-field values, curvature value, and
`BDG4DOperatorProfileData`.  Lean proves that this chart package constructs
the concrete recovered-stage 4D operator interface and yields the same
zero-error/operator-limit conclusion.
The physical-chart supplier interface now connects that chart package to the
existing physical Hauptvermutung certificate sequence: the certificates supply
chart density and coordinates, their displayed distortion bound tends to zero,
and the recovered-stage theorem now packages zero finite horizon error,
sampled 4D operator convergence, and chart-distortion collapse together.

## Verification

Checked directly without running `lake build`:

```bash
lake env lean UnifiedTheory/Audit/KFCausalCSpecQuantumGravityHauptvermutungCapstone.lean
lake env lean UnifiedTheory/Audit/KFCausalCSpecEntropyFluxLimit.lean
lake env lean UnifiedTheory/Audit/KFCausalCSpecFiniteHorizonSource.lean
lake env lean UnifiedTheory/Audit/KFCausalCSpecHauptvermutungPhysicalBridge.lean
lake env lean UnifiedTheory/Audit/KFCausalCSpecDiffeomorphismInvariantObservables.lean
lake env lean UnifiedTheory/Audit/KFCausalCSpecHorizonOrthogonalDefect.lean
lake env lean UnifiedTheory/Audit/KFCausalCSpecBridgeDefectObservable.lean
python3 -m py_compile horizon_second_order_leakage.py
python3 horizon_second_order_leakage.py --n 18 --paths 8 --burn 5 --starts 8 --coeffs 0.20,0.30,0.45
PYTHONDONTWRITEBYTECODE=1 python3 horizon_leakage_nullcone_scan.py --n 20 --paths 12 --burn 5 --starts 8 --tmin -2 --tmax 2 --step 0.05 --top 8
PYTHONDONTWRITEBYTECODE=1 python3 horizon_nullcone_stability.py --depths 18,20 --seeds 53,157 --paths 8 --burn 5 --starts 8 --tmin -2 --tmax 2 --step 0.10
PYTHONDONTWRITEBYTECODE=1 python3 horizon_multichannel_nullcone_search.py --n 20 --paths 8 --burn 5 --starts 8 --directions 600 --top 8
PYTHONDONTWRITEBYTECODE=1 python3 horizon_leakage_nullcone_scan.py --basis hv --n 18 --paths 4 --burn 5 --starts 8 --tmin -2 --tmax 2 --step 0.10 --top 8
PYTHONDONTWRITEBYTECODE=1 python3 horizon_nullcone_stability.py --basis hv --depths 18,20 --seeds 53,157 --paths 4 --burn 5 --starts 8 --tmin -2 --tmax 2 --step 0.10 --track hv_dim_spread:-gap,hv_logk_spread:-gap,hv_big_interval_count:-gap,hv_dim2_err:-gap,hv_rel2_abs:-gap
PYTHONDONTWRITEBYTECODE=1 python3 horizon_multichannel_nullcone_search.py --basis hv --n 20 --paths 4 --burn 5 --starts 8 --directions 600 --top 8
PYTHONDONTWRITEBYTECODE=1 python3 horizon_leakage_nullcone_scan.py --basis cert --n 18 --paths 4 --burn 5 --starts 8 --tmin -2 --tmax 2 --step 0.10 --top 8
PYTHONDONTWRITEBYTECODE=1 python3 horizon_nullcone_stability.py --basis cert --depths 18,20 --seeds 53,157 --paths 4 --burn 5 --starts 8 --tmin -2 --tmax 2 --step 0.10
PYTHONDONTWRITEBYTECODE=1 python3 horizon_multichannel_nullcone_search.py --basis cert --n 20 --paths 4 --burn 5 --starts 8 --directions 600 --top 8
```

Axiom printouts are clean: only `propext`, `Classical.choice`, and
`Quot.sound`.
