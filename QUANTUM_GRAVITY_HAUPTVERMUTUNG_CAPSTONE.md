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

## Verification

Checked directly without running `lake build`:

```bash
lake env lean UnifiedTheory/Audit/KFCausalCSpecQuantumGravityHauptvermutungCapstone.lean
lake env lean UnifiedTheory/Audit/KFCausalCSpecEntropyFluxLimit.lean
lake env lean UnifiedTheory/Audit/KFCausalCSpecFiniteHorizonSource.lean
lake env lean UnifiedTheory/Audit/KFCausalCSpecHauptvermutungPhysicalBridge.lean
lake env lean UnifiedTheory/Audit/KFCausalCSpecDiffeomorphismInvariantObservables.lean
```

Axiom printouts are clean: only `propext`, `Classical.choice`, and
`Quot.sound`.
