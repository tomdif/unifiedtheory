# TOE Completion Plan

Status: working plan for closing the repo's remaining theory-of-everything
gaps.  This is not a claim that the gaps are closed.

Date: 2026-08-20

## Scope Rule

Every claim should live in one of five buckets:

```text
proved finite theorem
conditional bridge
numerical evidence
physical conjecture
falsifiable prediction
```

The repo is strongest when each public claim points to a theorem, script,
dataset, or explicitly named assumption.

## Gates

### Gate 1: Physical Causal-Growth Law

Goal: select the actual microscopic dynamics.

Definition of done:

```text
one label-invariant, normalized, quantum-consistent causal-growth law
whose source terms are computed from parent order data
```

Open work:

- prove normalization/projective consistency for the physical law;
- prove strong positivity or the intended quantum-measure replacement;
- remove external geometric or embedding oracles from source selection.

### Gate 2: Physical Hauptvermutung Distortion

Goal: make manifold-likeness a finite certificate target.

Implemented start:

```text
physicalHauptvermutungDistortion
physicalHauptvermutungTotalDistortion
physicalHauptvermutungTotalDistortion_eq_zero_iff
```

The current aggregate has four finite components:

```text
countWindow
curvatureBias
spectralLocality
bridge-census transport defect
```

The bridge-census component is exact:

```text
cSpecBridgeTotalDistortion_pos_iff_candidate_ne_canonical
cSpecBridgeTotalDistortion_strict_min_of_ne
physicalHauptvermutungTotalDistortion_strict_transport_min_of_ne
```

Definition of done:

```text
the aggregate zero set is equivalent to the intended finite
order-to-geometry certificate, component by component
```

### Gate 3: Dynamical Contraction

Goal: prove physical growth drives the aggregate distortion down.

Implemented start:

```text
PhysicalGrowthSuppliesRepairSource
physicalGrowthSuppliesRepairSource_contracts
physicalGrowthSuppliesRepairSource_strictly_contracts
physicalGrowthSuppliesRepairSource_step_factor_of_relative_margin
physicalGrowthSuppliesRepairSource_step_factor_of_descent_budget
physicalGrowthSuppliesRepairSource_descent_budget_of_rate_floor
physicalGrowthSuppliesRepairSource_step_factor_of_rate_floor
physicalGrowthSuppliesRepairSource_protected_and_contracts
PhysicalGrowthRepairRefinement
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
physicalGrowthRepairRefinement_horizon_protection_and_total_tendsto_zero_of_stagewise_centered_source_component_gain_floor
physicalGrowthRepairRefinement_horizon_protection_and_total_tendsto_zero_of_positive_stagewise_centered_source_component_floors
physicalGrowthRepairRefinement_horizon_protection_and_total_tendsto_zero_of_positive_uniform_centered_source_component_floors
PhysicalHauptvermutungConvergenceCertificate
physicalHauptvermutungConvergenceCertificate_horizon_protection_and_total_tendsto_zero
```

This interface says: if physical growth supplies a source that protects the
horizon channel, descends the aggregate distortion, and has a controlled
finite update remainder, then the next aggregate distortion is strictly
smaller.

The refinement wrapper records this certificate at every finite stage and
proves each step preserves the horizon channel while strictly contracting the
tracked aggregate total:

```text
linearResponse(S_n, c_n - J_n) = 0
quadraticResponse(S_n, c_n - J_n) = 0
D_{n+1} < D_n
```

Under an additional geometric majorant `D_n <= D_0*q^n`, `0 <= q < 1`, Lean
proves aggregate convergence.  The current strongest gate derives the needed
one-step factor from a rate-floor package:

```text
rateFloor_n*D_n <= descentRate_n
2*(1 - q) <= step_n*rateFloor_n
```

These two inequalities imply the descent budget
`2*(1 - q)*D_n <= step_n*descentRate_n`, equivalently the relative descent
margin `(1 - q)*D_n <= step_n*descentRate_n/2`, so Lean now proves:

```text
D_n -> 0
```

The newest uniform gate uses one constant `gamma` and one lower step bound
`stepFloor`.  If

```text
gamma*D_n <= descentRate_n
stepFloor <= step_n
0 < stepFloor*gamma <= 2
```

then Lean proves convergence with the explicit contraction factor
`q = 1 - stepFloor*gamma/2`.  Next target: derive this uniform rate floor and
step lower bound from the actual causal-growth law, or replace them with a
summable-rate physical analogue.

The summable-rate analogue is now formal too.  For variable factors `q_n`,
Lean proves that

```text
D_{n+1} <= q_n*D_n
Product_{k<n} q_k -> 0
```

implies `D_n -> 0` while preserving the horizon channel.  The explicit
variable-rate-floor version uses
`q_n = 1 - step_n*rateFloor_n/2`, so a nonuniform causal-growth proof may aim
at product decay rather than a uniform contraction constant.

Lean also derives product decay from a uniform factor majorant:

```text
0 <= q_n <= qBound < 1
```

so the nonuniform target can be sharpened to bounding the explicit factors
`1 - step_n*rateFloor_n/2` below one.

The newest gain-window gate packages that factor bound in physical variables:

```text
0 < beta
beta <= step_n*rateFloor_n
step_n*rateFloor_n <= 2
```

Together with `rateFloor_n*D_n <= descentRate_n`, this proves horizon-protected
convergence with contraction ceiling `1 - beta/2`.

The newest physical-total version removes the external `D_n >= 0` bookkeeping
hypothesis when the tracked total is exactly
`physicalHauptvermutungTotalDistortion` and the count-window, curvature-bias,
and spectral-locality components are nonnegative at every stage.

The newest local-descent version removes the global
`rateFloor_n*D_n <= descentRate_n` assumption when each finite local component
satisfies
`rateFloor_n*localDistortion_{n,i} <= localDescent_{n,i}` and
`descentRate_n` is the sum of those local descent certificates.

The newest uniform local-rate version proves the roadmap's uniform gate from
local data: if `gamma <= rateFloor_n`, `stepFloor <= step_n`, and
`0 < stepFloor*gamma <= 2`, then the same summed local descent certificates
give horizon-protected convergence with `q = 1 - stepFloor*gamma/2`.

The newest source-local version identifies those local certificates with the
actual source's per-cell negative first-order response contribution,
`-w_{n,i}*D_{n,i}*centered(S_n)_i`, proves these contributions sum to
`-linearResponse(S_n, D_n)`, and derives the same uniform convergence gate from
cellwise lower bounds on that source-local response.

The newest centered-source floor gate reduces those cellwise response bounds to
a pointwise anti-alignment condition on the actual source:
`rateFloor_n <= -w_{n,i}*centered(S_n)_i`.  With nonnegative local distortion,
Lean proves this implies the source-local descent inequality cell by cell and
therefore the same protected convergence theorem.

The newest weighted anti-alignment gate splits that product condition into
local physical pieces: nonnegative sampling weights, a weighted rate floor
`rateFloor_n <= w_{n,i}*alignment_{n,i}`, and source anti-alignment
`alignment_{n,i} <= -centered(S_n)_i`.  Lean proves these imply the centered
source floor and therefore the same protected convergence theorem.

The newest uniform weighted-alignment gate reduces the weighted rate floor to
uniform lower bounds: `weightFloor <= w_{n,i}`,
`alignmentFloor <= alignment_{n,i}`, and
`rateFloor_n <= weightFloor*alignmentFloor`, with nonnegative floors.  This is
now the most concrete finite target for the source-amplitude part of the
causal-growth proof.

The newest rate-floor-free gate removes the auxiliary `rateFloor_n` sequence
from this branch: `gamma <= weightFloor*alignmentFloor` is enough, together
with the same uniform weight/alignment floors and anti-alignment, to prove the
uniform protected convergence theorem directly.

The newest direct centered-source floor gate removes the auxiliary `alignment`
observable too: `gamma <= weightFloor*sourceFloor`,
`weightFloor <= w_{n,i}`, and
`sourceFloor <= -centered(S_n)_i`, with nonnegative floors, prove the same
uniform protected convergence theorem directly.

The newest gamma-free product gate sets `gamma = weightFloor*sourceFloor`.
Thus the finite target becomes the directly physical product window
`0 < stepFloor*(weightFloor*sourceFloor) <= 2`, plus the same uniform weight
and centered-source floors.

The newest positive-floor gate derives the strict side of that product window
from `0 < stepFloor`, `0 < weightFloor`, and `0 < sourceFloor`; the only
remaining product-size side condition is the stability upper bound
`stepFloor*(weightFloor*sourceFloor) <= 2`.

The newest clipped-rate gate removes that stability upper-bound side condition:
with positive step, weight, and centered-source floors, Lean chooses the
effective uniform rate
`min (weightFloor*sourceFloor) (1/stepFloor)`.  This rate is still positive,
is bounded by the physical source product, and satisfies
`stepFloor*gamma <= 1`, so the geometric contraction proof applies directly.

The newest stagewise clipped-rate gate removes global uniformity at this layer:
for stage-dependent positive floors `weightFloor_n` and `sourceFloor_n`, Lean
uses
`rateFloor_n = min (weightFloor_n*sourceFloor_n) (1/step_n)` and proves
horizon-protected convergence from decay of the product of the corresponding
factors `1 - step_n*rateFloor_n/2`.

The newest clipped-gain gate derives that product decay from a concrete lower
bound: if `0 < beta` and
`beta <= step_n*min(weightFloor_n*sourceFloor_n, 1/step_n)` at every stage,
then Lean proves the same horizon-protected convergence theorem directly.

The newest unclipped-gain gate replaces that clipped lower bound by two simpler
conditions: `beta <= 1` and
`beta <= step_n*(weightFloor_n*sourceFloor_n)`.  The first condition is the
clipping cap; the second is the physical step times source-product gain.

The newest component-gain gate derives the ordinary gain floor from separate
component floors: a lower step floor, a lower weight-floor amplitude, and a
lower centered-source-floor amplitude.  Thus the finite proof target can be
split into three physical floor estimates plus
`beta <= stepFloor*(weightBase*sourceBase)`.

The newest positive component-floor gate removes the auxiliary `beta`
condition from that target.  If the step floor, weight-floor amplitude, and
centered-source-floor amplitude are all positive, Lean chooses
`beta = min 1 (stepFloor*(weightBase*sourceBase))` and proves the same
horizon-protected convergence theorem.

The newest direct uniform component-floor gate removes the auxiliary
stagewise floor sequences.  The finite proof target is now just positive
uniform lower bounds on the physical update step, the actual sampling weights,
and the actual centered source:

```text
0 < stepFloor, 0 < weightBase, 0 < sourceBase
stepFloor <= step_n
weightBase <= w_{n,i}
sourceBase <= -centered(S_n)_i
```

The newest certificate theorem packages this direct finite target with the
physical-total identity, nonnegative component hypotheses, the descent
identity, and the `PhysicalGrowthRepairRefinement` data:

```text
PhysicalHauptvermutungConvergenceCertificate
  -> horizon protection at every finite stage
  -> D_n -> 0
```

This is the current machine-checked "prove it" layer.  It does not construct
the physical certificate from microscopic dynamics; it proves that such a
certificate is sufficient.

The underlying convergence interface derives the required majorant from a
one-step multiplicative factor:

```text
D_{n+1} <= q * D_n,    0 <= q < 1
  -> D_n <= D_0*q^n
  -> D_n -> 0
```

Definition of done:

```text
derive gamma*D_n <= descentRate_n, stepFloor <= step_n, and
0 < stepFloor*gamma <= 2 for uniform constants gamma and stepFloor,
or prove variable product decay for q_n = 1 - step_n*rateFloor_n/2,
or prove 0 <= q_n <= qBound < 1 for those variable factors,
or prove beta <= step_n*rateFloor_n <= 2 for a beta > 0,
and prove D_n is the displayed physical aggregate with nonnegative components,
and prove summed local descent certificates for the physical aggregate,
and prove uniform lower bounds gamma <= rateFloor_n and stepFloor <= step_n,
and prove the source-local response dominates rateFloor_n times each local
distortion,
or prove the stronger centered-source floor
rateFloor_n <= -w_{n,i}*centered(S_n)_i,
or prove weighted anti-alignment plus
rateFloor_n <= w_{n,i}*alignment_{n,i},
or prove uniform lower bounds
weightFloor <= w_{n,i} and alignmentFloor <= alignment_{n,i},
or prove the rate-floor-free bound gamma <= weightFloor*alignmentFloor,
or prove the direct centered-source floor
gamma <= weightFloor*sourceFloor and sourceFloor <= -centered(S_n)_i,
or prove the gamma-free product window
0 < stepFloor*(weightFloor*sourceFloor) <= 2,
or prove positive floors
0 < stepFloor, 0 < weightFloor, 0 < sourceFloor and
stepFloor*(weightFloor*sourceFloor) <= 2,
or use the clipped effective rate
min (weightFloor*sourceFloor) (1/stepFloor) from positive floors alone,
or prove decay of the stagewise clipped product with
rateFloor_n = min (weightFloor_n*sourceFloor_n) (1/step_n),
or prove a clipped-gain floor
0 < beta <= step_n*min(weightFloor_n*sourceFloor_n, 1/step_n),
or prove an unclipped gain floor
0 < beta <= 1 and beta <= step_n*(weightFloor_n*sourceFloor_n),
or prove component floors
stepFloor <= step_n, weightBase <= weightFloor_n,
sourceBase <= sourceFloor_n, and
beta <= stepFloor*(weightBase*sourceBase),
or prove positive component floors
0 < stepFloor, 0 < weightBase, 0 < sourceBase,
stepFloor <= step_n, weightBase <= weightFloor_n,
sourceBase <= sourceFloor_n,
or prove direct positive uniform component floors
0 < stepFloor, 0 < weightBase, 0 < sourceBase,
stepFloor <= step_n, weightBase <= w_{n,i},
sourceBase <= -centered(S_n)_i,
or construct a PhysicalHauptvermutungConvergenceCertificate
for the actual causal-growth law,
from the physical causal-growth law
```

while first-order and second central horizon-area responses remain protected.

### Gate 4: Horizon-To-Einstein Limit

Goal: remove the remaining analytic caveats behind GR recovery.

Open work:

- prove finite horizon-hit estimators converge to Araki/null flux;
- prove per-cell errors vanish under the physical refinement;
- derive the null-balance hypotheses from the physical law;
- recover the semiclassical Einstein equation in the continuum limit.

### Gate 5: QFT And Standard Model IR Limit

Goal: recover known low-energy physics from the same dynamics.

Open work:

- construct the effective Hilbert space and local QFT limit;
- recover propagators, spin/statistics, gauge fields, and renormalization;
- connect finite Standard Model algebra to the same infrared limit;
- derive the parameter-identification chain instead of assuming it.

### Gate 6: Cosmology And Black Holes

Goal: cover sectors a complete theory cannot skip.

Open work:

- initial condition or cosmological measure;
- cosmological constant/dark-energy mechanism;
- dark matter prediction or exclusion;
- black-hole entropy, evaporation, and information recovery;
- compatibility with CMB, structure formation, and gravitational waves.

### Gate 7: External Tests

Goal: make the theory scientifically sharp.

Open work:

- freeze predictions before comparison;
- attach uncertainty estimates;
- record decisive future tests;
- keep a failure ledger.

## Immediate Next Theorem Targets

1. Derive each non-bridge aggregate component from order data.
2. Prove each component is quotient-invariant.
3. Prove each component has a strict zero-set theorem like the bridge-census
   component.
4. Instantiate `PhysicalGrowthSuppliesRepairSource` from the actual
   causal-growth law instead of assuming it.
5. Derive the one-step factor `D_{n+1} <= q * D_n` from the actual physical
   causal-growth law.
