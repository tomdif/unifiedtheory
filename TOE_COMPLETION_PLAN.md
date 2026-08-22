# TOE Completion Plan

Status: working plan for closing the repo's remaining theory-of-everything
gaps.  This is not a claim that the gaps are closed.

Date: 2026-08-21

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

- integrated support theorem:
  `completeChiralCausalSetGrowthLaw_transition_eq_zero_of_not_physical`;
- integrated parent-isomorphism covariance:
  `completeChiralCausalSetGrowthLaw_transition_eq_of_parent_isomorphic`;
- integrated concrete projective/quantum-consistency wrappers:
  `completeChiralCausalSetGrowthLaw_gate1_projective` and
  `completeChiralCausalSetGrowthLaw_gate1_quantum_consistent`;
- derive the physical aggregate-rate and residual-gap hypotheses from the
  microscopic law;
- remove external geometric or embedding oracles from source selection.

### Gate 2: Physical Hauptvermutung Distortion

Goal: make manifold-likeness a finite certificate target.

Implemented start:

```text
physicalHauptvermutungDistortion
physicalHauptvermutungBaseDistortion_eq_zero_iff
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
physicalHauptvermutungExactRecoveryCertificate_eventually_exact_zero
physicalHauptvermutungExactRecoveryCertificate_eventually_local_distortion_zero
physicalHauptvermutungExactRecoveryCertificate_eventually_full_operational_recovery
physicalHauptvermutungExactRecoveryCertificate_eventually_recoveredStage
physicalHauptvermutungExactRecoveryCertificate_exists_recovered_after
physicalHauptvermutungExactRecoveryCertificate_exists_observable_zero_after
physicalHauptvermutungExactRecoveryCertificate_horizon_protection_and_eventually_full_recovery
physicalHauptvermutungExactRecoveryCertificate_horizon_protection_and_recovered_after
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

The newest direct aggregate-rate theorem records the weakest current Gate 3
route.  If a positive aggregate rate `rateBase` and positive step floor
`stepFloor` satisfy

```text
rateBase*total_n <= descentRate_n
stepFloor <= step_n
```

with `total_n >= 0`, Lean clips the rate to
`min rateBase (1/stepFloor)` and proves the same horizon-protected
convergence theorem.  This bypasses the pointwise centered-source floor as a
logical requirement; that floor remains one possible way to derive the
aggregate rate from microscopic causal growth.

The newest exact-recovery theorem adds the finite-spectrum gap needed to turn
convergence into eventual recovery.  If every noncanonical bridge candidate has
uniform positive cost,

```text
0 < epsilon
candidate_n != canonical(edge_n) -> epsilon <= D_n
```

then the convergence certificate forces

```text
eventually candidate_n = canonical(edge_n)
```

The newest bridge-defect-floor theorem discharges that uniform gap from the
actual local bridge penalty.  It is enough to prove

```text
0 < epsilon
candidate_{n,i} != fourState.perm(edge_{n,i})
  -> epsilon <= bridgeCensusDefect(edge_{n,i}, candidate_{n,i})
```

for every stage and cell.  Nonnegative count, curvature, and spectral-locality
components then lift the local bridge penalty to the total physical distortion,
and the certificate gives eventual canonical recovery.

The newest parameter-free recovery theorem discharges the bridge-defect floor
too.  Lean proves

```text
candidate_{n,i} != fourState.perm(edge_{n,i})
  -> 18 <= bridgeCensusDefect(edge_{n,i}, candidate_{n,i})
```

from the fixed `18, 0, -9` census Gram pattern.  Therefore

```text
PhysicalHauptvermutungConvergenceCertificate
  -> eventually candidate_n = canonical(edge_n)
```

with no external exact-recovery gap hypothesis.

The newest operational recovery corollaries turn that candidate statement into
the bridge observables themselves:

```text
PhysicalHauptvermutungConvergenceCertificate
  -> eventually cSpecBridgeTotalDistortion_n = 0
  -> eventually every bridge incidence recovers candidate_n
```

The newest residual-split theorems isolate exactly what remains after bridge
recovery:

```text
PhysicalHauptvermutungConvergenceCertificate
  -> eventually total_n = baseDistortion_n
  -> baseDistortion_n -> 0
  -> each finite count/curvature/spectral residual -> 0
  -> fixed positive residual gaps imply eventually total_n = 0
```

The exact-recovery package records those residual gaps as one reusable
certificate:

```text
PhysicalHauptvermutungExactRecoveryCertificate
  -> horizon protected at every stage
  -> eventually total_n = 0
  -> eventually each local physical distortion is 0
  -> eventually bridge total is 0 and bridge incidences recover transport
  -> exists N, every n >= N satisfies PhysicalHauptvermutungRecoveredStage
  -> exists N, every n >= N has all observable defects zero/canonical
```

The base zero-set theorem now isolates the non-bridge part algebraically:
under nonnegative count-window, curvature-bias, and spectral-locality channels,

```text
physicalHauptvermutungBaseDistortion = 0
  <-> every countWindow, curvatureBias, and spectralLocality component is 0
```

The remaining Gate 2 work is semantic rather than arithmetic: prove that those
three zero component functions are exactly the intended finite order-to-geometry
conditions.

The underlying convergence interface derives the required majorant from a
one-step multiplicative factor:

```text
D_{n+1} <= q * D_n,    0 <= q < 1
  -> D_n <= D_0*q^n
  -> D_n -> 0
```

Definition of done:

```text
derive a positive direct aggregate rate
rateBase*D_n <= descentRate_n and stepFloor <= step_n,
or derive gamma*D_n <= descentRate_n, stepFloor <= step_n, and
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
from the physical causal-growth law
```

while first-order and second central horizon-area responses remain protected.

### Gate 4: Horizon-To-Einstein Limit

Goal: remove the remaining analytic caveats behind GR recovery.

Implemented start:

```text
KFCausalCSpecRecoveredStageGRLimit
PhysicalHauptvermutungRecoveredStage.rssPoissonError_zero
physicalHauptvermutungExactRecoveryCertificate_eventually_rssPoissonError_zero
physicalHauptvermutungExactRecoveryCertificate_exists_rssPoissonError_zero_after
KFCausalCSpecRecoveredStageBDGInterface
RecoveredStageBDGAsymptoticInterface
RecoveredStageBDGAsymptoticInterface.rssPoissonError_zero_and_bdg_dalembertian_tendsto
RecoveredStageBDGAsymptoticInterface.rssPoissonError_zero_and_standard_bdg_dalembertian_tendsto
KFCausalCSpecRecoveredStageBDGProfile
BDGProfileSequenceAsymptotics.layer_asymptotics
RecoveredStageBDGProfileSequenceInterface.rssPoissonError_zero_and_profile_bdg_dalembertian_tendsto
RecoveredStageBDGProfileSequenceInterface.rssPoissonError_zero_and_standard_profile_bdg_dalembertian_tendsto
KFCausalCSpecRecoveredStageBDG4DOperator
BDG4DOperatorProfileData.tendsto
BDG4DOperatorProfileData.sampled_tendsto
BDG4DOperatorProfileData.sequenceAsymptotics_layer_asymptotics
KFCausalCSpecRecoveredStageBDG4DRecovered
RecoveredStageBDG4DOperatorInterface.rssPoissonError_zero_and_operator_tendsto
RecoveredStageBDG4DOperatorInterface.recoveredStage_and_operator_tendsto
KFCausalCSpecRecoveredStageBDG4DChart
RecoveredStageBDG4DChartInterface.toOperatorInterface
RecoveredStageBDG4DChartInterface.rssPoissonError_zero_and_chart_operator_tendsto
RecoveredStageBDG4DChartInterface.recoveredStage_and_chart_operator_tendsto
KFCausalCSpecRecoveredStageBDG4DPhysicalChart
RecoveredStageBDG4DPhysicalChartInterface.applies_quantitative_hauptvermutung_at
RecoveredStageBDG4DPhysicalChartInterface.distortionBound_tendsto_zero
RecoveredStageBDG4DPhysicalChartInterface.rssPoissonError_zero_chart_operator_tendsto_and_distortionBound_tendsto_zero
RecoveredStageBDG4DPhysicalChartInterface.recoveredStage_chart_operator_tendsto_and_distortionBound_tendsto_zero
KFCausalCSpecRecoveredStageBDG4DMatchedChart
RecoveredStageExactCSpecSequence.countWindow_sum_tendsto_zero
RecoveredStageExactCSpecSequence.curvatureBias_sum_tendsto_zero
RecoveredStageExactCSpecSequence.spectralLocality_sum_tendsto_zero
RecoveredStageBDG4DMatchedPhysicalChartInterface.toPhysicalChartInterface
RecoveredStageBDG4DMatchedPhysicalChartInterface.rssPoissonError_zero_chart_operator_tendsto_and_distortionBound_tendsto_zero
RecoveredStageBDG4DMatchedPhysicalChartInterface.recoveredStage_chart_operator_tendsto_and_distortionBound_tendsto_zero
KFCausalCSpecRecoveredStageBDG4DScheduledDensity
affineDensity_tendsto_atTop
RecoveredStageBDG4DScheduledDensityInterface.density_tendsto_atTop
RecoveredStageBDG4DScheduledDensityInterface.toMatchedPhysicalChartInterface
RecoveredStageBDG4DScheduledDensityInterface.rssPoissonError_zero_chart_operator_tendsto_and_distortionBound_tendsto_zero
RecoveredStageBDG4DScheduledDensityInterface.recoveredStage_chart_operator_tendsto_and_distortionBound_tendsto_zero
KFCausalCSpecRecoveredStageBDG4DOperatorSplit
BDG4DOperatorProfileSplitData.toProfileData
BDG4DOperatorProfileSplitData.sampled_tendsto
RecoveredStageBDG4DScheduledDensitySplitOperatorInterface.toScheduledDensityInterface
RecoveredStageBDG4DScheduledDensitySplitOperatorInterface.rssPoissonError_zero_chart_operator_tendsto_and_distortionBound_tendsto_zero
RecoveredStageBDG4DScheduledDensitySplitOperatorInterface.recoveredStage_chart_operator_tendsto_and_distortionBound_tendsto_zero
KFCausalCSpecRecoveredStageBDG4DConeBound
BDG4DOperatorProfileConeBound.of_activeKernelBound
BDG4DOperatorProfileKernelSplitData.toSplitData
BDG4DOperatorProfileKernelSplitData.sampled_tendsto
RecoveredStageBDG4DScheduledDensityKernelOperatorInterface.toSplitOperatorInterface
RecoveredStageBDG4DScheduledDensityKernelOperatorInterface.rssPoissonError_zero_chart_operator_tendsto_and_distortionBound_tendsto_zero
RecoveredStageBDG4DScheduledDensityKernelOperatorInterface.recoveredStage_chart_operator_tendsto_and_distortionBound_tendsto_zero
```

This first finite bridge connects exact recovered CSpec stages to the concrete
RSS/Poisson error budget consumed by the entropy-flux limit module: recovered
zero count-window and curvature-bias residuals force the cellwise error
`(epsilon + b + epsilon*b) S` to be zero.

The BDG interface bridge now bundles exact finite recovery with the named
per-layer BDG/RNC asymptotic hypotheses and proves that this package yields
both zero finite horizon-flux error and the BDG d'Alembertian continuum limit.
The profile-sequence bridge now converts real high-density profile limits
sampled along `density n -> atTop` into the sequence-level per-layer
asymptotics consumed by that interface.
The concrete 4D operator bridge packages the existing reduced 4D BDG operator
theorem as a one-channel profile source for recovered stages.
The recovered 4D operator bridge now combines exact finite recovery with that
concrete profile source: supplied 4D operator data gives both zero finite
horizon-flux error and convergence of the sampled reduced 4D BDG operator
profile.
The local-chart supplier bridge splits the exact finite CSpec sequence from
the analytic chart profile data.  It proves that recovered local 4D charts
supplying density, point-field, curvature, and `BDG4DOperatorProfileData`
produce the concrete recovered-stage operator interface and the same combined
zero-error/operator-limit theorem.
The physical-chart supplier bridge now uses the existing
`PhysicalGrowthHauptvermutungCertificate` sequence as the density and coordinate
source for that chart data.  It proves that each finite chart certificate
applies the quantitative Hauptvermutung bridge, that the displayed chart
distortion bound tends to zero when count, curvature, and pair-consistency
channels vanish, and that exact finite recovery plus the chart/operator package
gives zero finite horizon error, sampled 4D operator convergence, and chart
distortion collapse together.
The matched-channel bridge removes the separate chart-channel convergence
assumptions when the physical chart certificate uses the recovered residual
sums:
`chart.countWindow = sum recovered.countWindow`,
`chart.curvatureBias = sum recovered.curvatureBias`, and
`chart.pairConsistency = sum recovered.spectralLocality`.  Exact recovery
proves those three sums tend to zero, then instantiates the physical-chart
interface.
The scheduled-density bridge removes one more free convergence input: if the
chart certificate density is affine in the refinement index,
`density_n = densityBase + densityStep*n`, and `densityStep > 0`, Lean proves
`density_n -> atTop` and instantiates the matched physical-chart interface.
The operator-split bridge factors the remaining monolithic
`BDG4DOperatorProfileData` package into function, scale, regularity,
uniform-bound, support, and cone-bound certificates.  Lean proves those split
certificates assemble back into the 4D operator profile package, then feeds
the assembled package through the scheduled-density chart bridge.
The cone-bound bridge narrows the hardest remaining analytic certificate:
instead of assuming the full product estimate directly, the chart side supplies
lower lightcone support and the existing uniform profile bound, the kernel side
supplies an active-region weighted `f4D` bound, and one cone-scale calibration
inequality assembles the combined estimate.

Open work:

- prove finite horizon-hit estimators converge to Araki/null flux;
- prove the physical causal-growth law supplies a
  `RecoveredStageBDG4DScheduledDensityInterface`, especially the affine density
  law and matched residual identities;
- prove the physical recovered chart supplies `BDG4DOperatorProfileKernelSplitData`:
  the profile functions, positive support scales, continuity and derivative
  regularity, uniform bounds, compact support, lower lightcone support,
  active-region weighted kernel estimate, and cone-scale calibration;
- derive the null-balance hypotheses from the physical law;
- recover the semiclassical Einstein equation in the continuum limit.

### Gate 5: QFT And Standard Model IR Limit

Goal: recover known low-energy physics from the same dynamics.

Completed algebraic groundwork:

- `KFHopfSpinorBlochBridge` proves the Hopf spinor/Bloch algebraic core:
  normalized two-component spinors map to unit Bloch vectors, and common unit
  `U(1)` phase multiplication is invisible to the Bloch coordinates.  The
  coordinates are proved to agree with the existing
  `WignerHardQubit.blochVector`, giving Gate 5 a concrete
  upstairs-state/phase-fiber/downstairs-observable architecture.
- `KFRecoveredCSpecHopfFiber` lifts that algebra to local recovered-stage
  fiber data: each stage/site normalized spinor has a unit Bloch observable,
  agrees with the repo Bloch vector, and is invariant under local stagewise
  `U(1)` phase choices.

Open work:

- construct the effective Hilbert space and local QFT limit;
- recover propagators, spin/statistics, gauge fields, and renormalization;
- lift the algebraic Hopf bridge to a topological/principal-bundle statement
  with quotient topology, local trivializations, and characteristic classes;
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

## Swarm Round 1 Integration

Six bounded agents reviewed the remaining gates without running `lake build`.
The integrated Lean results are:

```text
physicalHauptvermutungBaseDistortion_eq_zero_iff
physicalGrowthRepairRefinement_horizon_protection_and_total_tendsto_zero_of_positive_uniform_direct_rate_floor
```

The next high-value theorem targets are:

1. Gate 1: derive the physical aggregate-rate and residual-gap hypotheses from
   `completeChiralCausalSetGrowthLaw`, or identify the additional microscopic
   selection principle needed for the canonical pair coupling.
2. Gate 2: give semantic zero-set theorems for `countWindow`, `curvatureBias`,
   and `spectralLocality`, starting with the pair-consistency bridge.
3. Gate 3: derive the direct aggregate rate from the microscopic law.
4. Gate 4: instantiate `RecoveredStageBDG4DScheduledDensityInterface` from the
   physical causal-growth law, including the affine density law, matched
   residual identities, and the split `BDG4DOperatorProfileKernelSplitData`
   support/regularity/lightcone-kernel components.
5. Gate 5: attach finite Hilbert fibers and local Born normalization to each
   recovered CSpec stage before making continuum QFT claims.
6. Gate 7: use the canonical JSON preregistration ledger for future empirical
   comparisons.
