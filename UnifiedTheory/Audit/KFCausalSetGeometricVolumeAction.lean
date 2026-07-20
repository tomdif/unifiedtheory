/-
  Audit/KFCausalSetGeometricVolumeAction.lean

  GEOMETRIC ORIGIN OF THE HARMONIC SPECTATOR SOURCE

  The preceding microscopic-action module isolated one remaining input:
  a relabeling-invariant, unit-normalized event-slot density.  This file
  identifies an honest geometric origin for that density and, equally
  importantly, proves the precise limit of the derivation.

  In causal-set geometry, spacetime volume is event number times one nonzero
  cell volume.  A physical one-element birth therefore changes the volume by
  one cell.  Dividing that local volume action by the total post-birth volume
  gives

      (V_{n+1} - V_n) / V_{n+1} = 1 / (n+1).

  The cell volume and any nonzero cosmological coupling cancel.  Thus the
  previously postulated spectator action is constructed from the normalized
  cosmological-volume sector of a discrete gravitational action.  Its complete
  harmonic, zero-free, projective, strongly-positive dynamics follows from the
  existing promotion theorem.

  This is not a derivation from the full Benincasa--Dowker curvature action.
  Two sharp boundary theorems explain why:

  * order-isomorphism covariance admits normalized, nonuniform geometric
    densities (the normalized past-volume profile on a two-chain is explicit);
  * a trace-free curvature correction preserves total normalization, but the
    density remains harmonic exactly when that correction vanishes pointwise.

  Hence the new physics statement is scoped exactly: the harmonic law is the
  unique normalized NUMBER--VOLUME channel.  Deriving why the spectator sector
  projects out curvature, or how curvature feeds the independent orientation
  channel, remains the next dynamical frontier.
-/

import UnifiedTheory.Audit.KFCausalSetMicroscopicSpectatorAction
import UnifiedTheory.LayerA.VolumeFromCounting

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Audit.KFCausalSetGeometricVolumeAction

noncomputable section

open scoped BigOperators
open UnifiedTheory.Audit.KFCausalSetSequentialGrowth
open UnifiedTheory.Audit.KFCausalSetTransitionEdges
open UnifiedTheory.Audit.KFCausalSetBellCausality
open UnifiedTheory.Audit.KFCausalSetCompleteChiralLaw
open UnifiedTheory.Audit.KFCausalSetMultiplicityCorrectedRunning
open UnifiedTheory.Audit.KFCausalSetMicroscopicSpectatorAction
open UnifiedTheory.Audit.KFOrientationGrowthDecoherence
open UnifiedTheory.LayerA.VolumeFromCounting

/-! ## 1. Number is volume on a causal set -/

/-- The existing continuum-facing counting-volume structure specialized to
sequential-growth ranks. Region index `n` represents the post-birth causet with
`n+1` events. -/
noncomputable def sequentialGrowthCountingVolume
    (density : ℝ) (hDensity : 0 < density) : CountingVolume where
  count := fun n => (n + 1 : ℕ)
  count_pos := by
    intro n
    positivity
  density := density
  density_pos := hDensity

@[simp]
theorem sequentialGrowthCountingVolume_count
    (density : ℝ) (hDensity : 0 < density) (n : ℕ) :
    (sequentialGrowthCountingVolume density hDensity).count n =
      ((n + 1 : ℕ) : ℝ) :=
  rfl

/-- Direct bridge to `VolumeFromCounting`: the volume of one event divided by
the volume of an `n+1`-event causet is the parameter-free count ratio
`1/(n+1)`. The sprinkling density cancels by the pre-existing theorem. -/
theorem countingVolume_singleEvent_fraction_eq_uniform
    (density : ℝ) (hDensity : 0 < density) (n : ℕ) :
    (sequentialGrowthCountingVolume density hDensity).volume 0 /
        (sequentialGrowthCountingVolume density hDensity).volume n =
      (1 : ℝ) / (n + 1) := by
  rw [volume_ratio_parameter_free]
  simp [sequentialGrowthCountingVolume]

/-- Causal-set spacetime volume at rank `n`: event number times one microscopic
cell volume.  The cell volume is kept arbitrary so that its cancellation is a
theorem rather than a choice of units. -/
def causalSetCountingVolumeQ (cellVolume : ℚ) (n : ℕ) : ℚ :=
  (n : ℚ) * cellVolume

@[simp]
theorem causalSetCountingVolumeQ_zero (cellVolume : ℚ) :
    causalSetCountingVolumeQ cellVolume 0 = 0 := by
  simp [causalSetCountingVolumeQ]

theorem causalSetCountingVolumeQ_succ (cellVolume : ℚ) (n : ℕ) :
    causalSetCountingVolumeQ cellVolume (n + 1) =
      causalSetCountingVolumeQ cellVolume n + cellVolume := by
  simp [causalSetCountingVolumeQ]
  ring

/-- Every actual one-element extension changes number-volume by exactly one
cell.  The transition witness certifies that this is a physical edge, while
the fixed-cardinality types do the numerical work. -/
theorem physicalOneElementBirth_volume_increment
    (cellVolume : ℚ) {n : ℕ}
    (parent : UnlabeledCardinalCausalOrder n)
    (child : UnlabeledCardinalCausalOrder (n + 1))
    (_hPhysical : IsUnlabeledOneElementExtension parent child) :
    causalSetCountingVolumeQ cellVolume (n + 1) -
        causalSetCountingVolumeQ cellVolume n = cellVolume := by
  rw [causalSetCountingVolumeQ_succ]
  ring

/-- Fraction of the post-birth spacetime volume supplied by its one new event.
This is the normalized local cosmological-volume action density. -/
def normalizedNumberVolumeBirthDensityQ
    (cellVolume : ℚ) (n : ℕ) : ℚ :=
  (causalSetCountingVolumeQ cellVolume (n + 1) -
      causalSetCountingVolumeQ cellVolume n) /
    causalSetCountingVolumeQ cellVolume (n + 1)

/-- The microscopic cell volume cancels: normalized one-cell growth is the
uniform spectator source. -/
theorem normalizedNumberVolumeBirthDensityQ_eq_uniform
    (cellVolume : ℚ) (hCell : cellVolume ≠ 0) (n : ℕ) :
    normalizedNumberVolumeBirthDensityQ cellVolume n =
      (1 : ℚ) / (n + 1) := by
  rw [normalizedNumberVolumeBirthDensityQ,
    causalSetCountingVolumeQ_succ]
  simp only [add_sub_cancel_left]
  unfold causalSetCountingVolumeQ
  field_simp

/-- The same cancellation holds if the number-volume term carries an arbitrary
nonzero cosmological coupling.  Only the product of coupling and cell volume
enters, and neither scale survives normalization. -/
theorem normalizedCosmologicalVolumeBirthDensityQ_eq_uniform
    (cosmologicalCoupling cellVolume : ℚ)
    (hCoupling : cosmologicalCoupling ≠ 0)
    (hCell : cellVolume ≠ 0) (n : ℕ) :
    (cosmologicalCoupling *
          (causalSetCountingVolumeQ cellVolume (n + 1) -
            causalSetCountingVolumeQ cellVolume n)) /
        (cosmologicalCoupling *
          causalSetCountingVolumeQ cellVolume (n + 1)) =
      (1 : ℚ) / (n + 1) := by
  rw [causalSetCountingVolumeQ_succ]
  simp only [add_sub_cancel_left]
  unfold causalSetCountingVolumeQ
  field_simp

/-! ## 2. The geometric action and the complete quantum law -/

/-- The vacuum spectator action constructed, rather than postulated, from the
normalized number-volume increment. -/
def numberVolumeVacuumSpectatorCausalAction
    (cellVolume : ℚ) (hCell : cellVolume ≠ 0) :
    VacuumSpectatorCausalAction where
  source := fun n _path _i =>
    normalizedNumberVolumeBirthDensityQ cellVolume n
  relabelingInvariant := by
    intro n path
    unfold IsEventSlotRelabelingInvariant
    intro relabeling i
    rfl
  normalized := by
    intro n path
    simp_rw [normalizedNumberVolumeBirthDensityQ_eq_uniform
      cellVolume hCell n]
    simp [div_eq_mul_inv]
    field_simp

/-- The geometric construction is definitionally independent of the history
and uniquely coincides with the canonical microscopic action. -/
theorem numberVolumeVacuumSpectatorCausalAction_eq_canonical
    (cellVolume : ℚ) (hCell : cellVolume ≠ 0) :
    numberVolumeVacuumSpectatorCausalAction cellVolume hCell =
      canonicalVacuumSpectatorCausalAction :=
  vacuumSpectatorCausalAction_unique _

/-- On every genuine physical birth, the action source is exactly the
fractional geometric volume increment. -/
theorem geometricActionSource_eq_physicalVolumeIncrement
    (cellVolume : ℚ) (hCell : cellVolume ≠ 0) {n : ℕ}
    (path : RankedGrowthPath CausalSetGrowthBranch (n + 1))
    (parent : UnlabeledCardinalCausalOrder n)
    (child : UnlabeledCardinalCausalOrder (n + 1))
    (_hPhysical : IsUnlabeledOneElementExtension parent child)
    (i : Fin (n + 1)) :
    (numberVolumeVacuumSpectatorCausalAction cellVolume hCell).source
        n path i =
      (causalSetCountingVolumeQ cellVolume (n + 1) -
          causalSetCountingVolumeQ cellVolume n) /
        causalSetCountingVolumeQ cellVolume (n + 1) := by
  rfl

/-- The complete action-selected chiral dynamics now follows from one geometric
input: causal-set number is spacetime volume with a nonzero cell volume. -/
theorem numberVolumeAction_derives_completeQuantumGrowth
    (cellVolume : ℚ) (hCell : cellVolume ≠ 0)
    (chirality : Fin 2) :
    let action := numberVolumeVacuumSpectatorCausalAction cellVolume hCell
    action = canonicalVacuumSpectatorCausalAction
      ∧ microscopicCausalActionChargeQ action 2 = (3 : ℚ) / 2
      ∧ microscopicSpectatorPairCouplingQ action =
          harmonicCriticalPairCouplingQ
      ∧ (∀ n : ℕ, ∀ parent : CardinalCausalOrder n,
          causalEdgeAmplitudePartition
            (interactingChiralCausalEdgeAmplitude
              (microscopicSpectatorPairCoupling action n) chirality)
            parent ≠ 0)
      ∧ IsStronglyPositiveGrowthFunctional
          (infiniteRankedCylinderDecoherence
            (microscopicSpectatorCausalSetGrowthLaw action chirality)) := by
  dsimp
  have hComplete := microscopicSpectatorAction_completeLaw
    (numberVolumeVacuumSpectatorCausalAction cellVolume hCell) chirality
  exact ⟨numberVolumeVacuumSpectatorCausalAction_eq_canonical cellVolume hCell,
    hComplete.2.2.1, hComplete.2.2.2.1, hComplete.2.2.2.2.1,
    hComplete.2.2.2.2.2.2.2⟩

/-! ## 3. Why covariance alone cannot select the volume channel -/

/-- Correct covariance for an event density on labeled representatives:
transport the order and the event together along every order isomorphism.  This
is weaker than invariance under every permutation while holding the order fixed. -/
def IsCausalOrderRelabelingCovariant
    (density : ∀ {n : ℕ}, CardinalCausalOrder n → Fin n → ℚ) : Prop :=
  ∀ {n : ℕ} (parent parent' : CardinalCausalOrder n)
    (relabeling : Equiv.Perm (Fin n))
    (_hRel : ∀ i j,
      parent.rel i j = parent'.rel (relabeling i) (relabeling j))
    (i : Fin n),
    density parent' (relabeling i) = density parent i

/-- Order-sensitive local past volume: the number of events in the inclusive
causal past of an event. -/
def causalPastVolumeQ {n : ℕ} (parent : CardinalCausalOrder n)
    (i : Fin n) : ℚ :=
  ∑ j : Fin n, if parent.rel j i = true then 1 else 0

theorem causalPastVolumeQ_relabel {n : ℕ}
    (parent parent' : CardinalCausalOrder n)
    (relabeling : Equiv.Perm (Fin n))
    (hRel : ∀ i j,
      parent.rel i j = parent'.rel (relabeling i) (relabeling j))
    (i : Fin n) :
    causalPastVolumeQ parent' (relabeling i) =
      causalPastVolumeQ parent i := by
  unfold causalPastVolumeQ
  rw [← Equiv.sum_comp relabeling
    (fun j => if parent'.rel j (relabeling i) = true then (1 : ℚ) else 0)]
  apply Finset.sum_congr rfl
  intro j hj
  rw [← hRel j i]

/-- Total inclusive-past volume, used only to normalize the geometric profile. -/
def totalCausalPastVolumeQ {n : ℕ}
    (parent : CardinalCausalOrder n) : ℚ :=
  ∑ i : Fin n, causalPastVolumeQ parent i

theorem totalCausalPastVolumeQ_relabel {n : ℕ}
    (parent parent' : CardinalCausalOrder n)
    (relabeling : Equiv.Perm (Fin n))
    (hRel : ∀ i j,
      parent.rel i j = parent'.rel (relabeling i) (relabeling j)) :
    totalCausalPastVolumeQ parent' = totalCausalPastVolumeQ parent := by
  unfold totalCausalPastVolumeQ
  calc
    ∑ i, causalPastVolumeQ parent' i =
        ∑ i, causalPastVolumeQ parent' (relabeling i) :=
      (Equiv.sum_comp relabeling (causalPastVolumeQ parent')).symm
    _ = ∑ i, causalPastVolumeQ parent i := by
      apply Finset.sum_congr rfl
      intro i hi
      exact causalPastVolumeQ_relabel parent parent' relabeling hRel i

/-- A normalized but order-sensitive geometric event density. -/
def normalizedCausalPastVolumeDensityQ {n : ℕ}
    (parent : CardinalCausalOrder n) (i : Fin n) : ℚ :=
  causalPastVolumeQ parent i / totalCausalPastVolumeQ parent

theorem normalizedCausalPastVolumeDensityQ_covariant :
    IsCausalOrderRelabelingCovariant
      (@normalizedCausalPastVolumeDensityQ) := by
  intro n parent parent' relabeling hRel i
  unfold normalizedCausalPastVolumeDensityQ
  rw [causalPastVolumeQ_relabel parent parent' relabeling hRel,
    totalCausalPastVolumeQ_relabel parent parent' relabeling hRel]

theorem normalizedCausalPastVolumeDensityQ_sum_one {n : ℕ}
    (parent : CardinalCausalOrder n)
    (hTotal : totalCausalPastVolumeQ parent ≠ 0) :
    ∑ i, normalizedCausalPastVolumeDensityQ parent i = 1 := by
  unfold normalizedCausalPastVolumeDensityQ
  rw [← Finset.sum_div]
  exact div_self hTotal

/-- The two-event causal chain. -/
def cardinalCausalChainTwo : CardinalCausalOrder 2 where
  rel := fun i j => decide (i ≤ j)
  refl := by simp
  antisymm := by
    intro i j hij hji
    exact le_antisymm (of_decide_eq_true hij) (of_decide_eq_true hji)
  trans := by
    intro i j k hij hjk
    exact decide_eq_true
      (le_trans (of_decide_eq_true hij) (of_decide_eq_true hjk))

theorem chainTwo_causalPastVolumeQ_zero :
    causalPastVolumeQ cardinalCausalChainTwo (0 : Fin 2) = 1 := by
  simp only [causalPastVolumeQ, Fin.sum_univ_two]
  norm_num [cardinalCausalChainTwo]

theorem chainTwo_causalPastVolumeQ_one :
    causalPastVolumeQ cardinalCausalChainTwo (1 : Fin 2) = 2 := by
  simp only [causalPastVolumeQ, Fin.sum_univ_two]
  norm_num [cardinalCausalChainTwo]

theorem chainTwo_totalCausalPastVolumeQ :
    totalCausalPastVolumeQ cardinalCausalChainTwo = 3 := by
  simp only [totalCausalPastVolumeQ, Fin.sum_univ_two,
    chainTwo_causalPastVolumeQ_zero, chainTwo_causalPastVolumeQ_one]
  norm_num

theorem chainTwo_normalizedCausalPastVolumeDensityQ_zero :
    normalizedCausalPastVolumeDensityQ cardinalCausalChainTwo (0 : Fin 2) =
      (1 : ℚ) / 3 := by
  unfold normalizedCausalPastVolumeDensityQ
  rw [chainTwo_causalPastVolumeQ_zero,
    chainTwo_totalCausalPastVolumeQ]

theorem chainTwo_normalizedCausalPastVolumeDensityQ_one :
    normalizedCausalPastVolumeDensityQ cardinalCausalChainTwo (1 : Fin 2) =
      (2 : ℚ) / 3 := by
  unfold normalizedCausalPastVolumeDensityQ
  rw [chainTwo_causalPastVolumeQ_one,
    chainTwo_totalCausalPastVolumeQ]

theorem chainTwo_normalizedCausalPastVolumeDensityQ_sum_one :
    ∑ i, normalizedCausalPastVolumeDensityQ cardinalCausalChainTwo i = 1 := by
  apply normalizedCausalPastVolumeDensityQ_sum_one
  rw [chainTwo_totalCausalPastVolumeQ]
  norm_num

/-- Exact no-go: the correct order-isomorphism covariance condition admits a
normalized geometric density that is not invariant under arbitrary event-slot
permutations.  General covariance alone therefore cannot force `1/n`. -/
theorem causalOrderCovariance_does_not_force_eventSlotExchangeability :
    IsCausalOrderRelabelingCovariant
        (@normalizedCausalPastVolumeDensityQ)
      ∧ (∑ i,
          normalizedCausalPastVolumeDensityQ cardinalCausalChainTwo i = 1)
      ∧ ¬ IsEventSlotRelabelingInvariant
          (normalizedCausalPastVolumeDensityQ cardinalCausalChainTwo) := by
  refine ⟨normalizedCausalPastVolumeDensityQ_covariant,
    chainTwo_normalizedCausalPastVolumeDensityQ_sum_one, ?_⟩
  intro hInvariant
  have hSwap := hInvariant
    (Equiv.swap (0 : Fin 2) (1 : Fin 2)) (0 : Fin 2)
  simp only [Equiv.swap_apply_left] at hSwap
  rw [chainTwo_normalizedCausalPastVolumeDensityQ_one,
    chainTwo_normalizedCausalPastVolumeDensityQ_zero] at hSwap
  norm_num at hSwap

/-! ## 4. The exact curvature obstruction -/

/-- Add a local curvature correction to the one-cell volume term and normalize
by the uncorrected total volume.  A trace-free correction is the discrete
analogue of separating a pure volume mode from an inhomogeneous curvature
profile. -/
def volumeCurvatureDensityQ {n : ℕ} (cellVolume : ℚ)
    (curvatureCorrection : Fin n → ℚ) (i : Fin n) : ℚ :=
  (cellVolume + curvatureCorrection i) / ((n : ℚ) * cellVolume)

/-- Trace-free curvature changes the profile but not its total normalization. -/
theorem volumeCurvatureDensityQ_sum_one {n : ℕ}
    (hn : 0 < n) (cellVolume : ℚ) (hCell : cellVolume ≠ 0)
    (curvatureCorrection : Fin n → ℚ)
    (hTraceFree : ∑ i, curvatureCorrection i = 0) :
    ∑ i, volumeCurvatureDensityQ cellVolume curvatureCorrection i = 1 := by
  unfold volumeCurvatureDensityQ
  rw [← Finset.sum_div, Finset.sum_add_distrib, hTraceFree]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, add_zero]
  have hnQ : (n : ℚ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  exact div_self (mul_ne_zero hnQ hCell)

/-- Rigidity of the volume channel: after a trace-free curvature split, the
normalized density is uniform exactly when the curvature correction vanishes
at every event. -/
theorem volumeCurvatureDensityQ_eq_uniform_iff {n : ℕ}
    (hn : 0 < n) (cellVolume : ℚ) (hCell : cellVolume ≠ 0)
    (curvatureCorrection : Fin n → ℚ) :
    (∀ i, volumeCurvatureDensityQ cellVolume curvatureCorrection i =
        (1 : ℚ) / n) ↔
      ∀ i, curvatureCorrection i = 0 := by
  have hnQ : (n : ℚ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  constructor
  · intro hUniform i
    have hi := hUniform i
    unfold volumeCurvatureDensityQ at hi
    field_simp [hnQ, hCell] at hi
    linarith
  · intro hZero i
    unfold volumeCurvatureDensityQ
    rw [hZero i]
    field_simp [hnQ, hCell]
    simp

/-! ## 5. The unique volume projector and the orientation residual -/

/-- Project an arbitrary event density onto its permutation-invariant volume
mode by finite averaging. -/
def eventVolumeProjectionQ {n : ℕ} (density : Fin n → ℚ)
    (_i : Fin n) : ℚ :=
  (∑ j, density j) / n

/-- The complementary centered profile.  For a geometric action this is the
local curvature/shape information removed by the volume projection. -/
def eventCurvatureResidualQ {n : ℕ} (density : Fin n → ℚ)
    (i : Fin n) : ℚ :=
  density i - eventVolumeProjectionQ density i

theorem eventVolumeProjectionQ_relabelingInvariant {n : ℕ}
    (density : Fin n → ℚ) :
    IsEventSlotRelabelingInvariant (eventVolumeProjectionQ density) := by
  intro relabeling i
  rfl

/-- Averaging preserves the complete total weight. -/
theorem eventVolumeProjectionQ_sum {n : ℕ} (hn : 0 < n)
    (density : Fin n → ℚ) :
    ∑ i, eventVolumeProjectionQ density i = ∑ i, density i := by
  unfold eventVolumeProjectionQ
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul]
  have hnQ : (n : ℚ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  field_simp

/-- The removed geometric channel is trace-free. -/
theorem eventCurvatureResidualQ_sum_zero {n : ℕ} (hn : 0 < n)
    (density : Fin n → ℚ) :
    ∑ i, eventCurvatureResidualQ density i = 0 := by
  unfold eventCurvatureResidualQ
  rw [Finset.sum_sub_distrib, eventVolumeProjectionQ_sum hn]
  ring

/-- Every invariant density equals its own finite average. -/
theorem relabelingInvariant_eq_eventVolumeProjectionQ {n : ℕ}
    (hn : 0 < n) (density : Fin n → ℚ)
    (hInvariant : IsEventSlotRelabelingInvariant density) (i : Fin n) :
    density i = eventVolumeProjectionQ density i := by
  have hSum : ∑ j, density j = (n : ℚ) * density i := by
    calc
      ∑ j, density j = ∑ _j : Fin n, density i := by
        apply Finset.sum_congr rfl
        intro j hj
        exact eventSlotRelabelingInvariant_implies_exchangeable
          hInvariant j i
      _ = (n : ℚ) * density i := by simp
  unfold eventVolumeProjectionQ
  rw [hSum]
  have hnQ : (n : ℚ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  field_simp

/-- Exact channel criterion: the centered residual vanishes precisely for the
permutation-invariant volume sector. -/
theorem eventCurvatureResidualQ_eq_zero_iff {n : ℕ} (hn : 0 < n)
    (density : Fin n → ℚ) :
    (∀ i, eventCurvatureResidualQ density i = 0) ↔
      IsEventSlotRelabelingInvariant density := by
  constructor
  · intro hZero relabeling i
    unfold eventCurvatureResidualQ at hZero
    have hRelabeled := hZero (relabeling i)
    have hOriginal := hZero i
    dsimp [eventVolumeProjectionQ] at hRelabeled hOriginal
    linarith
  · intro hInvariant i
    unfold eventCurvatureResidualQ
    rw [relabelingInvariant_eq_eventVolumeProjectionQ
      hn density hInvariant i]
    ring

/-- A normalized density projects to the universal `1/n` number-volume law. -/
theorem normalized_eventVolumeProjectionQ_eq_uniform {n : ℕ}
    (density : Fin n → ℚ)
    (hNormalized : ∑ i, density i = 1) (i : Fin n) :
    eventVolumeProjectionQ density i = (1 : ℚ) / n := by
  unfold eventVolumeProjectionQ
  rw [hNormalized]

/-- The average is the unique assignment that is permutation invariant and
preserves the total event weight for every input density. -/
theorem eventVolumeProjectionQ_unique {n : ℕ} (hn : 0 < n)
    (projection : (Fin n → ℚ) → Fin n → ℚ)
    (hInvariant : ∀ density,
      IsEventSlotRelabelingInvariant (projection density))
    (hTotal : ∀ density,
      ∑ i, projection density i = ∑ i, density i) :
    projection = eventVolumeProjectionQ := by
  funext density i
  rw [relabelingInvariant_eq_eventVolumeProjectionQ
    hn (projection density) (hInvariant density) i]
  unfold eventVolumeProjectionQ
  rw [hTotal density]

def chainTwoGeometricCurvatureResidualQ (i : Fin 2) : ℚ :=
  eventCurvatureResidualQ
    (normalizedCausalPastVolumeDensityQ cardinalCausalChainTwo) i

theorem chainTwoGeometricCurvatureResidualQ_zero :
    chainTwoGeometricCurvatureResidualQ (0 : Fin 2) = -(1 : ℚ) / 6 := by
  unfold chainTwoGeometricCurvatureResidualQ eventCurvatureResidualQ
  rw [chainTwo_normalizedCausalPastVolumeDensityQ_zero,
    normalized_eventVolumeProjectionQ_eq_uniform
      (normalizedCausalPastVolumeDensityQ cardinalCausalChainTwo)
      chainTwo_normalizedCausalPastVolumeDensityQ_sum_one]
  norm_num

theorem chainTwoGeometricCurvatureResidualQ_one :
    chainTwoGeometricCurvatureResidualQ (1 : Fin 2) = (1 : ℚ) / 6 := by
  unfold chainTwoGeometricCurvatureResidualQ eventCurvatureResidualQ
  rw [chainTwo_normalizedCausalPastVolumeDensityQ_one,
    normalized_eventVolumeProjectionQ_eq_uniform
      (normalizedCausalPastVolumeDensityQ cardinalCausalChainTwo)
      chainTwo_normalizedCausalPastVolumeDensityQ_sum_one]
  norm_num

/-- At rank two the channel discarded by the volume projection is exactly
reflection odd, making it a geometric orientation candidate rather than lost
scalar volume data. -/
theorem chainTwoGeometricCurvatureResidualQ_reflectionOdd (i : Fin 2) :
    chainTwoGeometricCurvatureResidualQ
        (Equiv.swap (0 : Fin 2) (1 : Fin 2) i) =
      -chainTwoGeometricCurvatureResidualQ i := by
  fin_cases i
  · norm_num [chainTwoGeometricCurvatureResidualQ_zero,
      chainTwoGeometricCurvatureResidualQ_one]
  · norm_num [chainTwoGeometricCurvatureResidualQ_zero,
      chainTwoGeometricCurvatureResidualQ_one]

/-- Final boundary theorem: the number-volume sector derives the complete law,
whereas every nonzero trace-free curvature profile is a normalized deformation
away from the harmonic source. -/
theorem geometricVolumeAction_frontier
    (cellVolume : ℚ) (hCell : cellVolume ≠ 0)
    (chirality : Fin 2) :
    (numberVolumeVacuumSpectatorCausalAction cellVolume hCell =
        canonicalVacuumSpectatorCausalAction)
      ∧ (microscopicCausalActionChargeQ
          (numberVolumeVacuumSpectatorCausalAction cellVolume hCell) 2 =
            (3 : ℚ) / 2)
      ∧ IsCausalOrderRelabelingCovariant
          (@normalizedCausalPastVolumeDensityQ)
      ∧ ¬ IsEventSlotRelabelingInvariant
          (normalizedCausalPastVolumeDensityQ cardinalCausalChainTwo)
      ∧ IsStronglyPositiveGrowthFunctional
          (infiniteRankedCylinderDecoherence
            (microscopicSpectatorCausalSetGrowthLaw
              (numberVolumeVacuumSpectatorCausalAction cellVolume hCell)
              chirality)) := by
  have hComplete := numberVolumeAction_derives_completeQuantumGrowth
    cellVolume hCell chirality
  exact ⟨hComplete.1, hComplete.2.1,
    normalizedCausalPastVolumeDensityQ_covariant,
    causalOrderCovariance_does_not_force_eventSlotExchangeability.2.2,
    hComplete.2.2.2.2⟩

#print axioms normalizedNumberVolumeBirthDensityQ_eq_uniform
#print axioms countingVolume_singleEvent_fraction_eq_uniform
#print axioms normalizedCosmologicalVolumeBirthDensityQ_eq_uniform
#print axioms numberVolumeAction_derives_completeQuantumGrowth
#print axioms causalOrderCovariance_does_not_force_eventSlotExchangeability
#print axioms volumeCurvatureDensityQ_sum_one
#print axioms volumeCurvatureDensityQ_eq_uniform_iff
#print axioms eventVolumeProjectionQ_unique
#print axioms eventCurvatureResidualQ_eq_zero_iff
#print axioms chainTwoGeometricCurvatureResidualQ_reflectionOdd
#print axioms geometricVolumeAction_frontier

end

end UnifiedTheory.Audit.KFCausalSetGeometricVolumeAction
