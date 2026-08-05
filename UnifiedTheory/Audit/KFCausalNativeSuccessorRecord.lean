/-
  Audit/KFCausalNativeSuccessorRecord.lean

  THE RECORD CARRIER FROM THE NATIVE CAUSAL SUCCESSOR FIBER

  The abstract recorded-refinement theorem used a supplied finite outcome
  type.  Sequential causal growth already contains a canonical finite,
  nonempty outcome object at every parent: the subtype of genuine unlabeled
  one-element children in `physicalCausalSuccessors`.

  This module proves that:

  * the record labels are exactly those physical children, with no `Fin k`
    enumeration or external labeling;
  * forgetting which child occurred is the unique map from that successor
    fiber to the terminal one-point type;
  * its carrier-preserving complex linearization is the canonical coherent
    codiagonal;
  * stacking child-indexed operators against the native record basis gives an
    isometric and counital refinement exactly when the two double-conservation
    equations hold;
  * the canonical harmonic causal law realizes the construction at every
    rank after restriction to its genuine physical successor fiber.

  Thus causal order derives the finite record carrier and its canonical
  recombination map.  It still does not select the child-indexed operators or
  prove that coherent recombination is a laboratory measurement channel.

  Zero sorry. Zero custom axioms.
-/

import UnifiedTheory.Audit.KFCausalRecordedRefinementDilation
import UnifiedTheory.Audit.KFCausalSetSequentialGrowth

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Audit.KFCausalNativeSuccessorRecord

noncomputable section

open scoped BigOperators ComplexConjugate ComplexOrder
open Matrix
open UnifiedTheory.LayerB.StinespringDilation
open UnifiedTheory.Audit.KFOrientationGrowthDecoherence
open UnifiedTheory.Audit.KFOrientationCPChannelTower
open UnifiedTheory.Audit.KFCausalSetSequentialGrowth
open UnifiedTheory.Audit.KFCausalBornShellGeneralLaw
open UnifiedTheory.Audit.KFCausalBornNormalizationTransfer
open UnifiedTheory.Audit.KFCausalDoubleConservationLaw
open UnifiedTheory.Audit.KFCausalRecordedRefinementDilation

/-! ## 1. The causal order supplies the record labels -/

/-- The native one-step outcome type at a causal parent: a genuine unlabeled
one-element child, together with the proof that it is physically admissible. -/
abbrev NativeCausalSuccessor (n : ℕ)
    (pathPrefix : RankedGrowthPath CausalSetGrowthBranch n) :=
  { child : CausalSetGrowthBranch n //
    child ∈ physicalCausalSuccessors n pathPrefix }

/-- The native successor fiber is never empty. -/
theorem nativeCausalSuccessor_nonempty (n : ℕ)
    (pathPrefix : RankedGrowthPath CausalSetGrowthBranch n) :
    Nonempty (NativeCausalSuccessor n pathPrefix) := by
  obtain ⟨child, hChild⟩ := physicalCausalSuccessors_nonempty n pathPrefix
  exact ⟨⟨child, hChild⟩⟩

/-- Its cardinality is exactly the number of physical unlabeled children. -/
theorem nativeCausalSuccessor_card (n : ℕ)
    (pathPrefix : RankedGrowthPath CausalSetGrowthBranch n) :
    Fintype.card (NativeCausalSuccessor n pathPrefix) =
      (physicalCausalSuccessors n pathPrefix).card := by
  exact Fintype.card_coe _

/-- Forgetting a physical child is not extra data: there is a unique map from
the native successor fiber to the terminal record-forgotten type. -/
def forgetNativeCausalSuccessor {n : ℕ}
    {pathPrefix : RankedGrowthPath CausalSetGrowthBranch n} :
    NativeCausalSuccessor n pathPrefix → PUnit :=
  fun _ => PUnit.unit

theorem forgetNativeCausalSuccessor_unique {n : ℕ}
    {pathPrefix : RankedGrowthPath CausalSetGrowthBranch n}
    (forget : NativeCausalSuccessor n pathPrefix → PUnit) :
    forget = forgetNativeCausalSuccessor := by
  funext outcome
  exact Subsingleton.elim _ _

/-- Basis indices of the recorded carrier: the old carrier coordinate paired
with the actual physical child that occurred. -/
abbrev NativeCausalRecordCarrier (dimension n : ℕ)
    (pathPrefix : RankedGrowthPath CausalSetGrowthBranch n) :=
  Fin dimension × NativeCausalSuccessor n pathPrefix

/-- The carrier projection induced by forgetting the native child record. -/
def nativeCausalRecordProjection {dimension n : ℕ}
    {pathPrefix : RankedGrowthPath CausalSetGrowthBranch n} :
    NativeCausalRecordCarrier dimension n pathPrefix → Fin dimension :=
  fun indexed => indexed.1

/-- There is only one projection that retains every parent carrier coordinate
while forgetting the child record. -/
theorem nativeCausalRecordProjection_unique {dimension n : ℕ}
    {pathPrefix : RankedGrowthPath CausalSetGrowthBranch n}
    (projection : NativeCausalRecordCarrier dimension n pathPrefix →
      Fin dimension)
    (hRetains : ∀ carrier outcome, projection (carrier, outcome) = carrier) :
    projection = nativeCausalRecordProjection := by
  funext indexed
  exact hRetains indexed.1 indexed.2

/-! ## 2. Linearizing the unique forgetful map -/

/-- The complex-linear codiagonal induced by the native causal record
projection.  It carries each recorded basis state back to its parent carrier
basis state with coefficient one. -/
def nativeCausalRecordCounit (dimension n : ℕ)
    (pathPrefix : RankedGrowthPath CausalSetGrowthBranch n) :
    Matrix (Fin dimension)
      (NativeCausalRecordCarrier dimension n pathPrefix) ℂ :=
  fun row indexed =>
    if row = nativeCausalRecordProjection indexed then 1 else 0

/-- The native counit is uniquely characterized by carrier preservation and
unit-weight coherent forgetting on every physical child basis state. -/
theorem nativeCausalRecordCounit_unique {dimension n : ℕ}
    {pathPrefix : RankedGrowthPath CausalSetGrowthBranch n}
    (counit : Matrix (Fin dimension)
      (NativeCausalRecordCarrier dimension n pathPrefix) ℂ)
    (hBasis : ∀ row carrier outcome,
      counit row (carrier, outcome) = if row = carrier then 1 else 0) :
    counit = nativeCausalRecordCounit dimension n pathPrefix := by
  ext row indexed
  exact hBasis row indexed.1 indexed.2

/-- The stacked dilation is now indexed by actual causal children. -/
abbrev nativeCausalRecordedDilation {dimension n : ℕ}
    {pathPrefix : RankedGrowthPath CausalSetGrowthBranch n}
    (operator : NativeCausalSuccessor n pathPrefix →
      SquareMatrix dimension) :
    Matrix (NativeCausalRecordCarrier dimension n pathPrefix)
      (Fin dimension) ℂ :=
  krausToStinespring operator

/-- Coherent recombination of the native causal record gives exactly the sum
of the physical child operators. -/
theorem nativeCausalRecordCounit_mul_dilation
    {dimension n : ℕ}
    {pathPrefix : RankedGrowthPath CausalSetGrowthBranch n}
    (operator : NativeCausalSuccessor n pathPrefix →
      SquareMatrix dimension) :
    nativeCausalRecordCounit dimension n pathPrefix *
        nativeCausalRecordedDilation operator =
      ∑ outcome, operator outcome := by
  ext row column
  rw [Matrix.mul_apply, Fintype.sum_prod_type]
  change (∑ carrier : Fin dimension,
      ∑ outcome : NativeCausalSuccessor n pathPrefix,
        (if row = carrier then 1 else 0) *
          operator outcome carrier column) = _
  rw [Finset.sum_eq_single row]
  · simp only [ite_true, one_mul]
    symm
    rw [Finset.sum_apply, Finset.sum_apply]
  · intro carrier _ hCarrier
    simp [Ne.symm hCarrier]
  · simp

/-! ## 3. Native recorded-refinement rigidity -/

/-- On an arbitrary physical successor fiber, the stacked dilation is an
isometry exactly when the physical child operators are Born complete. -/
theorem nativeCausalRecordedDilation_isometry_iff_complete
    {dimension n : ℕ}
    {pathPrefix : RankedGrowthPath CausalSetGrowthBranch n}
    (operator : NativeCausalSuccessor n pathPrefix →
      SquareMatrix dimension) :
    IsIsometry (nativeCausalRecordedDilation operator) ↔
      (∑ outcome, (operator outcome)ᴴ * operator outcome) =
        (1 : SquareMatrix dimension) := by
  constructor
  · intro hIsometry
    unfold IsIsometry at hIsometry
    ext row column
    rw [Finset.sum_apply, Finset.sum_apply]
    calc
      (∑ outcome,
          ((operator outcome)ᴴ * operator outcome) row column) =
          ((nativeCausalRecordedDilation operator)ᴴ *
            nativeCausalRecordedDilation operator) row column :=
        (krausToStinespring_dagger_self_apply
          operator row column).symm
      _ = (1 : SquareMatrix dimension) row column := by
        rw [hIsometry]
  · intro hComplete
    exact krausToStinespring_isIsometry hComplete

/-- The native counit recovers the parent exactly iff the physical child
operators are coherently exhaustive. -/
theorem nativeCausalCounitalRecovery_iff_sum_eq_one
    {dimension n : ℕ}
    {pathPrefix : RankedGrowthPath CausalSetGrowthBranch n}
    (operator : NativeCausalSuccessor n pathPrefix →
      SquareMatrix dimension) :
    nativeCausalRecordCounit dimension n pathPrefix *
          nativeCausalRecordedDilation operator =
        (1 : SquareMatrix dimension) ↔
      ∑ outcome, operator outcome = (1 : SquareMatrix dimension) := by
  rw [nativeCausalRecordCounit_mul_dilation]

/-- **Native causal record theorem.**  With no externally supplied outcome
type, isometric refinement plus native coherent forgetting is exactly operator
double conservation on the physical successor fiber. -/
theorem nativeCausalRecordedRefinement_iff_doubleConservation
    {dimension n : ℕ}
    {pathPrefix : RankedGrowthPath CausalSetGrowthBranch n}
    (operator : NativeCausalSuccessor n pathPrefix →
      SquareMatrix dimension) :
    (IsIsometry (nativeCausalRecordedDilation operator) ∧
      nativeCausalRecordCounit dimension n pathPrefix *
          nativeCausalRecordedDilation operator =
        (1 : SquareMatrix dimension)) ↔
    ((∑ outcome, operator outcome) = (1 : SquareMatrix dimension) ∧
      (∑ outcome, (operator outcome)ᴴ * operator outcome) =
        (1 : SquareMatrix dimension)) := by
  rw [nativeCausalRecordedDilation_isometry_iff_complete,
    nativeCausalCounitalRecovery_iff_sum_eq_one]
  constructor
  · rintro ⟨hBorn, hCoherent⟩
    exact ⟨hCoherent, hBorn⟩
  · rintro ⟨hCoherent, hBorn⟩
    exact ⟨hBorn, hCoherent⟩

/-- Born completeness makes the adjoint of the native recorded dilation an
exact recovery map on its image. -/
theorem nativeCausalRecordedDilation_adjoint_recovers
    {dimension n : ℕ}
    {pathPrefix : RankedGrowthPath CausalSetGrowthBranch n}
    (operator : NativeCausalSuccessor n pathPrefix →
      SquareMatrix dimension)
    (hComplete :
      (∑ outcome, (operator outcome)ᴴ * operator outcome) =
        (1 : SquareMatrix dimension))
    (incoming : SquareMatrix dimension) :
    (nativeCausalRecordedDilation operator)ᴴ *
        (nativeCausalRecordedDilation operator * incoming) = incoming := by
  rw [← Matrix.mul_assoc]
  have hIsometry :=
    (nativeCausalRecordedDilation_isometry_iff_complete operator).2 hComplete
  unfold IsIsometry at hIsometry
  rw [hIsometry, Matrix.one_mul]

/-- Coherent exhaustivity makes the order-derived native counit an exact
recovery map for every incoming carrier amplitude. -/
theorem nativeCausalRecordCounit_recovers
    {dimension n : ℕ}
    {pathPrefix : RankedGrowthPath CausalSetGrowthBranch n}
    (operator : NativeCausalSuccessor n pathPrefix →
      SquareMatrix dimension)
    (hCoherent : ∑ outcome, operator outcome =
      (1 : SquareMatrix dimension))
    (incoming : SquareMatrix dimension) :
    nativeCausalRecordCounit dimension n pathPrefix *
        (nativeCausalRecordedDilation operator * incoming) = incoming := by
  rw [← Matrix.mul_assoc, nativeCausalRecordCounit_mul_dilation,
    hCoherent, Matrix.one_mul]

/-! ## 4. The all-rank harmonic causal realization -/

/-- Restrict the canonical harmonic transition to the actual physical child
fiber. -/
def nativeHarmonicCausalAmplitude (chirality : Fin 2) (n : ℕ)
    (pathPrefix : RankedGrowthPath CausalSetGrowthBranch n)
    (outcome : NativeCausalSuccessor n pathPrefix) : ℂ :=
  (canonicalHarmonicCriticalBornShellGrowthLaw chirality).transition
    n pathPrefix outcome.1

/-- The native physical restriction retains coherent normalization. -/
theorem nativeHarmonicCausalAmplitude_sum_one (chirality : Fin 2) (n : ℕ)
    (pathPrefix : RankedGrowthPath CausalSetGrowthBranch n) :
    ∑ outcome : NativeCausalSuccessor n pathPrefix,
        nativeHarmonicCausalAmplitude chirality n pathPrefix outcome = 1 := by
  let support := physicalCausalSuccessors n pathPrefix
  let amplitude :=
    (canonicalHarmonicCriticalBornShellGrowthLaw chirality).transition
      n pathPrefix
  have hSupport : ∑ child ∈ support, amplitude child = 1 := by
    rw [Finset.sum_subset (Finset.subset_univ _)
      (fun child _hAll hNotMem =>
        (canonicalHarmonicCriticalBornShell_all_rank chirality).2.2
          n pathPrefix child (by
            simpa [support, physicalCausalSuccessors] using hNotMem))]
    exact (canonicalHarmonicCriticalBornShell_all_rank chirality).1
      n pathPrefix
  exact (Finset.sum_subtype support (fun _ => Iff.rfl) amplitude).symm.trans
    hSupport

/-- The native physical restriction also retains Born normalization. -/
theorem nativeHarmonicCausalAmplitude_born_one (chirality : Fin 2) (n : ℕ)
    (pathPrefix : RankedGrowthPath CausalSetGrowthBranch n) :
    ∑ outcome : NativeCausalSuccessor n pathPrefix,
        star (nativeHarmonicCausalAmplitude chirality n pathPrefix outcome) *
          nativeHarmonicCausalAmplitude chirality n pathPrefix outcome = 1 := by
  let support := physicalCausalSuccessors n pathPrefix
  let amplitude :=
    (canonicalHarmonicCriticalBornShellGrowthLaw chirality).transition
      n pathPrefix
  have hSupport :
      ∑ child ∈ support, star (amplitude child) * amplitude child = 1 := by
    rw [Finset.sum_subset (Finset.subset_univ _)
      (fun child _hAll hNotMem => by
        have hZero :=
          (canonicalHarmonicCriticalBornShell_all_rank chirality).2.2
            n pathPrefix child (by
              simpa [support, physicalCausalSuccessors] using hNotMem)
        have hAmplitudeZero : amplitude child = 0 := by
          simpa only [amplitude] using hZero
        simp [hAmplitudeZero])]
    exact (canonicalHarmonicCriticalBornShell_all_rank chirality).2.1
      n pathPrefix
  exact (Finset.sum_subtype support (fun _ => Iff.rfl)
    (fun child => star (amplitude child) * amplitude child)).symm.trans hSupport

/-- Lift the scalar native causal amplitude to one-dimensional carrier
operators. -/
def nativeHarmonicCausalOperator (chirality : Fin 2) (n : ℕ)
    (pathPrefix : RankedGrowthPath CausalSetGrowthBranch n)
    (outcome : NativeCausalSuccessor n pathPrefix) : SquareMatrix 1 :=
  fun _ _ => nativeHarmonicCausalAmplitude chirality n pathPrefix outcome

theorem nativeHarmonicCausalOperator_sum_one (chirality : Fin 2) (n : ℕ)
    (pathPrefix : RankedGrowthPath CausalSetGrowthBranch n) :
    ∑ outcome, nativeHarmonicCausalOperator chirality n pathPrefix outcome =
      (1 : SquareMatrix 1) := by
  ext row column
  fin_cases row
  fin_cases column
  rw [Finset.sum_apply, Finset.sum_apply]
  simpa [nativeHarmonicCausalOperator] using
    nativeHarmonicCausalAmplitude_sum_one chirality n pathPrefix

theorem nativeHarmonicCausalOperator_complete (chirality : Fin 2) (n : ℕ)
    (pathPrefix : RankedGrowthPath CausalSetGrowthBranch n) :
    ∑ outcome,
        (nativeHarmonicCausalOperator chirality n pathPrefix outcome)ᴴ *
          nativeHarmonicCausalOperator chirality n pathPrefix outcome =
      (1 : SquareMatrix 1) := by
  ext row column
  fin_cases row
  fin_cases column
  rw [Finset.sum_apply, Finset.sum_apply]
  simpa [nativeHarmonicCausalOperator, Matrix.mul_apply] using
    nativeHarmonicCausalAmplitude_born_one chirality n pathPrefix

/-- At every parent, the harmonic causal dynamics therefore has an isometric,
counital record dilation whose outcome basis is derived from causal order. -/
theorem nativeHarmonicCausalRecordedRefinement (chirality : Fin 2) (n : ℕ)
    (pathPrefix : RankedGrowthPath CausalSetGrowthBranch n) :
    IsIsometry
        (nativeCausalRecordedDilation
          (nativeHarmonicCausalOperator chirality n pathPrefix)) ∧
      nativeCausalRecordCounit 1 n pathPrefix *
          nativeCausalRecordedDilation
            (nativeHarmonicCausalOperator chirality n pathPrefix) =
        (1 : SquareMatrix 1) := by
  exact (nativeCausalRecordedRefinement_iff_doubleConservation
    (nativeHarmonicCausalOperator chirality n pathPrefix)).2
      ⟨nativeHarmonicCausalOperator_sum_one chirality n pathPrefix,
        nativeHarmonicCausalOperator_complete chirality n pathPrefix⟩

/-! ## 5. Capstone and axiom audit -/

/-- Causal order supplies the record carrier and its unique forgetful
codiagonal at every parent; the established harmonic dynamics realizes both
recovery laws on that native carrier at every rank. -/
theorem causalNativeSuccessorRecord_capstone :
    (∀ (n : ℕ) (pathPrefix : RankedGrowthPath CausalSetGrowthBranch n),
      Nonempty (NativeCausalSuccessor n pathPrefix) ∧
        Fintype.card (NativeCausalSuccessor n pathPrefix) =
          (physicalCausalSuccessors n pathPrefix).card) ∧
    (∀ (chirality : Fin 2) (n : ℕ)
      (pathPrefix : RankedGrowthPath CausalSetGrowthBranch n),
      IsIsometry
          (nativeCausalRecordedDilation
            (nativeHarmonicCausalOperator chirality n pathPrefix)) ∧
        nativeCausalRecordCounit 1 n pathPrefix *
            nativeCausalRecordedDilation
              (nativeHarmonicCausalOperator chirality n pathPrefix) =
          (1 : SquareMatrix 1)) := by
  constructor
  · intro n pathPrefix
    exact ⟨nativeCausalSuccessor_nonempty n pathPrefix,
      nativeCausalSuccessor_card n pathPrefix⟩
  · exact nativeHarmonicCausalRecordedRefinement

#print axioms nativeCausalSuccessor_nonempty
#print axioms forgetNativeCausalSuccessor_unique
#print axioms nativeCausalRecordProjection_unique
#print axioms nativeCausalRecordCounit_unique
#print axioms nativeCausalRecordCounit_mul_dilation
#print axioms nativeCausalRecordedRefinement_iff_doubleConservation
#print axioms nativeCausalRecordedDilation_adjoint_recovers
#print axioms nativeCausalRecordCounit_recovers
#print axioms nativeHarmonicCausalRecordedRefinement
#print axioms causalNativeSuccessorRecord_capstone

end

end UnifiedTheory.Audit.KFCausalNativeSuccessorRecord
