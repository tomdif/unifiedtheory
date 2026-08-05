/-
  Audit/KFCausalDeterminantWeakCurrent.lean

  FROM THE CSPEC DETERMINANT LINE TO A CHIRAL WEAK VERTEX

  The CSpec atlas orientation is a complex scalar only because it acts on the
  complex carrier.  Its square is one, so it is exactly +1 or -1 and its real
  part is a nonzero real sign.  Feeding that *derived* sign into the existing
  gamma-five weak projector yields, for every atlas history, exactly one of
  the two nontrivial purely chiral charged-current vertices.  The witnessed
  odd loop gives the right mirror in the repository's fixed convention; the
  trivial/even sector gives the standard left vertex.

  This closes the finite algebraic identification without introducing a new
  Xi input.  It does not derive a continuum Lorentzian Dirac field, a weak
  coupling constant, or an absolute selection between the conjugate sectors.

  Zero sorry. Zero custom axioms.
-/

import UnifiedTheory.Audit.KFCausalRegularPhaseEntry
import UnifiedTheory.Audit.KFCausalSetWeakHandednessBridge

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Audit.KFCausalDeterminantWeakCurrent

noncomputable section

open UnifiedTheory.Audit.KFCausalSetSequentialGrowth
open UnifiedTheory.Audit.KFCausalCSpecDeterminantChirality
open UnifiedTheory.Audit.KFCausalSetWeakHandednessBridge
open UnifiedTheory.Audit.KFCausalRegularPhaseEntry

/-! ## 1. The determinant orientation is a real nonzero sign -/

/-- Real weak-sector sign extracted from the complex determinant-line action. -/
def cSpecAtlasWeakSign (n : ℕ)
    (history : RankedGrowthPath CSpecAtlasBranch n) : ℝ :=
  (cSpecAtlasOrientation n history).re

theorem cSpecAtlasOrientation_eq_one_or_neg_one (n : ℕ)
    (history : RankedGrowthPath CSpecAtlasBranch n) :
    cSpecAtlasOrientation n history = 1 ∨
      cSpecAtlasOrientation n history = -1 := by
  exact sq_eq_one_iff.mp (cSpecAtlasOrientation_sq n history)

theorem cSpecAtlasWeakSign_eq_one_or_neg_one (n : ℕ)
    (history : RankedGrowthPath CSpecAtlasBranch n) :
    cSpecAtlasWeakSign n history = 1 ∨
      cSpecAtlasWeakSign n history = -1 := by
  rcases cSpecAtlasOrientation_eq_one_or_neg_one n history with
    hPositive | hNegative
  · left
    simp [cSpecAtlasWeakSign, hPositive]
  · right
    simp [cSpecAtlasWeakSign, hNegative]

theorem cSpecAtlasWeakSign_ne_zero (n : ℕ)
    (history : RankedGrowthPath CSpecAtlasBranch n) :
    cSpecAtlasWeakSign n history ≠ 0 := by
  rcases cSpecAtlasWeakSign_eq_one_or_neg_one n history with
    hPositive | hNegative
  · rw [hPositive]
    norm_num
  · rw [hNegative]
    norm_num

/-! ## 2. Every determinant history selects one pure weak sector -/

/-- Charged weak vertex whose chirality sign is read from CSpec determinant
transport rather than supplied independently. -/
def cSpecAtlasWeakVertex (n : ℕ)
    (history : RankedGrowthPath CSpecAtlasBranch n) :
    DiracWeakSpinor → DiracWeakSpinor :=
  causalWeakVertex (cSpecAtlasWeakSign n history) weakRaising

theorem cSpecAtlasWeakVertex_of_orientation_one (n : ℕ)
    (history : RankedGrowthPath CSpecAtlasBranch n)
    (hPositive : cSpecAtlasOrientation n history = 1) :
    cSpecAtlasWeakVertex n history = leftWeakVertex weakRaising := by
  funext psi
  unfold cSpecAtlasWeakVertex cSpecAtlasWeakSign
  rw [hPositive]
  simpa using causalWeakVertex_one weakRaising psi

theorem cSpecAtlasWeakVertex_of_orientation_neg_one (n : ℕ)
    (history : RankedGrowthPath CSpecAtlasBranch n)
    (hNegative : cSpecAtlasOrientation n history = -1) :
    cSpecAtlasWeakVertex n history = rightWeakVertex weakRaising := by
  funext psi
  unfold cSpecAtlasWeakVertex cSpecAtlasWeakSign
  rw [hNegative]
  simpa using causalWeakVertex_neg_one weakRaising psi

/-- **Derived finite weak-sector theorem.** Every CSpec determinant history
selects exactly a nontrivial purely left charged current or its nontrivial
purely right mirror. -/
theorem cSpecDeterminant_derives_purelyChiral_weakVertex (n : ℕ)
    (history : RankedGrowthPath CSpecAtlasBranch n) :
    (cSpecAtlasOrientation n history = 1 ∧
        IsNontrivialPurelyLeftHanded (cSpecAtlasWeakVertex n history))
      ∨ (cSpecAtlasOrientation n history = -1 ∧
        IsNontrivialPurelyRightHanded (cSpecAtlasWeakVertex n history)) := by
  rcases cSpecAtlasOrientation_eq_one_or_neg_one n history with
    hPositive | hNegative
  · left
    refine ⟨hPositive, ?_⟩
    rw [cSpecAtlasWeakVertex_of_orientation_one n history hPositive]
    exact standard_charged_current_is_nontrivial_purely_left
  · right
    refine ⟨hNegative, ?_⟩
    rw [cSpecAtlasWeakVertex_of_orientation_neg_one n history hNegative]
    exact mirror_charged_current_is_nontrivial_purely_right

/-! ## 3. Concrete sectors and combined boundary -/

/-- The based depth-zero history lies in the positive determinant sector and
therefore gives the standard purely left charged-current vertex. -/
theorem cSpecTrivialHistory_derives_leftWeakVertex :
    IsNontrivialPurelyLeftHanded
      (cSpecAtlasWeakVertex 0 PUnit.unit) := by
  have hPositive : cSpecAtlasOrientation 0 PUnit.unit = 1 := rfl
  rw [cSpecAtlasWeakVertex_of_orientation_one 0 PUnit.unit hPositive]
  exact standard_charged_current_is_nontrivial_purely_left

/-- The continuation-derived odd loop lies in the opposite determinant sector
and gives the nontrivial right-handed mirror. -/
theorem cSpecOddLoop_derives_rightWeakMirror :
    IsNontrivialPurelyRightHanded
      (cSpecAtlasWeakVertex 3 cSpecOddLoopHistory) := by
  rw [cSpecAtlasWeakVertex_of_orientation_neg_one 3 cSpecOddLoopHistory
    cSpecOddLoopHistory_orientation]
  exact mirror_charged_current_is_nontrivial_purely_right

/-- Combined finite promotion statement. Physical causal growth reaches the
local Boolean three-direction seed at rank eight; on the constructed CSpec
atlas every determinant history then yields a nonzero pure weak sector.  The
statement deliberately does not identify the physical prefix path with a
particular nontrivial atlas loop. -/
theorem physicalRegularPhase_and_determinantWeakSector :
    ((∀ n : ℕ, (h : n < 8) →
        IsUnlabeledOneElementExtension
          (Quotient.mk _ (cubePrefixOrder n (Nat.le_of_lt h)))
          (Quotient.mk _ (cubePrefixOrder (n + 1) h)))
      ∧ IsExactBooleanCubePhase (cubePrefixOrder 8 (by omega))
      ∧ ContainsBooleanCubeSeed (cubePrefixOrder 8 (by omega))
      ∧ (∀ child : CardinalCausalOrder 9,
          IsLabeledOneElementExtension
              (cubePrefixOrder 8 (by omega)) child →
            ContainsBooleanCubeSeed child))
      ∧ (∀ (n : ℕ) (history : RankedGrowthPath CSpecAtlasBranch n),
        (cSpecAtlasOrientation n history = 1 ∧
            IsNontrivialPurelyLeftHanded (cSpecAtlasWeakVertex n history))
          ∨ (cSpecAtlasOrientation n history = -1 ∧
            IsNontrivialPurelyRightHanded
              (cSpecAtlasWeakVertex n history))) := by
  exact ⟨⟨cubePrefixOrder_unlabeledExtension,
      ⟨cubePrefixEightOrderIso⟩,
      cubePrefixEight_containsBooleanCubeSeed,
      every_birth_after_rankEight_preserves_regularSeed⟩,
    cSpecDeterminant_derives_purelyChiral_weakVertex⟩

#print axioms cSpecAtlasWeakSign_ne_zero
#print axioms cSpecDeterminant_derives_purelyChiral_weakVertex
#print axioms cSpecTrivialHistory_derives_leftWeakVertex
#print axioms cSpecOddLoop_derives_rightWeakMirror
#print axioms physicalRegularPhase_and_determinantWeakSector

end

end UnifiedTheory.Audit.KFCausalDeterminantWeakCurrent
