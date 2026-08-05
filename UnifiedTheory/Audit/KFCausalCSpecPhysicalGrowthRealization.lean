/-
  Audit/KFCausalCSpecPhysicalGrowthRealization.lean

  PHYSICAL SEQUENTIAL-GROWTH REALIZATION OF THE FULL-S3 CSPEC ATLAS

  The intrinsic global CSpec atlas was previously a finite causal poset, while
  the physical growth theory was formulated as successive maximal-element
  births.  This file closes that representation gap.

  First, it proves a general theorem: every finite partial order can be put in
  a linear-extension order, and its successive initial segments are genuine
  labeled and unlabeled one-element causal births.  The final prefix is order
  isomorphic to the original poset.  Applying this construction to the native
  140-event global atlas gives an explicit physical causal-growth history.

  The history is not merely kinematically allowed.  The uniform physical
  growth law assigns every one of its transitions, and hence the complete
  finite path, nonzero amplitude.  At its endpoint the already-derived CSpec
  continuation geometry supplies the odd determinant loop and the associated
  pure mirror weak sector.

  Honest boundary: finite-poset reachability does not make this history unique
  or dynamically dominant.  Nor does the eight-event Boolean seed by itself
  determine the 140-event atlas.  The continuum Dirac interpretation remains
  a separate bridge.

  Zero sorry. Zero custom axioms.
-/

import Mathlib.Data.Finset.Sort
import Mathlib.Order.Extension.Linear
import UnifiedTheory.Audit.KFCausalDeterminantWeakCurrent

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Audit.KFCausalCSpecPhysicalGrowthRealization

noncomputable section

open UnifiedTheory.Audit.KFCausalSetSequentialGrowth
open UnifiedTheory.Audit.KFCausalCSpecGlobalAtlas
open UnifiedTheory.Audit.KFCausalCSpecDeterminantChirality
open UnifiedTheory.Audit.KFCausalDeterminantWeakCurrent
open UnifiedTheory.Audit.KFCausalSetWeakHandednessBridge
open UnifiedTheory.Audit.KFCausalRegularPhaseEntry
open UnifiedTheory.Audit.KFCausalDeterminantPhysicalBoundary

/-! ## 1. Every finite partial order is a physical sequential-growth endpoint -/

noncomputable instance linearExtensionFintype
    (alpha : Type*) [Fintype alpha] : Fintype (LinearExtension alpha) :=
  inferInstanceAs (Fintype alpha)

/-- Increasing enumeration of a finite partial order after extending it to a
linear order. -/
def finiteCausalLinearOrderIso (alpha : Type*) [Fintype alpha]
    [PartialOrder alpha] :
    Fin (Fintype.card alpha) ≃o LinearExtension alpha :=
  Fintype.orderIsoFinOfCardEq (LinearExtension alpha) rfl

/-- The event occupying one slot of the linear-extension enumeration. -/
def finiteCausalEvent (alpha : Type*) [Fintype alpha] [PartialOrder alpha]
    (index : Fin (Fintype.card alpha)) : alpha :=
  finiteCausalLinearOrderIso alpha index

theorem finiteCausalEvent_injective (alpha : Type*) [Fintype alpha]
    [PartialOrder alpha] : Function.Injective (finiteCausalEvent alpha) := by
  exact (finiteCausalLinearOrderIso alpha).injective

/-- Original causal precedence implies precedence of birth slots in the
chosen linear extension. -/
theorem finiteCausalEvent_le_implies_index_le
    (alpha : Type*) [Fintype alpha] [PartialOrder alpha]
    (first second : Fin (Fintype.card alpha))
    (hCausal : finiteCausalEvent alpha first ≤ finiteCausalEvent alpha second) :
    first ≤ second := by
  apply (finiteCausalLinearOrderIso alpha).le_iff_le.mp
  exact (toLinearExtension : alpha →o LinearExtension alpha).monotone hCausal

/-- The causal order induced on the first `n` events of a linear extension. -/
def finiteCausalPrefixOrder (alpha : Type*) [Fintype alpha]
    [PartialOrder alpha] (n : ℕ) (h : n ≤ Fintype.card alpha) :
    CardinalCausalOrder n := by
  classical
  exact
    { rel := fun first second => decide
        (finiteCausalEvent alpha (Fin.castLE h first) ≤
          finiteCausalEvent alpha (Fin.castLE h second))
      refl := by
        intro index
        simp
      antisymm := by
        intro first second hFirstSecond hSecondFirst
        have hFirstSecond' :
            finiteCausalEvent alpha (Fin.castLE h first) ≤
              finiteCausalEvent alpha (Fin.castLE h second) :=
          of_decide_eq_true hFirstSecond
        have hSecondFirst' :
            finiteCausalEvent alpha (Fin.castLE h second) ≤
              finiteCausalEvent alpha (Fin.castLE h first) :=
          of_decide_eq_true hSecondFirst
        have hEvents := le_antisymm hFirstSecond' hSecondFirst'
        have hIndices := finiteCausalEvent_injective alpha hEvents
        apply Fin.ext
        simpa using congrArg
          (fun index : Fin (Fintype.card alpha) => index.val) hIndices
      trans := by
        intro first second third hFirstSecond hSecondThird
        apply decide_eq_true
        exact le_trans (of_decide_eq_true hFirstSecond)
          (of_decide_eq_true hSecondThird) }

/-- Every consecutive pair of finite-poset prefixes is a genuine maximal
one-element birth. -/
theorem finiteCausalPrefixOrder_oneElementExtension
    (alpha : Type*) [Fintype alpha] [PartialOrder alpha]
    (n : ℕ) (h : n < Fintype.card alpha) :
    IsLabeledOneElementExtension
      (finiteCausalPrefixOrder alpha n (Nat.le_of_lt h))
      (finiteCausalPrefixOrder alpha (n + 1) h) := by
  classical
  constructor
  · intro first second
    change decide
        (finiteCausalEvent alpha
            (Fin.castLE (Nat.le_of_lt h) first) ≤
          finiteCausalEvent alpha
            (Fin.castLE (Nat.le_of_lt h) second)) =
      decide
        (finiteCausalEvent alpha (Fin.castLE h first.castSucc) ≤
          finiteCausalEvent alpha (Fin.castLE h second.castSucc))
    congr 2
  · intro old
    change decide
      (finiteCausalEvent alpha (Fin.castLE h (Fin.last n)) ≤
        finiteCausalEvent alpha (Fin.castLE h old.castSucc)) = false
    apply decide_eq_false
    intro hBackward
    have hIndex := finiteCausalEvent_le_implies_index_le alpha _ _ hBackward
    change n ≤ old.val at hIndex
    omega

theorem finiteCausalPrefixOrder_unlabeledExtension
    (alpha : Type*) [Fintype alpha] [PartialOrder alpha]
    (n : ℕ) (h : n < Fintype.card alpha) :
    IsUnlabeledOneElementExtension
      (Quotient.mk _
        (finiteCausalPrefixOrder alpha n (Nat.le_of_lt h)))
      (Quotient.mk _ (finiteCausalPrefixOrder alpha (n + 1) h)) := by
  exact isUnlabeledOneElementExtension_mk
    (finiteCausalPrefixOrder_oneElementExtension alpha n h)

/-- At full cardinality the sequentially grown order is exactly the original
finite partial order, up to the linear-extension relabeling. -/
def finiteCausalPrefixFullOrderIso
    (alpha : Type*) [Fintype alpha] [PartialOrder alpha] :
    CausalOrderPoint
        (finiteCausalPrefixOrder alpha (Fintype.card alpha) le_rfl) ≃o alpha := by
  classical
  exact
    { toEquiv := (finiteCausalLinearOrderIso alpha).toEquiv
      map_rel_iff' := by
        intro first second
        change
          (finiteCausalEvent alpha first ≤ finiteCausalEvent alpha second) ↔
            decide
              (finiteCausalEvent alpha first ≤ finiteCausalEvent alpha second) = true
        exact decide_eq_true_iff.symm }

/-! ## 2. Instantiate the theorem on the native global CSpec atlas -/

instance globalAtlasEventPartialOrder : PartialOrder GlobalAtlasEvent where
  le := globalAtlasLE
  le_refl := globalAtlasLE_refl
  le_trans := globalAtlasLE_trans
  le_antisymm := globalAtlasLE_antisymm

/-- The native global CSpec atlas, written in a physical birth ordering. -/
def globalAtlasPhysicalPrefix (n : ℕ) (h : n ≤ 140) :
    CardinalCausalOrder n :=
  finiteCausalPrefixOrder GlobalAtlasEvent n
    (by simpa [globalAtlasEvent_card] using h)

/-- Every one of the 140 atlas births is physically admissible. -/
theorem globalAtlasPhysicalPrefix_oneElementExtension
    (n : ℕ) (h : n < 140) :
    IsLabeledOneElementExtension
      (globalAtlasPhysicalPrefix n (Nat.le_of_lt h))
      (globalAtlasPhysicalPrefix (n + 1) h) := by
  exact finiteCausalPrefixOrder_oneElementExtension GlobalAtlasEvent n
    (by simpa [globalAtlasEvent_card] using h)

theorem globalAtlasPhysicalPrefix_unlabeledExtension
    (n : ℕ) (h : n < 140) :
    IsUnlabeledOneElementExtension
      (Quotient.mk _
        (globalAtlasPhysicalPrefix n (Nat.le_of_lt h)))
      (Quotient.mk _ (globalAtlasPhysicalPrefix (n + 1) h)) := by
  exact isUnlabeledOneElementExtension_mk
    (globalAtlasPhysicalPrefix_oneElementExtension n h)

/-- The physical rank-140 endpoint has exactly the order type used by the
native global CSpec construction. -/
def globalAtlasPhysicalEndpointOrderIso :
    CausalOrderPoint (globalAtlasPhysicalPrefix 140 le_rfl) ≃o
      GlobalAtlasEvent := by
  simpa [globalAtlasPhysicalPrefix, globalAtlasEvent_card] using
    (finiteCausalPrefixFullOrderIso GlobalAtlasEvent)

/-- One native Boolean chart embeds into the physically grown global-atlas
endpoint.  Thus the earlier eight-event carrier geometry is not discarded;
it occurs as a local seed inside the full monodromy realization. -/
def globalAtlasChartZeroEmbedding : Fin 8 ↪ GlobalAtlasEvent where
  toFun index := .cell 0 (cubeBitset index)
  inj' := by
    intro first second hEqual
    injection hEqual with _ hCells
    exact cubeBitset_injective hCells

def globalAtlasPhysicalCubeEmbedding : Fin 8 ↪ Fin 140 :=
  globalAtlasChartZeroEmbedding.trans
    globalAtlasPhysicalEndpointOrderIso.symm.toEmbedding

theorem globalAtlasPhysicalEndpoint_containsBooleanCubeSeed :
    ContainsBooleanCubeSeed (globalAtlasPhysicalPrefix 140 le_rfl) := by
  classical
  refine ⟨globalAtlasPhysicalCubeEmbedding, ?_⟩
  intro first second
  change decide
      (finiteCausalEvent GlobalAtlasEvent
          (globalAtlasPhysicalCubeEmbedding first) ≤
        finiteCausalEvent GlobalAtlasEvent
          (globalAtlasPhysicalCubeEmbedding second)) =
    decide (cubeBitset first ⊆ cubeBitset second)
  apply Bool.decide_congr
  have hFirst :
      finiteCausalEvent GlobalAtlasEvent
          (globalAtlasPhysicalCubeEmbedding first) =
        .cell 0 (cubeBitset first) := by
    change (finiteCausalLinearOrderIso GlobalAtlasEvent)
      ((finiteCausalLinearOrderIso GlobalAtlasEvent).symm
        (.cell 0 (cubeBitset first))) = .cell 0 (cubeBitset first)
    exact (finiteCausalLinearOrderIso GlobalAtlasEvent).apply_symm_apply _
  have hSecond :
      finiteCausalEvent GlobalAtlasEvent
          (globalAtlasPhysicalCubeEmbedding second) =
        .cell 0 (cubeBitset second) := by
    change (finiteCausalLinearOrderIso GlobalAtlasEvent)
      ((finiteCausalLinearOrderIso GlobalAtlasEvent).symm
        (.cell 0 (cubeBitset second))) = .cell 0 (cubeBitset second)
    exact (finiteCausalLinearOrderIso GlobalAtlasEvent).apply_symm_apply _
  rw [hFirst, hSecond]
  exact globalAtlasLE_cell_iff 0 (cubeBitset first) (cubeBitset second)

/-! ## 3. An actual physical path with nonzero growth amplitude -/

/-- The nested unlabeled growth history obtained from the atlas prefixes. -/
def globalAtlasPhysicalGrowthPath :
    (n : ℕ) → (h : n ≤ 140) → RankedGrowthPath CausalSetGrowthBranch n
  | 0, _ => PUnit.unit
  | n + 1, h =>
      (globalAtlasPhysicalGrowthPath n (Nat.le_trans (Nat.le_succ n) h),
        Quotient.mk _ (globalAtlasPhysicalPrefix (n + 1) h))

theorem globalAtlasPhysicalGrowthPath_currentOrder :
    ∀ (n : ℕ) (h : n ≤ 140),
      currentUnlabeledCausalOrder n (globalAtlasPhysicalGrowthPath n h) =
        Quotient.mk _ (globalAtlasPhysicalPrefix n h)
  | 0, h => by
      apply Quotient.sound
      refine ⟨Equiv.refl _, ?_⟩
      intro first
      exact Fin.elim0 first
  | n + 1, h => rfl

/-- The complete atlas history lies on the genuine unlabeled physical
extension graph. -/
theorem globalAtlasPhysicalGrowthPath_isPhysical :
    ∀ (n : ℕ) (h : n ≤ 140),
      IsPhysicalCausalGrowthPath n (globalAtlasPhysicalGrowthPath n h)
  | 0, _ => trivial
  | n + 1, h => by
      constructor
      · exact globalAtlasPhysicalGrowthPath_isPhysical n
          (Nat.le_trans (Nat.le_succ n) h)
      · unfold IsPhysicalCausalGrowthStep
        change IsUnlabeledOneElementExtension
          (currentUnlabeledCausalOrder n
            (globalAtlasPhysicalGrowthPath n
              (Nat.le_trans (Nat.le_succ n) h)))
          (Quotient.mk _ (globalAtlasPhysicalPrefix (n + 1) h))
        rw [globalAtlasPhysicalGrowthPath_currentOrder]
        exact globalAtlasPhysicalPrefix_unlabeledExtension n (by omega)

theorem uniformCausalSetTransition_ne_zero_of_physical
    (n : ℕ) (path : RankedGrowthPath CausalSetGrowthBranch n)
    (child : CausalSetGrowthBranch n)
    (hPhysical : IsPhysicalCausalGrowthStep n path child) :
    uniformCausalSetTransition n path child ≠ 0 := by
  have hMember : child ∈ physicalCausalSuccessors n path := by
    simp [physicalCausalSuccessors, hPhysical]
  rw [uniformCausalSetTransition]
  simp only [if_pos hMember]
  exact inv_ne_zero
    (Nat.cast_ne_zero.mpr
      (Nat.ne_of_gt (physicalCausalSuccessors_card_pos n path)))

/-- Every finite prefix of the atlas history has nonzero amplitude under the
repo's unconditional uniform physical growth dynamics. -/
theorem globalAtlasPhysicalGrowthPath_uniformAmplitude_ne_zero :
    ∀ (n : ℕ) (h : n ≤ 140),
      finiteRankedPathAmplitude uniformUnlabeledCausalSetGrowthLaw n
          (globalAtlasPhysicalGrowthPath n h) ≠ 0
  | 0, _ => by simp
  | n + 1, h => by
      change
        finiteRankedPathAmplitude uniformUnlabeledCausalSetGrowthLaw n
            (globalAtlasPhysicalGrowthPath n
              (Nat.le_trans (Nat.le_succ n) h)) *
          uniformCausalSetTransition n
            (globalAtlasPhysicalGrowthPath n
              (Nat.le_trans (Nat.le_succ n) h))
            (Quotient.mk _ (globalAtlasPhysicalPrefix (n + 1) h)) ≠ 0
      apply mul_ne_zero
      · exact globalAtlasPhysicalGrowthPath_uniformAmplitude_ne_zero n
          (Nat.le_trans (Nat.le_succ n) h)
      · apply uniformCausalSetTransition_ne_zero_of_physical
        exact (globalAtlasPhysicalGrowthPath_isPhysical (n + 1) h).2

/-! ## 4. Physical full-S3/determinant capstone -/

/-- **Physical CSpec realization theorem.** Ordinary unlabeled sequential
growth contains a nonzero-amplitude history whose endpoint is the native
full-S3 CSpec atlas.  That endpoint contains the continuation-derived odd
loop, whose determinant supplies the nontrivial pure mirror weak sector.

This is existence, not selection or dominance. -/
theorem physicalGrowth_realizes_fullS3_CSpec_determinantSector :
    IsPhysicalCausalGrowthPath 140
        (globalAtlasPhysicalGrowthPath 140 le_rfl)
      ∧ finiteRankedPathAmplitude uniformUnlabeledCausalSetGrowthLaw 140
          (globalAtlasPhysicalGrowthPath 140 le_rfl) ≠ 0
      ∧ Nonempty
          (CausalOrderPoint (globalAtlasPhysicalPrefix 140 le_rfl) ≃o
            GlobalAtlasEvent)
      ∧ ContainsBooleanCubeSeed (globalAtlasPhysicalPrefix 140 le_rfl)
      ∧ cSpecAtlasOrientation 3 cSpecOddLoopHistory = -1
      ∧ IsNontrivialPurelyRightHanded
          (cSpecAtlasWeakVertex 3 cSpecOddLoopHistory) := by
  exact ⟨globalAtlasPhysicalGrowthPath_isPhysical 140 le_rfl,
    globalAtlasPhysicalGrowthPath_uniformAmplitude_ne_zero 140 le_rfl,
    ⟨globalAtlasPhysicalEndpointOrderIso⟩,
    globalAtlasPhysicalEndpoint_containsBooleanCubeSeed,
    cSpecOddLoopHistory_orientation,
    cSpecOddLoop_derives_rightWeakMirror⟩

#print axioms finiteCausalPrefixOrder_oneElementExtension
#print axioms finiteCausalPrefixFullOrderIso
#print axioms globalAtlasPhysicalGrowthPath_isPhysical
#print axioms globalAtlasPhysicalGrowthPath_uniformAmplitude_ne_zero
#print axioms globalAtlasPhysicalEndpoint_containsBooleanCubeSeed
#print axioms physicalGrowth_realizes_fullS3_CSpec_determinantSector

end

end UnifiedTheory.Audit.KFCausalCSpecPhysicalGrowthRealization
