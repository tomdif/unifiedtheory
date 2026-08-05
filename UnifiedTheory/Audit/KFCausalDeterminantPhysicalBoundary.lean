/-
  Audit/KFCausalDeterminantPhysicalBoundary.lean

  THE PHYSICAL BOUNDARY OF THE CSPEC DETERMINANT LAW

  The determinant-line construction is intrinsic on the Boolean three-
  direction regular locus, but it cannot be a fiber attached to every state
  of physical unlabeled sequential growth.  The first physical birth already
  gives a counterexample: a singleton causal order has no Hasse cover edge,
  hence its diamond-direction quotient is empty rather than three-element.

  This file also closes the normalization qualification for the finite CPTP
  history-block channel.  Trace preservation is not preservation of the
  decoherence-functional total-event value.  Block pinching preserves that
  value exactly when the total cross-block interference vanishes; in
  particular it does so on an exactly block-decoherent functional.  The
  existing two-antichain source example proves that this condition cannot be
  omitted.

  The strongest correct physical statement is therefore a regular-locus law:

    three intrinsic causal directions
      -> S3 transport
      -> determinant chirality,

  with event-normalized record pinching only on decoherent block partitions.

  Zero sorry. Zero custom axioms.
-/

import UnifiedTheory.Audit.KFCausalCSpecDeterminantChirality
import UnifiedTheory.Audit.KFCausalSetSpectatorRecordChannel

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Audit.KFCausalDeterminantPhysicalBoundary

noncomputable section

open scoped BigOperators ComplexConjugate ComplexOrder
open Matrix
open UnifiedTheory.Audit.KFCausalProduct3SheetBridge
open UnifiedTheory.Audit.KFCausalDiamondDirectionCover
open UnifiedTheory.Audit.KFCausalSetSequentialGrowth
open UnifiedTheory.Audit.KFCausalCSpecDeterminantChirality
open UnifiedTheory.Audit.KFCausalSetSpectatorRecordChannel

/-! ## 1. The universal three-sheet claim fails at the first birth -/

/-- A causal neighborhood supports the determinant-sheet construction when
its intrinsic diamond-direction quotient is a three-element type. -/
def SupportsThreeIntrinsicDirections (P : Type*) [PartialOrder P] : Prop :=
  Nonempty (LocalCausalDirection P ≃ Fin 3)

/-- The order carried by a fixed-cardinality causal-set representative,
exposed as an actual `PartialOrder` for the intrinsic direction construction. -/
def CausalOrderPoint {n : ℕ} (_P : CardinalCausalOrder n) := Fin n

instance causalOrderPointPartialOrder {n : ℕ}
    (P : CardinalCausalOrder n) : PartialOrder (CausalOrderPoint P) where
  le i j := P.rel i j = true
  le_refl i := P.refl i
  le_trans _ _ _ := P.trans _ _ _
  le_antisymm _ _ := P.antisymm _ _

/-- The Boolean tangent cube is the proved regular local model. -/
theorem tangentCube_supportsThreeIntrinsicDirections :
    SupportsThreeIntrinsicDirections TangentCube3 := by
  exact ⟨cubeLocalDirectionEquivFin3⟩

/-- Any subsingleton causal neighborhood has no Hasse cover edge. -/
theorem subsingletonCausalCoverEdge_isEmpty
    (P : Type*) [PartialOrder P] [Subsingleton P] :
    IsEmpty (CausalCoverEdge P) := by
  constructor
  intro edge
  have hEqual : edge.lower = edge.upper := Subsingleton.elim _ _
  exact edge.covBy.lt.ne hEqual

/-- Therefore its intrinsic diamond-direction quotient is empty. -/
theorem subsingletonLocalCausalDirection_isEmpty
    (P : Type*) [PartialOrder P] [Subsingleton P] :
    IsEmpty (LocalCausalDirection P) := by
  constructor
  intro direction
  refine Quotient.inductionOn direction ?_
  intro edge
  exact (subsingletonCausalCoverEdge_isEmpty P).false edge

/-- In particular the singleton cannot carry the intrinsic three-sheet
fiber used by determinant chirality. -/
theorem singleton_not_supportsThreeIntrinsicDirections :
    ¬ SupportsThreeIntrinsicDirections (Fin 1) := by
  rintro ⟨equiv⟩
  exact (subsingletonLocalCausalDirection_isEmpty (Fin 1)).false
    (equiv.symm (0 : Fin 3))

/-- The singleton is not an artificial poset: it is the explicit isolated
one-element child of the empty root in the physical unlabeled growth graph. -/
def singletonLabeledCausalOrder : CardinalCausalOrder 1 :=
  isolatedOneElementExtension emptyCardinalCausalOrder

instance singletonCausalOrderPointSubsingleton :
    Subsingleton (CausalOrderPoint singletonLabeledCausalOrder) where
  allEq first second := by
    change Fin 1 at first second
    change first = second
    exact Subsingleton.elim _ _

def singletonUnlabeledCausalOrder : UnlabeledCardinalCausalOrder 1 :=
  Quotient.mk _ singletonLabeledCausalOrder

theorem emptyRoot_has_physical_singletonChild :
    IsUnlabeledOneElementExtension emptyUnlabeledCausalOrder
      singletonUnlabeledCausalOrder := by
  exact isUnlabeledOneElementExtension_mk
    (isolated_is_oneElementExtension emptyCardinalCausalOrder)

/-- The direction no-go applies to the causal order carried by that very
physical child, not merely to an unrelated singleton type. -/
theorem physicalSingleton_intrinsicDirections_isEmpty :
    IsEmpty (LocalCausalDirection
      (CausalOrderPoint singletonLabeledCausalOrder)) := by
  exact subsingletonLocalCausalDirection_isEmpty
    (CausalOrderPoint singletonLabeledCausalOrder)

theorem physicalSingleton_not_supportsThreeIntrinsicDirections :
    ¬ SupportsThreeIntrinsicDirections
      (CausalOrderPoint singletonLabeledCausalOrder) := by
  rintro ⟨equiv⟩
  exact physicalSingleton_intrinsicDirections_isEmpty.false
    (equiv.symm (0 : Fin 3))

/-- **Universal-atlas no-go.** Physical sequential growth does not imply a
three-direction determinant sheet at every stage.  Its first realized child
already has an empty direction quotient. -/
theorem physicalGrowth_not_universally_threeSheeted :
    (∃ child : UnlabeledCardinalCausalOrder 1,
        IsUnlabeledOneElementExtension emptyUnlabeledCausalOrder child)
      ∧ ¬ SupportsThreeIntrinsicDirections
        (CausalOrderPoint singletonLabeledCausalOrder) := by
  exact ⟨⟨singletonUnlabeledCausalOrder,
      emptyRoot_has_physical_singletonChild⟩,
    physicalSingleton_not_supportsThreeIntrinsicDirections⟩

/-! ## 2. Exact event-normalization criterion for history pinching -/

/-- The decoherence-functional value of the total event on the flattened
history carrier.  Unlike density-matrix normalization, it sums every matrix
entry, not only the trace. -/
def historyTotalEventValue (histories : ℕ)
    (rho : Matrix (Fin (histories * 2)) (Fin (histories * 2)) ℂ) : ℂ :=
  ∑ row, ∑ column, rho row column

/-- The total interference between distinct history blocks. -/
def crossHistoryInterference (histories : ℕ)
    (rho : Matrix (Fin (histories * 2)) (Fin (histories * 2)) ℂ) : ℂ :=
  ∑ row, ∑ column,
    if historyFiberIndex histories row = historyFiberIndex histories column then
      0
    else
      rho row column

/-- Total-event value splits exactly into the retained block value and the
discarded cross-history interference. -/
theorem historyTotalEventValue_eq_pinched_add_cross
    (histories : ℕ)
    (rho : Matrix (Fin (histories * 2)) (Fin (histories * 2)) ℂ) :
    historyTotalEventValue histories rho =
      historyTotalEventValue histories
          ((historyBlockPinchingKraus histories).apply rho) +
        crossHistoryInterference histories rho := by
  classical
  unfold historyTotalEventValue crossHistoryInterference
  simp_rw [historyBlockPinching_apply_entry]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro row _
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro column _
  by_cases hBlock :
      historyFiberIndex histories row = historyFiberIndex histories column
  · simp [hBlock]
  · simp [hBlock]

/-- The CPTP pinching preserves the total-event value exactly iff the total
discarded interference vanishes. -/
theorem historyBlockPinching_preserves_totalEventValue_iff
    (histories : ℕ)
    (rho : Matrix (Fin (histories * 2)) (Fin (histories * 2)) ℂ) :
    historyTotalEventValue histories
        ((historyBlockPinchingKraus histories).apply rho) =
      historyTotalEventValue histories rho
      ↔ crossHistoryInterference histories rho = 0 := by
  have hDecomposition := historyTotalEventValue_eq_pinched_add_cross
    histories rho
  constructor
  · intro hEqual
    exact add_left_cancel
      ((hEqual.trans hDecomposition).symm.trans (add_zero _).symm)
  · intro hCross
    have hOriginalEqualsPinched :
        historyTotalEventValue histories rho =
          historyTotalEventValue histories
            ((historyBlockPinchingKraus histories).apply rho) := by
      calc
        historyTotalEventValue histories rho =
            historyTotalEventValue histories
                ((historyBlockPinchingKraus histories).apply rho) +
              crossHistoryInterference histories rho := hDecomposition
        _ = historyTotalEventValue histories
              ((historyBlockPinchingKraus histories).apply rho) := by
            rw [hCross, add_zero]
    exact hOriginalEqualsPinched.symm

/-- Exact block decoherence is the pointwise condition that different
history fibers have no matrix coherence. -/
def IsHistoryBlockDecoherent (histories : ℕ)
    (rho : Matrix (Fin (histories * 2)) (Fin (histories * 2)) ℂ) : Prop :=
  ∀ row column,
    historyFiberIndex histories row ≠ historyFiberIndex histories column →
      rho row column = 0

/-- On an exactly decoherent partition, history pinching is the identity. -/
theorem historyBlockPinching_eq_self_of_decoherent
    (histories : ℕ)
    (rho : Matrix (Fin (histories * 2)) (Fin (histories * 2)) ℂ)
    (hDecoherent : IsHistoryBlockDecoherent histories rho) :
    (historyBlockPinchingKraus histories).apply rho = rho := by
  ext row column
  rw [historyBlockPinching_apply_entry]
  by_cases hBlock :
      historyFiberIndex histories row = historyFiberIndex histories column
  · simp [hBlock]
  · rw [if_neg hBlock, hDecoherent row column hBlock]

/-- Hence exact block decoherence is sufficient for both density-matrix and
decoherence-functional normalization to survive the same CPTP channel. -/
theorem historyBlockPinching_preserves_totalEventValue_of_decoherent
    (histories : ℕ)
    (rho : Matrix (Fin (histories * 2)) (Fin (histories * 2)) ℂ)
    (hDecoherent : IsHistoryBlockDecoherent histories rho) :
    historyTotalEventValue histories
        ((historyBlockPinchingKraus histories).apply rho) =
      historyTotalEventValue histories rho := by
  rw [historyBlockPinching_eq_self_of_decoherent histories rho hDecoherent]

/-! ## 3. Corrected capstone -/

/-- The universal claim and its strongest correct replacement, collected in
one theorem: the regular cube has the required intrinsic sheet, physical
growth is not everywhere regular, and the derived CPTP record operation has
the event normalization required of a decoherence functional precisely when
its erased interference has zero total. -/
theorem determinantChirality_physical_boundary
    (histories : ℕ)
    (rho : Matrix (Fin (histories * 2)) (Fin (histories * 2)) ℂ) :
    SupportsThreeIntrinsicDirections TangentCube3
      ∧ ((∃ child : UnlabeledCardinalCausalOrder 1,
          IsUnlabeledOneElementExtension emptyUnlabeledCausalOrder child)
        ∧ ¬ SupportsThreeIntrinsicDirections
          (CausalOrderPoint singletonLabeledCausalOrder))
      ∧ (historyTotalEventValue histories
            ((historyBlockPinchingKraus histories).apply rho) =
          historyTotalEventValue histories rho
        ↔ crossHistoryInterference histories rho = 0) := by
  exact ⟨tangentCube_supportsThreeIntrinsicDirections,
    physicalGrowth_not_universally_threeSheeted,
    historyBlockPinching_preserves_totalEventValue_iff histories rho⟩

#print axioms physicalGrowth_not_universally_threeSheeted
#print axioms historyTotalEventValue_eq_pinched_add_cross
#print axioms historyBlockPinching_preserves_totalEventValue_iff
#print axioms historyBlockPinching_preserves_totalEventValue_of_decoherent
#print axioms determinantChirality_physical_boundary

end

end UnifiedTheory.Audit.KFCausalDeterminantPhysicalBoundary
