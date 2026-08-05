/-
  Audit/KFCausalCSpecDeterminantChirality.lean

  CSPEC DETERMINANT-LINE CHIRALITY

  The intrinsic global CSpec atlas already derives a three-sheet transport
  permutation on every chart edge.  This file proves that the missing
  orientation sign is not independent data: it is the sign representation,
  or determinant line, of that same permutation local system.

  On the standard rank-two carrier an odd sheet transport reverses the unique
  parity-odd chirality operator.  Its determinant-line sign reverses at the
  same time, so their product is transported exactly.  Iterating the edge
  signs defines the orientation label of every sequential-growth history;
  no separately supplied Xi field enters the construction.

  A final finite Kraus construction promotes history-block pinching to a
  genuine CPTP channel on the flattened direct-sum carrier and proves that it
  fixes the relational chirality block exactly.

  The physical scope is the constructed finite regular CSpec atlas.  The
  following `KFCausalDeterminantPhysicalBoundary` audit proves that arbitrary
  physical causal-set growth cannot be three-sheeted at every stage: its
  singleton first child has no intrinsic diamond direction at all.

  Zero sorry. Zero custom axioms.
-/

import Mathlib.GroupTheory.Perm.Sign
import UnifiedTheory.Audit.KFCausalCSpecGlobalAtlas
import UnifiedTheory.Audit.KFCausalBundleProtectedChirality
import UnifiedTheory.LayerB.KrausExistence

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Audit.KFCausalCSpecDeterminantChirality

noncomputable section

open scoped BigOperators ComplexConjugate ComplexOrder
open Matrix
open UnifiedTheory.LayerB.Kraus
open UnifiedTheory.Audit.KFCausalSetSequentialGrowth
open UnifiedTheory.Audit.KFCausalCylinderRecordTransport
open UnifiedTheory.Audit.KFCausalBundleProtectedChirality
open UnifiedTheory.Audit.KFCausalSheetHolonomyWitness
open UnifiedTheory.Audit.KFCausalCSpecGlobalAtlas

/-! ## 1. The orientation line is derived from CSpec sheet transport -/

/-- The determinant-line transport of one intrinsic CSpec chart edge.  It is
`+1` for an even direction matching and `-1` for an odd matching. -/
def cSpecEdgeParity (first second : WitnessState) : ℂ :=
  ((Equiv.Perm.sign (recoveredCSpecDirectionTransport first second) : ℤ) : ℂ)

/-- Carrier transport induced by the continuation-recovered edge.  The
global witness has only the identity and the two adjacent transpositions on
elementary edges; nontrivial composite permutations arise as path holonomy. -/
def cSpecEdgeCarrierTransport (first second : WitnessState) :
    Matrix (Fin 2) (Fin 2) ℂ :=
  if recoveredCSpecDirectionTransport first second = swapZeroOne then
    sheetSwapZeroOne
  else if recoveredCSpecDirectionTransport first second = swapOneTwo then
    sheetSwapOneTwo
  else
    1

/-- Every elementary edge in the constructed global CSpec atlas is either
flat or carries one of the two recovered adjacent transpositions. -/
theorem recoveredCSpecDirectionTransport_edge_classification
    (first second : WitnessState) :
    recoveredCSpecDirectionTransport first second = Equiv.refl (Fin 3) ∨
      recoveredCSpecDirectionTransport first second = swapZeroOne ∨
      recoveredCSpecDirectionTransport first second = swapOneTwo := by
  rw [recoveredCSpecDirectionTransport_eq_witness]
  fin_cases first <;> fin_cases second <;>
    simp [witnessSheetTransport, swapZeroOne, swapOneTwo]

/-- The determinant-line sign and the carrier action are not two assumptions:
they are two representations of the same continuation-recovered CSpec edge.
Their sign reversals cancel on the chirality observable. -/
theorem cSpecEdgeParity_chirality_covariance
    (first second : WitnessState) :
    (cSpecEdgeParity first second • sheetChiralityObservable) *
        cSpecEdgeCarrierTransport first second =
      cSpecEdgeCarrierTransport first second * sheetChiralityObservable := by
  rcases recoveredCSpecDirectionTransport_edge_classification first second with
    hIdentity | hZeroOne | hOneTwo
  · have hNotZeroOne : (Equiv.refl (Fin 3)) ≠ swapZeroOne := by
      intro hEqual
      have hAtZero := DFunLike.congr_fun hEqual (0 : Fin 3)
      norm_num [swapZeroOne] at hAtZero
    have hNotOneTwo : (Equiv.refl (Fin 3)) ≠ swapOneTwo := by
      intro hEqual
      have hAtOne := DFunLike.congr_fun hEqual (1 : Fin 3)
      norm_num [swapOneTwo] at hAtOne
      omega
    simp [cSpecEdgeParity, cSpecEdgeCarrierTransport, hIdentity,
      hNotZeroOne, hNotOneTwo, Equiv.Perm.sign_refl]
  · simpa [cSpecEdgeParity, cSpecEdgeCarrierTransport, hZeroOne,
      swapZeroOne, Equiv.Perm.sign_swap, neg_mul] using
      sheetSwapZeroOne_anticommutes_chirality.symm
  · simpa [cSpecEdgeParity, cSpecEdgeCarrierTransport, hOneTwo,
      swapOneTwo, Equiv.Perm.sign_swap, neg_mul] using
      sheetSwapOneTwo_anticommutes_chirality.symm

/-! ## 2. Sequential histories inherit the determinant orientation -/

/-- A sequential history through the finite global CSpec chart graph chooses
one next chart at every rank. -/
abbrev CSpecAtlasBranch : ℕ → Type := fun _ => WitnessState

/-- Current chart of a history, based at chart zero. -/
def cSpecAtlasCurrentChart :
    ∀ n : ℕ, RankedGrowthPath CSpecAtlasBranch n → WitnessState
  | 0, _ => 0
  | _ + 1, path => path.2

/-- The determinant orientation of a history.  It is generated recursively
from the intrinsic CSpec edge parities and has no independent sign input. -/
def cSpecAtlasOrientation :
    ∀ n : ℕ, RankedGrowthPath CSpecAtlasBranch n → ℂ
  | 0, _ => 1
  | n + 1, path =>
      cSpecEdgeParity (cSpecAtlasCurrentChart n path.1) path.2 *
        cSpecAtlasOrientation n path.1

@[simp]
theorem cSpecAtlasOrientation_zero
    (path : RankedGrowthPath CSpecAtlasBranch 0) :
    cSpecAtlasOrientation 0 path = 1 := rfl

@[simp]
theorem cSpecAtlasOrientation_snoc {n : ℕ}
    (path : RankedGrowthPath CSpecAtlasBranch n) (next : WitnessState) :
    cSpecAtlasOrientation (n + 1) (path, next) =
      cSpecEdgeParity (cSpecAtlasCurrentChart n path) next *
        cSpecAtlasOrientation n path := rfl

/-- The successor orientation written on the definitional one-step product
used by the bundle-growth matrix. -/
def cSpecAtlasNextOrientation {n : ℕ}
    (refined : RankedGrowthPath CSpecAtlasBranch n × WitnessState) : ℂ :=
  cSpecEdgeParity (cSpecAtlasCurrentChart n refined.1) refined.2 *
    cSpecAtlasOrientation n refined.1

@[simp]
theorem cSpecAtlasNextOrientation_eq {n : ℕ}
    (path : RankedGrowthPath CSpecAtlasBranch n) (next : WitnessState) :
    cSpecAtlasNextOrientation (path, next) =
      cSpecAtlasOrientation (n + 1) (path, next) := rfl

/-- Every intrinsic edge parity is a genuine sign. -/
theorem cSpecEdgeParity_sq (first second : WitnessState) :
    cSpecEdgeParity first second ^ 2 = 1 := by
  unfold cSpecEdgeParity
  rcases Int.units_eq_one_or
      (Equiv.Perm.sign (recoveredCSpecDirectionTransport first second)) with
    hSign | hSign
  · rw [hSign]
    norm_num
  · rw [hSign]
    norm_num

/-- The recursively generated determinant orientation can never vanish. -/
theorem cSpecAtlasOrientation_sq :
    ∀ (n : ℕ) (path : RankedGrowthPath CSpecAtlasBranch n),
      cSpecAtlasOrientation n path ^ 2 = 1 := by
  intro n
  induction n with
  | zero =>
      intro path
      simp
  | succ n ih =>
      intro path
      rcases path with ⟨path, next⟩
      change (cSpecEdgeParity (cSpecAtlasCurrentChart n path) next *
        cSpecAtlasOrientation n path) ^ 2 = 1
      calc
        (cSpecEdgeParity (cSpecAtlasCurrentChart n path) next *
            cSpecAtlasOrientation n path) ^ 2 =
            cSpecEdgeParity (cSpecAtlasCurrentChart n path) next ^ 2 *
              cSpecAtlasOrientation n path ^ 2 := by ring
        _ = 1 := by rw [cSpecEdgeParity_sq, ih]; norm_num

theorem cSpecAtlasOrientation_ne_zero (n : ℕ)
    (path : RankedGrowthPath CSpecAtlasBranch n) :
    cSpecAtlasOrientation n path ≠ 0 := by
  intro hZero
  have hSq := cSpecAtlasOrientation_sq n path
  rw [hZero] at hSq
  norm_num at hSq

/-- The internal carrier transport assigned to the next growth edge is
computed from the current chart and the continuation-recovered CSpec match. -/
def cSpecAtlasHistoryCarrierTransport {n : ℕ}
    (path : RankedGrowthPath CSpecAtlasBranch n) (next : WitnessState) :
    Matrix (Fin 2) (Fin 2) ℂ :=
  cSpecEdgeCarrierTransport (cSpecAtlasCurrentChart n path) next

/-- **Microscopic determinant-line law.** The history orientation generated
by CSpec edge parity makes the relational chirality covariant on every edge.
Unlike the preceding abstract bundle theorem, the outgoing sign is no longer
supplied as a hypothesis. -/
theorem cSpecAtlasHistory_relationalChirality {n : ℕ} :
    RelationalFiberTransport
      (Branch := CSpecAtlasBranch) (n := n)
      (cSpecAtlasOrientation n)
      cSpecAtlasNextOrientation
      sheetChiralityObservable
      cSpecAtlasHistoryCarrierTransport := by
  intro path next
  change
    (cSpecAtlasNextOrientation (path, next) • sheetChiralityObservable) *
        cSpecAtlasHistoryCarrierTransport path next =
      cSpecAtlasHistoryCarrierTransport path next *
        (cSpecAtlasOrientation n path • sheetChiralityObservable)
  rw [show cSpecAtlasNextOrientation (path, next) =
      cSpecEdgeParity (cSpecAtlasCurrentChart n path) next *
        cSpecAtlasOrientation n path from rfl]
  let first := cSpecAtlasCurrentChart n path
  have hEdge := cSpecEdgeParity_chirality_covariance first next
  ext row column
  have hEntry := congrArg (fun matrix => matrix row column) hEdge
  simp only [Matrix.mul_apply, Matrix.smul_apply, smul_eq_mul] at hEntry ⊢
  calc
    (∑ x,
        (cSpecEdgeParity first next * cSpecAtlasOrientation n path) *
            sheetChiralityObservable row x *
          cSpecEdgeCarrierTransport first next x column) =
        cSpecAtlasOrientation n path *
          ∑ x, cSpecEdgeParity first next *
              sheetChiralityObservable row x *
            cSpecEdgeCarrierTransport first next x column := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro x _hx
      ring
    _ = cSpecAtlasOrientation n path *
          ∑ x, cSpecEdgeCarrierTransport first next row x *
            sheetChiralityObservable x column := by rw [hEntry]
    _ = ∑ x, cSpecEdgeCarrierTransport first next row x *
          (cSpecAtlasOrientation n path *
            sheetChiralityObservable x column) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro x _hx
      ring

/-- Consequently every scalar transition law on the CSpec atlas transports
the determinant-twisted chirality through bundle-valued sequential growth. -/
theorem cSpecAtlasGrowth_transports_derivedChirality {n : ℕ}
    (transition : RankedGrowthPath CSpecAtlasBranch n → WitnessState → ℂ) :
    fiberwiseOperator (cSpecAtlasNextOrientation (n := n))
          sheetChiralityObservable *
        bundleGrowthDilation transition cSpecAtlasHistoryCarrierTransport =
      bundleGrowthDilation transition cSpecAtlasHistoryCarrierTransport *
        fiberwiseOperator (cSpecAtlasOrientation n)
          sheetChiralityObservable := by
  exact relationalFiberTransport_intertwiner transition
    cSpecAtlasHistoryCarrierTransport
    (cSpecAtlasOrientation n) (cSpecAtlasNextOrientation (n := n))
    sheetChiralityObservable cSpecAtlasHistory_relationalChirality

/-! ## 3. The determinant line is genuinely nontrivial -/

/-- The first continuation-derived unfilled atlas loop, now represented as a
sequential chart history based at chart zero. -/
def cSpecOddLoopHistory : RankedGrowthPath CSpecAtlasBranch 3 :=
  (((PUnit.unit, (1 : WitnessState)), (3 : WitnessState)), (0 : WitnessState))

/-- The orientation reversal around the witnessed CSpec loop is computed
from continuation-derived sheet transport.  In particular, the nonzero
orientation datum is not an independently chosen field. -/
theorem cSpecOddLoopHistory_orientation :
    cSpecAtlasOrientation 3 cSpecOddLoopHistory = -1 := by
  have hZeroOneTransport :
      recoveredCSpecDirectionTransport 0 1 = swapZeroOne := by
    simp [recoveredCSpecDirectionTransport_eq_witness,
      witnessSheetTransport]
  have hOneThreeTransport :
      recoveredCSpecDirectionTransport 1 3 = Equiv.refl (Fin 3) := by
    simp [recoveredCSpecDirectionTransport_eq_witness,
      witnessSheetTransport]
  have hThreeZeroTransport :
      recoveredCSpecDirectionTransport 3 0 = Equiv.refl (Fin 3) := by
    simp [recoveredCSpecDirectionTransport_eq_witness,
      witnessSheetTransport]
  have hZeroOne : cSpecEdgeParity 0 1 = -1 := by
    rw [cSpecEdgeParity, hZeroOneTransport]
    norm_num [swapZeroOne, Equiv.Perm.sign_swap]
  have hOneThree : cSpecEdgeParity 1 3 = 1 := by
    rw [cSpecEdgeParity, hOneThreeTransport]
    norm_num [Equiv.Perm.sign_refl]
  have hThreeZero : cSpecEdgeParity 3 0 = 1 := by
    rw [cSpecEdgeParity, hThreeZeroTransport]
    norm_num [Equiv.Perm.sign_refl]
  change cSpecEdgeParity 3 0 *
    (cSpecEdgeParity 1 3 * (cSpecEdgeParity 0 1 * 1)) = -1
  rw [hThreeZero, hOneThree, hZeroOne]
  norm_num

/-! ## 4. A finite CPTP record instrument that protects chirality -/

/-- The indicator of one history block in the flattened direct sum
`Fin histories × Fin 2 ≃ Fin (histories * 2)`. -/
def historyFiberIndex (histories : ℕ)
    (index : Fin (histories * 2)) : Fin histories :=
  (finProdFinEquiv.symm index).1

def historyBlockMask (histories : ℕ) (history : Fin histories)
    (index : Fin (histories * 2)) : ℂ :=
  if historyFiberIndex histories index = history then 1 else 0

/-- Orthogonal projector onto one two-dimensional history fiber. -/
def historyBlockProjector (histories : ℕ) (history : Fin histories) :
    Matrix (Fin (histories * 2)) (Fin (histories * 2)) ℂ :=
  Matrix.diagonal (historyBlockMask histories history)

@[simp]
theorem historyBlockProjector_conjTranspose (histories : ℕ)
    (history : Fin histories) :
    (historyBlockProjector histories history)ᴴ =
      historyBlockProjector histories history := by
  ext row column
  by_cases hrc : row = column
  · subst column
    simp [historyBlockProjector, historyBlockMask]
  · simp [historyBlockProjector, hrc, Ne.symm hrc]

@[simp]
theorem historyBlockProjector_mul_self (histories : ℕ)
    (history : Fin histories) :
    historyBlockProjector histories history *
        historyBlockProjector histories history =
      historyBlockProjector histories history := by
  rw [historyBlockProjector, Matrix.diagonal_mul_diagonal]
  congr 1
  funext index
  simp [historyBlockMask]

/-- The family of history-block projectors is a complete Kraus family. -/
noncomputable def historyBlockPinchingKraus (histories : ℕ) :
    KrausRepresentation (histories * 2) (histories * 2) histories where
  K := historyBlockProjector histories
  complete := by
    simp_rw [historyBlockProjector_conjTranspose,
      historyBlockProjector_mul_self]
    ext row column
    by_cases hrc : row = column
    · subst column
      rw [Matrix.sum_apply]
      rw [Finset.sum_eq_single (historyFiberIndex histories row)]
      · simp [historyBlockProjector, historyBlockMask]
      · intro history _hMem hHistory
        have hNe : historyFiberIndex histories row ≠ history :=
          Ne.symm hHistory
        simp [historyBlockProjector, historyBlockMask, hNe]
      · intro hAbsent
        exact (hAbsent (Finset.mem_univ _)).elim
    · rw [Matrix.sum_apply]
      simp only [Matrix.one_apply, if_neg hrc]
      apply Finset.sum_eq_zero
      intro history _hHistory
      simp [historyBlockProjector, hrc]

/-- Hence history-block pinching is a genuine finite CPTP channel, not merely
an entrywise operation called a coarse graining. -/
theorem historyBlockPinching_isCPTP (histories : ℕ) :
    IsCPTP (historyBlockPinchingKraus histories).toLinearMap :=
  kraus_isCPTP (historyBlockPinchingKraus histories)

/-- Exact entrywise action of the finite channel: it retains precisely the
two-dimensional diagonal history blocks. -/
theorem historyBlockPinching_apply_entry (histories : ℕ)
    (ρ : Matrix (Fin (histories * 2)) (Fin (histories * 2)) ℂ)
    (row column : Fin (histories * 2)) :
    (historyBlockPinchingKraus histories).apply ρ row column =
      if historyFiberIndex histories row =
          historyFiberIndex histories column then
        ρ row column
      else
        0 := by
  rw [KrausRepresentation.apply]
  change
    (∑ history, historyBlockProjector histories history * ρ *
      (historyBlockProjector histories history)ᴴ) row column = _
  simp_rw [historyBlockProjector_conjTranspose]
  rw [Matrix.sum_apply]
  simp only [historyBlockProjector,
    Matrix.diagonal_mul, Matrix.mul_diagonal]
  by_cases hBlock :
      historyFiberIndex histories row = historyFiberIndex histories column
  · rw [if_pos hBlock]
    rw [Finset.sum_eq_single (historyFiberIndex histories row)]
    · simp [historyBlockMask, hBlock]
    · intro history _hMem hHistory
      have hNe : historyFiberIndex histories row ≠ history :=
        Ne.symm hHistory
      simp [historyBlockMask, hNe]
    · intro hAbsent
      exact (hAbsent (Finset.mem_univ _)).elim
  · rw [if_neg hBlock]
    apply Finset.sum_eq_zero
    intro history _hHistory
    by_cases hRow : historyFiberIndex histories row = history
    · have hColumn : historyFiberIndex histories column ≠ history := by
        intro hColumn
        exact hBlock (hRow.trans hColumn.symm)
      simp [historyBlockMask, hRow, hColumn]
    · simp [historyBlockMask, hRow]

/-- Flatten a fiberwise two-by-two operator into the direct-sum history
carrier.  Off-block entries vanish; within a block the orientation scalar
multiplies the common internal operator. -/
def flattenedFiberwiseOperator (histories : ℕ)
    (orientation : Fin histories → ℂ)
    (operator : Matrix (Fin 2) (Fin 2) ℂ) :
    Matrix (Fin (histories * 2)) (Fin (histories * 2)) ℂ :=
  fun row column =>
    if historyFiberIndex histories row = historyFiberIndex histories column then
      orientation (historyFiberIndex histories row) *
        operator (finProdFinEquiv.symm row).2
          (finProdFinEquiv.symm column).2
    else
      0

/-- The CPTP record instrument removes coherence between different histories
while fixing every fiberwise observable. -/
theorem historyBlockPinching_fixes_fiberwiseOperator (histories : ℕ)
    (orientation : Fin histories → ℂ)
    (operator : Matrix (Fin 2) (Fin 2) ℂ) :
    (historyBlockPinchingKraus histories).apply
        (flattenedFiberwiseOperator histories orientation operator) =
      flattenedFiberwiseOperator histories orientation operator := by
  ext row column
  rw [historyBlockPinching_apply_entry]
  by_cases hBlock :
      historyFiberIndex histories row = historyFiberIndex histories column
  · rw [if_pos hBlock]
  · rw [if_neg hBlock]
    rw [flattenedFiberwiseOperator, if_neg hBlock]

/-- **CPTP protection capstone.**  The concrete record channel fixes the
relational chirality whose orientation is generated by the CSpec determinant
line.  Thus record classicalization and derived chirality coexist in one
finite, state-independent CPTP model. -/
theorem historyBlockPinching_protects_derivedChirality (histories : ℕ)
    (orientation : Fin histories → ℂ) :
    (historyBlockPinchingKraus histories).apply
        (flattenedFiberwiseOperator histories orientation
          sheetChiralityObservable) =
      flattenedFiberwiseOperator histories orientation
        sheetChiralityObservable :=
  historyBlockPinching_fixes_fiberwiseOperator histories orientation
    sheetChiralityObservable

#print axioms cSpecAtlasHistory_relationalChirality
#print axioms cSpecAtlasGrowth_transports_derivedChirality
#print axioms cSpecAtlasOrientation_ne_zero
#print axioms cSpecOddLoopHistory_orientation
#print axioms historyBlockPinching_isCPTP
#print axioms historyBlockPinching_apply_entry
#print axioms historyBlockPinching_protects_derivedChirality

end

end UnifiedTheory.Audit.KFCausalCSpecDeterminantChirality
