/-
  Audit/KFCausalSheetHolonomyWitness.lean

  AN EXPLICIT FINITE FULL-S3 SHEET HOLONOMY WITNESS

  This file removes the abstract holonomy hypothesis for one finite connected
  sheet complex.  Four states carry a uniform reversible Markov law.  Two
  triangle loops based at state zero transport the adjacent transpositions
  (0 1) and (1 2).  Six explicit loop words realize all six permutations of
  Fin 3, so the connection has full S3 holonomy.

  Feeding this witness into the general connection-Laplacian theorem gives a
  concrete finite law with trivial twisted kernel and strictly positive
  energy on every nonzero carrier field.

  This is an explicit combinatorial sheet connection.  It is not yet proved
  to arise from an independently defined causal set or CSpec neighborhood.

  Zero sorry. Zero custom axioms.
-/

import Mathlib.Tactic.FinCases
import UnifiedTheory.Audit.KFCausalSheetConnectionLaplacian

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Audit.KFCausalSheetHolonomyWitness

noncomputable section

open UnifiedTheory.Audit.KFCausalSheetConnectionLaplacian
open UnifiedTheory.Audit.KFCausalProduct3SheetBridge

abbrev WitnessState := Fin 4

def swapZeroOne : Equiv.Perm (Fin 3) :=
  Equiv.swap (0 : Fin 3) 1

def swapOneTwo : Equiv.Perm (Fin 3) :=
  Equiv.swap (1 : Fin 3) 2

/-- The two distinguished undirected edges carry adjacent transpositions;
all remaining edges carry the identity. -/
def witnessSheetTransport
    (first second : WitnessState) : Equiv.Perm (Fin 3) :=
  if (first = 0 ∧ second = 1) ∨ (first = 1 ∧ second = 0) then
    swapZeroOne
  else if (first = 0 ∧ second = 2) ∨ (first = 2 ∧ second = 0) then
    swapOneTwo
  else
    Equiv.refl (Fin 3)

theorem witnessSheetTransport_refl (state : WitnessState) :
    witnessSheetTransport state state = Equiv.refl (Fin 3) := by
  fin_cases state <;> rfl

theorem witnessSheetTransport_reverse (first second : WitnessState) :
    witnessSheetTransport second first =
      (witnessSheetTransport first second).symm := by
  fin_cases first <;> fin_cases second <;>
    ext sheet <;> fin_cases sheet <;> rfl

/-- Uniform complete four-state reversible connection.  The complete support
makes positive connectivity immediate; the sheet labels retain the two-cycle
holonomy data. -/
def fullS3WitnessConnection : ReversibleSheetConnection WitnessState where
  stationary := fun _ => 1
  transition := fun _ _ => 1 / 4
  sheetTransport := witnessSheetTransport
  stationary_pos := by intro; norm_num
  transition_nonneg := by intro; norm_num
  row_stochastic := by
    intro state
    fin_cases state <;> norm_num [Fin.sum_univ_succ]
  detailed_balance := by intro; norm_num
  transport_refl := witnessSheetTransport_refl
  transport_reverse := witnessSheetTransport_reverse

/-- Realize every sheet transport by an actual order automorphism of the
Boolean causal tangent cube. -/
def witnessChartTransition (first second : WitnessState) :
    TangentCube3 ≃o TangentCube3 :=
  directionPermToOrderAut (witnessSheetTransport first second)

/-- The finite witness is therefore a regular Boolean-cube chart complex,
not merely a table of abstract permutations. -/
def fullS3WitnessRegularProductLaw :
    RegularProduct3TransitionData WitnessState (fun _ => WitnessState) where
  target := fun _ next => next
  weight := fun _ _ => (1 / 4 : ℂ)
  chartTransition := witnessChartTransition

theorem witnessChartTransition_direction_permutation
    (first second : WitnessState) :
    orderAutToDirectionPerm (witnessChartTransition first second) =
      witnessSheetTransport first second := by
  exact orderAutToDirectionPerm_directionPermToOrderAut _

theorem fullS3WitnessConnection_transition_pos
    (first second : WitnessState) :
    0 < fullS3WitnessConnection.transition first second := by
  norm_num [fullS3WitnessConnection]

/-! ## Explicit loops and their six holonomies -/

/-- Append positive connection paths. -/
def appendPositiveConnectionPath
    {law : ReversibleSheetConnection WitnessState}
    {start middle finish : WitnessState}
    (first : PositiveConnectionPath law start middle)
    (second : PositiveConnectionPath law middle finish) :
    PositiveConnectionPath law start finish :=
  match first with
  | .nil _ => second
  | .cons start next hPositive tail =>
      .cons start next hPositive (appendPositiveConnectionPath tail second)

theorem positivePathSheetTransport_append
    {law : ReversibleSheetConnection WitnessState}
    {start middle finish : WitnessState}
    (first : PositiveConnectionPath law start middle)
    (second : PositiveConnectionPath law middle finish) :
    positivePathSheetTransport law
        (appendPositiveConnectionPath first second) =
      (positivePathSheetTransport law second).trans
        (positivePathSheetTransport law first) := by
  induction first with
  | nil state => rfl
  | cons start next hPositive tail ih =>
      simp only [appendPositiveConnectionPath, positivePathSheetTransport]
      rw [ih, Equiv.trans_assoc]

/-- First triangle: 0 -> 1 -> 3 -> 0. -/
def swapZeroOneLoop :
    PositiveConnectionPath fullS3WitnessConnection 0 0 :=
  .cons 0 1 (fullS3WitnessConnection_transition_pos 0 1)
    (.cons 1 3 (fullS3WitnessConnection_transition_pos 1 3)
      (.cons 3 0 (fullS3WitnessConnection_transition_pos 3 0)
        (.nil 0)))

/-- Second triangle: 0 -> 2 -> 3 -> 0. -/
def swapOneTwoLoop :
    PositiveConnectionPath fullS3WitnessConnection 0 0 :=
  .cons 0 2 (fullS3WitnessConnection_transition_pos 0 2)
    (.cons 2 3 (fullS3WitnessConnection_transition_pos 2 3)
      (.cons 3 0 (fullS3WitnessConnection_transition_pos 3 0)
        (.nil 0)))

theorem swapZeroOneLoop_holonomy :
    positivePathSheetTransport fullS3WitnessConnection swapZeroOneLoop =
      swapZeroOne := by
  ext sheet
  fin_cases sheet <;> rfl

theorem swapOneTwoLoop_holonomy :
    positivePathSheetTransport fullS3WitnessConnection swapOneTwoLoop =
      swapOneTwo := by
  ext sheet
  fin_cases sheet <;> rfl

/-- Two concrete closed paths realize the adjacent transpositions that
generate all of S3. -/
theorem witness_has_two_generating_transposition_loops :
    (∃ path : PositiveConnectionPath fullS3WitnessConnection 0 0,
      positivePathSheetTransport fullS3WitnessConnection path = swapZeroOne)
    ∧
    (∃ path : PositiveConnectionPath fullS3WitnessConnection 0 0,
      positivePathSheetTransport fullS3WitnessConnection path = swapOneTwo) := by
  exact ⟨⟨swapZeroOneLoop, swapZeroOneLoop_holonomy⟩,
    ⟨swapOneTwoLoop, swapOneTwoLoop_holonomy⟩⟩

/-- The six standard words in the two adjacent transpositions. -/
def fullS3WitnessLoop : Fin 6 →
    PositiveConnectionPath fullS3WitnessConnection 0 0 :=
  ![
    .nil 0,
    swapZeroOneLoop,
    swapOneTwoLoop,
    appendPositiveConnectionPath swapZeroOneLoop swapOneTwoLoop,
    appendPositiveConnectionPath swapOneTwoLoop swapZeroOneLoop,
    appendPositiveConnectionPath
      (appendPositiveConnectionPath swapZeroOneLoop swapOneTwoLoop)
      swapZeroOneLoop
  ]

def fullS3WitnessHolonomy (index : Fin 6) : Equiv.Perm (Fin 3) :=
  positivePathSheetTransport fullS3WitnessConnection
    (fullS3WitnessLoop index)

/-- Pure permutation word table corresponding to the six witnessed loops.
Keeping this table independent of the real-valued Markov structure makes its
finite exhaustiveness executable. -/
def fullS3PermutationWord : Fin 6 → Equiv.Perm (Fin 3) :=
  ![
    Equiv.refl (Fin 3),
    swapZeroOne,
    swapOneTwo,
    swapOneTwo.trans swapZeroOne,
    swapZeroOne.trans swapOneTwo,
    swapZeroOne.trans (swapOneTwo.trans swapZeroOne)
  ]

theorem fullS3WitnessHolonomy_eq_word (index : Fin 6) :
    fullS3WitnessHolonomy index = fullS3PermutationWord index := by
  fin_cases index <;> ext sheet <;> fin_cases sheet <;> rfl

theorem fullS3PermutationWord_injective :
    Function.Injective fullS3PermutationWord := by
  decide

theorem fullS3WitnessHolonomy_injective :
    Function.Injective fullS3WitnessHolonomy := by
  intro first second hEqual
  apply fullS3PermutationWord_injective
  rw [← fullS3WitnessHolonomy_eq_word first,
    ← fullS3WitnessHolonomy_eq_word second]
  exact hEqual

theorem fullS3WitnessHolonomy_surjective :
    Function.Surjective fullS3WitnessHolonomy := by
  have hCard :
      Fintype.card (Fin 6) = Fintype.card (Equiv.Perm (Fin 3)) := by
    norm_num [Fintype.card_perm]
  exact ((Fintype.bijective_iff_injective_and_card
    fullS3WitnessHolonomy).2
      ⟨fullS3WitnessHolonomy_injective, hCard⟩).2

/-- **Explicit full-holonomy theorem.** Every sheet permutation is the
transport of a positive closed path in the four-state witness. -/
theorem fullS3WitnessConnection_hasFullS3Holonomy :
    HasFullS3Holonomy fullS3WitnessConnection 0 := by
  intro relabeling
  obtain ⟨index, hIndex⟩ := fullS3WitnessHolonomy_surjective relabeling
  exact ⟨fullS3WitnessLoop index, hIndex⟩

theorem fullS3WitnessConnection_positiveConnected :
    PositiveConnectedFrom fullS3WitnessConnection 0 := by
  intro state
  exact ⟨.cons 0 state
    (fullS3WitnessConnection_transition_pos 0 state) (.nil state)⟩

/-! ## Unconditional finite spectral consequence -/

/-- The explicit witnessed connection has no nonzero parallel carrier mode. -/
theorem fullS3WitnessConnection_kernel_trivial
    (field : WitnessState → SheetCarrier)
    (hKernel : ∀ state,
      connectionLaplacian fullS3WitnessConnection field state = 0) :
    field = 0 := by
  exact fullS3Holonomy_connectionLaplacian_kernel_trivial
    fullS3WitnessConnection 0 fullS3WitnessConnection_hasFullS3Holonomy
    fullS3WitnessConnection_positiveConnected field hKernel

/-- Every nonzero carrier field on the explicit witness has positive energy. -/
theorem fullS3WitnessConnection_nonzero_energy_pos
    (field : WitnessState → SheetCarrier) (hField : field ≠ 0) :
    0 < connectionLaplacianEnergy fullS3WitnessConnection field := by
  exact fullS3Holonomy_nonzero_energy_pos
    fullS3WitnessConnection 0 fullS3WitnessConnection_hasFullS3Holonomy
    fullS3WitnessConnection_positiveConnected field hField

#print axioms swapZeroOneLoop_holonomy
#print axioms swapOneTwoLoop_holonomy
#print axioms witnessChartTransition_direction_permutation
#print axioms witness_has_two_generating_transposition_loops
#print axioms fullS3WitnessConnection_hasFullS3Holonomy
#print axioms fullS3WitnessConnection_kernel_trivial
#print axioms fullS3WitnessConnection_nonzero_energy_pos

end

end UnifiedTheory.Audit.KFCausalSheetHolonomyWitness
