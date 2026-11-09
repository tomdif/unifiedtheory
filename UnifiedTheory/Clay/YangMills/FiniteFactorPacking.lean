/- A source-independent block is selected from each actual finite interaction
support family. Maximal packing supplies independence, nonemptiness and a
quantitative density bound without an assumed elimination schedule. -/
import UnifiedTheory.Clay.YangMills.FiniteFactorSupportGrowth
import Mathlib.Data.Finset.Max

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Clay.YangMills.FiniteFactorPacking
noncomputable section
open FiniteFactorConditional FiniteFactorElimination FiniteFactorSupportGrowth

variable {I P : Type*}

/-- All admissible blocks inside the current active inventory. -/
def candidates (D : P → Finset I) (U : Finset I) : Finset (Finset I) := by
  classical
  exact U.powerset.filter (Independent D)

theorem candidates_nonempty (D : P → Finset I) (U : Finset I) :
    (candidates D U).Nonempty := by
  classical
  refine ⟨∅, Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr (Finset.empty_subset _), ?_⟩⟩
  intro p i hi
  simp only [Finset.notMem_empty] at hi

/-- The selection depends on the support geometry, not on fields, sources or coupling. -/
def chosenBlock (D : P → Finset I) (U : Finset I) : Finset I :=
  Classical.choose ((candidates D U).exists_max_image Finset.card (candidates_nonempty D U))

theorem chosenBlock_mem (D : P → Finset I) (U : Finset I) :
    chosenBlock D U ∈ candidates D U :=
  (Classical.choose_spec ((candidates D U).exists_max_image Finset.card
    (candidates_nonempty D U))).1

theorem chosenBlock_maximal (D : P → Finset I) (U T : Finset I)
    (hT : T ∈ candidates D U) : T.card ≤ (chosenBlock D U).card :=
  (Classical.choose_spec ((candidates D U).exists_max_image Finset.card
    (candidates_nonempty D U))).2 T hT

theorem chosenBlock_subset (D : P → Finset I) (U : Finset I) : chosenBlock D U ⊆ U := by
  classical
  exact Finset.mem_powerset.mp (Finset.mem_filter.mp (chosenBlock_mem D U)).1

theorem chosenBlock_independent (D : P → Finset I) (U : Finset I) :
    Independent D (chosenBlock D U) := by
  classical
  exact (Finset.mem_filter.mp (chosenBlock_mem D U)).2

variable [Fintype P] [DecidableEq I]

/-- Every unselected active coordinate conflicts with a selected coordinate in an actual factor. -/
theorem chosenBlock_cover (D : P → Finset I) (U : Finset I) :
    U ⊆ (chosenBlock D U).biUnion (fun e => insert e (factorStar D e)) := by
  classical
  let T := chosenBlock D U
  have hTU : T ⊆ U := chosenBlock_subset D U
  have hT : Independent D T := chosenBlock_independent D U
  intro e heU
  by_contra heC
  have heT : e ∉ T := fun heT => heC
    (Finset.mem_biUnion.mpr ⟨e, heT, Finset.mem_insert_self _ _⟩)
  have hi : Independent D (insert e T) := by
    intro p d hd f hf hdD hfD
    rcases Finset.mem_insert.mp hd with hde | hdT
    · subst d
      rcases Finset.mem_insert.mp hf with hfe | hfT
      · exact hfe.symm
      · exact (heC (Finset.mem_biUnion.mpr ⟨f, hfT, Finset.mem_insert_of_mem
          ((mem_factorStar D f e).mpr ⟨p, hfD, hdD⟩)⟩)).elim
    · rcases Finset.mem_insert.mp hf with hfe | hfT
      · subst f
        exact (heC (Finset.mem_biUnion.mpr ⟨d, hdT, Finset.mem_insert_of_mem
          ((mem_factorStar D d e).mpr ⟨p, hdD, hfD⟩)⟩)).elim
      · exact hT p d hdT f hfT hdD hfD
  have him : insert e T ∈ candidates D U := Finset.mem_filter.mpr
    ⟨Finset.mem_powerset.mpr (Finset.insert_subset heU hTU), hi⟩
  have hc := chosenBlock_maximal D U (insert e T) him
  change (insert e T).card ≤ T.card at hc
  rw [Finset.card_insert_of_notMem heT] at hc
  omega

/-- The density cost is the size of an actual factor-star conflict neighborhood. -/
theorem chosenBlock_card_bound (D : P → Finset I) (U : Finset I)
    (M : ℕ) (hM : ∀ i, (factorStar D i).card ≤ M) :
    U.card ≤ (M + 1) * (chosenBlock D U).card := by
  calc
    _ ≤ ((chosenBlock D U).biUnion (fun e => insert e (factorStar D e))).card :=
      Finset.card_le_card (chosenBlock_cover D U)
    _ ≤ ∑ e ∈ chosenBlock D U, (insert e (factorStar D e)).card := Finset.card_biUnion_le
    _ ≤ ∑ _e ∈ chosenBlock D U, (M + 1) := by
      apply Finset.sum_le_sum
      intro e _
      exact (Finset.card_insert_le _ _).trans (Nat.add_le_add_right (hM e) 1)
    _ = _ := by simp [mul_comm]

/-- Proven factor-cardinality and incidence bounds give a concrete nonuniform-stage density. -/
theorem chosenBlock_card_bound_of_incidence (D : P → Finset I) (U : Finset I)
    (d t : ℕ) (hD : ∀ p, (D p).card ≤ d) (ht : ∀ i, (touching D i).card ≤ t) :
    U.card ≤ (t * d + 1) * (chosenBlock D U).card :=
  chosenBlock_card_bound D U (t * d) (factorStar_card_bound D d t hD ht)

omit [Fintype P] [DecidableEq I] in
/-- The selected actual independent block is nonempty whenever any active coordinate remains. -/
theorem chosenBlock_nonempty (D : P → Finset I) (U : Finset I) (hU : U.Nonempty) :
    (chosenBlock D U).Nonempty := by
  classical
  obtain ⟨e, he⟩ := hU
  have hi : Independent D {e} := by
    intro p i hi j hj _ _
    exact (Finset.mem_singleton.mp hi).trans (Finset.mem_singleton.mp hj).symm
  have hm : {e} ∈ candidates D U := Finset.mem_filter.mpr
    ⟨Finset.mem_powerset.mpr (Finset.singleton_subset_iff.mpr he), hi⟩
  have hc := chosenBlock_maximal D U {e} hm
  exact Finset.card_pos.mp (by simpa only [Finset.card_singleton, Nat.succ_le_iff] using hc)

omit [Fintype P] in
/-- Each nonterminal selected block strictly reduces the active coordinate inventory. -/
theorem active_card_decreases (D : P → Finset I) (U : Finset I) (hU : U.Nonempty) :
    (U \ chosenBlock D U).card < U.card := by
  have hp := Finset.card_pos.mpr (chosenBlock_nonempty D U hU)
  have hc := Finset.card_sdiff_add_card_eq_card (chosenBlock_subset D U)
  omega

end
end UnifiedTheory.Clay.YangMills.FiniteFactorPacking
