/- Actual induced Wilson stars admit an extensive separated second block.
A maximal finite packing is constructed from the surviving edge inventory;
its density bound uses the proved twenty-four-edge star bound. -/
import UnifiedTheory.Clay.YangMills.WilsonInducedProduct
import Mathlib.Data.Finset.Max

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Clay.YangMills.WilsonSeparatedBlockPacking
noncomputable section
open RegulatedGauge PeriodicLattice4 WilsonInducedSupport WilsonInducedProduct

variable (n : ℕ) [NeZero n]
local instance edgeDecidableEq : DecidableEq (Edge (Vertex n)) := Classical.decEq _

/-- Closed conflict neighborhood: equal edges or overlapping actual stars. -/
def conflict (e : Edge (Vertex n)) : Finset (Edge (Vertex n)) :=
  insert e ((star n e).biUnion (star n))

omit [NeZero n] in
theorem mem_conflict_self (e : Edge (Vertex n)) : e ∈ conflict n e :=
  Finset.mem_insert_self _ _

theorem overlap_mem_conflict (e d : Edge (Vertex n))
    (h : ¬ Disjoint (star n e) (star n d)) : d ∈ conflict n e := by
  obtain ⟨z, hze, hzd⟩ := Finset.not_disjoint_iff.mp h
  exact Finset.mem_insert_of_mem (Finset.mem_biUnion.mpr
    ⟨z, hze, (star_symm n d z).mp hzd⟩)

/-- The conflict bound is uniform in the lattice period and the previous elimination. -/
theorem conflict_card (e : Edge (Vertex n)) : (conflict n e).card ≤ 577 := by
  have h : ((star n e).biUnion (star n)).card ≤ 576 := by
    calc
      _ ≤ ∑ d ∈ star n e, (star n d).card := Finset.card_biUnion_le
      _ ≤ ∑ _d ∈ star n e, 24 := Finset.sum_le_sum (fun d _ => star_card n d)
      _ ≤ 576 := by
        simp only [Finset.sum_const, smul_eq_mul]
        have hc := star_card n e
        omega
  exact (Finset.card_insert_le _ _).trans (by omega)

/-- A maximal packing in any actual edge inventory covers that inventory by bounded conflicts. -/
theorem exists_separated_subset (U : Finset (Edge (Vertex n))) :
    ∃ T ⊆ U, SeparatedStars n T ∧ U.card ≤ 577 * T.card := by
  classical
  let L := U.powerset.filter (SeparatedStars n)
  have hL : L.Nonempty := by
    refine ⟨∅, Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr (Finset.empty_subset _), ?_⟩⟩
    intro e he
    simp only [Finset.notMem_empty] at he
  obtain ⟨T, hT, hmax⟩ := L.exists_max_image Finset.card hL
  obtain ⟨hTU, hsep⟩ := Finset.mem_filter.mp hT
  have hTU : T ⊆ U := Finset.mem_powerset.mp hTU
  have hcover : U ⊆ T.biUnion (conflict n) := by
    intro e heU
    by_contra heC
    have heT : e ∉ T := fun heT => heC
      (Finset.mem_biUnion.mpr ⟨e, heT, mem_conflict_self n e⟩)
    have hed (d : Edge (Vertex n)) (hd : d ∈ T) : Disjoint (star n e) (star n d) := by
      by_contra h
      exact heC (Finset.mem_biUnion.mpr ⟨d, hd,
        overlap_mem_conflict n d e (fun hde => h hde.symm)⟩)
    have hi : SeparatedStars n (insert e T) := by
      intro d hd f hf hdf
      rcases Finset.mem_insert.mp hd with hde | hdT
      · subst d
        rcases Finset.mem_insert.mp hf with hfe | hfT
        · exact (hdf hfe.symm).elim
        · exact hed f hfT
      · rcases Finset.mem_insert.mp hf with hfe | hfT
        · subst f
          exact (hed d hdT).symm
        · exact hsep d hdT f hfT hdf
    have him : insert e T ∈ L := Finset.mem_filter.mpr
      ⟨Finset.mem_powerset.mpr (Finset.insert_subset heU hTU), hi⟩
    have hc := hmax (insert e T) him
    rw [Finset.card_insert_of_notMem heT] at hc
    omega
  refine ⟨T, hTU, hsep, ?_⟩
  calc
    U.card ≤ (T.biUnion (conflict n)).card := Finset.card_le_card hcover
    _ ≤ ∑ e ∈ T, (conflict n e).card := Finset.card_biUnion_le
    _ ≤ ∑ _e ∈ T, 577 := Finset.sum_le_sum (fun e _ => conflict_card n e)
    _ = 577 * T.card := by simp [mul_comm]

/-- A genuine retained-subtype block satisfies the exact induced-product hypothesis
and occupies at least one in 577 surviving coordinates. -/
theorem exists_next_block (S : Finset (Edge (Vertex n))) :
    ∃ T : Finset {e : Edge (Vertex n) // e ∉ S},
      NextSeparated n S T ∧ (Finset.univ \ S).card ≤ 577 * T.card := by
  classical
  obtain ⟨E, hE, hsep, hcard⟩ := exists_separated_subset n (Finset.univ \ S)
  have hES (e : Edge (Vertex n)) (he : e ∈ E) : e ∉ S := (Finset.mem_sdiff.mp (hE he)).2
  let T := E.subtype (fun e => e ∉ S)
  have himage : T.image Subtype.val = E := by
    ext e
    simp only [T, Finset.mem_image, Finset.mem_subtype]
    constructor
    · rintro ⟨d, hd, rfl⟩
      exact hd
    · intro he
      exact ⟨⟨e, hES e he⟩, he, rfl⟩
  have hc : T.card = E.card := by
    change (E.subtype (fun e => e ∉ S)).card = E.card
    rw [Finset.card_subtype, Finset.filter_true_of_mem hES]
  refine ⟨T, ?_, ?_⟩
  · change SeparatedStars n (T.image Subtype.val)
    rwa [himage]
  · simpa only [hc] using hcard

/-- A surviving coordinate guarantees that the constructed admissible second block is nonempty. -/
theorem exists_nonempty_next_block (S : Finset (Edge (Vertex n)))
    (hS : (Finset.univ \ S).Nonempty) :
    ∃ T : Finset {e : Edge (Vertex n) // e ∉ S}, NextSeparated n S T ∧ T.Nonempty := by
  obtain ⟨T, hT, hc⟩ := exists_next_block n S
  refine ⟨T, hT, Finset.card_pos.mp ?_⟩
  have hp := Finset.card_pos.mpr hS
  omega

end
end UnifiedTheory.Clay.YangMills.WilsonSeparatedBlockPacking
