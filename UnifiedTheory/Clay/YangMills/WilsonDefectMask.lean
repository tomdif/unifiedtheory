/- Actual good-link masks remove internal plaquette defects and the boundary
collar. Their size is paid by internal energy plus a surface term. -/
import UnifiedTheory.Clay.YangMills.WilsonSpatialCutTranslate
import UnifiedTheory.Clay.YangMills.WilsonSpatialGramNeighborhood
import UnifiedTheory.Clay.YangMills.QuaternionDefectCurvature

set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace UnifiedTheory.Clay.YangMills.WilsonDefectMask
noncomputable section
open WilsonTimeSlab WilsonSlabOperator WilsonSpatialCutEnergy
open scoped Quaternion

variable (n : ℕ) [NeZero n]
local instance linkDecidableEq : DecidableEq (SpatialVertex n × Fin 3) := Classical.decEq _
local instance plaquetteDecidableEq : DecidableEq (Plaquette n) := Classical.decEq _

omit [NeZero n] in
theorem support_card (p : Plaquette n) : (support n p).card ≤ 4 :=
  WilsonSpatialGramNeighborhood.plaquetteLinks_card n p

def bad (P : Finset (Plaquette n)) (δ : ℝ) (u : Slice n) : Finset (Plaquette n) :=
  P.filter (fun p => δ^2 < defect n u p)

def stars (P : Finset (Plaquette n)) : Finset (SpatialVertex n × Fin 3) :=
  P.biUnion (support n)

def good (S : Finset (SpatialVertex n × Fin 3)) (δ : ℝ) (u : Slice n) :
    Finset (SpatialVertex n × Fin 3) :=
  S \ stars n (bad n (bulk n S) δ u ∪ boundary n S)

def removed (S : Finset (SpatialVertex n × Fin 3)) (δ : ℝ) (u : Slice n) :
    Finset (SpatialVertex n × Fin 3) := S \ good n S δ u

omit [NeZero n] in
theorem bad_card_energy (P : Finset (Plaquette n)) (δ : ℝ) (u : Slice n) :
    δ^2*((bad n P δ u).card : ℝ) ≤ partPotential n P u := by
  have h1 := Finset.sum_le_sum (s := bad n P δ u) (f := fun _ => δ^2)
    (g := defect n u) (fun p hp => (Finset.mem_filter.mp hp).2.le)
  have h2 := Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ P)
    (fun p (_ : p ∈ P) (_ : p ∉ bad n P δ u) =>
      (WilsonSlabBounds.characterDefect_bounds (spatialHolonomy u p.1 p.2.1.1 p.2.1.2)).1)
  change (∑ p ∈ bad n P δ u, defect n u p) ≤ partPotential n P u at h2
  have hh : δ^2*((bad n P δ u).card : ℝ) ≤ ∑ p ∈ bad n P δ u, defect n u p := by
    simpa only [Finset.sum_const, nsmul_eq_mul, mul_comm] using h1
  exact hh.trans h2

omit [NeZero n] in
theorem stars_card (P : Finset (Plaquette n)) : (stars n P).card ≤ 4*P.card := by
  calc
    _ ≤ ∑ p ∈ P, (support n p).card := Finset.card_biUnion_le
    _ ≤ ∑ _p ∈ P, 4 := Finset.sum_le_sum (fun p _ => support_card n p)
    _ = _ := by simp [Nat.mul_comm]

theorem good_subset (S : Finset (SpatialVertex n × Fin 3)) (δ : ℝ) (u : Slice n) :
    good n S δ u ⊆ S := Finset.sdiff_subset

theorem removed_subset (S : Finset (SpatialVertex n × Fin 3)) (δ : ℝ) (u : Slice n) :
    removed n S δ u ⊆ stars n (bad n (bulk n S) δ u ∪ boundary n S) := by
  intro e he
  by_contra h
  exact (Finset.mem_sdiff.mp he).2 (Finset.mem_sdiff.mpr ⟨(Finset.mem_sdiff.mp he).1,h⟩)

theorem removed_card (S : Finset (SpatialVertex n × Fin 3)) (δ : ℝ) (u : Slice n) :
    (removed n S δ u).card ≤ 4*((bad n (bulk n S) δ u).card+(boundary n S).card) := by
  exact (Finset.card_le_card (removed_subset n S δ u)).trans
    ((stars_card n _).trans (Nat.mul_le_mul_left 4 (Finset.card_union_le _ _)))

/-- The loss of active directions is controlled by actual defect energy. -/
theorem removed_budget (S : Finset (SpatialVertex n × Fin 3)) (δ : ℝ) (u : Slice n) :
    δ^2*((removed n S δ u).card : ℝ) ≤
      4*bulkPotential n S u+4*δ^2*(boundary n S).card := by
  have hc : ((removed n S δ u).card : ℝ) ≤
      4*(((bad n (bulk n S) δ u).card : ℝ)+(boundary n S).card) := by
    exact_mod_cast removed_card n S δ u
  have hh := mul_le_mul_of_nonneg_left hc (sq_nonneg δ)
  have he := bad_card_energy n (bulk n S) δ u
  change δ^2*((bad n (bulk n S) δ u).card : ℝ) ≤ bulkPotential n S u at he
  nlinarith

/-- Every plaquette touching a retained link is internal and has small defect. -/
theorem good_touches (S : Finset (SpatialVertex n × Fin 3)) (δ : ℝ) (u : Slice n)
    (e : SpatialVertex n × Fin 3) (he : e ∈ good n S δ u) (p : Plaquette n)
    (hp : e ∈ support n p) : p ∈ bulk n S ∧ defect n u p ≤ δ^2 := by
  have hS := (Finset.mem_sdiff.mp he).1
  have hnot := (Finset.mem_sdiff.mp he).2
  have hboundary : p ∉ boundary n S := fun h => hnot
    (Finset.mem_biUnion.mpr ⟨p,Finset.mem_union.mpr (Or.inr h),hp⟩)
  have hbulk : p ∈ bulk n S := by
    by_contra h
    apply hboundary
    apply Finset.mem_sdiff.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    intro hm
    rcases Finset.mem_union.mp hm with hm | hm
    · exact h hm
    · exact (Finset.mem_compl.mp ((Finset.mem_filter.mp hm).2 hp)) hS
  refine ⟨hbulk, ?_⟩
  by_contra h
  exact hnot (Finset.mem_biUnion.mpr ⟨p,Finset.mem_union.mpr
    (Or.inl (Finset.mem_filter.mpr ⟨hbulk,lt_of_not_ge h⟩)),hp⟩)

theorem good_chord (S : Finset (SpatialVertex n × Fin 3)) (δ : ℝ) (hδ : 0 ≤ δ)
    (u : Slice n) (e : SpatialVertex n × Fin 3) (he : e ∈ good n S δ u)
    (p : Plaquette n) (hp : e ∈ support n p) :
    ‖((spatialHolonomy u p.1 p.2.1.1 p.2.1.2 : Q) : ℍ)-1‖ ≤ δ := by
  have hh := (good_touches n S δ u e he p hp).2
  change 2-(WilsonSingleLinkStaples.character _).re ≤ δ^2 at hh
  rw [QuaternionDefectCurvature.character_chord] at hh
  nlinarith [norm_nonneg (((spatialHolonomy u p.1 p.2.1.1 p.2.1.2 : Q) : ℍ)-1)]

omit [NeZero n] in
theorem defect_gauge (p : Plaquette n) (h : SliceGauge n Q) (u : Slice n) :
    defect n (gaugeSlice h u) p = defect n u p := by
  simpa only [partPotential, Finset.sum_singleton] using part_gauge n {p} h u

theorem good_gauge (S : Finset (SpatialVertex n × Fin 3)) (δ : ℝ)
    (h : SliceGauge n Q) (u : Slice n) : good n S δ (gaugeSlice h u) = good n S δ u := by
  have hb : bad n (bulk n S) δ (gaugeSlice h u) = bad n (bulk n S) δ u := by
    ext p
    simp only [bad, Finset.mem_filter, defect_gauge]
  simp only [good, hb]

theorem bulk_le_total (S : Finset (SpatialVertex n × Fin 3)) (u : Slice n) :
    bulkPotential n S u ≤ potential WilsonSingleLinkStaples.character 2 u := by
  have h := potential_split n S u
  have he := (part_bounds n (bulk n Sᶜ) u).1
  have hb := (part_bounds n (boundary n S) u).1
  change 0 ≤ bulkPotential n Sᶜ u at he
  change 0 ≤ boundaryPotential n S u at hb
  linarith


omit [NeZero n] in
theorem defect_continuous (p : Plaquette n) : Continuous (fun u : Slice n => defect n u p) := by
  have h := part_continuous n {p}
  change Continuous (fun u : Slice n => ∑ q ∈ ({p} : Finset (Plaquette n)), defect n u q) at h
  simpa only [Finset.sum_singleton] using h

theorem mem_bad_measurable (P : Finset (Plaquette n)) (δ : ℝ) (p : Plaquette n) :
    MeasurableSet {u : Slice n | p ∈ bad n P δ u} := by
  simp only [bad, Finset.mem_filter]
  exact (MeasurableSet.const (p ∈ P)).inter
    (measurableSet_lt measurable_const (defect_continuous n p).measurable)

theorem mem_removed_measurable (S : Finset (SpatialVertex n × Fin 3)) (δ : ℝ)
    (e : SpatialVertex n × Fin 3) : MeasurableSet {u : Slice n | e ∈ removed n S δ u} := by
  have hstar : MeasurableSet {u : Slice n |
      e ∈ stars n (bad n (bulk n S) δ u ∪ boundary n S)} := by
    have he : {u : Slice n | e ∈ stars n (bad n (bulk n S) δ u ∪ boundary n S)} =
        ⋃ p : Plaquette n, {u : Slice n |
          (p ∈ bad n (bulk n S) δ u ∨ p ∈ boundary n S) ∧ e ∈ support n p} := by
      ext u
      simp only [stars, Finset.mem_biUnion, Finset.mem_union, Set.mem_setOf_eq, Set.mem_iUnion]
    rw [he]
    exact MeasurableSet.iUnion (fun p =>
      ((mem_bad_measurable n (bulk n S) δ p).union
        (MeasurableSet.const (p ∈ boundary n S))).inter (MeasurableSet.const (e ∈ support n p)))
  simp only [removed, good, Finset.mem_sdiff]
  exact (MeasurableSet.const (e ∈ S)).inter
    ((MeasurableSet.const (e ∈ S)).inter hstar.compl).compl

theorem removed_card_measurable (S : Finset (SpatialVertex n × Fin 3)) (δ : ℝ) :
    Measurable (fun u : Slice n => ((removed n S δ u).card : ℝ)) := by
  classical
  have he : (fun u : Slice n => ((removed n S δ u).card : ℝ)) =
      (fun u => ∑ e : SpatialVertex n × Fin 3, if e ∈ removed n S δ u then (1 : ℝ) else 0) := by
    funext u
    rw [← Finset.sum_filter]
    simp only [Finset.filter_univ_mem, Finset.sum_const, nsmul_eq_mul, mul_one]
  rw [he]
  exact Finset.measurable_sum _ (fun e _ =>
    Measurable.ite (mem_removed_measurable n S δ e) measurable_const measurable_const)

end
end UnifiedTheory.Clay.YangMills.WilsonDefectMask
