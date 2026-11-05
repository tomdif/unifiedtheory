/- Concrete boxes instantiate the local cut estimate. Their crossing cost
is a surface term, while a high internal spatial energy is volumetric. -/
import UnifiedTheory.Clay.YangMills.WilsonSpatialCutDecay
import UnifiedTheory.Clay.YangMills.WilsonAxialBox
import UnifiedTheory.Clay.YangMills.WilsonHighFieldSector

set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace UnifiedTheory.Clay.YangMills.WilsonSpatialCutBox
noncomputable section
open WilsonTimeSlab WilsonSlabOperator WilsonSpatialCutEnergy WilsonSpatialCutDecay
open WilsonAxialBox WilsonPhysicalVariance WilsonHighFieldDecay

variable (n : ℕ) [NeZero n]
local instance linkDecidableEq : DecidableEq (SpatialVertex n × Fin 3) := Classical.decEq _
local instance plaquetteDecidableEq : DecidableEq (SpatialVertex n × SpatialPlane) :=
  Classical.decEq _

def links (L : ℕ) : Finset (SpatialVertex n × Fin 3) := (block n L).product Finset.univ

omit [NeZero n] in
theorem links_card (L : ℕ) (hL : L + 1 ≤ n) : (links n L).card = 3*L^3 := by
  simp [links, Finset.card_product, block_card n L hL, Nat.mul_comm]

theorem bulk_origin (L : ℕ) (p : Plaquette n) (hp : p ∈ bulk n (links n L)) : p.1 ∈ block n L := by
  have he := (Finset.mem_filter.mp hp).2 (by simp [support] : (p.1,p.2.1.1) ∈ support n p)
  exact (Finset.mem_product.mp he).1

theorem bulk_card_le (L : ℕ) (hL : L + 1 ≤ n) : (bulk n (links n L)).card ≤ 3*L^3 := by
  have hsub : bulk n (links n L) ⊆ (block n L).product (Finset.univ : Finset SpatialPlane) := by
    intro p hp
    exact Finset.mem_product.mpr ⟨bulk_origin n L p hp, Finset.mem_univ _⟩
  have h := Finset.card_le_card hsub
  simpa only [Finset.product_eq_sprod, Finset.card_product, block_card n L hL, Finset.card_univ,
    WilsonSlabBounds.spatialPlane_card, Nat.mul_comm] using h

variable [Fact (1 < n)]

theorem core_bulk (L : ℕ) (hL : L + 1 ≤ n) (p : Plaquette n)
    (hp : p.1 ∈ vertices n 1 L) : p ∈ bulk n (links n L) := by
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ _, ?_⟩
  intro e he
  have hc (i : Fin 3) : (p.1,i) ∈ core n L := Finset.mem_product.mpr ⟨hp,Finset.mem_univ _⟩
  have hs := core_source n L hL _ (hc p.2.1.1)
  have hi := core_target n L hL _ (hc p.2.1.1)
  have hj := core_target n L hL _ (hc p.2.1.2)
  simp only [support, Finset.mem_insert, Finset.mem_singleton] at he
  rcases he with rfl | rfl | rfl | rfl
  all_goals exact Finset.mem_product.mpr ⟨by assumption,Finset.mem_univ _⟩

theorem boundary_origin_outer (L : ℕ) (hL : L + 1 ≤ n) (p : Plaquette n)
    (hp : p ∈ boundary n (links n L)) : p.1 ∈ vertices n 0 (L + 1) := by
  have hout : p ∉ bulk n (links n L)ᶜ := by
    exact fun h => (Finset.mem_sdiff.mp hp).2 (Finset.mem_union.mpr (Or.inr h))
  have hn : ¬support n p ⊆ (links n L)ᶜ := by
    intro h
    exact hout (Finset.mem_filter.mpr ⟨Finset.mem_univ _,h⟩)
  obtain ⟨e,he,hs⟩ := Finset.not_subset.mp hn
  have hes : e ∈ links n L := by simpa only [Finset.mem_compl, not_not] using hs
  have hx := (Finset.mem_product.mp hes).1
  have hf (i : Fin 3) (hi : p.1 ∈ block n L ∨ spatialStep n p.1 i ∈ block n L) :
      p.1 ∈ vertices n 0 (L + 1) :=
    (Finset.mem_product.mp (touched_subset_outer n L hL
      (Finset.mem_filter.mpr ⟨Finset.mem_univ (p.1,i),hi⟩))).1
  simp only [support, Finset.mem_insert, Finset.mem_singleton] at he
  rcases he with rfl | rfl | rfl | rfl
  · exact hf p.2.1.1 (Or.inl hx)
  · exact hf p.2.1.1 (Or.inr hx)
  · exact hf p.2.1.2 (Or.inr hx)
  · exact hf p.2.1.2 (Or.inl hx)

theorem boundary_surface (L : ℕ) (hpos : 0 < L) (hL : L + 1 ≤ n) :
    ((boundary n (links n L)).card : ℝ) ≤ 24*(L : ℝ)^2 := by
  have hsub : boundary n (links n L) ⊆
      (vertices n 0 (L + 1) \ vertices n 1 L).product (Finset.univ : Finset SpatialPlane) := by
    intro p hp
    apply Finset.mem_product.mpr
    refine ⟨Finset.mem_sdiff.mpr ⟨boundary_origin_outer n L hL p hp, ?_⟩,Finset.mem_univ _⟩
    intro hc
    exact (Finset.mem_sdiff.mp hp).2 (Finset.mem_union.mpr (Or.inl (core_bulk n L hL p hc)))
  have hcard := Finset.card_le_card hsub
  have hv : vertices n 1 L ⊆ vertices n 0 (L + 1) := by
    intro x hx
    have hh := (mem_vertices n 1 L (by omega) x).mp hx
    apply (mem_vertices n 0 (L + 1) hL x).mpr
    intro i
    have := hh i
    omega
  rw [Finset.product_eq_sprod, Finset.card_product, Finset.card_sdiff_of_subset hv,
    vertices_card n 0 (L + 1) hL, vertices_card n 1 L (by omega),
    Finset.card_univ, WilsonSlabBounds.spatialPlane_card, Nat.sub_zero] at hcard
  have hpow : (L-1)^3 ≤ (L+1)^3 := Nat.pow_le_pow_left (by omega) 3
  have hh : ((boundary n (links n L)).card : ℝ) ≤
      (((L+1)^3-(L-1)^3 : ℕ) : ℝ)*3 := by exact_mod_cast hcard
  simp only [Nat.cast_sub hpow, Nat.cast_pow, Nat.cast_add, Nat.cast_one,
    Nat.cast_sub (show 1 ≤ L by omega)] at hh
  have h1 : (1 : ℝ) ≤ L := by exact_mod_cast hpos
  nlinarith [sq_nonneg ((L : ℝ)-1)]

/-- The ambient period appears only in the geometric fit condition. -/
theorem box_decay (β : ℝ) (hβ : 0 < β) (L : ℕ) (hL : L + 1 ≤ n) (hlarge : 4096 ≤ L)
    (he : WilsonGroundSlabEnergy.envelope β ≤ 1 / 96) (f : C(Slice n, ℝ))
    (hs : ∀ u, bulkPotential n (links n L) u < (L : ℝ) ^ 3 → f u = 0) :
    mass n β hβ.le (step n β hβ.le f) ≤ Real.exp (-β*(L : ℝ) ^ 3/4)*mass n β hβ.le f := by
  have hb := boundary_surface n L (by omega) hL
  have hp := bulk_card_le n L hL
  have hn := links_card n L hL
  have h0 : (4096 : ℝ) ≤ L := by exact_mod_cast hlarge
  have h1 : 0 ≤ WilsonGroundSlabEnergy.envelope β := by
    have hl : 0 ≤ Real.log (2*β+5) := Real.log_nonneg (by linarith)
    unfold WilsonGroundSlabEnergy.envelope
    positivity
  have hcount : ((bulk n (links n L)).card : ℝ)+(links n L).card ≤ 6*(L : ℝ) ^ 3 := by
    rw [hn]
    have hh : ((bulk n (links n L)).card : ℝ) ≤ 3*(L : ℝ) ^ 3 := by exact_mod_cast hp
    norm_num only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
    linarith
  have hprice := mul_le_mul_of_nonneg_right hcount h1
  have hbound := mul_le_mul_of_nonneg_left he (show 0 ≤ 24*(L : ℝ) ^ 3 by positivity)
  have hr : 8*((boundary n (links n L)).card : ℝ)+(L : ℝ) ^ 3/2 ≤ (L : ℝ) ^ 3 := by
    have hpow := mul_nonneg (show 0 ≤ (L : ℝ)-384 by linarith) (sq_nonneg (L : ℝ))
    nlinarith
  have hlocal := local_decay n β hβ (links n L) ((L : ℝ) ^ 3) ((L : ℝ) ^ 3/2) hr
    (by nlinarith) f hs
  convert hlocal using 1
  congr 2
  ring

theorem bulk_card_lower (L : ℕ) (hL : L + 1 ≤ n) :
    3*(L-1)^3 ≤ (bulk n (links n L)).card := by
  have hsub : (vertices n 1 L).product (Finset.univ : Finset SpatialPlane) ⊆
      bulk n (links n L) := by
    intro p hp
    exact core_bulk n L hL p (Finset.mem_product.mp hp).1
  have h := Finset.card_le_card hsub
  simpa only [Finset.product_eq_sprod, Finset.card_product, Finset.card_univ,
    WilsonSlabBounds.spatialPlane_card, vertices_card n 1 L (by omega), Nat.mul_comm] using h

omit [Fact (1 < n)] in
theorem maximal_bulk (S : Finset (SpatialVertex n × Fin 3)) :
    bulkPotential n S (WilsonHighFieldSector.largeField n) = 4*((bulk n S).card : ℝ) := by
  have hp (p : Plaquette n) : defect n (WilsonHighFieldSector.largeField n) p = 4 := by
    rw [defect, WilsonHighFieldSector.large_holonomy]
    norm_num [WilsonSingleLinkStaples.character_re, Unitary.coe_neg]
  simp only [bulkPotential, partPotential, hp, Finset.sum_const, nsmul_eq_mul, mul_comm]

omit [Fact (1 < n)] in
theorem flat_bulk (S : Finset (SpatialVertex n × Fin 3)) : bulkPotential n S (1 : Slice n) = 0 := by
  simp [bulkPotential, partPotential, defect, spatialHolonomy, WilsonSingleLinkStaples.character_re]

/-- An explicit field lies strictly above the hard-event threshold in every
admissible box. Thus the region is not eliminated by a vacuous threshold. -/
theorem high_box_nonempty (L : ℕ) (hL : L + 1 ≤ n) (hlarge : 4096 ≤ L) :
    2*(L : ℝ) ^ 3 < bulkPotential n (links n L) (WilsonHighFieldSector.largeField n) := by
  rw [maximal_bulk]
  have h := bulk_card_lower n L hL
  have hh : 3*((L : ℝ)-1)^3 ≤ ((bulk n (links n L)).card : ℝ) := by
    have hh : (3*((L-1)^3) : ℕ) ≤ (bulk n (links n L)).card := h
    have hx : ((3*(L-1)^3 : ℕ) : ℝ) ≤ ((bulk n (links n L)).card : ℝ) := by
      exact_mod_cast hh
    simpa only [Nat.cast_mul, Nat.cast_pow, Nat.cast_sub (show 1 ≤ L by omega),
      Nat.cast_ofNat, Nat.cast_one] using hx
  have h0 : (4096 : ℝ) ≤ L := by exact_mod_cast hlarge
  have h1 := pow_nonneg (show 0 ≤ (L : ℝ)-4 by linarith) 3
  nlinarith [sq_nonneg ((L : ℝ)-4)]

omit n [NeZero n] [Fact (1 < n)] in
theorem eventual_condition :
    ∀ᶠ β : ℝ in Filter.atTop, 0 < β ∧ WilsonGroundSlabEnergy.envelope β ≤ 1 / 96 := by
  have h := WilsonGroundSlabEnergy.envelope_tendsto.eventually
    (eventually_lt_nhds (show (0 : ℝ) < 1 / 96 by norm_num))
  filter_upwards [Filter.eventually_gt_atTop (0 : ℝ), h] with β hb he
  exact ⟨hb,he.le⟩

end
end UnifiedTheory.Clay.YangMills.WilsonSpatialCutBox
