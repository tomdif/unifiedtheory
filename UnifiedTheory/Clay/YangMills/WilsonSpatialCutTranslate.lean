/- Actual translated spatial blocks retain the same internal and crossing
counts, including translations across the periodic seam. -/
import UnifiedTheory.Clay.YangMills.WilsonSpatialCutBox
import UnifiedTheory.Clay.YangMills.WilsonGroundTranslation

set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace UnifiedTheory.Clay.YangMills.WilsonSpatialCutTranslate
noncomputable section
open WilsonTimeSlab WilsonSlabOperator WilsonSpatialCutEnergy

variable (n : ℕ) [NeZero n]
local instance linkDecidableEq : DecidableEq (SpatialVertex n × Fin 3) := Classical.decEq _
local instance plaquetteDecidableEq : DecidableEq (SpatialVertex n × SpatialPlane) :=
  Classical.decEq _

def linkShift (a : SpatialVertex n) : (SpatialVertex n × Fin 3) ≃ (SpatialVertex n × Fin 3) :=
  Equiv.prodCongr (Equiv.addRight a) (Equiv.refl _)

def plaquetteShift (a : SpatialVertex n) : Plaquette n ≃ Plaquette n :=
  Equiv.prodCongr (Equiv.addRight a) (Equiv.refl _)

def translate (a : SpatialVertex n) (S : Finset (SpatialVertex n × Fin 3)) :
    Finset (SpatialVertex n × Fin 3) := S.map (linkShift n a).toEmbedding

omit [NeZero n] in
theorem support_shift (a : SpatialVertex n) (p : Plaquette n) :
    support n (plaquetteShift n a p) = (support n p).map (linkShift n a).toEmbedding := by
  simp [support, linkShift, plaquetteShift, WilsonGroundTranslation.step_add]

theorem bulk_mem (a : SpatialVertex n) (S : Finset (SpatialVertex n × Fin 3))
    (p : Plaquette n) :
    plaquetteShift n a p ∈ bulk n (translate n a S) ↔ p ∈ bulk n S := by
  simp only [bulk, Finset.mem_filter, Finset.mem_univ, true_and, support_shift,
    translate, Finset.map_subset_map]

theorem bulk_translate (a : SpatialVertex n) (S : Finset (SpatialVertex n × Fin 3)) :
    bulk n (translate n a S) = (bulk n S).map (plaquetteShift n a).toEmbedding := by
  ext p
  rw [Finset.mem_map_equiv]
  simpa only [Equiv.apply_symm_apply] using bulk_mem n a S ((plaquetteShift n a).symm p)

theorem translate_compl (a : SpatialVertex n) (S : Finset (SpatialVertex n × Fin 3)) :
    translate n a Sᶜ = (translate n a S)ᶜ := by
  ext e
  simp only [translate, Finset.mem_map_equiv, Finset.mem_compl]

theorem boundary_translate (a : SpatialVertex n) (S : Finset (SpatialVertex n × Fin 3)) :
    boundary n (translate n a S) = (boundary n S).map (plaquetteShift n a).toEmbedding := by
  unfold boundary
  rw [← translate_compl, bulk_translate, bulk_translate, Finset.map_sdiff, Finset.map_union,
    Finset.map_univ_equiv]

omit [NeZero n] in
theorem translate_card (a : SpatialVertex n) (S : Finset (SpatialVertex n × Fin 3)) :
    (translate n a S).card = S.card := Finset.card_map _

theorem bulk_card (a : SpatialVertex n) (S : Finset (SpatialVertex n × Fin 3)) :
    (bulk n (translate n a S)).card = (bulk n S).card := by rw [bulk_translate, Finset.card_map]

theorem boundary_card (a : SpatialVertex n) (S : Finset (SpatialVertex n × Fin 3)) :
    (boundary n (translate n a S)).card = (boundary n S).card := by
  rw [boundary_translate, Finset.card_map]

theorem potential_translate (a : SpatialVertex n) (S : Finset (SpatialVertex n × Fin 3))
    (u : Slice n) : bulkPotential n (translate n a S) u =
      bulkPotential n S (WilsonGroundTranslation.shiftSlice n a u) := by
  simp only [bulkPotential, partPotential, bulk_translate, Finset.sum_map]
  apply Finset.sum_congr rfl
  intro p _
  simp only [defect, WilsonGroundTranslation.spatialHolonomy_shift]
  rfl

def box (L : ℕ) (a : SpatialVertex n) : Finset (SpatialVertex n × Fin 3) :=
  translate n a (WilsonSpatialCutBox.links n L)

omit [NeZero n] in
theorem box_card (L : ℕ) (hL : L + 1 ≤ n) (a : SpatialVertex n) : (box n L a).card = 3*L^3 := by
  rw [box, translate_card, WilsonSpatialCutBox.links_card n L hL]

theorem box_bulk_le (L : ℕ) (hL : L + 1 ≤ n) (a : SpatialVertex n) :
    (bulk n (box n L a)).card ≤ 3*L^3 := by
  rw [box, bulk_card]
  exact WilsonSpatialCutBox.bulk_card_le n L hL

variable [Fact (1 < n)]

theorem box_boundary_le (L : ℕ) (hL : L + 1 ≤ n) (hpos : 0 < L) (a : SpatialVertex n) :
    ((boundary n (box n L a)).card : ℝ) ≤ 24*(L : ℝ)^2 := by
  rw [box, boundary_card]
  exact WilsonSpatialCutBox.boundary_surface n L hpos hL

theorem box_bulk_lower (L : ℕ) (hL : L + 1 ≤ n) (a : SpatialVertex n) :
    3*(L-1)^3 ≤ (bulk n (box n L a)).card := by
  rw [box, bulk_card]
  exact WilsonSpatialCutBox.bulk_card_lower n L hL

end
end UnifiedTheory.Clay.YangMills.WilsonSpatialCutTranslate
