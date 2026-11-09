/- A fixed fraction of any plaquette pattern fits into one translated
six-plaquette cell tiling. The counting is independent of spatial volume. -/
import UnifiedTheory.Clay.YangMills.WilsonCubeTransport

set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace UnifiedTheory.Clay.YangMills.WilsonCubeCover
noncomputable section
open WilsonTimeSlab SpatialPlaquetteCutGeometry WilsonCubeCells DyadicCellCoordinates
open WilsonPlaquetteFrames WilsonProfileTransport

variable (m : ℕ) [NeZero m]

def offsetVertex (b : Offsets) : SpatialVertex (2 * m) := fun j => ((b j).val : ℕ)

theorem bit_shift (x : ZMod (2 * m)) (b : Fin 2) :
    bit m (x + (b.val : ℕ)) = 0 ↔ b = bit m x := by
  have hb : b = 0 ∨ b = 1 := by omega
  rcases hb with rfl | rfl
  · simp only [Fin.val_zero, Nat.cast_zero, add_zero, eq_comm]
  · have hx := (bit m x).isLt
    have hs := bit_succ_val m x
    simp only [Fin.val_one, Nat.cast_one]
    rw [Fin.ext_iff, Fin.ext_iff]
    change (bit m (x + 1)).val = 0 ↔ 1 = (bit m x).val
    omega

theorem internal_shift (b : Offsets) (p : Plaquette m) :
    Internal m ((translation m (offsetVertex m b)).plaquettes p) ↔
      b p.2.val.1 = offsets m p.1 p.2.val.1 ∧
      b p.2.val.2 = offsets m p.1 p.2.val.2 := by
  change (bit m (p.1 p.2.val.1 + ((b p.2.val.1).val : ℕ)) = 0 ∧
    bit m (p.1 p.2.val.2 + ((b p.2.val.2).val : ℕ)) = 0) ↔ _
  rw [bit_shift, bit_shift]
  rfl

omit m [NeZero m] in
theorem offsets_card : Fintype.card Offsets = 8 := by decide

omit m [NeZero m] in
theorem matching_card : ∀ (p : SpatialPlane) (x : Offsets),
    (Finset.univ.filter (fun b : Offsets => b p.val.1 = x p.val.1 ∧
      b p.val.2 = x p.val.2)).card = 2 := by decide

open Classical in
def retained (S : Finset (Plaquette m)) (b : Offsets) : Finset (Plaquette m) :=
  S.filter (fun p => Internal m ((translation m (offsetVertex m b)).plaquettes p))

theorem retained_subset (S : Finset (Plaquette m)) (b : Offsets) : retained m S b ⊆ S := by
  classical
  exact Finset.filter_subset _ _

theorem retained_sum (S : Finset (Plaquette m)) :
    (∑ b : Offsets, (retained m S b).card) = 2 * S.card := by
  classical
  simp only [retained, Finset.card_eq_sum_ones, Finset.sum_filter]
  rw [Finset.sum_comm]
  have h (p : Plaquette m) :
      (∑ b : Offsets, if Internal m ((translation m (offsetVertex m b)).plaquettes p)
        then 1 else 0) = 2 := by
    simpa only [internal_shift, Finset.card_eq_sum_ones, Finset.sum_filter] using
      matching_card p.2 (offsets m p.1)
  simp only [h, Finset.sum_const, smul_eq_mul]
  omega

theorem retained_quarter (S : Finset (Plaquette m)) :
    ∃ b : Offsets, S.card ≤ 4 * (retained m S b).card := by
  classical
  obtain ⟨b,hb,hm⟩ := Finset.exists_max_image Finset.univ
    (fun b : Offsets => (retained m S b).card) (Finset.univ_nonempty)
  have h := Finset.sum_le_sum (fun c (hc : c ∈ Finset.univ) => hm c hc)
  rw [retained_sum] at h
  simp only [Finset.sum_const, Finset.card_univ, offsets_card, smul_eq_mul] at h
  exact ⟨b,by omega⟩

open Classical in
def cells (S : Finset (Plaquette m)) (b : Offsets) : Finset (SpatialVertex m) :=
  (pushSet m (translation m (offsetVertex m b)) (retained m S b)).image
    (fun p => coarseVertex m p.1)

theorem cells_card (S : Finset (Plaquette m)) (b : Offsets) :
    (cells m S b).card ≤ (retained m S b).card := by
  classical
  exact (Finset.card_image_le).trans_eq (pushSet_card m _ _)

def cover (S : Finset (Plaquette m)) (b : Offsets) : Finset (Plaquette m) :=
  pushSet m (inverse m (translation m (offsetVertex m b))) (cellSet m (cells m S b))

theorem retained_cover (S : Finset (Plaquette m)) (b : Offsets) :
    retained m S b ⊆ cover m S b := by
  classical
  intro p hp
  rw [cover, pushSet_mem]
  change (translation m (offsetVertex m b)).plaquettes p ∈ cellSet m (cells m S b)
  rw [cellSet_mem]
  refine ⟨(Finset.mem_filter.mp hp).2,?_⟩
  apply Finset.mem_image.mpr
  refine ⟨(translation m (offsetVertex m b)).plaquettes p,?_,rfl⟩
  rw [pushSet_mem, Equiv.symm_apply_apply]
  exact hp

theorem cover_card (S : Finset (Plaquette m)) (b : Offsets) :
    (cover m S b).card ≤ 6 * (retained m S b).card := by
  rw [cover, pushSet_card, cellSet_card]
  exact Nat.mul_le_mul_left 6 (cells_card m S b)

end
end UnifiedTheory.Clay.YangMills.WilsonCubeCover
