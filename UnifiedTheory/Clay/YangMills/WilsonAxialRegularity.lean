/- Plaquette defects control links in the explicitly constructed coordinate
gauge, inside a nonwrapping box. The proof retains the strip length. -/
import UnifiedTheory.Clay.YangMills.WilsonAxialGauge

set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace UnifiedTheory.Clay.YangMills.WilsonAxialRegularity
noncomputable section
open WilsonTimeSlab WilsonSlabOperator WilsonAxialGauge
open scoped Quaternion

variable (n : ℕ)

def FlatBox (u : Slice n) (L : ℕ) (δ : ℝ) : Prop :=
  ∀ a b c : ℕ, a < L → b < L → c < L → ∀ i j : Fin 3, i < j →
    ‖((spatialHolonomy u (vertex n a b c) i j : Q) : ℍ)-1‖ ≤ δ

abbrev fixed (u : Slice n) : Slice n := gaugeSlice (gauge n u) u

omit n in
theorem defect_step (a b : Q) (δ E : ℝ)
    (hab : ‖(a : ℍ) - (b : ℍ)‖ ≤ δ) (hb : ‖(b : ℍ) - 1‖ ≤ E) :
    ‖(a : ℍ)-1‖ ≤ E+δ := by
  calc
    _ = ‖((a : ℍ)-(b : ℍ))+((b : ℍ)-1)‖ := by congr 1; abel
    _ ≤ ‖(a : ℍ)-(b : ℍ)‖+‖(b : ℍ)-1‖ := norm_add_le _ _
    _ ≤ _ := by linarith

theorem vertical_zero (u : Slice n) (L : ℕ) (hL : L ≤ n) (δ : ℝ)
    (hflat : FlatBox n u L δ) (a b c : ℕ)
    (ha : a + 1 < L) (hb : b < L) (hc : c + 1 < L) :
    ‖(fixed n u (vertex n a b c,0) : ℍ)-
      (fixed n u (vertex n a b (c + 1),0) : ℍ)‖ ≤ δ := by
  have h0 := tree_two n u a b c (by omega) (by omega) (by omega)
  have h1 : fixed n u (spatialStep n (vertex n a b c) 0,2) = 1 := by
    rw [vertex_step_zero]
    exact tree_two n u (a + 1) b c (by omega) (by omega) (by omega)
  have hs := strip_difference n (fixed n u) (vertex n a b c) 0 2 h0 h1
  rw [vertex_step_two, holonomy_defect_gauge] at hs
  exact hs.trans_le (hflat a b c (by omega) hb (by omega) 0 2 (by decide))

theorem vertical_one (u : Slice n) (L : ℕ) (hL : L ≤ n) (δ : ℝ)
    (hflat : FlatBox n u L δ) (a b c : ℕ)
    (ha : a < L) (hb : b + 1 < L) (hc : c + 1 < L) :
    ‖(fixed n u (vertex n a b c,1) : ℍ)-
      (fixed n u (vertex n a b (c + 1),1) : ℍ)‖ ≤ δ := by
  have h0 := tree_two n u a b c (by omega) (by omega) (by omega)
  have h1 : fixed n u (spatialStep n (vertex n a b c) 1,2) = 1 := by
    rw [vertex_step_one]
    exact tree_two n u a (b + 1) c (by omega) (by omega) (by omega)
  have hs := strip_difference n (fixed n u) (vertex n a b c) 1 2 h0 h1
  rw [vertex_step_two, holonomy_defect_gauge] at hs
  exact hs.trans_le (hflat a b c ha (by omega) (by omega) 1 2 (by decide))

theorem horizontal_zero (u : Slice n) (L : ℕ) (hL : L ≤ n) (δ : ℝ)
    (hflat : FlatBox n u L δ) (a b : ℕ)
    (ha : a + 1 < L) (hb : b + 1 < L) :
    ‖(fixed n u (vertex n a b 0,0) : ℍ)-
      (fixed n u (vertex n a (b + 1) 0,0) : ℍ)‖ ≤ δ := by
  have h0 := tree_one n u a b (by omega) (by omega)
  have h1 : fixed n u (spatialStep n (vertex n a b 0) 0,1) = 1 := by
    rw [vertex_step_zero]
    exact tree_one n u (a + 1) b (by omega) (by omega)
  have hs := strip_difference n (fixed n u) (vertex n a b 0) 0 1 h0 h1
  rw [vertex_step_one, holonomy_defect_gauge] at hs
  exact hs.trans_le (hflat a b 0 (by omega) (by omega) (by omega) 0 1 (by decide))

theorem zero_base_bound (u : Slice n) (L : ℕ) (hL : L ≤ n) (δ : ℝ)
    (hflat : FlatBox n u L δ) (a b : ℕ) (ha : a + 1 < L) (hb : b < L) :
    ‖(fixed n u (vertex n a b 0,0) : ℍ)-1‖ ≤ (b : ℝ)*δ := by
  induction b with
  | zero => simp only [fixed, tree_zero n u a (by omega), OneMemClass.coe_one,
      sub_self, norm_zero, Nat.cast_zero, zero_mul, le_refl]
  | succ b ih =>
    have hd := horizontal_zero n u L hL δ hflat a b ha hb
    rw [norm_sub_rev] at hd
    have h := defect_step _ _ δ ((b : ℝ)*δ) hd (ih (by omega))
    simpa only [Nat.cast_succ, add_mul, one_mul] using h

theorem zero_bound (u : Slice n) (L : ℕ) (hL : L ≤ n) (δ : ℝ)
    (hflat : FlatBox n u L δ) (a b c : ℕ)
    (ha : a + 1 < L) (hb : b < L) (hc : c < L) :
    ‖(fixed n u (vertex n a b c,0) : ℍ)-1‖ ≤ ((b : ℝ)+(c : ℝ))*δ := by
  induction c with
  | zero => simpa only [Nat.cast_zero, add_zero] using
      zero_base_bound n u L hL δ hflat a b ha hb
  | succ c ih =>
    have hd := vertical_zero n u L hL δ hflat a b c ha hb hc
    rw [norm_sub_rev] at hd
    have h := defect_step _ _ δ (((b : ℝ)+(c : ℝ))*δ) hd (ih (by omega))
    convert h using 1
    push_cast
    ring

theorem one_bound (u : Slice n) (L : ℕ) (hL : L ≤ n) (δ : ℝ)
    (hflat : FlatBox n u L δ) (a b c : ℕ)
    (ha : a < L) (hb : b + 1 < L) (hc : c < L) :
    ‖(fixed n u (vertex n a b c,1) : ℍ)-1‖ ≤ (c : ℝ)*δ := by
  induction c with
  | zero => simp only [fixed, tree_one n u a b (by omega) (by omega), OneMemClass.coe_one,
      sub_self, norm_zero, Nat.cast_zero, zero_mul, le_refl]
  | succ c ih =>
    have hd := vertical_one n u L hL δ hflat a b c ha hb hc
    rw [norm_sub_rev] at hd
    have h := defect_step _ _ δ ((c : ℝ)*δ) hd (ih (by omega))
    simpa only [Nat.cast_succ, add_mul, one_mul] using h

/-- A uniform interior bound, with the box side retained explicitly. -/
theorem interior_bound (u : Slice n) (L : ℕ) (hL : L ≤ n) (δ : ℝ) (hδ : 0 ≤ δ)
    (hflat : FlatBox n u L δ) (a b c : ℕ)
    (ha : a + 1 < L) (hb : b + 1 < L) (hc : c + 1 < L) (i : Fin 3) :
    ‖(fixed n u (vertex n a b c,i) : ℍ)-1‖ ≤ 2*(L : ℝ)*δ := by
  have hb' : (b : ℝ) ≤ L := by exact_mod_cast (show b ≤ L by omega)
  have hc' : (c : ℝ) ≤ L := by exact_mod_cast (show c ≤ L by omega)
  fin_cases i
  · exact (zero_bound n u L hL δ hflat a b c ha (by omega) (by omega)).trans
      (mul_le_mul_of_nonneg_right (by linarith) hδ)
  · exact (one_bound n u L hL δ hflat a b c (by omega) hb (by omega)).trans
      (mul_le_mul_of_nonneg_right (by have := Nat.cast_nonneg (α := ℝ) L; linarith) hδ)
  · change ‖(gaugeSlice (gauge n u) u (vertex n a b c, 2) : ℍ)-1‖ ≤ _
    rw [tree_two n u a b c (by omega) (by omega) (by omega),
      OneMemClass.coe_one, sub_self, norm_zero]
    positivity

def alignment (u v : Slice n) : SliceGauge n Q := (gauge n u)⁻¹*gauge n v

theorem alignment_fixed (u v : Slice n) :
    gaugeSlice (gauge n u) (gaugeSlice (alignment n u v) v) = fixed n v := by
  rw [← WilsonSlabGauge.gaugeSlice_mul]
  simp only [alignment, mul_inv_cancel_left]

theorem link_chord_gauge (h : SliceGauge n Q) (u v : Slice n)
    (e : SpatialVertex n × Fin 3) :
    ‖(gaugeSlice h u e : ℍ)-(gaugeSlice h v e : ℍ)‖ = ‖(u e : ℍ)-(v e : ℍ)‖ := by
  exact (chord_mul_right _ _ _).trans (chord_mul_left _ _ _)

/-- The relative gauge aligns two fields whose actual plaquette defects are small. -/
theorem alignment_bound (u v : Slice n) (L : ℕ) (hL : L ≤ n) (δ : ℝ) (hδ : 0 ≤ δ)
    (hu : FlatBox n u L δ) (hv : FlatBox n v L δ) (a b c : ℕ)
    (ha : a + 1 < L) (hb : b + 1 < L) (hc : c + 1 < L) (i : Fin 3) :
    ‖(u (vertex n a b c,i) : ℍ)-
      (gaugeSlice (alignment n u v) v (vertex n a b c,i) : ℍ)‖ ≤ 4*(L : ℝ)*δ := by
  rw [← link_chord_gauge n (gauge n u), alignment_fixed]
  have h1 := interior_bound n u L hL δ hδ hu a b c ha hb hc i
  have h2 := interior_bound n v L hL δ hδ hv a b c ha hb hc i
  calc
    _ = ‖((fixed n u (vertex n a b c,i) : ℍ)-1)-
        ((fixed n v (vertex n a b c,i) : ℍ)-1)‖ := by congr 1; abel
    _ ≤ ‖(fixed n u (vertex n a b c,i) : ℍ)-1‖+
        ‖(fixed n v (vertex n a b c,i) : ℍ)-1‖ := norm_sub_le _ _
    _ ≤ _ := by linarith

end
end UnifiedTheory.Clay.YangMills.WilsonAxialRegularity
