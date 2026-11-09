/- A supported gauge witness turns low spatial curvature and high local
temporal mismatch into the already normalized block-instability event. -/
import UnifiedTheory.Clay.YangMills.WilsonAxialBox
import UnifiedTheory.Clay.YangMills.WilsonGaugeBlockTail

set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace UnifiedTheory.Clay.YangMills.WilsonAxialAlignment
noncomputable section
open WilsonTimeSlab WilsonSlabOperator WilsonAxialGauge WilsonAxialRegularity WilsonAxialBox
open WilsonSingleLinkStaples (character)
open scoped Quaternion

variable (n : ℕ) [NeZero n]

theorem vertex_values (x : SpatialVertex n) :
    vertex n (x 0).val (x 1).val (x 2).val = x := by
  funext i
  fin_cases i <;> simp [vertex]

def parameters (L : ℕ) (u v : Slice n) : WilsonGaugeBlock.Parameters n (block n L) :=
  fun x => alignment n u v x

def rotated (L : ℕ) (u v : Slice n) : Slice n :=
  WilsonGaugeBlock.rotate n (block n L) (parameters n L u v) v

theorem rotated_outside (L : ℕ) (u v : Slice n) (e : SpatialVertex n × Fin 3)
    (he : e ∉ touched n L) : rotated n L u v e = v e := by
  have hs : e.1 ∉ block n L := fun h => he (Finset.mem_filter.mpr ⟨Finset.mem_univ _, Or.inl h⟩)
  have ht : spatialStep n e.1 e.2 ∉ block n L :=
    fun h => he (Finset.mem_filter.mpr ⟨Finset.mem_univ _, Or.inr h⟩)
  simp [rotated, WilsonGaugeBlock.rotate, gaugeSlice, WilsonGaugeBlock.gauge, hs, ht]

omit n [NeZero n] in
theorem chord_le_two (a b : Q) : ‖(a : ℍ)-(b : ℍ)‖ ≤ 2 := by
  have h := norm_sub_le (a : ℍ) (b : ℍ)
  simpa only [QuaternionSymmetricChange.unit_norm, show (1 : ℝ)+1 = 2 by norm_num] using h

variable [Fact (1 < n)]

theorem rotated_core (L : ℕ) (hL : L + 1 ≤ n) (u v : Slice n)
    (e : SpatialVertex n × Fin 3) (he : e ∈ core n L) :
    rotated n L u v e = gaugeSlice (alignment n u v) v e := by
  have hs := core_source n L hL e he
  have ht := core_target n L hL e he
  simp only [rotated, WilsonGaugeBlock.rotate, gaugeSlice, WilsonGaugeBlock.gauge,
    dif_pos hs, dif_pos ht, parameters]

set_option maxHeartbeats 800000 in
-- Specializing the coordinate-tree bound to actual box links exceeds the default elaboration budget.
theorem rotated_core_bound (L : ℕ) (hL : L + 1 ≤ n) (u v : Slice n) (δ : ℝ) (hδ : 0 ≤ δ)
    (hu : FlatBox n u (L + 1) δ) (hv : FlatBox n v (L + 1) δ)
    (e : SpatialVertex n × Fin 3) (he : e ∈ core n L) :
    ‖(u e : ℍ)-(rotated n L u v e : ℍ)‖ ≤ 4*((L : ℝ)+1)*δ := by
  rw [rotated_core n L hL u v e he]
  have hx := (mem_vertices n 1 L (by omega) e.1).mp (Finset.mem_product.mp he).1
  have h := alignment_bound n u v (L + 1) hL δ hδ hu hv
    (e.1 0).val (e.1 1).val (e.1 2).val
    (by have := hx 0; omega) (by have := hx 1; omega) (by have := hx 2; omega) e.2
  rw [vertex_values n e.1] at h
  simpa only [Nat.cast_add, Nat.cast_one] using h

omit [Fact (1 < n)] in
def energy (L : ℕ) (u v : Slice n) : ℝ :=
  ∑ e ∈ touched n L, ‖(u e : ℍ)-(v e : ℍ)‖^2

omit [Fact (1 < n)] in
theorem kinetic_eq_sum (u v : Slice n) :
    kineticAction character 2 u v = ∑ e, ‖(u e : ℍ)-(v e : ℍ)‖^2 := by
  unfold kineticAction
  simp only [QuaternionDefectCurvature.relative_character, sub_sub_cancel]

omit [Fact (1 < n)] in
theorem action_decrease (L : ℕ) (u v : Slice n) :
    kineticAction character 2 u v-kineticAction character 2 u (rotated n L u v) =
      energy n L u v-energy n L u (rotated n L u v) := by
  rw [kinetic_eq_sum, kinetic_eq_sum, ← Finset.sum_sub_distrib]
  have hs := Finset.sum_subset (Finset.subset_univ (touched n L))
    (f := fun e => ‖(u e : ℍ)-(v e : ℍ)‖^2-‖(u e : ℍ)-(rotated n L u v e : ℍ)‖^2)
    (fun e _ he => by dsimp only; rw [rotated_outside n L u v e he]; ring)
  rw [← hs, Finset.sum_sub_distrib]
  rfl

omit n [NeZero n] [Fact (1 < n)] in
def budget (L : ℕ) (δ : ℝ) : ℝ := 48*((L : ℝ)+1)^5*δ^2+96*(L : ℝ)^2

/-- The supported witness pays only a surface term and a curvature term. -/
theorem rotated_energy (L : ℕ) (hpos : 0 < L) (hL : L + 1 ≤ n)
    (u v : Slice n) (δ : ℝ) (hδ : 0 ≤ δ)
    (hu : FlatBox n u (L + 1) δ) (hv : FlatBox n v (L + 1) δ) :
    energy n L u (rotated n L u v) ≤ budget L δ := by
  let E := fun e : SpatialVertex n × Fin 3 => ‖(u e : ℍ)-(rotated n L u v e : ℍ)‖^2
  have hext : energy n L u (rotated n L u v) ≤ ∑ e ∈ outer n L, E e :=
    Finset.sum_le_sum_of_subset_of_nonneg (touched_subset_outer n L hL)
      (fun _ _ _ => sq_nonneg _)
  have hcore : (∑ e ∈ core n L, E e) ≤
      ((core n L).card : ℝ)*(16*((L : ℝ)+1)^2*δ^2) := by
    calc
      _ ≤ ∑ _e ∈ core n L, 16*((L : ℝ)+1)^2*δ^2 := by
        apply Finset.sum_le_sum
        intro e he
        dsimp only [E]
        have h := rotated_core_bound n L hL u v δ hδ hu hv e he
        have hn := norm_nonneg ((u e : ℍ)-(rotated n L u v e : ℍ))
        nlinarith [mul_nonneg (sub_nonneg.mpr h)
          (show 0 ≤ 4*((L : ℝ)+1)*δ+‖(u e : ℍ)-(rotated n L u v e : ℍ)‖ by positivity)]
      _ = _ := by simp only [Finset.sum_const, nsmul_eq_mul]
  have hshell : (∑ e ∈ outer n L \ core n L, E e) ≤
      ((outer n L \ core n L).card : ℝ)*4 := by
    calc
      _ ≤ ∑ _e ∈ outer n L \ core n L, (4 : ℝ) := by
        apply Finset.sum_le_sum
        intro e _
        dsimp only [E]
        have h := chord_le_two (u e) (rotated n L u v e)
        nlinarith [norm_nonneg ((u e : ℍ)-(rotated n L u v e : ℍ))]
      _ = _ := by simp only [Finset.sum_const, nsmul_eq_mul]
  have hc : ((core n L).card : ℝ) ≤ 3*((L : ℝ)+1)^3 := by
    have h := Finset.card_le_card (core_subset_outer n L hL)
    have ho : (outer n L).card = (L + 1)^3*3 := by
      simp [outer, Finset.card_product, vertices_card n 0 (L + 1) hL]
    rw [ho] at h
    exact_mod_cast (by simpa only [mul_comm] using h)
  have hmul := mul_le_mul_of_nonneg_right hc
    (show 0 ≤ 16*((L : ℝ)+1)^2*δ^2 by positivity)
  have hs := mul_le_mul_of_nonneg_right (shell_surface n L hpos hL)
    (show (0 : ℝ) ≤ 4 by norm_num)
  have hsum := Finset.sum_sdiff (core_subset_outer n L hL) (f := E)
  unfold budget
  nlinarith [hext, hcore, hshell, hsum, hmul, hs]

/-- A concrete low-curvature/high-mismatch event is a block-instability event. -/
theorem bad_of_energy (L : ℕ) (hpos : 0 < L) (hL : L + 1 ≤ n)
    (u v : Slice n) (δ t : ℝ) (hδ : 0 ≤ δ)
    (hu : FlatBox n u (L + 1) δ) (hv : FlatBox n v (L + 1) δ)
    (he : budget L δ + t < energy n L u v) :
    (u, v) ∈ WilsonGaugeBlockTail.bad n (block n L) t := by
  refine ⟨parameters n L u v, ?_⟩
  change t < kineticAction character 2 u v-kineticAction character 2 u (rotated n L u v)
  rw [action_decrease]
  have h := rotated_energy n L hpos hL u v δ hδ hu hv
  linarith

omit n [NeZero n] [Fact (1 < n)] in
/-- Explicit scales make the curvature and surface costs smaller than the
chosen extensive mismatch allowance. Constants are deliberately conservative. -/
theorem budget_small (L : ℕ) (hL : 4096 ≤ L) (δ : ℝ) (hδ : 0 ≤ δ)
    (hd : δ ≤ 1 / (100 * ((L : ℝ) + 1))) : budget L δ ≤ (L : ℝ)^3/16 := by
  have hl : (4096 : ℝ) ≤ L := by exact_mod_cast hL
  have hp : 0 < 100*((L : ℝ)+1) := by positivity
  have hm : δ*(100*((L : ℝ)+1)) ≤ 1 := (le_div_iff₀ hp).mp hd
  have h0 : 0 ≤ δ*(100*((L : ℝ)+1)) := mul_nonneg hδ hp.le
  have hs : ((L : ℝ)+1)^2*δ^2 ≤ 1/10000 := by nlinarith [sq_nonneg (1-δ*(100*((L : ℝ)+1)))]
  have hc : ((L : ℝ)+1)^3 ≤ 8*(L : ℝ)^3 := by
    have h := pow_le_pow_left₀ (show 0 ≤ (L : ℝ)+1 by positivity)
      (show (L : ℝ)+1 ≤ 2*(L : ℝ) by linarith) 3
    nlinarith [h]
  have hcurv := mul_le_mul_of_nonneg_left hs
    (show 0 ≤ 48*((L : ℝ)+1)^3 by positivity)
  have hsurf := mul_le_mul_of_nonneg_right hl (sq_nonneg (L : ℝ))
  unfold budget
  nlinarith [hcurv, hsurf, pow_nonneg (show 0 ≤ (L : ℝ) by positivity) 3]

end
end UnifiedTheory.Clay.YangMills.WilsonAxialAlignment
