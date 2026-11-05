/- Actual spatial-link rotations and quadratic symmetric differences of the
Wilson input action. Constants are independent of the spatial volume. -/
import UnifiedTheory.Clay.YangMills.QuaternionSymmetricChange
import Mathlib.MeasureTheory.Group.Integral

set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace UnifiedTheory.Clay.YangMills.WilsonSymmetricLinkChange
noncomputable section
open MeasureTheory WilsonTimeSlab WilsonSlabOperator QuaternionSymmetricChange
open scoped Quaternion

variable (n : ℕ) [NeZero n]
local instance linkDecidableEq : DecidableEq (SpatialVertex n × Fin 3) := Classical.decEq _
local instance haar_left : (WilsonSlabOperator.measure n).IsMulLeftInvariant := by
  unfold WilsonSlabOperator.measure WilsonSlabGauge.spatialHaar
  infer_instance

def shift (e : SpatialVertex n × Fin 3) (q : Q) (u : Slice n) : Slice n :=
  Function.update (1 : Slice n) e q * u

omit [NeZero n] in
theorem shift_at (e : SpatialVertex n × Fin 3) (q : Q) (u : Slice n) :
    shift n e q u e = q * u e := by simp [shift]

omit [NeZero n] in
theorem shift_away (e : SpatialVertex n × Fin 3) (q : Q) (u : Slice n)
    (j : SpatialVertex n × Fin 3) (hj : j ≠ e) : shift n e q u j = u j := by
  simp [shift, Function.update_of_ne hj]

omit [NeZero n] in
theorem shift_continuous (e : SpatialVertex n × Fin 3) (q : Q) :
    Continuous (shift n e q) := continuous_const.mul continuous_id

theorem shift_integral (e : SpatialVertex n × Fin 3) (q : Q) (F : Slice n → ℝ) :
    (∫ u, F (shift n e q u) ∂WilsonSlabOperator.measure n) =
      ∫ u, F u ∂WilsonSlabOperator.measure n :=
  integral_mul_left_eq_self F (Function.update (1 : Slice n) e q)

omit [NeZero n] in
theorem link_variation (e j : SpatialVertex n × Fin 3) (q : Q) (u : Slice n) :
    Variation (u j) (shift n e q u j) (shift n e q⁻¹ u j) ‖(q : ℍ)-1‖ 1 := by
  by_cases hj : j = e
  · subst j
    simpa only [shift_at] using rotation q (u e)
  · simpa only [shift_away n e q u j hj, shift_away n e q⁻¹ u j hj] using
      same_one (u j) ‖(q : ℍ)-1‖ (norm_nonneg _)

omit [NeZero n] in
theorem holonomy_variation (e : SpatialVertex n × Fin 3) (q : Q) (u : Slice n)
    (x : SpatialVertex n) (i j : Fin 3) :
    Variation (spatialHolonomy u x i j) (spatialHolonomy (shift n e q u) x i j)
      (spatialHolonomy (shift n e q⁻¹ u) x i j) ‖(q : ℍ)-1‖ 4 := by
  have h1 := link_variation n e (x,i) q u
  have h2 := link_variation n e (spatialStep n x i,j) q u
  have h3 := inverse _ _ _ _ _ (link_variation n e (spatialStep n x j,i) q u)
  have h4 := inverse _ _ _ _ _ (link_variation n e (x,j) q u)
  have h12 := product _ _ _ _ _ _ _ 1 1 (norm_nonneg _) (by norm_num) (by norm_num) h1 h2
  have h123 := product _ _ _ _ _ _ _ 2 1 (norm_nonneg _) (by norm_num) (by norm_num)
    (by simpa only [show (1+1 : ℝ)=2 by norm_num] using h12) h3
  have h1234 := product _ _ _ _ _ _ _ 3 1 (norm_nonneg _) (by norm_num) (by norm_num)
    (by simpa only [show (2+1 : ℝ)=3 by norm_num] using h123) h4
  simpa only [spatialHolonomy, show (3+1 : ℝ)=4 by norm_num] using h1234

theorem potential_second_bound (e : SpatialVertex n × Fin 3) (q : Q) (u : Slice n) :
    potential WilsonSingleLinkStaples.character 2 (shift n e q u) +
      potential WilsonSingleLinkStaples.character 2 (shift n e q⁻¹ u) -
      potential WilsonSingleLinkStaples.character 2 u -
      potential WilsonSingleLinkStaples.character 2 u ≤ 128 * ‖(q : ℍ)-1‖^2 := by
  let χ := WilsonSingleLinkStaples.character
  let D : SpatialVertex n × SpatialPlane → ℝ := fun p =>
    (2-(χ (spatialHolonomy (shift n e q u) p.1 p.2.1.1 p.2.1.2)).re) +
    (2-(χ (spatialHolonomy (shift n e q⁻¹ u) p.1 p.2.1.1 p.2.1.2)).re) -
    (2-(χ (spatialHolonomy u p.1 p.2.1.1 p.2.1.2)).re) -
    (2-(χ (spatialHolonomy u p.1 p.2.1.1 p.2.1.2)).re)
  have he : potential χ 2 (shift n e q u) + potential χ 2 (shift n e q⁻¹ u) -
      potential χ 2 u - potential χ 2 u = ∑ p, D p := by
    simp only [D, Fintype.sum_prod_type, Finset.sum_sub_distrib, Finset.sum_add_distrib,
      potential]
  have hz (p : SpatialVertex n × SpatialPlane)
      (hp : p ∉ WilsonSlabLocalComparison.affected n e.1 e.2) : D p = 0 := by
    have hq := WilsonSlabLocalComparison.holonomy_unchanged n Q e.1 e.2 p hp u
      (shift n e q u) (fun j hj => (shift_away n e q u j hj).symm)
    have hqi := WilsonSlabLocalComparison.holonomy_unchanged n Q e.1 e.2 p hp u
      (shift n e q⁻¹ u) (fun j hj => (shift_away n e q⁻¹ u j hj).symm)
    dsimp only [D]
    rw [← hq, ← hqi]
    ring
  have hs : (∑ p, D p) = ∑ p ∈ WilsonSlabLocalComparison.affected n e.1 e.2, D p := by
    symm
    exact Finset.sum_subset (Finset.subset_univ _) (fun p _ hp => hz p hp)
  have hd (p : SpatialVertex n × SpatialPlane) : D p ≤ 32*‖(q : ℍ)-1‖^2 := by
    have h := character_second _ _ _ _ _ (holonomy_variation n e q u p.1 p.2.1.1 p.2.1.2)
    have hh := (abs_le.mp h).1
    dsimp only [D, χ]
    norm_num at hh
    linarith
  change potential χ 2 _ + potential χ 2 _ - potential χ 2 _ - potential χ 2 _ ≤ _
  rw [he, hs]
  calc
    _ ≤ ∑ _p ∈ WilsonSlabLocalComparison.affected n e.1 e.2, 32*‖(q : ℍ)-1‖^2 :=
      Finset.sum_le_sum (fun p _ => hd p)
    _ = ((WilsonSlabLocalComparison.affected n e.1 e.2).card : ℝ) *
        (32*‖(q : ℍ)-1‖^2) := by simp
    _ ≤ _ := by
      have hc : ((WilsonSlabLocalComparison.affected n e.1 e.2).card : ℝ) ≤ 4 :=
        by exact_mod_cast WilsonSlabLocalComparison.affected_card n e.1 e.2
      nlinarith [sq_nonneg ‖(q : ℍ)-1‖]

theorem kinetic_second_bound (e : SpatialVertex n × Fin 3) (q : Q) (u v : Slice n) :
    kineticAction WilsonSingleLinkStaples.character 2 (shift n e q u) v +
      kineticAction WilsonSingleLinkStaples.character 2 (shift n e q⁻¹ u) v -
      kineticAction WilsonSingleLinkStaples.character 2 u v -
      kineticAction WilsonSingleLinkStaples.character 2 u v ≤ 2 * ‖(q : ℍ)-1‖^2 := by
  let χ := WilsonSingleLinkStaples.character
  let D := fun j => (2-(χ ((shift n e q u j)⁻¹*v j)).re) +
    (2-(χ ((shift n e q⁻¹ u j)⁻¹*v j)).re) -
    (2-(χ ((u j)⁻¹*v j)).re) - (2-(χ ((u j)⁻¹*v j)).re)
  have he : kineticAction χ 2 (shift n e q u) v + kineticAction χ 2 (shift n e q⁻¹ u) v -
      kineticAction χ 2 u v - kineticAction χ 2 u v = ∑ j, D j := by
    simp only [kineticAction, D, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  have hs : (∑ j, D j) = D e := by
    apply Finset.sum_eq_single e
    · intro j _ hj
      dsimp only [D]
      rw [shift_away n e q u j hj, shift_away n e q⁻¹ u j hj]
      ring
    · simp
  have h1 := inverse _ _ _ _ _ (rotation q (u e))
  have h2 := product _ _ _ _ _ _ _ 1 0 (norm_nonneg _) (by norm_num) (by norm_num)
    h1 (same (v e) ‖(q : ℍ)-1‖)
  have hh := (abs_le.mp (character_second _ _ _ _ _ h2)).1
  norm_num only [add_zero, one_pow, mul_one] at hh
  change kineticAction χ 2 _ _ + kineticAction χ 2 _ _ -
    kineticAction χ 2 _ _ - kineticAction χ 2 _ _ ≤ _
  rw [he, hs]
  dsimp only [D, χ]
  rw [shift_at, shift_at]
  linarith

/-- Exactly the part of the raw Wilson slab action that depends on its input. -/
def inputAction (β : ℝ) (u v : Slice n) : ℝ :=
  (β/2) * potential WilsonSingleLinkStaples.character 2 u +
    β * kineticAction WilsonSingleLinkStaples.character 2 u v

theorem inputAction_continuous (β : ℝ) :
    Continuous (fun uv : Slice n × Slice n => inputAction n β uv.1 uv.2) := by
  have hc := WilsonSingleLinkStaples.character_continuous
  unfold inputAction potential kineticAction spatialHolonomy
  fun_prop

theorem inputAction_second_bound (β : ℝ) (hβ : 0 ≤ β)
    (e : SpatialVertex n × Fin 3) (q : Q) (u v : Slice n) :
    inputAction n β (shift n e q u) v + inputAction n β (shift n e q⁻¹ u) v -
      inputAction n β u v - inputAction n β u v ≤ 66*β*‖(q : ℍ)-1‖^2 := by
  have hp := mul_le_mul_of_nonneg_left (potential_second_bound n e q u)
    (show 0 ≤ β/2 by positivity)
  have hk := mul_le_mul_of_nonneg_left (kinetic_second_bound n e q u v) hβ
  unfold inputAction
  nlinarith

end
end UnifiedTheory.Clay.YangMills.WilsonSymmetricLinkChange
