/- Simultaneous link rotations have an action second-difference budget in
squared l2 displacement. Incidence counting keeps the constant independent
of the number of rotated links and of the spatial volume. -/
import UnifiedTheory.Clay.YangMills.WilsonGroundPeak

set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace UnifiedTheory.Clay.YangMills.WilsonJointRotation
noncomputable section
open MeasureTheory WilsonTimeSlab WilsonSlabOperator QuaternionSymmetricChange
open WilsonSymmetricLinkChange
open scoped Quaternion

variable (n : ℕ) [NeZero n]

omit [NeZero n] in
def displacement (q : Slice n) (e : SpatialVertex n × Fin 3) : ℝ := ‖(q e : ℍ)-1‖

def cost (q : Slice n) : ℝ := ∑ e, (displacement n q e)^2

theorem cost_nonneg (q : Slice n) : 0 ≤ cost n q :=
  Finset.sum_nonneg (fun _e _ => sq_nonneg _)

omit n [NeZero n] in
theorem rotation_unit_scale (q a : Q) :
    Variation a (q*a) (q⁻¹*a) 1 ‖(q : ℍ)-1‖ := by
  simpa only [Variation, one_mul, mul_one, one_pow] using rotation q a

omit n [NeZero n] in
theorem square_four_bound (a b c d : ℝ) :
    (a+b+c+d)^2 ≤ 4*(a^2+b^2+c^2+d^2) := by
  nlinarith [sq_nonneg (a-b), sq_nonneg (a-c), sq_nonneg (a-d),
    sq_nonneg (b-c), sq_nonneg (b-d), sq_nonneg (c-d)]

omit n [NeZero n] in
theorem plane_sum (f : Fin 3 → ℝ) :
    (∑ p : SpatialPlane, (f p.1.1+f p.1.2)) = 2*∑ i, f i := by
  rw [← Finset.sum_subtype (Finset.univ.filter (fun p : Fin 3 × Fin 3 => p.1 < p.2))
    (by intro p; simp) (fun p => f p.1+f p.2)]
  simp [Finset.sum_filter, Fintype.sum_prod_type, Fin.sum_univ_three]
  ring

theorem step_sum (f : SpatialVertex n → ℝ) (i : Fin 3) :
    (∑ x, f (spatialStep n x i)) = ∑ x, f x :=
  Equiv.sum_comp (Equiv.addRight (Pi.single i 1)) f

/-- Each spatial link occurs four times among the oriented plaquette words. -/
theorem incidence_sum (q : Slice n) :
    (∑ x : SpatialVertex n, ∑ p : SpatialPlane,
      ((displacement n q (x,p.1.1))^2 +
        (displacement n q (spatialStep n x p.1.1,p.1.2))^2 +
        (displacement n q (spatialStep n x p.1.2,p.1.1))^2 +
        (displacement n q (x,p.1.2))^2)) = 4*cost n q := by
  rw [Finset.sum_comm]
  have he (p : SpatialPlane) :
      (∑ x : SpatialVertex n, ((displacement n q (x,p.1.1))^2 +
        (displacement n q (spatialStep n x p.1.1,p.1.2))^2 +
        (displacement n q (spatialStep n x p.1.2,p.1.1))^2 +
        (displacement n q (x,p.1.2))^2)) =
        2*∑ x : SpatialVertex n,
          ((displacement n q (x,p.1.1))^2+(displacement n q (x,p.1.2))^2) := by
    simp only [Finset.sum_add_distrib]
    rw [step_sum n (fun x => (displacement n q (x,p.1.2))^2),
      step_sum n (fun x => (displacement n q (x,p.1.1))^2)]
    ring
  simp_rw [he]
  rw [← Finset.mul_sum, Finset.sum_comm]
  have hp (x : SpatialVertex n) := plane_sum (fun i => (displacement n q (x,i))^2)
  simp_rw [hp]
  rw [← Finset.mul_sum]
  unfold cost
  rw [Fintype.sum_prod_type]
  ring

omit [NeZero n] in
theorem holonomy_variation (q u : Slice n) (x : SpatialVertex n) (i j : Fin 3) :
    Variation (spatialHolonomy u x i j) (spatialHolonomy (q*u) x i j)
      (spatialHolonomy (q⁻¹*u) x i j) 1
      (displacement n q (x,i)+displacement n q (spatialStep n x i,j)+
        displacement n q (spatialStep n x j,i)+displacement n q (x,j)) := by
  have h1 := rotation_unit_scale (q (x,i)) (u (x,i))
  have h2 := rotation_unit_scale (q (spatialStep n x i,j)) (u (spatialStep n x i,j))
  have h3 := inverse _ _ _ _ _
    (rotation_unit_scale (q (spatialStep n x j,i)) (u (spatialStep n x j,i)))
  have h4 := inverse _ _ _ _ _ (rotation_unit_scale (q (x,j)) (u (x,j)))
  have h12 := product _ _ _ _ _ _ _ _ _ (by norm_num : (0 : ℝ) ≤ 1)
    (norm_nonneg _) (norm_nonneg _) h1 h2
  have h123 := product _ _ _ _ _ _ _ _ _ (by norm_num : (0 : ℝ) ≤ 1)
    (add_nonneg (norm_nonneg _) (norm_nonneg _)) (norm_nonneg _) h12 h3
  exact product _ _ _ _ _ _ _ _ _ (by norm_num : (0 : ℝ) ≤ 1)
    (add_nonneg (add_nonneg (norm_nonneg _) (norm_nonneg _)) (norm_nonneg _))
    (norm_nonneg _) h123 h4

/-- The constant is independent of how many links are rotated. -/
theorem potential_second_bound (q u : Slice n) :
    potential WilsonSingleLinkStaples.character 2 (q*u) +
      potential WilsonSingleLinkStaples.character 2 (q⁻¹*u) -
      potential WilsonSingleLinkStaples.character 2 u -
      potential WilsonSingleLinkStaples.character 2 u ≤ 32*cost n q := by
  let χ := WilsonSingleLinkStaples.character
  have h (x : SpatialVertex n) (p : SpatialPlane) :
      (2-(χ (spatialHolonomy (q*u) x p.1.1 p.1.2)).re) +
      (2-(χ (spatialHolonomy (q⁻¹*u) x p.1.1 p.1.2)).re) -
      (2-(χ (spatialHolonomy u x p.1.1 p.1.2)).re) -
      (2-(χ (spatialHolonomy u x p.1.1 p.1.2)).re) ≤
      8*((displacement n q (x,p.1.1))^2 +
        (displacement n q (spatialStep n x p.1.1,p.1.2))^2 +
        (displacement n q (spatialStep n x p.1.2,p.1.1))^2 +
        (displacement n q (x,p.1.2))^2) := by
    have hh := (abs_le.mp (character_second _ _ _ _ _
      (holonomy_variation n q u x p.1.1 p.1.2))).1
    have hs := square_four_bound (displacement n q (x,p.1.1))
      (displacement n q (spatialStep n x p.1.1,p.1.2))
      (displacement n q (spatialStep n x p.1.2,p.1.1)) (displacement n q (x,p.1.2))
    simp only [one_pow, mul_one] at hh
    dsimp only [χ]
    nlinarith
  let D := fun (x : SpatialVertex n) (p : SpatialPlane) =>
    (displacement n q (x,p.1.1))^2 +
      (displacement n q (spatialStep n x p.1.1,p.1.2))^2 +
      (displacement n q (spatialStep n x p.1.2,p.1.1))^2 +
      (displacement n q (x,p.1.2))^2
  have hs := Finset.sum_le_sum (fun x (_ : x ∈ Finset.univ) =>
    Finset.sum_le_sum (fun p (_ : p ∈ Finset.univ) => h x p))
  have hm (x : SpatialVertex n) : (∑ p, (8 : ℝ)*D x p) = 8*∑ p, D x p :=
    (Finset.mul_sum Finset.univ (D x) 8).symm
  change _ ≤ ∑ x, ∑ p, (8 : ℝ)*D x p at hs
  simp_rw [hm] at hs
  rw [← Finset.mul_sum] at hs
  have hi : (∑ x, ∑ p, D x p) = 4*cost n q := incidence_sum n q
  rw [hi] at hs
  simp only [χ, Finset.sum_sub_distrib, Finset.sum_add_distrib] at hs
  simp only [potential, Finset.sum_sub_distrib]
  nlinarith

theorem kinetic_second_bound (q u v : Slice n) :
    kineticAction WilsonSingleLinkStaples.character 2 (q*u) v +
      kineticAction WilsonSingleLinkStaples.character 2 (q⁻¹*u) v -
      kineticAction WilsonSingleLinkStaples.character 2 u v -
      kineticAction WilsonSingleLinkStaples.character 2 u v ≤ 2*cost n q := by
  have h (e : SpatialVertex n × Fin 3) :
      (2-(WilsonSingleLinkStaples.character (((q*u) e)⁻¹*v e)).re) +
      (2-(WilsonSingleLinkStaples.character (((q⁻¹*u) e)⁻¹*v e)).re) -
      (2-(WilsonSingleLinkStaples.character ((u e)⁻¹*v e)).re) -
      (2-(WilsonSingleLinkStaples.character ((u e)⁻¹*v e)).re) ≤
      2*(displacement n q e)^2 := by
    have hi := inverse _ _ _ _ _ (rotation_unit_scale (q e) (u e))
    have hp := product _ _ _ _ _ _ _ _ _ (by norm_num : (0 : ℝ) ≤ 1)
      (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 0) hi (same (v e) 1)
    have hh := (abs_le.mp (character_second _ _ _ _ _ hp)).1
    simp only [add_zero, one_pow, mul_one] at hh
    change _ ≤ 2*‖(q e : ℍ)-1‖^2
    simp only [Pi.mul_apply, Pi.inv_apply]
    linarith
  have hs := Finset.sum_le_sum (fun e (_ : e ∈ Finset.univ) => h e)
  simpa only [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum,
    kineticAction, cost] using hs

theorem inputAction_second_bound (β : ℝ) (hβ : 0 ≤ β) (q u v : Slice n) :
    inputAction n β (q*u) v + inputAction n β (q⁻¹*u) v -
      inputAction n β u v - inputAction n β u v ≤ 18*β*cost n q := by
  have hp := mul_le_mul_of_nonneg_left (potential_second_bound n q u)
    (show 0 ≤ β/2 by positivity)
  have hk := mul_le_mul_of_nonneg_left (kinetic_second_bound n q u v) hβ
  unfold inputAction
  nlinarith

end
end UnifiedTheory.Clay.YangMills.WilsonJointRotation
