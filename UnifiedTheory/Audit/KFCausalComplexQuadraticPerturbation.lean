/- Quantitative bounds for complex bilinear Gaussian quadratics near the
real subspace. These finite-dimensional estimates keep the perturbation
and baseline constants explicit; identifying a physical coordinate map
with these hypotheses is a separate step. -/
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Complex.Exponential

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2000000

namespace UnifiedTheory.Audit.KFCausalComplexQuadraticPerturbation
noncomputable section
open scoped BigOperators
variable {ι : Type*} [Fintype ι]

def mass (z : ι → ℂ) : ℝ := ∑ i, ‖z i‖^2
def bilinear (z v : ι → ℂ) : ℂ := ∑ i, z i*v i
def quadratic (z : ι → ℂ) : ℂ := ∑ i, (z i)^2
def weightedQuadratic (w : ι → ℝ) (z : ι → ℂ) : ℂ := ∑ i, (w i:ℂ)*(z i)^2

theorem mass_nonnegative (z : ι → ℂ) : 0 ≤ mass z :=
  Finset.sum_nonneg (fun _ _ => sq_nonneg _)

theorem bilinear_norm_sq (z v : ι → ℂ) : ‖bilinear z v‖^2 ≤ mass z*mass v := by
  have h₁ : ‖bilinear z v‖ ≤ ∑ i, ‖z i‖*‖v i‖ := by
    simpa only [bilinear,norm_mul] using norm_sum_le Finset.univ (fun i => z i*v i)
  have h₂ := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun i => ‖z i‖) (fun i => ‖v i‖)
  change (∑ i, ‖z i‖*‖v i‖)^2 ≤ mass z*mass v at h₂
  exact (sq_le_sq₀ (norm_nonneg _) (Finset.sum_nonneg (fun _ _ => mul_nonneg (norm_nonneg _) (norm_nonneg _)))).mpr h₁ |>.trans h₂

theorem quadratic_norm (z : ι → ℂ) : ‖quadratic z‖ ≤ mass z := by
  have h : ‖∑ i, (z i)^2‖ ≤ ∑ i, ‖(z i)^2‖ := norm_sum_le Finset.univ (fun i => (z i)^2)
  simpa only [quadratic,mass,norm_pow] using h

theorem quadratic_expansion (z v : ι → ℂ) :
    quadratic (z+v) = quadratic z+2*bilinear z v+quadratic v := by
  simp only [quadratic,bilinear,Pi.add_apply,Finset.mul_sum,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem real_quadratic (x : ι → ℂ) (hx : ∀ i, (x i).im=0) : (quadratic x).re=mass x := by
  simp only [quadratic,mass,Complex.re_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [Complex.sq_norm]
  simp [pow_two,Complex.mul_re,Complex.normSq_apply,hx]

theorem perturbation_lower (x z : ι → ℂ) (hx : ∀ i, (x i).im=0)
    (ρ : ℝ) (hρ : 0 ≤ ρ) (he : mass (z-x) ≤ ρ^2*mass x) :
    (1-2*ρ-ρ^2)*mass x ≤ (quadratic z).re := by
  have hm := mass_nonnegative x
  have hb := bilinear_norm_sq x (z-x)
  have hmul := mul_le_mul_of_nonneg_left he hm
  have hbn : ‖bilinear x (z-x)‖ ≤ ρ*mass x := by
    nlinarith [norm_nonneg (bilinear x (z-x)),mul_nonneg hρ hm]
  have hbre := (abs_le.mp (Complex.abs_re_le_norm (bilinear x (z-x)))).1
  have hq := quadratic_norm (z-x)
  have hqre := (abs_le.mp (Complex.abs_re_le_norm (quadratic (z-x)))).1
  have heq := quadratic_expansion x (z-x)
  rw [add_sub_cancel] at heq
  have hre := congrArg Complex.re heq
  norm_num [Complex.add_re,Complex.mul_re,real_quadratic x hx] at hre
  nlinarith

theorem baseline_upper (w : ι → ℝ) (v : ι → ℂ) (hw : ∀ i, 0 ≤ w i ∧ w i ≤ 1/4) :
    (weightedQuadratic w v).re ≤ mass v/4 := by
  simp only [weightedQuadratic,Complex.re_sum,mass,Finset.sum_div]
  apply Finset.sum_le_sum
  intro i _
  have hq := (Complex.re_le_norm ((v i)^2)).trans_eq (norm_pow _ 2)
  have hm := mul_le_mul_of_nonneg_left hq (hw i).1
  simp only [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]
  nlinarith [(mul_le_mul_of_nonneg_right (hw i).2 (sq_nonneg ‖v i‖))]

theorem difference_coercive (w : ι → ℝ) (x z v : ι → ℂ)
    (hx : ∀ i, (x i).im=0) (hw : ∀ i, 0 ≤ w i ∧ w i ≤ 1/4)
    (hz : mass (z-x) ≤ (3/17:ℝ)^2*mass x) (hv : mass v ≤ (20/17:ℝ)^2*mass x) :
    (78/289:ℝ)*mass x ≤ (quadratic z-weightedQuadratic w v).re := by
  have h₁ := perturbation_lower x z hx (3/17) (by norm_num) hz
  have h₂ := baseline_upper w v hw
  rw [Complex.sub_re]
  nlinarith

theorem gaussian_difference_bound (w : ι → ℝ) (x z v : ι → ℂ)
    (hx : ∀ i, (x i).im=0) (hw : ∀ i, 0 ≤ w i ∧ w i ≤ 1/4)
    (hz : mass (z-x) ≤ (3/17:ℝ)^2*mass x) (hv : mass v ≤ (20/17:ℝ)^2*mass x) :
    ‖Complex.exp (-quadratic z+weightedQuadratic w v)‖ ≤ Real.exp (-(78/289:ℝ)*mass x) := by
  rw [Complex.norm_exp]
  apply Real.exp_le_exp.mpr
  have h := difference_coercive w x z v hx hw hz hv
  simp only [Complex.add_re,Complex.neg_re,Complex.sub_re] at h ⊢
  linarith

#print axioms mass_nonnegative
#print axioms bilinear_norm_sq
#print axioms quadratic_norm
#print axioms quadratic_expansion
#print axioms real_quadratic
#print axioms perturbation_lower
#print axioms baseline_upper
#print axioms difference_coercive
#print axioms gaussian_difference_bound
end
end UnifiedTheory.Audit.KFCausalComplexQuadraticPerturbation
