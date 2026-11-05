/- One renormalization step for a Gaussian weight, done exactly. For the block quadratic form
`Q(x, y) = xᵀAx + 2 xᵀBy + yᵀDy` of `TwistedSchurStep`, integrating out the fine variables `x` gives
`∫ e^{−Q(x,y)} dx = e^{−yᵀSy} ∫ e^{−xᵀAx} dx`, with `S = D − BᵀA⁻¹B` the Schur complement. So the coarse
effective action `U(y) = −log ∫ e^{−Q(x,y)} dx` is `yᵀSy` plus a constant, and its Hessian is exactly
`2S`. If the full form is uniformly coercive, `Q(x,y) ≥ c (|x|² + |y|²)` with `c > 0`, then the
normalizing integral is finite and positive and `S ≥ c`: the step preserves the uniform Hessian lower
bound. This is the small-field (quadratic) case of the Brascamp-Lieb step of the README section "One RG
step as a Schur complement", where Brascamp-Lieb holds with equality. The non-Gaussian step (a convex
non-quadratic action, which needs Prékopa's theorem) and the large-field region are not covered. -/
import UnifiedTheory.Clay.YangMills.Twisted.TwistedSchurStep

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Clay.YangMills.Twisted.TwistedGaussianStep

open Matrix MeasureTheory Real
open UnifiedTheory.Clay.YangMills.Twisted.TwistedSchurStep

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m]

/-- **Integrating out the fine variables.** For symmetric invertible `A`,
`∫ e^{−Q(x,y)} dx = e^{−yᵀSy} ∫ e^{−xᵀAx} dx`. (Both sides are `0` if the integral diverges.) -/
theorem gaussian_marginal (A : Matrix m m ℝ) (B : Matrix m n ℝ) (D : Matrix n n ℝ)
    (hA : Aᵀ = A) (hdet : IsUnit A.det) (y : n → ℝ) :
    ∫ x, exp (-Q A B D x y) = exp (-(y ⬝ᵥ (schur A B D *ᵥ y))) * ∫ x, exp (-(x ⬝ᵥ (A *ᵥ x))) := by
  have h : (fun x => exp (-Q A B D x y)) = fun x =>
      exp (-(y ⬝ᵥ (schur A B D *ᵥ y))) *
        (fun z => exp (-(z ⬝ᵥ (A *ᵥ z)))) (x - argmin A B y) := by
    funext x
    rw [complete_square A B D hA hdet x y, ← exp_add]
    ring_nf
  rw [h, integral_const_mul, integral_sub_right_eq_self (fun z => exp (-(z ⬝ᵥ (A *ᵥ z))))]

omit [DecidableEq m] in
/-- A uniformly coercive fine block gives an integrable Gaussian weight. -/
theorem gaussian_integrable (A : Matrix m m ℝ) (c : ℝ) (hc : 0 < c)
    (hcoer : ∀ x : m → ℝ, c * (x ⬝ᵥ x) ≤ x ⬝ᵥ (A *ᵥ x)) :
    Integrable (fun x : m → ℝ => exp (-(x ⬝ᵥ (A *ᵥ x)))) := by
  have hprod : Integrable (fun x : m → ℝ => ∏ i, exp (-c * x i ^ 2))
      (Measure.pi fun _ => volume) :=
    Integrable.fintype_prod (f := fun _ t => exp (-c * t ^ 2)) fun _ => integrable_exp_neg_mul_sq hc
  rw [← volume_pi] at hprod
  refine hprod.mono' (by fun_prop) (Filter.Eventually.of_forall fun x => ?_)
  rw [Real.norm_eq_abs, abs_of_pos (exp_pos _), ← exp_sum, exp_le_exp]
  have hsum : ∑ i, -c * x i ^ 2 = -(c * (x ⬝ᵥ x)) := by
    simp only [dotProduct, Finset.mul_sum, ← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [hsum]
  linarith [hcoer x]

omit [DecidableEq m] in
/-- The Gaussian normalization is positive. -/
theorem gaussian_Z_pos (A : Matrix m m ℝ) (c : ℝ) (hc : 0 < c)
    (hcoer : ∀ x : m → ℝ, c * (x ⬝ᵥ x) ≤ x ⬝ᵥ (A *ᵥ x)) :
    0 < ∫ x : m → ℝ, exp (-(x ⬝ᵥ (A *ᵥ x))) :=
  integral_exp_pos (gaussian_integrable A c hc hcoer)

/-- A coercive block is invertible. -/
theorem isUnit_det_of_coercive (A : Matrix m m ℝ) (c : ℝ) (hc : 0 < c)
    (hcoer : ∀ x : m → ℝ, c * (x ⬝ᵥ x) ≤ x ⬝ᵥ (A *ᵥ x)) : IsUnit A.det := by
  rw [isUnit_iff_ne_zero]
  intro h0
  obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr h0
  have h1 := hcoer v
  rw [hv, dotProduct_zero] at h1
  have h2 : v ⬝ᵥ v = 0 := le_antisymm (nonpos_of_mul_nonpos_right h1 hc) (by
    simp only [dotProduct]; exact Finset.sum_nonneg fun i _ => mul_self_nonneg _)
  exact hv0 (dotProduct_self_eq_zero.mp h2)

/-- **The Schur complement inherits the lower bound.** If `Q(x, y) ≥ c (|x|² + |y|²)` then
`yᵀSy ≥ c |y|²`. -/
theorem schur_coercive (A : Matrix m m ℝ) (B : Matrix m n ℝ) (D : Matrix n n ℝ)
    (hA : Aᵀ = A) (hdet : IsUnit A.det) (c : ℝ) (hc : 0 ≤ c)
    (hQ : ∀ x y, c * (x ⬝ᵥ x + y ⬝ᵥ y) ≤ Q A B D x y) (y : n → ℝ) :
    c * (y ⬝ᵥ y) ≤ y ⬝ᵥ (schur A B D *ᵥ y) := by
  rw [← schur_attained A B D hA hdet y]
  have h := hQ (argmin A B y) y
  have hxx : 0 ≤ argmin A B y ⬝ᵥ argmin A B y := by
    simp only [dotProduct]; exact Finset.sum_nonneg fun i _ => mul_self_nonneg _
  nlinarith only [h, hxx, hc]

/-- The coarse effective action after integrating out the fine variables. -/
noncomputable def Ueff (A : Matrix m m ℝ) (B : Matrix m n ℝ) (D : Matrix n n ℝ) (y : n → ℝ) : ℝ :=
  -Real.log (∫ x, exp (-Q A B D x y))

/-- **The effective action is the Schur quadratic form plus a constant.** -/
theorem Ueff_eq (A : Matrix m m ℝ) (B : Matrix m n ℝ) (D : Matrix n n ℝ)
    (hA : Aᵀ = A) (c : ℝ) (hc : 0 < c) (hcoer : ∀ x : m → ℝ, c * (x ⬝ᵥ x) ≤ x ⬝ᵥ (A *ᵥ x))
    (y : n → ℝ) :
    Ueff A B D y = y ⬝ᵥ (schur A B D *ᵥ y) - Real.log (∫ x, exp (-(x ⬝ᵥ (A *ᵥ x)))) := by
  rw [Ueff, gaussian_marginal A B D hA (isUnit_det_of_coercive A c hc hcoer) y,
    Real.log_mul (exp_pos _).ne' (gaussian_Z_pos A c hc hcoer).ne', Real.log_exp]
  ring

/-- **Exact Hessian of the coarse action.** `U(y+h) + U(y−h) − 2U(y) = 2 hᵀSh`. -/
theorem Ueff_second_diff (A : Matrix m m ℝ) (B : Matrix m n ℝ) (D : Matrix n n ℝ)
    (hA : Aᵀ = A) (c : ℝ) (hc : 0 < c) (hcoer : ∀ x : m → ℝ, c * (x ⬝ᵥ x) ≤ x ⬝ᵥ (A *ᵥ x))
    (y h : n → ℝ) :
    Ueff A B D (y + h) + Ueff A B D (y - h) - 2 * Ueff A B D y =
      2 * (h ⬝ᵥ (schur A B D *ᵥ h)) := by
  simp only [Ueff_eq A B D hA c hc hcoer, mulVec_add, mulVec_sub, dotProduct_add, dotProduct_sub,
    add_dotProduct, sub_dotProduct]
  ring

omit [DecidableEq m] in
/-- **One Gaussian RG step preserves the uniform Hessian lower bound.** If the fine-plus-coarse form
satisfies `Q(x, y) ≥ c (|x|² + |y|²)` with `c > 0`, the coarse effective action is finite and its
second differences satisfy `U(y+h) + U(y−h) − 2U(y) ≥ 2c |h|²`, the same bound in the coarse
variables. -/
theorem gaussian_rg_step (A : Matrix m m ℝ) (B : Matrix m n ℝ) (D : Matrix n n ℝ)
    (hA : Aᵀ = A) (c : ℝ) (hc : 0 < c) (hQ : ∀ x y, c * (x ⬝ᵥ x + y ⬝ᵥ y) ≤ Q A B D x y) :
    (0 < ∫ x : m → ℝ, exp (-(x ⬝ᵥ (A *ᵥ x)))) ∧
      ∀ y h : n → ℝ,
        2 * c * (h ⬝ᵥ h) ≤ Ueff A B D (y + h) + Ueff A B D (y - h) - 2 * Ueff A B D y := by
  classical
  have hcoer : ∀ x : m → ℝ, c * (x ⬝ᵥ x) ≤ x ⬝ᵥ (A *ᵥ x) := by
    intro x
    have := hQ x 0
    simpa [Q] using this
  refine ⟨gaussian_Z_pos A c hc hcoer, fun y h => ?_⟩
  rw [Ueff_second_diff A B D hA c hc hcoer]
  have := schur_coercive A B D hA (isUnit_det_of_coercive A c hc hcoer) c hc.le hQ h
  linarith

end UnifiedTheory.Clay.YangMills.Twisted.TwistedGaussianStep
