/- Actual real-translation derivatives of correlated charged Gaussian kernels. -/
import UnifiedTheory.Audit.KFCausalChargedCoolingFixedV
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.Calculus.Deriv.Star

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalChargedCoolingDerivative
noncomputable section
open Matrix
open scoped Topology BigOperators ComplexOrder
open KFCausalChargedCoolingWidthPositive KFCausalChargedCoolingFixedV

def kernel (p : ℂ) (w z v : ℝ) : ℂ :=
  Complex.exp (-widthSum p w z*(v^2:ℝ))/
    (widthSum p w z ^ (1/2:ℂ)*widthSum (starRingEnd ℂ p) w z)

theorem widthSum_derivative {f : ℝ → ℂ} {f' : ℂ} {x : ℝ}
    (hf : HasDerivAt f f' x) (w z : ℝ) :
    HasDerivAt (fun t => widthSum (f t) w z) (widthSum f' w z) x := by
  simpa only [widthSum,Complex.star_def] using
    (hf.mul_const (w:ℂ)).add (hf.star.mul_const (z:ℂ))

theorem kernel_derivative {f : ℝ → ℂ} {f' : ℂ} {x : ℝ}
    (hf : HasDerivAt f f' x) (hp : 0 < (f x).re)
    (w z v : ℝ) (hw : 0 < w) (hz : 0 < z) :
    HasDerivAt (fun t => kernel (f t) w z v) (-dissipation (f x) f' w z v) x := by
  have hS := widthSum_derivative hf w z
  have hT := widthSum_derivative hf.star w z
  simp only [Complex.star_def] at hT
  have hSr : 0 < (widthSum (f x) w z).re := by
    rw [widthSum_re]
    exact mul_pos hp (add_pos hw hz)
  have hTr : 0 < (widthSum (starRingEnd ℂ (f x)) w z).re := by
    rw [widthSum_re,Complex.conj_re]
    exact mul_pos hp (add_pos hw hz)
  have hS0 : widthSum (f x) w z ≠ 0 := by intro h; rw [h] at hSr; exact lt_irrefl _ hSr
  have hT0 : widthSum (starRingEnd ℂ (f x)) w z ≠ 0 := by
    intro h; rw [h] at hTr; exact lt_irrefl _ hTr
  have hH0 : widthSum (f x) w z ^ (1/2:ℂ) ≠ 0 := Complex.cpow_ne_zero_iff.mpr (Or.inl hS0)
  have hH := (Complex.hasStrictDerivAt_cpow_const (c := (1/2:ℂ))
    (show widthSum (f x) w z ∈ Complex.slitPlane from Or.inl hSr)).hasDerivAt.scomp x hS
  simp only [smul_eq_mul,Complex.cpow_sub _ _ hS0,Complex.cpow_one] at hH
  have hE := (hS.neg.mul_const ((v^2:ℝ):ℂ)).cexp
  have hd := hE.div (hH.mul hT) (mul_ne_zero hH0 hT0)
  convert hd using 1
  unfold dissipation coolingB coolingC
  simp only [Pi.neg_apply,Pi.mul_apply,Function.comp_apply]
  field_simp [hS0,hT0,hH0]
  ring

theorem real_gamma_derivative (α : ℝ) (r : ℂ) :
    HasDerivAt (fun t : ℝ => (α:ℂ)*(r+(t:ℂ))^2/2) ((α:ℂ)*r) 0 := by
  have h := ((((hasDerivAt_id (0:ℝ)).ofReal_comp.const_add r).pow 2).const_mul (α:ℂ)).div_const 2
  convert h using 1
  simp
  ring

theorem actual_kernel_derivative (α : ℝ) (r : ℂ) (hα : 0 < α) (hr : |r.im| < r.re)
    (w z v : ℝ) (hw : 0 < w) (hz : 0 < z) :
    HasDerivAt (fun t : ℝ => kernel ((α:ℂ)*(r+(t:ℂ))^2/2) w z v)
      (-dissipation ((α:ℂ)*r^2/2) ((α:ℂ)*r) w z v) 0 := by
  simpa only [Complex.ofReal_zero,add_zero] using
    kernel_derivative (real_gamma_derivative α r)
      (by simpa only [Complex.ofReal_zero,add_zero] using actual_gamma_re_positive α r hα hr)
      w z v hw hz

variable {n : Type*} [Fintype n]

def form (p : ℂ) (w : n → ℝ) (v : ℝ) (c : n → ℂ) : ℂ :=
  star c ⬝ᵥ ((fun i j => kernel p (w i) (w j) v) *ᵥ c)

theorem actual_form_derivative (α : ℝ) (r : ℂ) (hα : 0 < α) (hr : |r.im| < r.re)
    (w : n → ℝ) (hw : ∀ i, 0 < w i) (v : ℝ) (c : n → ℂ) :
    HasDerivAt (fun t : ℝ => form ((α:ℂ)*(r+(t:ℂ))^2/2) w v c)
      (-(star c ⬝ᵥ ((fun i j => dissipation ((α:ℂ)*r^2/2) ((α:ℂ)*r) (w i) (w j) v) *ᵥ c))) 0 := by
  have hd := HasDerivAt.sum (u := Finset.univ) (fun i _ =>
    (HasDerivAt.sum (u := Finset.univ) (fun j _ =>
      (actual_kernel_derivative α r hα hr (w i) (w j) v (hw i) (hw j)).mul_const (c j))).const_mul (star (c i)))
  convert hd using 1
  · funext t
    simp only [form,dotProduct,Matrix.mulVec,Pi.star_apply,Finset.sum_apply]
  · simp only [dotProduct,Matrix.mulVec,Pi.star_apply,
      neg_mul,Finset.sum_neg_distrib,mul_neg]

theorem actual_form_derivative_nonpositive (α : ℝ) (r : ℂ) (hα : 0 < α) (hr : |r.im| < r.re)
    (w : n → ℝ) (hw : ∀ i, 0 < w i) (v : ℝ) (c : n → ℂ) :
    (deriv (fun t : ℝ => form ((α:ℂ)*(r+(t:ℂ))^2/2) w v c) 0).re ≤ 0 := by
  rw [(actual_form_derivative α r hα hr w hw v c).deriv,Complex.neg_re]
  exact neg_nonpos.mpr (actual_dissipation_form_nonnegative α r hα hr w hw v c)

#print axioms widthSum_derivative
#print axioms kernel_derivative
#print axioms real_gamma_derivative
#print axioms actual_kernel_derivative
#print axioms actual_form_derivative
#print axioms actual_form_derivative_nonpositive
end
end UnifiedTheory.Audit.KFCausalChargedCoolingDerivative
