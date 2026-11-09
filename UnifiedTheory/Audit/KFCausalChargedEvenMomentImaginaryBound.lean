/- All even charged Gaussian--Laplace moments have a uniform-in-width
imaginary-variation lower bound. The loss depends on the moment degree.
This is an actual moment-kernel statement, not the unrestricted quartic
response estimate. -/
import UnifiedTheory.Audit.KFCausalChargedCoolingDerivative
import UnifiedTheory.Audit.KFCausalChargedFourierPolynomialGram

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalChargedEvenMomentImaginaryBound
noncomputable section
open MeasureTheory Matrix
open scoped Topology BigOperators ComplexOrder
open KFCausalChargedCoolingWidthPositive KFCausalChargedCoolingFixedV
open KFCausalPositiveKernelExponential

def momentConstant : ℕ → ℝ
  | 0 => Real.pi
  | l+1 => ((2*l+1:ℝ)/2)*momentConstant l

def kernel (l : ℕ) (p : ℂ) (w z : ℝ) : ℂ :=
  (widthSum p w z)⁻¹^(l+1)*(widthSum (starRingEnd ℂ p) w z)⁻¹

def slope (l : ℕ) (p q : ℂ) (w z : ℝ) : ℂ :=
  -((l+1:ℂ)*(widthSum q w z/widthSum p w z)+
    widthSum (starRingEnd ℂ q) w z/widthSum (starRingEnd ℂ p) w z)*kernel l p w z

theorem momentConstant_positive (l : ℕ) : 0 < momentConstant l := by
  induction l with
  | zero => exact Real.pi_pos
  | succ l ih => simp only [momentConstant]; positivity

theorem even_integral (S T : ℂ) (hS : 0 < S.re) (hT : 0 < T.re) (l : ℕ) :
    KFCausalChargedFourierGaussianMoments.integral S T 0 (2*l) =
      (momentConstant l:ℂ)*S⁻¹^(l+1)*T⁻¹ := by
  have hS0 : S ≠ 0 := by intro h; simp [h] at hS
  have hT0 : T ≠ 0 := by intro h; simp [h] at hT
  induction l with
  | zero =>
      rw [show 2*0=0 by omega,KFCausalChargedFourierGaussianMoments.integral_zero S T 0 hS hT]
      simp [KFCausalChargedFourierGaussianMoments.kernel,momentConstant,div_eq_mul_inv,_root_.mul_inv_rev]
      ring
  | succ l ih =>
      have h := KFCausalChargedFourierGaussianMoments.recurrence S T 0 hS hT (2*l)
      rw [ih] at h
      simp only [zero_mul,add_zero] at h
      rw [show 2*(l+1)=2*l+2 by omega]
      apply (mul_left_cancel₀ (show (2:ℂ)*S ≠ 0 by exact mul_ne_zero (by norm_num) hS0))
      rw [h]
      simp only [momentConstant,Complex.ofReal_mul,Complex.ofReal_div,Complex.ofReal_natCast,
        Complex.ofReal_add,Complex.ofReal_one,Complex.ofReal_ofNat,pow_succ]
      push_cast
      field_simp

variable {ι : Type*} [Fintype ι]

theorem kernel_positive (l : ℕ) (p : ℂ) (hp : 0 < p.re)
    (w : ι → ℝ) (hw : ∀ i, 0 < w i) :
    Matrix.PosSemidef (fun i j => kernel l p (w i) (w j)) := by
  exact schur_positive (schur_power_positive (inverse_width_positive p hp w hw) (l+1))
    (inverse_width_positive (starRingEnd ℂ p) (by simpa only [Complex.conj_re] using hp) w hw)

theorem kernel_derivative {f : ℝ → ℂ} {f' : ℂ} {x : ℝ}
    (hf : HasDerivAt f f' x) (hp : 0 < (f x).re)
    (l : ℕ) (w z : ℝ) (hw : 0 < w) (hz : 0 < z) :
    HasDerivAt (fun t => kernel l (f t) w z) (slope l (f x) f' w z) x := by
  have hS := KFCausalChargedCoolingDerivative.widthSum_derivative hf w z
  have hT : HasDerivAt (fun t => widthSum (starRingEnd ℂ (f t)) w z)
      (widthSum (starRingEnd ℂ f') w z) x := by
    simpa only [Complex.star_def] using
      KFCausalChargedCoolingDerivative.widthSum_derivative hf.star w z
  have hS0 : widthSum (f x) w z ≠ 0 := by
    have h : 0 < (widthSum (f x) w z).re := by rw [widthSum_re]; positivity
    intro e; simp [e] at h
  have hT0 : widthSum (starRingEnd ℂ (f x)) w z ≠ 0 := by
    have h : 0 < (widthSum (starRingEnd ℂ (f x)) w z).re := by
      rw [widthSum_re,Complex.conj_re]; positivity
    intro e; simp [e] at h
  have hSi := (hasDerivAt_const x (1:ℂ)).div hS hS0
  have hTi := (hasDerivAt_const x (1:ℂ)).div hT hT0
  simp only [zero_mul,one_mul,zero_sub] at hSi hTi
  have hd := (hSi.pow (l+1)).mul hTi
  convert hd using 1
  · funext t; simp [kernel]
  · unfold slope kernel
    simp only [Nat.add_sub_cancel,Pi.div_apply,Pi.pow_apply,one_div,Nat.cast_add,Nat.cast_one,pow_succ]
    field_simp
    ring

def area (r : ℂ) : ℝ := r.re^2-r.im^2
def radial (r : ℂ) : ℝ := r.re^2+r.im^2
def gamma (α : ℝ) (r : ℂ) : ℂ := (α:ℂ)*r^2/2
def gammaSlope (α : ℝ) (r : ℂ) : ℂ := (α:ℂ)*r*Complex.I

theorem area_positive (r : ℂ) (hr : |r.im| < r.re) : 0 < area r := by
  have ha : 0 < r.re := lt_of_le_of_lt (abs_nonneg _) hr
  unfold area
  nlinarith [sq_abs r.im,mul_pos (sub_pos.mpr hr)
    (add_pos_of_pos_of_nonneg ha (abs_nonneg r.im))]

private theorem gamma_relation (α : ℝ) (r : ℂ) (hA : area r ≠ 0) :
    (r.im:ℂ)*gammaSlope α r =
      ((1/2-r.im^2/area r:ℝ):ℂ)*gamma α r-
      ((radial r/(2*area r):ℝ):ℂ)*starRingEnd ℂ (gamma α r) := by
  have hAc : (area r:ℂ) ≠ 0 := by exact_mod_cast hA
  push_cast
  field_simp [hAc]
  unfold gamma gammaSlope
  simp only [map_div₀,map_mul,map_pow,Complex.conj_ofReal,map_ofNat]
  apply Complex.ext <;>
    norm_num [area,radial,Complex.mul_re,Complex.mul_im,pow_two] <;> ring

private theorem width_relation (α : ℝ) (r : ℂ) (hA : area r ≠ 0) (w z : ℝ) :
    (r.im:ℂ)*widthSum (gammaSlope α r) w z =
      ((1/2-r.im^2/area r:ℝ):ℂ)*widthSum (gamma α r) w z-
      ((radial r/(2*area r):ℝ):ℂ)*widthSum (starRingEnd ℂ (gamma α r)) w z := by
  have h := gamma_relation α r hA
  have hc := congrArg (starRingEnd ℂ) h
  simp only [map_mul,map_sub,Complex.conj_ofReal,Complex.conj_conj] at hc
  unfold widthSum
  simp only [Complex.conj_conj]
  linear_combination (w:ℂ)*h+(z:ℂ)*hc

theorem actual_kernel_identity (α : ℝ) (r : ℂ) (hα : 0 < α) (hr : |r.im| < r.re)
    (l : ℕ) (w z : ℝ) (hw : 0 < w) (hz : 0 < z) :
    (r.im:ℂ)*slope l (gamma α r) (gammaSlope α r) w z+
      (((l+2:ℝ)/2):ℂ)*kernel l (gamma α r) w z =
    (((l+2:ℝ)*r.im^2/area r):ℂ)*kernel l (gamma α r) w z+
      ((radial r/(2*area r):ℝ):ℂ)*
        ((l+1:ℂ)*(widthSum (gamma α r) w z)⁻¹^(l+2)+
          (widthSum (gamma α r) w z)⁻¹^l*
            (widthSum (starRingEnd ℂ (gamma α r)) w z)⁻¹^2) := by
  have hA := ne_of_gt (area_positive r hr)
  have hp := actual_gamma_re_positive α r hα hr
  have hS0 : widthSum (gamma α r) w z ≠ 0 := by
    have h : 0 < (widthSum (gamma α r) w z).re := by rw [widthSum_re]; exact mul_pos hp (add_pos hw hz)
    intro e; simp [e] at h
  have hT0 : widthSum (starRingEnd ℂ (gamma α r)) w z ≠ 0 := by
    have h : 0 < (widthSum (starRingEnd ℂ (gamma α r)) w z).re := by
      rw [widthSum_re,Complex.conj_re]; exact mul_pos hp (add_pos hw hz)
    intro e; simp [e] at h
  have h := width_relation α r hA w z
  have hc := congrArg (starRingEnd ℂ) h
  simp only [map_mul,map_sub,Complex.conj_ofReal] at hc
  have he (p : ℂ) : starRingEnd ℂ (widthSum p w z)=widthSum (starRingEnd ℂ p) w z := by
    simp [widthSum]
  simp only [he,Complex.conj_conj] at hc
  rw [show (r.im:ℂ)*slope l (gamma α r) (gammaSlope α r) w z =
      -((l+1:ℂ)*((r.im:ℂ)*widthSum (gammaSlope α r) w z)/widthSum (gamma α r) w z+
        ((r.im:ℂ)*widthSum (starRingEnd ℂ (gammaSlope α r)) w z)/
          widthSum (starRingEnd ℂ (gamma α r)) w z)*kernel l (gamma α r) w z by
        unfold slope; ring]
  rw [h,hc]
  unfold kernel
  simp only [pow_succ]
  push_cast
  field_simp [hS0,hT0]
  ring

theorem actual_kernel_lower_positive (α : ℝ) (r : ℂ) (hα : 0 < α) (hr : |r.im| < r.re)
    (l : ℕ) (w : ι → ℝ) (hw : ∀ i, 0 < w i) :
    Matrix.PosSemidef (fun i j => (r.im:ℂ)*slope l (gamma α r) (gammaSlope α r) (w i) (w j)+
      (((l+2:ℝ)/2):ℂ)*kernel l (gamma α r) (w i) (w j)) := by
  have hp := actual_gamma_re_positive α r hα hr
  have hS := inverse_width_positive (gamma α r) hp w hw
  have hT := inverse_width_positive (starRingEnd ℂ (gamma α r)) (by simpa only [Complex.conj_re] using hp) w hw
  have hA := area_positive r hr
  have hK := (kernel_positive l (gamma α r) hp w hw).smul
    (show 0 ≤ (l+2:ℝ)*r.im^2/area r by positivity)
  have hP := ((schur_power_positive hS (l+2)).smul (show (0:ℝ) ≤ l+1 by positivity)).add
    (schur_positive (schur_power_positive hS l) (schur_power_positive hT 2))
  have hP' := hP.smul (show 0 ≤ radial r/(2*area r) by unfold radial; positivity)
  convert hK.add hP' using 1
  ext i j
  rw [actual_kernel_identity α r hα hr l (w i) (w j) (hw i) (hw j)]
  simp only [Matrix.add_apply,Matrix.smul_apply,Complex.real_smul,Complex.ofReal_natCast,
    Complex.ofReal_add,Complex.ofReal_one]
  push_cast
  ring

theorem imaginary_gamma_derivative (α : ℝ) (r : ℂ) :
    HasDerivAt (fun t : ℝ => gamma α (r+Complex.I*(t:ℂ))) (gammaSlope α r) 0 := by
  have hd := (((((hasDerivAt_id (0:ℝ)).ofReal_comp.const_mul Complex.I).const_add r).pow 2).const_mul (α:ℂ)).div_const 2
  convert hd using 1
  simp [gammaSlope]
  ring

def form (l : ℕ) (p : ℂ) (w : ι → ℝ) (c : ι → ℂ) : ℂ :=
  star c ⬝ᵥ ((fun i j => kernel l p (w i) (w j)) *ᵥ c)

theorem actual_form_derivative (α : ℝ) (r : ℂ) (hα : 0 < α) (hr : |r.im| < r.re)
    (l : ℕ) (w : ι → ℝ) (hw : ∀ i, 0 < w i) (c : ι → ℂ) :
    HasDerivAt (fun t : ℝ => form l (gamma α (r+Complex.I*(t:ℂ))) w c)
      (star c ⬝ᵥ ((fun i j => slope l (gamma α r) (gammaSlope α r) (w i) (w j)) *ᵥ c)) 0 := by
  have hp := actual_gamma_re_positive α r hα hr
  have hd := HasDerivAt.sum (u := Finset.univ) (fun i _ =>
    (HasDerivAt.sum (u := Finset.univ) (fun j _ =>
      (kernel_derivative (imaginary_gamma_derivative α r)
        (by simpa only [Complex.ofReal_zero,mul_zero,add_zero] using hp)
        l (w i) (w j) (hw i) (hw j)).mul_const (c j))).const_mul (star (c i)))
  convert hd using 1
  · funext t; simp only [form,dotProduct,Matrix.mulVec,Pi.star_apply,Finset.sum_apply]
  · simp only [Complex.ofReal_zero,mul_zero,add_zero,dotProduct,Matrix.mulVec,Pi.star_apply]

theorem actual_form_derivative_lower (α : ℝ) (r : ℂ) (hα : 0 < α) (hr : |r.im| < r.re)
    (l : ℕ) (w : ι → ℝ) (hw : ∀ i, 0 < w i) (c : ι → ℂ) :
    -((l+2:ℝ)/2)*(form l (gamma α r) w c).re ≤
      r.im*(deriv (fun t : ℝ => form l (gamma α (r+Complex.I*(t:ℂ))) w c) 0).re := by
  rw [(actual_form_derivative α r hα hr l w hw c).deriv]
  have h := (actual_kernel_lower_positive α r hα hr l w hw).dotProduct_mulVec_nonneg c |>.1
  have he : star c ⬝ᵥ ((fun i j => (r.im:ℂ)*slope l (gamma α r) (gammaSlope α r) (w i) (w j)+
      (((l+2:ℝ)/2):ℂ)*kernel l (gamma α r) (w i) (w j)) *ᵥ c) =
      (r.im:ℂ)*(star c ⬝ᵥ ((fun i j => slope l (gamma α r) (gammaSlope α r) (w i) (w j)) *ᵥ c))+
      (((l+2:ℝ)/2):ℂ)*form l (gamma α r) w c := by
    simp only [form,dotProduct,Matrix.mulVec,Pi.star_apply,add_mul,Finset.sum_add_distrib,
      mul_add,Finset.mul_sum]
    congr 1 <;> apply Finset.sum_congr rfl <;> intro i _ <;>
      apply Finset.sum_congr rfl <;> intro j _ <;> ring
  rw [he] at h
  norm_num [Complex.mul_re,Complex.div_re,Complex.div_im] at h
  linarith

#print axioms momentConstant_positive
#print axioms even_integral
#print axioms kernel_positive
#print axioms kernel_derivative
#print axioms area_positive
#print axioms actual_kernel_identity
#print axioms actual_kernel_lower_positive
#print axioms imaginary_gamma_derivative
#print axioms actual_form_derivative
#print axioms actual_form_derivative_lower
end
end UnifiedTheory.Audit.KFCausalChargedEvenMomentImaginaryBound
