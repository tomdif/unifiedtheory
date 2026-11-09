/- Exact normalization of the actual two-width cooling matrix. -/
import UnifiedTheory.Audit.KFCausalChargedCoolingDerivative

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalChargedCoolingTwoWidthNormalization
noncomputable section
open KFCausalChargedCoolingWidthPositive KFCausalChargedCoolingFixedV
open KFCausalChargedCoolingDerivative

def diagonalScale (s : ℝ) : ℝ := 1 / (Real.sqrt s * s)

def residual (α : ℝ) (r : ℂ) (m w z : ℝ) : ℂ :=
  coolingB ((α:ℂ)*r^2/2) ((α:ℂ)*r) w z -
    (α*r.re*m/4:ℝ) * kernel ((α:ℂ)*r^2/2) w z 0

def normalizedDistance (α : ℝ) (r : ℂ) (m u : ℝ) : ℝ :=
  2 * ‖widthSum ((α:ℂ)*r^2/2) m (m*u^2)‖ / (α*(r.re^2-r.im^2)*m)

theorem widthSum_conjugate (p : ℂ) (w z : ℝ) :
    widthSum (starRingEnd ℂ p) w z = starRingEnd ℂ (widthSum p w z) := by
  simp [widthSum]

theorem actual_widthSum (α : ℝ) (r : ℂ) (w z : ℝ) :
    widthSum ((α:ℂ)*r^2/2) w z =
      (α*(r.re^2-r.im^2)/2*(w+z):ℝ) +
      (α*r.re*r.im*(w-z):ℝ)*Complex.I := by
  apply Complex.ext <;> simp [widthSum, pow_two, Complex.conj_ofNat] <;> ring

theorem actual_slopeSum (α : ℝ) (r : ℂ) (w z : ℝ) :
    widthSum ((α:ℂ)*r) w z =
      (α*r.re*(w+z):ℝ) + (α*r.im*(w-z):ℝ)*Complex.I := by
  apply Complex.ext <;> simp [widthSum] <;> ring

theorem half_power_normSq (z : ℂ) : Complex.normSq (z^(1/2:ℂ)) = ‖z‖ := by
  have h : (z^(1/2:ℂ))^2 = z := by
    simpa only [one_div] using Complex.cpow_nat_inv_pow z (n := 2) (by decide)
  have hn := congrArg norm h
  simpa only [norm_pow, Complex.normSq_eq_norm_sq] using hn

theorem kernel_zero_normSq (p : ℂ) (w z : ℝ) :
    Complex.normSq (kernel p w z 0) = 1 / ‖widthSum p w z‖^3 := by
  simp only [kernel, zero_pow (by norm_num : (2:ℕ) ≠ 0), Complex.ofReal_zero,
    mul_zero, Complex.exp_zero]
  rw [Complex.normSq_div, Complex.normSq_one, Complex.normSq_mul,
    widthSum_conjugate, Complex.normSq_conj, half_power_normSq,
    Complex.normSq_eq_norm_sq]
  congr 1
  ring

theorem diagonalScale_positive (s : ℝ) (hs : 0 < s) : 0 < diagonalScale s := by
  unfold diagonalScale
  positivity

theorem diagonalScale_sq (s : ℝ) (hs : 0 ≤ s) :
    diagonalScale s ^ 2 = 1 / s^3 := by
  unfold diagonalScale
  rw [div_pow, one_pow, mul_pow, Real.sq_sqrt hs]
  congr 1
  ring

theorem diagonalScale_mul_sq (s u : ℝ) (hs : 0 ≤ s) (hu : 0 ≤ u) :
    diagonalScale (s*u^2) = diagonalScale s / u^3 := by
  unfold diagonalScale
  rw [Real.sqrt_mul hs, Real.sqrt_sq_eq_abs, abs_of_nonneg hu]
  rw [div_div]
  congr 1
  ring

theorem actual_kernel_diagonal (α : ℝ) (r : ℂ) (w : ℝ)
    (hs : 0 ≤ α*(r.re^2-r.im^2)*w) :
    kernel ((α:ℂ)*r^2/2) w w 0 =
      (diagonalScale (α*(r.re^2-r.im^2)*w):ℂ) := by
  have hS : widthSum ((α:ℂ)*r^2/2) w w = (α*(r.re^2-r.im^2)*w:ℝ) := by
    rw [actual_widthSum]
    push_cast
    ring
  simp only [kernel, zero_pow (by norm_num : (2:ℕ) ≠ 0), Complex.ofReal_zero,
    mul_zero, Complex.exp_zero, widthSum_conjugate, hS, Complex.conj_ofReal]
  have hc : (α*(r.re^2-r.im^2)*w:ℝ) ^ (1/2:ℂ) =
      (Real.sqrt (α*(r.re^2-r.im^2)*w):ℂ) := by
    rw [Real.sqrt_eq_rpow, Complex.ofReal_cpow hs]
    norm_num
  rw [hc]
  simp [diagonalScale]

theorem residual_factor (α : ℝ) (r : ℂ) (m w z : ℝ) :
    residual α r m w z =
      (widthSum ((α:ℂ)*r) w z - (α*r.re*m/4:ℝ)) *
        kernel ((α:ℂ)*r^2/2) w z 0 := by
  simp [residual, coolingB, kernel, sub_mul, div_eq_mul_inv]

theorem residual_diagonal (α : ℝ) (r : ℂ) (m w : ℝ)
    (hs : 0 ≤ α*(r.re^2-r.im^2)*w) :
    residual α r m w w =
      (α*r.re*(2*w-m/4)*diagonalScale (α*(r.re^2-r.im^2)*w):ℝ) := by
  rw [residual_factor, actual_slopeSum, actual_kernel_diagonal α r w hs]
  push_cast
  ring

theorem residual_off_normSq (α : ℝ) (r : ℂ) (m u : ℝ) (ha : r.re ≠ 0) :
    Complex.normSq (residual α r m m (m*u^2)) =
      (α*r.re*m)^2 * ((u^2+3/4)^2+(r.im/r.re)^2*(u^2-1)^2) /
        ‖widthSum ((α:ℂ)*r^2/2) m (m*u^2)‖^3 := by
  rw [residual_factor, Complex.normSq_mul, kernel_zero_normSq, actual_slopeSum]
  have hn : Complex.normSq
      ((α*r.re*(m+m*u^2):ℝ)+(α*r.im*(m-m*u^2):ℝ)*Complex.I-
        (α*r.re*m/4:ℝ)) =
      (α*r.re*m)^2*((u^2+3/4)^2+(r.im/r.re)^2*(u^2-1)^2) := by
    simp only [Complex.normSq_apply, Complex.sub_re, Complex.add_re, Complex.mul_re,
      Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
      Complex.sub_im, Complex.add_im, Complex.mul_im]
    field_simp [ha]
    ring
  rw [hn]
  ring

theorem actual_parameters_positive (r : ℂ) (hr : |r.im| < r.re) :
    0 < r.re ∧ 0 < r.re^2-r.im^2 := by
  constructor
  · exact (abs_nonneg r.im).trans_lt hr
  · have hp := mul_pos (sub_pos.mpr hr) (add_pos_of_pos_of_nonneg
      ((abs_nonneg r.im).trans_lt hr) (abs_nonneg r.im))
    nlinarith [sq_abs r.im]

theorem normalizedDistance_positive (α : ℝ) (r : ℂ) (m u : ℝ)
    (hα : 0 < α) (hr : |r.im| < r.re) (hm : 0 < m) (hu : 0 < u) :
    0 < normalizedDistance α r m u := by
  have hA := (actual_parameters_positive r hr).2
  have hS : 0 < (widthSum ((α:ℂ)*r^2/2) m (m*u^2)).re := by
    rw [widthSum_re]
    exact mul_pos (actual_gamma_re_positive α r hα hr) (by positivity)
  have hn : 0 < ‖widthSum ((α:ℂ)*r^2/2) m (m*u^2)‖ := by
    apply norm_pos_iff.mpr
    intro hz
    rw [hz] at hS
    exact lt_irrefl _ hS
  unfold normalizedDistance
  positivity

theorem normalizedDistance_sq (α : ℝ) (r : ℂ) (m u : ℝ)
    (hα : α ≠ 0) (hA : r.re^2-r.im^2 ≠ 0) (hm : m ≠ 0) :
    normalizedDistance α r m u ^ 2 =
      (1+u^2)^2+(2*r.re*r.im/(r.re^2-r.im^2))^2*(u^2-1)^2 := by
  have hn : ‖widthSum ((α:ℂ)*r^2/2) m (m*u^2)‖^2 =
      (α*(r.re^2-r.im^2)/2*(m+m*u^2))^2 +
      (α*r.re*r.im*(m-m*u^2))^2 := by
    rw [Complex.sq_norm, actual_widthSum]
    simp [Complex.normSq_apply, pow_two]
  unfold normalizedDistance
  rw [div_pow, mul_pow, hn]
  field_simp [hα, hA, hm]
  ring

theorem normalizedDistance_lower (α : ℝ) (r : ℂ) (m u : ℝ)
    (hα : 0 < α) (hr : |r.im| < r.re) (hm : 0 < m) :
    (1+u^2)^2+4*(r.im/r.re)^2*(u^2-1)^2 ≤ normalizedDistance α r m u ^ 2 := by
  have ha := (actual_parameters_positive r hr).1
  have hA := (actual_parameters_positive r hr).2
  rw [normalizedDistance_sq α r m u hα.ne' hA.ne' hm.ne']
  have he : (2*r.re*r.im/(r.re^2-r.im^2))^2-4*(r.im/r.re)^2 =
      4*r.im^4*(2*r.re^2-r.im^2)/(r.re^2*(r.re^2-r.im^2)^2) := by
    field_simp [ha.ne', hA.ne']
    ring
  have hp : 0 ≤ (2*r.re*r.im/(r.re^2-r.im^2))^2-4*(r.im/r.re)^2 := by
    rw [he]
    apply div_nonneg
    · apply mul_nonneg
      · positivity
      · nlinarith [sq_nonneg r.re]
    · positivity
  nlinarith [mul_nonneg hp (sq_nonneg (u^2-1))]

theorem widthSum_swap (p : ℂ) (w z : ℝ) :
    widthSum p z w = starRingEnd ℂ (widthSum p w z) := by
  simp [widthSum]
  ring

theorem kernel_zero_conjugate (p : ℂ) (w z : ℝ) (hp : 0 < p.re)
    (hw : 0 < w) (hz : 0 < z) :
    kernel p z w 0 = starRingEnd ℂ (kernel p w z 0) := by
  have hS : 0 < (widthSum p w z).re := by
    rw [widthSum_re]
    exact mul_pos hp (add_pos hw hz)
  have ha : (widthSum p w z).arg ≠ Real.pi := by
    have hb := (abs_lt.mp (Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl hS))).2
    linarith [Real.pi_pos]
  have hc : starRingEnd ℂ (1/2:ℂ) = (1/2:ℂ) := by simp [Complex.conj_ofNat]
  have hpow : starRingEnd ℂ (widthSum p w z ^ (1/2:ℂ)) =
      starRingEnd ℂ (widthSum p w z) ^ (1/2:ℂ) := by
    simpa only [hc] using (Complex.conj_cpow (widthSum p w z) (1/2:ℂ) ha).symm
  simp only [kernel, zero_pow (by norm_num : (2:ℕ) ≠ 0), Complex.ofReal_zero,
    mul_zero, Complex.exp_zero, widthSum_conjugate, widthSum_swap p w z,
    map_div₀, map_one, map_mul, hpow]

theorem residual_conjugate (α : ℝ) (r : ℂ) (m w z : ℝ)
    (hα : 0 < α) (hr : |r.im| < r.re) (hw : 0 < w) (hz : 0 < z) :
    residual α r m z w = starRingEnd ℂ (residual α r m w z) := by
  rw [residual_factor, residual_factor, widthSum_swap,
    kernel_zero_conjugate _ w z (actual_gamma_re_positive α r hα hr) hw hz]
  simp [Complex.conj_ofNat]

#print axioms widthSum_conjugate
#print axioms actual_widthSum
#print axioms actual_slopeSum
#print axioms half_power_normSq
#print axioms kernel_zero_normSq
#print axioms diagonalScale_positive
#print axioms diagonalScale_sq
#print axioms diagonalScale_mul_sq
#print axioms actual_kernel_diagonal
#print axioms residual_factor
#print axioms residual_diagonal
#print axioms residual_off_normSq
#print axioms actual_parameters_positive
#print axioms normalizedDistance_positive
#print axioms normalizedDistance_sq
#print axioms normalizedDistance_lower
#print axioms widthSum_swap
#print axioms kernel_zero_conjugate
#print axioms residual_conjugate
end
end UnifiedTheory.Audit.KFCausalChargedCoolingTwoWidthNormalization
