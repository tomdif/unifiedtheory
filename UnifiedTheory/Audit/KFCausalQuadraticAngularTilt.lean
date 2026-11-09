/- Actual angular exponential-tilt estimate for quadratic amplitudes.
This file controls the tilt term only, not the moving field coefficient
or the full charged response. -/
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import UnifiedTheory.Audit.KFCausalQuadraticSemicircleGram

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 3200000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalQuadraticAngularTilt
noncomputable section
open MeasureTheory intervalIntegral Real

def realQuad (a b c θ : ℝ) : ℝ := a+b*Real.sin θ+c*(Real.sin θ)^2

def halfMoment (a b c : ℝ) : ℝ :=
  Real.pi*a^2+4*a*b+Real.pi/2*b^2+Real.pi*a*c+(8/3:ℝ)*b*c+3*Real.pi/8*c^2

def fullMoment (a b c : ℝ) : ℝ :=
  2*Real.pi*a^2+Real.pi*b^2+2*Real.pi*a*c+3*Real.pi/4*c^2

private theorem quad_continuous (a b c : ℝ) : Continuous (realQuad a b c) := by
  unfold realQuad
  fun_prop

private theorem sin_power_integrable (n : ℕ) (a b : ℝ) :
    IntervalIntegrable (fun θ : ℝ => Real.sin θ ^ n) volume a b :=
  (Real.continuous_sin.pow n).intervalIntegrable _ _

private theorem half_sin_three : (∫ θ in (0:ℝ)..Real.pi, Real.sin θ^3) = 4/3 := by
  norm_num [integral_sin_pow_three]

private theorem half_sin_four : (∫ θ in (0:ℝ)..Real.pi, Real.sin θ^4) = 3*Real.pi/8 := by
  convert integral_sin_pow_even 2 using 1
  norm_num
  ring

theorem half_integral (a b c : ℝ) :
    (∫ θ in (0:ℝ)..Real.pi, realQuad a b c θ^2) = halfMoment a b c := by
  have he (θ : ℝ) : realQuad a b c θ^2 = a^2+(2*a*b)*Real.sin θ+
      (b^2+2*a*c)*Real.sin θ^2+(2*b*c)*Real.sin θ^3+c^2*Real.sin θ^4 := by
    unfold realQuad
    ring
  simp_rw [he]
  rw [intervalIntegral.integral_add, intervalIntegral.integral_add,
    intervalIntegral.integral_add, intervalIntegral.integral_add]
  · simp only [intervalIntegral.integral_const_mul, intervalIntegral.integral_const, smul_eq_mul, sub_zero,
      integral_sin, Real.sin_zero, Real.cos_zero, Real.sin_pi, Real.cos_pi,
      integral_sin_sq, half_sin_three, half_sin_four]
    unfold halfMoment
    ring
  all_goals
    apply Continuous.intervalIntegrable
    fun_prop

theorem negative_half_integral (a b c : ℝ) :
    (∫ θ in -Real.pi..(0:ℝ), realQuad a b c θ^2) = halfMoment a (-b) c := by
  have hn := intervalIntegral.integral_comp_neg (fun θ => realQuad a b c θ^2)
    (a := (0:ℝ)) (b := Real.pi)
  simp only [neg_zero] at hn
  rw [← hn]
  convert half_integral a (-b) c using 1
  apply intervalIntegral.integral_congr
  intro θ hθ
  simp only [realQuad, Real.sin_neg]
  ring

theorem full_integral (a b c : ℝ) :
    (∫ θ in -Real.pi..Real.pi, realQuad a b c θ^2) = fullMoment a b c := by
  rw [← intervalIntegral.integral_add_adjacent_intervals
    ((quad_continuous a b c).pow 2 |>.intervalIntegrable (-Real.pi) 0)
    ((quad_continuous a b c).pow 2 |>.intervalIntegrable 0 Real.pi)]
  rw [negative_half_integral, half_integral]
  unfold halfMoment fullMoment
  ring

def density (κ a b c θ : ℝ) : ℝ :=
  Real.exp (-κ*Real.sin θ)*(realQuad a b c θ)^2

def energy (κ a b c : ℝ) : ℝ :=
  ∫ θ in -Real.pi..Real.pi, density κ a b c θ

def tilt (κ a b c : ℝ) : ℝ :=
  ∫ θ in -Real.pi..Real.pi, (-κ*Real.sin θ)*density κ a b c θ

private theorem density_continuous (κ a b c : ℝ) : Continuous (density κ a b c) := by
  unfold density
  exact (show Continuous (fun θ : ℝ => Real.exp (-κ*Real.sin θ)) by fun_prop).mul
    ((quad_continuous a b c).pow 2)

private theorem density_nonnegative (κ a b c θ : ℝ) : 0 ≤ density κ a b c θ := by
  unfold density
  positivity

theorem energy_reflect (κ a b c : ℝ) : energy κ a b c = energy (-κ) a (-b) c := by
  have hn := intervalIntegral.integral_comp_neg (density κ a b c)
    (a := -Real.pi) (b := Real.pi)
  simp only [neg_neg] at hn
  unfold energy
  rw [← hn]
  apply intervalIntegral.integral_congr
  intro θ hθ
  simp only [density, realQuad, Real.sin_neg]
  congr 2 <;> ring

theorem half_le_energy (κ a b c : ℝ) (hκ : κ ≤ 0) :
    halfMoment a b c ≤ energy κ a b c := by
  have hhalf : halfMoment a b c ≤ ∫ θ in (0:ℝ)..Real.pi, density κ a b c θ := by
    rw [← half_integral]
    apply intervalIntegral.integral_mono_on Real.pi_pos.le
      ((quad_continuous a b c).pow 2 |>.intervalIntegrable _ _)
      ((density_continuous κ a b c).intervalIntegrable _ _)
    intro θ hθ
    have hs : 0 ≤ Real.sin θ := Real.sin_nonneg_of_nonneg_of_le_pi hθ.1 hθ.2
    have he : 1 ≤ Real.exp (-κ*Real.sin θ) :=
      Real.one_le_exp_iff.mpr (mul_nonneg (neg_nonneg.mpr hκ) hs)
    unfold density
    simpa only [one_mul] using mul_le_mul_of_nonneg_right he (sq_nonneg (realQuad a b c θ))
  have hleft : 0 ≤ ∫ θ in -Real.pi..(0:ℝ), density κ a b c θ :=
    intervalIntegral.integral_nonneg (by linarith [Real.pi_pos])
      (fun θ hθ => density_nonnegative κ a b c θ)
  unfold energy
  rw [← intervalIntegral.integral_add_adjacent_intervals
    ((density_continuous κ a b c).intervalIntegrable (-Real.pi) 0)
    ((density_continuous κ a b c).intervalIntegrable 0 Real.pi)]
  linarith

theorem tilt_lower_unweighted (κ a b c : ℝ) : -fullMoment a b c ≤ tilt κ a b c := by
  have he : Real.exp (-1) ≤ 1 := Real.exp_le_one_iff.mpr (by norm_num)
  rw [← full_integral]
  unfold tilt
  rw [← intervalIntegral.integral_neg]
  apply intervalIntegral.integral_mono_on (by linarith [Real.pi_pos])
    ((quad_continuous a b c).pow 2 |>.neg.intervalIntegrable _ _)
    ((continuous_const.mul Real.continuous_sin).mul
      (density_continuous κ a b c) |>.intervalIntegrable _ _)
  intro θ hθ
  have hm := (Real.mul_exp_neg_le_exp_neg_one (κ*Real.sin θ)).trans he
  have hp := mul_le_mul_of_nonneg_right hm (sq_nonneg (realQuad a b c θ))
  change -(realQuad a b c θ)^2 ≤
    (-κ*Real.sin θ)*(Real.exp (-κ*Real.sin θ)*(realQuad a b c θ)^2)
  have hexp : Real.exp (-(κ*Real.sin θ)) = Real.exp (-κ*Real.sin θ) := by congr 1; ring
  rw [hexp] at hp
  nlinarith

theorem unweighted_le_energy (κ a b c : ℝ) : fullMoment a b c ≤ 2400*energy κ a b c := by
  have hh (a b c : ℝ) : fullMoment a b c ≤ 2400*halfMoment a b c :=
    KFCausalQuadraticSemicircleGram.full_le_2400_half a b c
  by_cases hk : κ ≤ 0
  · have h := half_le_energy κ a b c hk
    linarith [hh a b c]
  · have h := half_le_energy (-κ) a (-b) c (by linarith)
    have he : fullMoment a (-b) c = fullMoment a b c := by unfold fullMoment; ring
    have hc := hh a (-b) c
    rw [he] at hc
    rw [energy_reflect]
    linarith

theorem real_tilt_lower (κ a b c : ℝ) : -2400*energy κ a b c ≤ tilt κ a b c := by
  linarith [unweighted_le_energy κ a b c, tilt_lower_unweighted κ a b c]

def quad (a b c : ℂ) (θ : ℝ) : ℂ :=
  a+b*(Real.sin θ:ℂ)+c*(Real.sin θ:ℂ)^2

theorem norm_quad (a b c : ℂ) (θ : ℝ) :
    ‖quad a b c θ‖^2 = realQuad a.re b.re c.re θ^2+realQuad a.im b.im c.im θ^2 := by
  rw [Complex.sq_norm, Complex.normSq_apply]
  simp only [quad, realQuad,
    pow_two, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
    Complex.ofReal_re, Complex.ofReal_im]
  ring

theorem complex_energy (κ : ℝ) (a b c : ℂ) :
    (∫ θ in -Real.pi..Real.pi, Real.exp (-κ*Real.sin θ)*‖quad a b c θ‖^2) =
      energy κ a.re b.re c.re+energy κ a.im b.im c.im := by
  simp_rw [norm_quad, mul_add]
  exact intervalIntegral.integral_add
    ((density_continuous κ a.re b.re c.re).intervalIntegrable _ _)
    ((density_continuous κ a.im b.im c.im).intervalIntegrable _ _)

theorem complex_tilt (κ : ℝ) (a b c : ℂ) :
    (∫ θ in -Real.pi..Real.pi,
      (-κ*Real.sin θ)*(Real.exp (-κ*Real.sin θ)*‖quad a b c θ‖^2)) =
      tilt κ a.re b.re c.re+tilt κ a.im b.im c.im := by
  simp_rw [norm_quad, mul_add]
  exact intervalIntegral.integral_add
    ((continuous_const.mul Real.continuous_sin).mul
      (density_continuous κ a.re b.re c.re) |>.intervalIntegrable _ _)
    ((continuous_const.mul Real.continuous_sin).mul
      (density_continuous κ a.im b.im c.im) |>.intervalIntegrable _ _)

theorem quadratic_tilt_lower (κ : ℝ) (a b c : ℂ) :
    -2400*(∫ θ in -Real.pi..Real.pi,
        Real.exp (-κ*Real.sin θ)*‖quad a b c θ‖^2) ≤
      ∫ θ in -Real.pi..Real.pi,
        (-κ*Real.sin θ)*(Real.exp (-κ*Real.sin θ)*‖quad a b c θ‖^2) := by
  rw [complex_energy, complex_tilt]
  linarith [real_tilt_lower κ a.re b.re c.re, real_tilt_lower κ a.im b.im c.im]

theorem radius_tilt_lower (κ R : ℝ) (a b c : ℂ) :
    -2400*(∫ θ in -Real.pi..Real.pi,
        Real.exp (-2*κ*(R*Real.sin θ))*
          ‖a+b*(R*Real.sin θ:ℝ)+c*(R*Real.sin θ:ℝ)^2‖^2) ≤
      ∫ θ in -Real.pi..Real.pi,
        (-2*κ*(R*Real.sin θ))*(Real.exp (-2*κ*(R*Real.sin θ))*
          ‖a+b*(R*Real.sin θ:ℝ)+c*(R*Real.sin θ:ℝ)^2‖^2) := by
  have hq (θ : ℝ) : a+b*(R*Real.sin θ:ℝ)+c*(R*Real.sin θ:ℝ)^2 =
      quad a ((R:ℂ)*b) ((R:ℂ)^2*c) θ := by
    simp only [quad, Complex.ofReal_mul]
    ring
  simp_rw [hq]
  have he (θ : ℝ) : -2*κ*(R*Real.sin θ) = -(2*κ*R)*Real.sin θ := by ring
  simp_rw [he]
  exact quadratic_tilt_lower (2*κ*R) a ((R:ℂ)*b) ((R:ℂ)^2*c)

#print axioms half_integral
#print axioms negative_half_integral
#print axioms full_integral
#print axioms energy_reflect
#print axioms half_le_energy
#print axioms tilt_lower_unweighted
#print axioms unweighted_le_energy
#print axioms real_tilt_lower
#print axioms norm_quad
#print axioms complex_energy
#print axioms complex_tilt
#print axioms quadratic_tilt_lower
#print axioms radius_tilt_lower
end
end UnifiedTheory.Audit.KFCausalQuadraticAngularTilt
