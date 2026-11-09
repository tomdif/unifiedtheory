/- Strong monotonicity of the actual clock chart controls the complex
interpolation coefficient by its real part. This gives a uniform
one-sided bound for a field-derivative forcing term. -/
import UnifiedTheory.Audit.KFCausalActualImaginaryShearCurve
import UnifiedTheory.Audit.KFCausalFieldCorrectionRealPairing

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 800000

namespace UnifiedTheory.Audit.KFCausalImaginaryShearCocoercivity
noncomputable section
open UnifiedTheory.Audit.KFCausalComplexClockChart
open UnifiedTheory.Audit.KFCausalComplexClockInverse
open UnifiedTheory.Audit.KFCausalClockFloorRelativeShift
open UnifiedTheory.Audit.KFCausalImaginaryShearCoefficient

theorem relative_coercivity (ε y s : ℝ) (hε : 0 < ε) (hy : |y| ≤ Real.pi*ε/3) :
    ε*‖relative ε y s‖^2 ≤ y*(relative ε y s).im := by
  have hq := argument_mem ε y s hε hy
  have hs : (s:ℂ) ∈ closedStrip := by
    change |(s:ℂ).im| ≤ Real.pi/2
    simp only [Complex.ofReal_im,abs_zero]
    positivity
  have hz : complexInverse ε (argument ε y s) ∈ closedStrip := by
    change |(complexInverse ε (argument ε y s)).im| ≤ Real.pi/2
    exact (show |(complexInverse ε (argument ε y s)).im| < Real.pi/2 from
      complexInverse_mem ε hε _ hq).le
  have hm := KFCausalComplexClockCoercivity.complexChart_strong_monotone ε (s:ℂ)
    (complexInverse ε (argument ε y s)) hs hz
  rw [complexInverse_right ε hε _ hq,complexChart_real,Complex.normSq_eq_norm_sq] at hm
  change ε*‖relative ε y s‖^2 ≤ ((argument ε y s-
    (KFCausalRegularizedLongitudinalChart.chart ε s:ℂ))*star (relative ε y s)).re at hm
  simpa only [argument,add_sub_cancel_left,Complex.star_def,Complex.mul_re,Complex.mul_im,
    Complex.ofReal_re,Complex.ofReal_im,Complex.I_re,Complex.I_im,
    Complex.conj_re,Complex.conj_im,mul_zero,zero_mul,sub_zero,mul_one,zero_add,add_zero,zero_sub,mul_neg,neg_neg] using hm

theorem coefficient_coercivity (ε h s : ℝ) (hε : 0 < ε) (hh : h ≠ 0)
    (hb : |h| ≤ 2*Real.pi*ε/3) :
    2*ε*‖coefficient ε h s‖^2 ≤ (coefficient ε h s).re := by
  have hm := relative_coercivity ε (-h/2) s hε (half_shift_bound ε h hb)
  change ε*‖displacement ε h s‖^2 ≤ (-h/2)*(displacement ε h s).im at hm
  have hn : ‖coefficient ε h s‖^2 = ‖displacement ε h s‖^2/h^2 := by
    simp only [coefficient,norm_div,norm_mul,Complex.norm_I,one_mul,
      Complex.norm_real,Real.norm_eq_abs,div_pow,sq_abs]
  rw [hn,coefficient_re]
  calc
    _ = (2*ε*‖displacement ε h s‖^2)/h^2 := by ring
    _ ≤ (-h*(displacement ε h s).im)/h^2 := div_le_div_of_nonneg_right
      (by linarith only [hm]) (sq_nonneg h)
    _ = _ := by field_simp

theorem scalar_forced_lower (ε h : ℝ) (hε : 0 < ε) (c z d : ℂ)
    (hc : 2*ε*‖c‖^2 ≤ c.re) :
    -(h^2/(4*ε))*‖d‖^2 ≤ 2*(inner ℂ z (c*(z+(Complex.I*(h:ℂ))*d))).re := by
  have he : (inner ℂ z (c*z)).re = c.re*‖z‖^2 := by
    simpa only [Complex.ofReal_one,one_mul,mul_one] using
      KFCausalFieldCorrectionRealPairing.mixed_real_inner 1 1 c z
  have hb := (Complex.abs_re_le_norm (inner ℂ z (c*((Complex.I*(h:ℂ))*d)))).trans
    (norm_inner_le_norm (𝕜 := ℂ) z (c*((Complex.I*(h:ℂ))*d)))
  simp only [norm_mul,Complex.norm_I,one_mul,Complex.norm_real,Real.norm_eq_abs] at hb
  have hcross : -‖z‖*(‖c‖*(|h| *‖d‖)) ≤ (inner ℂ z (c*((Complex.I*(h:ℂ))*d))).re := by
    linarith only [(neg_abs_le (inner ℂ z (c*((Complex.I*(h:ℂ))*d))).re),hb]
  have hp := mul_le_mul_of_nonneg_right hc (sq_nonneg ‖z‖)
  have hs := sq_nonneg (2*ε*‖c‖*‖z‖-|h|/2*‖d‖)
  rw [mul_add,inner_add_right,Complex.add_re,he]
  have hy : -(h^2/(4*ε))*‖d‖^2 ≤
      4*ε*‖c‖^2*‖z‖^2-2*‖z‖*(‖c‖*(|h| *‖d‖)) := by
    apply (mul_le_mul_iff_right₀ hε).mp
    field_simp
    nlinarith only [hs,sq_abs h]
  linarith only [hy,hp,hcross]

#print axioms relative_coercivity
#print axioms coefficient_coercivity
#print axioms scalar_forced_lower
end
end UnifiedTheory.Audit.KFCausalImaginaryShearCocoercivity
