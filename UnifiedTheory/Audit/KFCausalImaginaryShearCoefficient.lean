/- The coefficient of imaginary-shear interpolation has positive real
part at the actual clock shift, for either sign of nonzero hbar. This is
a scalar sign and boundedness result, not yet a Hilbert-space derivative
or a sign theorem for the Hamiltonian response. -/
import UnifiedTheory.Audit.KFCausalClockFloorRelativeShift
import UnifiedTheory.Audit.KFCausalClockFloorDefectSign

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 500000

namespace UnifiedTheory.Audit.KFCausalImaginaryShearCoefficient
noncomputable section
open UnifiedTheory.Audit.KFCausalComplexClockChart
open UnifiedTheory.Audit.KFCausalComplexClockInverse
open UnifiedTheory.Audit.KFCausalClockFloorRelativeShift

theorem inverse_im_product_positive (ε : ℝ) (hε : 0 < ε) (q : ℂ)
    (hq : q ∈ targetStrip ε) (hn : q.im ≠ 0) :
    0 < q.im * (complexInverse ε q).im := by
  let z := complexInverse ε q
  have hi := congrArg Complex.im (complexInverse_right ε hε q hq)
  rw [complexChart_im] at hi
  change Real.exp z.re * Real.sin z.im + ε*z.im = q.im at hi
  have hz : z.im ≠ 0 := by
    intro he
    apply hn
    rw [he,Real.sin_zero,mul_zero,mul_zero,zero_add] at hi
    exact hi.symm
  have hstrip : z ∈ closedStrip := by
    change |z.im| ≤ Real.pi/2
    exact le_of_lt (complexInverse_mem ε hε q hq)
  have hs := KFCausalClockFloorDefectSign.strip_im_sin_nonnegative z hstrip
  have hp := mul_nonneg (Real.exp_pos z.re).le hs
  have he := mul_pos hε (sq_pos_of_ne_zero hz)
  change 0 < q.im*z.im
  rw [← hi]
  nlinarith

def displacement (ε h s : ℝ) : ℂ := relative ε (-h/2) s
def coefficient (ε h s : ℝ) : ℂ := Complex.I * displacement ε h s / (h:ℂ)

theorem half_shift_bound (ε h : ℝ) (hb : |h| ≤ 2*Real.pi*ε/3) :
    |-h/2| ≤ Real.pi*ε/3 := by
  rw [abs_div,abs_neg,abs_of_pos (by norm_num : (0:ℝ)<2)]
  linarith

theorem displacement_smooth (ε h : ℝ) (hε : 0 < ε)
    (hb : |h| ≤ 2*Real.pi*ε/3) : ContDiff ℝ 1 (displacement ε h) :=
  (inverse_smooth ε (-h/2) hε (half_shift_bound ε h hb)).sub Complex.ofRealCLM.contDiff

theorem coefficient_smooth (ε h : ℝ) (hε : 0 < ε)
    (hb : |h| ≤ 2*Real.pi*ε/3) : ContDiff ℝ 1 (coefficient ε h) :=
  (contDiff_const.mul (displacement_smooth ε h hε hb)).div_const (h:ℂ)

theorem displacement_bound (ε h s : ℝ) (hε : 0 < ε)
    (hb : |h| ≤ 2*Real.pi*ε/3) : ‖displacement ε h s‖ ≤ |h|/(2*ε) := by
  have hr := relative_bound ε (-h/2) s hε (half_shift_bound ε h hb)
  rw [abs_div,abs_neg,abs_of_pos (by norm_num : (0:ℝ)<2)] at hr
  convert hr using 1
  ring

theorem displacement_im_sign (ε h s : ℝ) (hε : 0 < ε) (hh : h ≠ 0)
    (hb : |h| ≤ 2*Real.pi*ε/3) : h * (displacement ε h s).im < 0 := by
  have ha : (argument ε (-h/2) s).im = -h/2 := by simp [argument]
  have hn : (argument ε (-h/2) s).im ≠ 0 := by
    rw [ha]
    exact div_ne_zero (neg_ne_zero.mpr hh) (by norm_num)
  have hp := inverse_im_product_positive ε hε _
    (argument_mem ε (-h/2) s hε (half_shift_bound ε h hb)) hn
  rw [ha] at hp
  simp only [displacement,relative,inverse,Complex.sub_im,Complex.ofReal_im,sub_zero]
  nlinarith

theorem coefficient_re (ε h s : ℝ) :
    (coefficient ε h s).re = -(displacement ε h s).im/h := by
  simp [coefficient,Complex.div_ofReal_re,Complex.mul_re]

theorem coefficient_re_positive (ε h s : ℝ) (hε : 0 < ε) (hh : h ≠ 0)
    (hb : |h| ≤ 2*Real.pi*ε/3) : 0 < (coefficient ε h s).re := by
  have hp := displacement_im_sign ε h s hε hh hb
  have hq := div_pos (neg_pos.mpr hp) (sq_pos_of_ne_zero hh)
  rw [coefficient_re]
  convert hq using 1
  field_simp

theorem coefficient_bound (ε h s : ℝ) (hε : 0 < ε) (hh : h ≠ 0)
    (hb : |h| ≤ 2*Real.pi*ε/3) : ‖coefficient ε h s‖ ≤ 1/(2*ε) := by
  simp only [coefficient,norm_div,norm_mul,Complex.norm_I,one_mul,
    Complex.norm_real,Real.norm_eq_abs]
  apply (div_le_iff₀ (abs_pos.mpr hh)).mpr
  convert displacement_bound ε h s hε hb using 1
  ring

theorem coefficient_generator_identity (ε h s : ℝ) (hh : h ≠ 0) :
    coefficient ε h s * (-(h:ℂ)*Complex.I) = displacement ε h s := by
  have hc : (h:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hh
  unfold coefficient
  field_simp
  linear_combination -(displacement ε h s) * Complex.I_sq

#print axioms inverse_im_product_positive
#print axioms half_shift_bound
#print axioms displacement_smooth
#print axioms coefficient_smooth
#print axioms displacement_bound
#print axioms displacement_im_sign
#print axioms coefficient_re
#print axioms coefficient_re_positive
#print axioms coefficient_bound
#print axioms coefficient_generator_identity
end
end UnifiedTheory.Audit.KFCausalImaginaryShearCoefficient
