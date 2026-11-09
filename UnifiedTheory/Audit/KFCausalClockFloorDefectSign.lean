/- The imaginary part of the squared analytic defect has a definite sign
at the actual longitudinal exponential shift. This scalar result will be
transported to an operator form pairing, without postulating dynamics. -/
import UnifiedTheory.Audit.KFCausalClockFloorDefectShift

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 800000

namespace UnifiedTheory.Audit.KFCausalClockFloorDefectSign
noncomputable section
open UnifiedTheory.Audit.KFCausalComplexClockChart
open UnifiedTheory.Audit.KFCausalComplexClockInverse
open UnifiedTheory.Audit.KFCausalClockFloorComplexDefect

theorem strip_im_sin_nonnegative (z : ℂ) (hz : z ∈ closedStrip) :
    0 ≤ z.im * Real.sin z.im := by
  change |z.im| ≤ Real.pi/2 at hz
  obtain ⟨hl,hu⟩ := abs_le.mp hz
  by_cases h : 0 ≤ z.im
  · exact mul_nonneg h (Real.sin_nonneg_of_nonneg_of_le_pi h (by linarith [Real.pi_pos]))
  · exact mul_nonneg_of_nonpos_of_nonpos (le_of_not_ge h)
      (Real.sin_nonpos_of_nonpos_of_neg_pi_le (le_of_not_ge h) (by linarith [Real.pi_pos]))

theorem complexClock_re_positive (ε : ℝ) (hε : 0 < ε) (q : ℂ) (hq : q ∈ targetStrip ε) :
    0 < (complexClock ε q).re := by
  have hz : complexInverse ε q ∈ closedStrip := by
    change |(complexInverse ε q).im| ≤ Real.pi/2
    exact le_of_lt (complexInverse_mem ε hε q hq)
  have he := strip_exp_re_nonnegative (complexInverse ε q) hz
  simp only [complexClock,Complex.add_re,Complex.ofReal_re]
  linarith

theorem complexClock_im_sign (ε : ℝ) (hε : 0 < ε) (q : ℂ) (hq : q ∈ targetStrip ε) :
    0 ≤ q.im * (complexClock ε q).im := by
  let z := complexInverse ε q
  have hz : z ∈ closedStrip := by
    change |(complexInverse ε q).im| ≤ Real.pi/2
    exact le_of_lt (complexInverse_mem ε hε q hq)
  have hi := congrArg Complex.im (complexInverse_right ε hε q hq)
  rw [complexChart_im] at hi
  change Real.exp z.re * Real.sin z.im + ε*z.im = q.im at hi
  have hp := mul_nonneg (mul_nonneg hε.le (Real.exp_pos z.re).le) (strip_im_sin_nonnegative z hz)
  simp only [complexClock,Complex.add_im,Complex.ofReal_im,add_zero,Complex.exp_im]
  change 0 ≤ q.im*(Real.exp z.re*Real.sin z.im)
  rw [← hi]
  nlinarith [sq_nonneg (Real.exp z.re*Real.sin z.im)]

theorem complexDefect_re_nonnegative (ε : ℝ) (hε : 0 < ε) (q : ℂ) (hq : q ∈ targetStrip ε) :
    0 ≤ (complexDefect ε q).re := by
  simp only [complexDefect,Complex.div_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,zero_div,add_zero]
  exact div_nonneg (mul_nonneg hε.le (complexClock_re_positive ε hε q hq).le) (Complex.normSq_nonneg _)

theorem complexDefect_im_sign (ε : ℝ) (hε : 0 < ε) (q : ℂ) (hq : q ∈ targetStrip ε) :
    q.im * (complexDefect ε q).im ≤ 0 := by
  simp only [complexDefect,Complex.div_im,Complex.ofReal_re,Complex.ofReal_im,zero_mul,zero_div,zero_sub]
  have hp := div_nonneg (mul_nonneg hε.le (complexClock_im_sign ε hε q hq)) (Complex.normSq_nonneg (complexClock ε q))
  convert neg_nonpos.mpr hp using 1
  ring

theorem complexDefect_square_im_sign (ε : ℝ) (hε : 0 < ε) (q : ℂ) (hq : q ∈ targetStrip ε) :
    q.im * (complexDefect ε q ^ 2).im ≤ 0 := by
  have hp := mul_nonpos_of_nonneg_of_nonpos
    (mul_nonneg (by norm_num : (0:ℝ) ≤ 2) (complexDefect_re_nonnegative ε hε q hq))
    (complexDefect_im_sign ε hε q hq)
  rw [pow_two,Complex.mul_im]
  nlinarith

theorem half_exponential_square_sign (ε hbar q : ℝ) (hε : 0 < ε)
    (hh : |hbar| ≤ 2*Real.pi*ε/3) :
    0 ≤ hbar * (complexDefect ε ((q:ℂ)+(-hbar/2:ℝ)*Complex.I)^2).im := by
  have hy : |-hbar/2| ≤ Real.pi*ε/3 := by
    rw [abs_div,abs_neg,abs_of_pos (by norm_num : (0:ℝ)<2)]
    linarith
  have ht : ((q:ℂ)+(-hbar/2:ℝ)*Complex.I) ∈ targetStrip ε := by
    change |(((q:ℂ)+(-hbar/2:ℝ)*Complex.I):ℂ).im| ≤ Real.pi*ε/2
    simp only [Complex.add_im,Complex.ofReal_im,Complex.mul_im,Complex.ofReal_re,
      Complex.I_im,Complex.I_re,mul_one,mul_zero,add_zero,zero_add]
    nlinarith [Real.pi_pos]
  have h := complexDefect_square_im_sign ε hε _ ht
  simp only [Complex.add_im,Complex.ofReal_im,Complex.mul_im,Complex.ofReal_re,
    Complex.I_im,Complex.I_re,mul_one,mul_zero,add_zero,zero_add] at h
  nlinarith

#print axioms strip_im_sin_nonnegative
#print axioms complexClock_re_positive
#print axioms complexClock_im_sign
#print axioms complexDefect_re_nonnegative
#print axioms complexDefect_im_sign
#print axioms complexDefect_square_im_sign
#print axioms half_exponential_square_sign

end
end UnifiedTheory.Audit.KFCausalClockFloorDefectSign
