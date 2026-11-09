/- Strict signs for the actual analytic clock shift. Nonzero hbar makes
its imaginary shift nonzero, so no nonzero output can have zero drift. -/
import UnifiedTheory.Audit.KFCausalClockFloorDefectSign
import UnifiedTheory.Audit.KFCausalClockFloorShiftedDefectPhysical

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

namespace UnifiedTheory.Audit.KFCausalClockFloorStrictDefectSign
noncomputable section
open UnifiedTheory.Audit.KFCausalComplexClockChart
open UnifiedTheory.Audit.KFCausalComplexClockInverse
open UnifiedTheory.Audit.KFCausalClockFloorComplexDefect
open UnifiedTheory.Audit.KFCausalClockFloorDefectSign
open UnifiedTheory.Audit.KFCausalClockFloorShiftedDefectPhysical
open UnifiedTheory.Audit.KFCausalCoupledLongitudinalFlow (Configuration)

theorem strip_im_sin_positive (z : ℂ) (hz : |z.im| < Real.pi/2) (hn : z.im ≠ 0) :
    0 < z.im*Real.sin z.im := by
  obtain ⟨hl,hu⟩ := abs_lt.mp hz
  rcases lt_or_gt_of_ne hn with h | h
  · exact mul_pos_of_neg_of_neg h (Real.sin_neg_of_neg_of_neg_pi_lt h (by linarith [Real.pi_pos]))
  · exact mul_pos h (Real.sin_pos_of_pos_of_lt_pi h (by linarith [Real.pi_pos]))

theorem complexClock_im_strict_sign (ε : ℝ) (hε : 0 < ε) (q : ℂ)
    (hq : q ∈ targetStrip ε) (hn : q.im ≠ 0) : 0 < q.im*(complexClock ε q).im := by
  let z := complexInverse ε q
  have hi := congrArg Complex.im (complexInverse_right ε hε q hq)
  rw [complexChart_im] at hi
  change Real.exp z.re*Real.sin z.im+ε*z.im=q.im at hi
  have hz : z.im ≠ 0 := by
    intro he
    apply hn
    rw [he,Real.sin_zero,mul_zero,mul_zero,zero_add] at hi
    exact hi.symm
  have hp := mul_pos (mul_pos hε (Real.exp_pos z.re))
    (strip_im_sin_positive z (complexInverse_mem ε hε q hq) hz)
  simp only [complexClock,Complex.add_im,Complex.ofReal_im,add_zero,Complex.exp_im]
  change 0 < q.im*(Real.exp z.re*Real.sin z.im)
  rw [← hi]
  nlinarith [sq_nonneg (Real.exp z.re*Real.sin z.im)]

theorem complexDefect_im_strict_sign (ε : ℝ) (hε : 0 < ε) (q : ℂ)
    (hq : q ∈ targetStrip ε) (hn : q.im ≠ 0) : q.im*(complexDefect ε q).im < 0 := by
  have hc : complexClock ε q ≠ 0 := by
    intro he
    have hp := complexClock_re_positive ε hε q hq
    rw [he,Complex.zero_re] at hp
    exact (lt_irrefl 0) hp
  have hp := div_pos (mul_pos hε (complexClock_im_strict_sign ε hε q hq hn))
    (Complex.normSq_pos.mpr hc)
  simp only [complexDefect,Complex.div_im,Complex.ofReal_re,Complex.ofReal_im,zero_mul,zero_div,zero_sub]
  convert neg_neg_of_pos hp using 1
  ring

theorem half_exponential_strict_sign (ε hbar q : ℝ) (hε : 0 < ε)
    (hh : hbar ≠ 0) (hb : |hbar| ≤ 2*Real.pi*ε/3) :
    0 < hbar*(complexDefect ε ((q:ℂ)+(-hbar/2:ℝ)*Complex.I)).im := by
  have ht : ((q:ℂ)+(-hbar/2:ℝ)*Complex.I) ∈ targetStrip ε := by
    change |(((q:ℂ)+(-hbar/2:ℝ)*Complex.I):ℂ).im| ≤ Real.pi*ε/2
    simp only [Complex.add_im,Complex.ofReal_im,Complex.mul_im,Complex.ofReal_re,
      Complex.I_im,Complex.I_re,mul_one,mul_zero,add_zero,zero_add,abs_div,abs_neg]
    rw [abs_of_pos (by norm_num : (0:ℝ)<2)]
    nlinarith [Real.pi_pos]
  have hn : (((q:ℂ)+(-hbar/2:ℝ)*Complex.I):ℂ).im ≠ 0 := by
    simpa using div_ne_zero (neg_ne_zero.mpr hh) (by norm_num : (2:ℝ) ≠ 0)
  have h := complexDefect_im_strict_sign ε hε _ ht hn
  simp only [Complex.add_im,Complex.ofReal_im,Complex.mul_im,Complex.ofReal_re,
    Complex.I_im,Complex.I_re,mul_one,mul_zero,add_zero,zero_add] at h
  nlinarith

theorem half_exponential_velocity_negative (ε hbar q : ℝ) (hε : 0 < ε)
    (hh : hbar ≠ 0) (hb : |hbar| ≤ 2*Real.pi*ε/3) :
    (-2/hbar)*(complexDefect ε ((q:ℂ)+(-hbar/2:ℝ)*Complex.I)).im < 0 := by
  have hp := half_exponential_strict_sign ε hbar q hε hh hb
  have hs := div_pos hp (sq_pos_of_ne_zero hh)
  have he : (-2/hbar)*(complexDefect ε ((q:ℂ)+(-hbar/2:ℝ)*Complex.I)).im =
      -2*(hbar*(complexDefect ε ((q:ℂ)+(-hbar/2:ℝ)*Complex.I)).im/hbar^2) := by
    field_simp
  rw [he]
  exact mul_neg_of_neg_of_pos (by norm_num) hs

theorem physicalSymbol_velocity_negative (ε hbar : ℝ) (hε : 0 < ε)
    (hh : hbar ≠ 0) (hb : |hbar| ≤ 2*Real.pi*ε/3) (x : Configuration) :
    (-2/hbar)*(physicalSymbol ε hbar x).im < 0 :=
  half_exponential_velocity_negative ε hbar _ hε hh hb

theorem complexDefect_re_positive (ε : ℝ) (hε : 0 < ε) (q : ℂ)
    (hq : q ∈ targetStrip ε) : 0 < (complexDefect ε q).re := by
  have hc : complexClock ε q ≠ 0 := by
    intro he
    have hp := complexClock_re_positive ε hε q hq
    rw [he,Complex.zero_re] at hp
    exact (lt_irrefl 0) hp
  simp only [complexDefect,Complex.div_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,zero_div,add_zero]
  exact div_pos (mul_pos hε (complexClock_re_positive ε hε q hq)) (Complex.normSq_pos.mpr hc)

theorem half_exponential_re_positive (ε hbar q : ℝ) (hε : 0 < ε)
    (hb : |hbar| ≤ 2*Real.pi*ε/3) :
    0 < (complexDefect ε ((q:ℂ)+(-hbar/2:ℝ)*Complex.I)).re := by
  apply complexDefect_re_positive ε hε
  change |(((q:ℂ)+(-hbar/2:ℝ)*Complex.I):ℂ).im| ≤ Real.pi*ε/2
  simp only [Complex.add_im,Complex.ofReal_im,Complex.mul_im,Complex.ofReal_re,
    Complex.I_im,Complex.I_re,mul_one,mul_zero,add_zero,zero_add,abs_div,abs_neg]
  rw [abs_of_pos (by norm_num : (0:ℝ)<2)]
  nlinarith [Real.pi_pos]

theorem half_exponential_square_velocity_negative (ε hbar q : ℝ) (hε : 0 < ε)
    (hh : hbar ≠ 0) (hb : |hbar| ≤ 2*Real.pi*ε/3) :
    (-2/hbar)*(complexDefect ε ((q:ℂ)+(-hbar/2:ℝ)*Complex.I)^2).im < 0 := by
  have hn := mul_neg_of_pos_of_neg
    (mul_pos (by norm_num : (0:ℝ)<2) (half_exponential_re_positive ε hbar q hε hb))
    (half_exponential_velocity_negative ε hbar q hε hh hb)
  rw [pow_two,Complex.mul_im]
  convert hn using 1
  ring

theorem physicalSymbol_square_velocity_negative (ε hbar : ℝ) (hε : 0 < ε)
    (hh : hbar ≠ 0) (hb : |hbar| ≤ 2*Real.pi*ε/3) (x : Configuration) :
    (-2/hbar)*(physicalSymbol ε hbar x^2).im < 0 :=
  half_exponential_square_velocity_negative ε hbar _ hε hh hb

#print axioms complexDefect_re_positive
#print axioms half_exponential_re_positive
#print axioms half_exponential_square_velocity_negative
#print axioms physicalSymbol_square_velocity_negative

#print axioms strip_im_sin_positive
#print axioms complexClock_im_strict_sign
#print axioms complexDefect_im_strict_sign
#print axioms half_exponential_strict_sign
#print axioms half_exponential_velocity_negative
#print axioms physicalSymbol_velocity_negative

end
end UnifiedTheory.Audit.KFCausalClockFloorStrictDefectSign
