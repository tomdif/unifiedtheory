/- Quantitative inverse-clock bounds on narrower strips. These use the
already constructed analytic inverse; no new inverse branch is assumed. -/
import UnifiedTheory.Audit.KFCausalComplexClockWeights

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 800000

namespace UnifiedTheory.Audit.KFCausalClockInverseStripBounds
noncomputable section
open Set
open UnifiedTheory.Audit.KFCausalComplexClockChart
open UnifiedTheory.Audit.KFCausalComplexClockInverse
open UnifiedTheory.Audit.KFCausalComplexClockWeights

theorem inverse_im_bound (ε : ℝ) (hε : 0 < ε) (q : ℂ) (hq : q ∈ targetStrip ε) :
    |(complexInverse ε q).im| ≤ |q.im|/ε := by
  have hr : (q.re:ℂ) ∈ targetStrip ε := by
    change |(q.re:ℂ).im| ≤ Real.pi*ε/2
    simp only [Complex.ofReal_im,abs_zero]
    positivity
  have hb := complexInverse_norm_bound ε hε q (q.re:ℂ) hq hr
  have hi := Complex.abs_im_le_norm (complexInverse ε q - complexInverse ε (q.re:ℂ))
  rw [Complex.sub_im,complexInverse_real ε hε,Complex.ofReal_im,sub_zero] at hi
  have he : q-(q.re:ℂ) = (q.im:ℂ)*Complex.I := by
    apply Complex.ext <;> simp
  rw [he,norm_mul,Complex.norm_I,mul_one,Complex.norm_real,Real.norm_eq_abs] at hb
  rw [complexInverse_real ε hε] at hb
  exact hi.trans hb

theorem inverse_im_third_strip (ε : ℝ) (hε : 0 < ε) (q : ℂ)
    (hq : |q.im| ≤ Real.pi*ε/3) : |(complexInverse ε q).im| ≤ Real.pi/3 := by
  have ht : q ∈ targetStrip ε := by
    change |q.im| ≤ Real.pi*ε/2
    nlinarith [Real.pi_pos]
  exact (inverse_im_bound ε hε q ht).trans ((div_le_iff₀ hε).mpr (by nlinarith))

theorem cos_lower_third (y : ℝ) (hy : |y| ≤ Real.pi/3) : 1/2 ≤ Real.cos y := by
  have hc := Real.cos_le_cos_of_nonneg_of_le_pi (abs_nonneg y)
    (by linarith [Real.pi_pos] : Real.pi/3 ≤ Real.pi) hy
  simpa only [Real.cos_pi_div_three,Real.cos_abs] using hc

theorem inverse_exp_re_lower (ε : ℝ) (hε : 0 < ε) (q : ℂ)
    (hq : |q.im| ≤ Real.pi*ε/3) :
    Real.exp (complexInverse ε q).re / 2 ≤ (Complex.exp (complexInverse ε q)).re := by
  rw [Complex.exp_re]
  have hc := cos_lower_third _ (inverse_im_third_strip ε hε q hq)
  nlinarith [mul_le_mul_of_nonneg_left hc (Real.exp_pos (complexInverse ε q).re).le]

theorem inverse_negative_power_bound (ε p : ℝ) (hε : 0 < ε) (hp : 0 ≤ p)
    (q : ℂ) (hq : q ∈ targetStrip ε) :
    Real.exp (-p*(complexInverse ε q).re) ≤ 1 + Real.exp (p*(1-q.re)/ε) := by
  by_cases hs : 0 ≤ (complexInverse ε q).re
  · have he : Real.exp (-p*(complexInverse ε q).re) ≤ 1 :=
      Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hp) hs)
    linarith [Real.exp_pos (p*(1-q.re)/ε)]
  · have hl := complexInverse_re_lower_of_nonpos ε hε q hq (le_of_not_ge hs)
    have hb := mul_le_mul_of_nonneg_left hl hp
    have he : -p*(complexInverse ε q).re ≤ p*(1-q.re)/ε := by
      have hid : p*((q.re-1)/ε) = -(p*(1-q.re)/ε) := by ring
      rw [hid] at hb
      linarith
    linarith [Real.exp_le_exp.mpr he]

#print axioms inverse_im_bound
#print axioms inverse_im_third_strip
#print axioms cos_lower_third
#print axioms inverse_exp_re_lower
#print axioms inverse_negative_power_bound

end
end UnifiedTheory.Audit.KFCausalClockInverseStripBounds
