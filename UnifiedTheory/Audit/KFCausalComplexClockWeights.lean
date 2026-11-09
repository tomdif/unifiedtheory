/- Growth bounds for the analytic clock inverse and the coefficients of
the transverse field after straightening. Bounds hold at the closed strip
boundary; they are not a regulator-removal theorem. -/
import UnifiedTheory.Audit.KFCausalComplexClockInverse

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 800000

namespace UnifiedTheory.Audit.KFCausalComplexClockWeights
noncomputable section
open Set
open UnifiedTheory.Audit.KFCausalComplexClockChart
open UnifiedTheory.Audit.KFCausalComplexClockInverse

theorem complexInverse_re_upper (ε : ℝ) (hε : 0 < ε) (q : ℂ) (hq : q ∈ targetStrip ε) :
    (complexInverse ε q).re ≤ q.re/ε := by
  apply (le_div_iff₀ hε).mpr
  have he := congrArg Complex.re (complexInverse_right ε hε q hq)
  rw [complexChart_re] at he
  have hn := strip_exp_re_nonnegative (complexInverse ε q)
    (show |(complexInverse ε q).im| ≤ Real.pi/2 from le_of_lt (complexInverse_mem ε hε q hq))
  rw [Complex.exp_re] at hn
  nlinarith

theorem complexInverse_re_lower_of_nonpos (ε : ℝ) (hε : 0 < ε) (q : ℂ)
    (hq : q ∈ targetStrip ε) (hu : (complexInverse ε q).re ≤ 0) :
    (q.re-1)/ε ≤ (complexInverse ε q).re := by
  apply (div_le_iff₀ hε).mpr
  have he := congrArg Complex.re (complexInverse_right ε hε q hq)
  rw [complexChart_re] at he
  have hb : Real.exp (complexInverse ε q).re*Real.cos (complexInverse ε q).im ≤ 1 :=
    (mul_le_of_le_one_right (Real.exp_pos _).le (Real.cos_le_one _)).trans
      (Real.exp_le_one_iff.mpr hu)
  nlinarith

theorem complexInverse_inverse_clock_bound (ε : ℝ) (hε : 0 < ε) (q : ℂ)
    (hq : q ∈ targetStrip ε) :
    Real.exp (-(complexInverse ε q).re) ≤ 1+Real.exp ((1-q.re)/ε) := by
  by_cases hu : 0 ≤ (complexInverse ε q).re
  · have he := Real.exp_le_one_iff.mpr (neg_nonpos.mpr hu)
    linarith [Real.exp_pos ((1-q.re)/ε)]
  · have hl := complexInverse_re_lower_of_nonpos ε hε q hq (le_of_not_ge hu)
    have he : -(complexInverse ε q).re ≤ (1-q.re)/ε := by
      have hr : (1-q.re)/ε= -((q.re-1)/ε) := by ring
      rw [hr]
      linarith
    linarith [Real.exp_le_exp.mpr he]

def complexPhase (ε : ℝ) (z : ℂ) : ℂ := z-(ε:ℂ)*Complex.exp (-z)
def fieldCoefficient (ε j : ℝ) (q : ℂ) : ℂ :=
  Complex.exp (((j/2:ℝ):ℂ)*complexPhase ε (complexInverse ε q))

theorem complexPhase_analytic (ε : ℝ) (z : ℂ) : AnalyticAt ℂ (complexPhase ε) z := by
  unfold complexPhase
  fun_prop

theorem complexPhase_re_upper (ε : ℝ) (hε : 0 ≤ ε) (z : ℂ) (hz : z ∈ closedStrip) :
    (complexPhase ε z).re ≤ z.re := by
  have hn : -z ∈ closedStrip := by
    change |(-z).im| ≤ Real.pi/2
    simpa only [Complex.neg_im,abs_neg] using hz
  have hp := mul_nonneg hε (strip_exp_re_nonnegative (-z) hn)
  simpa only [complexPhase,Complex.sub_re,Complex.mul_re,Complex.ofReal_re,
    Complex.ofReal_im,zero_mul,sub_zero,sub_le_self_iff] using hp

theorem fieldCoefficient_analytic (ε j : ℝ) (hε : 0 < ε) (q : ℂ) (hq : q ∈ targetStrip ε) :
    AnalyticAt ℂ (fieldCoefficient ε j) q := by
  have h := (complexPhase_analytic ε (complexInverse ε q)).comp (complexInverse_analytic ε hε q hq)
  exact (analyticAt_const.mul h).cexp

theorem fieldCoefficient_norm_bound (ε j : ℝ) (hε : 0 < ε) (hj : 0 ≤ j)
    (q : ℂ) (hq : q ∈ targetStrip ε) :
    ‖fieldCoefficient ε j q‖ ≤ Real.exp (j*q.re/(2*ε)) := by
  rw [fieldCoefficient,Complex.norm_exp]
  apply Real.exp_le_exp.mpr
  simp only [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]
  have hp := complexPhase_re_upper ε hε.le (complexInverse ε q)
    (show |(complexInverse ε q).im| ≤ Real.pi/2 from le_of_lt (complexInverse_mem ε hε q hq))
  have hb := mul_le_mul_of_nonneg_left (hp.trans (complexInverse_re_upper ε hε q hq))
    (show 0 ≤ j/2 by positivity)
  convert hb using 1
  ring

#print axioms complexInverse_re_upper
#print axioms complexInverse_re_lower_of_nonpos
#print axioms complexInverse_inverse_clock_bound
#print axioms complexPhase_analytic
#print axioms complexPhase_re_upper
#print axioms fieldCoefficient_analytic
#print axioms fieldCoefficient_norm_bound

end
end UnifiedTheory.Audit.KFCausalComplexClockWeights
