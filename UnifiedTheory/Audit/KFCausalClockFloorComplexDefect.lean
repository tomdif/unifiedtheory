/- Analytic continuation of the actual clock defect through the already
constructed clock inverse. The bounds compare a complex horizontal-line
value with the real defect at the same straightened clock coordinate. -/
import UnifiedTheory.Audit.KFCausalClockInverseStripBounds
import UnifiedTheory.Audit.KFCausalClockFloorCanonicalDefect

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 800000

namespace UnifiedTheory.Audit.KFCausalClockFloorComplexDefect
noncomputable section
open Set
open UnifiedTheory.Audit.KFCausalComplexClockChart
open UnifiedTheory.Audit.KFCausalComplexClockInverse
open UnifiedTheory.Audit.KFCausalClockInverseStripBounds
open UnifiedTheory.Audit.KFCausalRegularizedLongitudinalChart
open UnifiedTheory.Audit.KFCausalClockFloorFlow (clock)
open UnifiedTheory.Audit.KFCausalClockFloorCanonicalDefect (defect clock_positive defect_positive)

def complexClock (ε : ℝ) (q : ℂ) : ℂ := Complex.exp (complexInverse ε q) + (ε:ℂ)
def complexDefect (ε : ℝ) (q : ℂ) : ℂ := (ε:ℂ) / complexClock ε q
def realClock (ε : ℝ) (hε : 0 < ε) (q : ℝ) : ℝ := clock ε ((chartIso ε hε).symm q)
def realDefect (ε : ℝ) (hε : 0 < ε) (q : ℝ) : ℝ := defect ε ((chartIso ε hε).symm q)

theorem realClock_positive (ε : ℝ) (hε : 0 < ε) (q : ℝ) : 0 < realClock ε hε q :=
  clock_positive ε _ hε.le

theorem realDefect_positive (ε : ℝ) (hε : 0 < ε) (q : ℝ) : 0 < realDefect ε hε q :=
  defect_positive ε _ hε

theorem complexClock_real (ε : ℝ) (hε : 0 < ε) (q : ℝ) :
    complexClock ε (q:ℂ) = (realClock ε hε q : ℂ) := by
  simp only [complexClock, complexInverse_real ε hε, realClock, clock,
    Complex.ofReal_add, Complex.ofReal_exp]

theorem complexDefect_real (ε : ℝ) (hε : 0 < ε) (q : ℝ) :
    complexDefect ε (q:ℂ) = (realDefect ε hε q : ℂ) := by
  rw [complexDefect, complexClock_real ε hε q]
  simp only [realDefect, defect, realClock, Complex.ofReal_div]

theorem complexClock_ne_zero (ε : ℝ) (hε : 0 < ε) (q : ℂ) (hq : q ∈ targetStrip ε) :
    complexClock ε q ≠ 0 :=
  complexChart_derivative_ne_zero ε hε _
    (show |(complexInverse ε q).im| ≤ Real.pi/2 from
      le_of_lt (complexInverse_mem ε hε q hq))

theorem complexDefect_analytic (ε : ℝ) (hε : 0 < ε) (q : ℂ) (hq : q ∈ targetStrip ε) :
    AnalyticAt ℂ (complexDefect ε) q := by
  exact analyticAt_const.div
    (((complexInverse_analytic ε hε q hq).cexp).add analyticAt_const)
    (complexClock_ne_zero ε hε q hq)

/-- On a vertical line the real part of the inverse never lies to the
left of the real inverse at the same real clock coordinate. -/
theorem inverse_re_ge_real (ε : ℝ) (hε : 0 < ε) (q : ℂ) (hq : q ∈ targetStrip ε) :
    (chartIso ε hε).symm q.re ≤ (complexInverse ε q).re := by
  have he := congrArg Complex.re (complexInverse_right ε hε q hq)
  rw [complexChart_re] at he
  have hr : chart ε ((chartIso ε hε).symm q.re) = q.re := (chartIso ε hε).apply_symm_apply _
  apply (chart_strictMono ε hε).le_iff_le.mp
  rw [hr]
  unfold chart
  have hc := mul_le_of_le_one_right (Real.exp_pos (complexInverse ε q).re).le
    (Real.cos_le_one (complexInverse ε q).im)
  linarith

theorem complexClock_norm_lower (ε : ℝ) (hε : 0 < ε) (q : ℂ)
    (hq : |q.im| ≤ Real.pi*ε/3) :
    realClock ε hε q.re / 2 ≤ ‖complexClock ε q‖ := by
  have ht : q ∈ targetStrip ε := by change |q.im| ≤ Real.pi*ε/2; nlinarith [Real.pi_pos]
  have he := inverse_exp_re_lower ε hε q hq
  have hr := Real.exp_le_exp.mpr (inverse_re_ge_real ε hε q ht)
  have hn := (Complex.re_le_norm (complexClock ε q))
  simp only [complexClock, Complex.add_re, Complex.ofReal_re] at hn
  unfold realClock clock complexClock
  linarith

theorem complexDefect_norm_bound (ε : ℝ) (hε : 0 < ε) (q : ℂ)
    (hq : |q.im| ≤ Real.pi*ε/3) :
    ‖complexDefect ε q‖ ≤ 2 * realDefect ε hε q.re := by
  have hc := realClock_positive ε hε q.re
  rw [complexDefect, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hε]
  have h := div_le_div_of_nonneg_left hε.le (half_pos hc) (complexClock_norm_lower ε hε q hq)
  change ε / ‖complexClock ε q‖ ≤ 2 * (ε / realClock ε hε q.re)
  convert h using 1
  ring

theorem complexDefect_norm_le_two (ε : ℝ) (hε : 0 < ε) (q : ℂ)
    (hq : |q.im| ≤ Real.pi*ε/3) : ‖complexDefect ε q‖ ≤ 2 := by
  apply (complexDefect_norm_bound ε hε q hq).trans
  have he : realDefect ε hε q.re ≤ 1 := by
    unfold realDefect defect
    apply (div_le_one (clock_positive ε _ hε.le)).mpr
    unfold clock
    linarith [Real.exp_pos ((chartIso ε hε).symm q.re)]
  linarith

#print axioms complexClock_real
#print axioms complexDefect_real
#print axioms complexClock_ne_zero
#print axioms complexDefect_analytic
#print axioms inverse_re_ge_real
#print axioms complexClock_norm_lower
#print axioms complexDefect_norm_bound
#print axioms complexDefect_norm_le_two

end
end UnifiedTheory.Audit.KFCausalClockFloorComplexDefect
