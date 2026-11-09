/- First-order expansion of the actual complex clock shift. The error
retains a squared-defect factor, uniformly over the physical clock. -/
import UnifiedTheory.Audit.KFCausalClockFloorClockShiftDifference
import UnifiedTheory.Audit.KFCausalClockFloorComplexDefectDerivative

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

namespace UnifiedTheory.Audit.KFCausalClockFloorClockShiftTaylor
noncomputable section
open Set
open UnifiedTheory.Audit.KFCausalCoupledLongitudinalFlow (Configuration)
open UnifiedTheory.Audit.KFCausalClockFloorFlow (clock)
open UnifiedTheory.Audit.KFCausalRegularizedLongitudinalChart
open UnifiedTheory.Audit.KFCausalComplexClockChart
open UnifiedTheory.Audit.KFCausalComplexClockInverse
open UnifiedTheory.Audit.KFCausalClockFloorComplexDefect
open UnifiedTheory.Audit.KFCausalClockFloorComplexDefectDerivative (inverse_derivative)
open UnifiedTheory.Audit.KFCausalClockFloorDefectShift
open UnifiedTheory.Audit.KFCausalClockFloorShiftedDefect (shift_bound)
open UnifiedTheory.Audit.KFCausalClockFloorClockShiftDifference
open UnifiedTheory.Audit.KFCausalClockFloorCanonicalDefect (defect response response_add_defect)

theorem clock_derivative (ε : ℝ) (hε : 0 < ε) (q : ℂ) (hq : q ∈ targetStrip ε) :
    HasDerivAt (complexClock ε) (1-complexDefect ε q) q := by
  have hd := ((inverse_derivative ε hε q hq).cexp).add_const (ε:ℂ)
  convert hd using 1
  have hn := complexClock_ne_zero ε hε q hq
  unfold complexDefect complexClock
  unfold complexClock at hn
  field_simp
  ring

theorem vertical_clock_derivative (ε : ℝ) (hε : 0 < ε) (q y : ℝ)
    (hy : |y| ≤ Real.pi*ε/3) :
    HasDerivAt (fun r : ℝ => complexClock ε ((q:ℂ)+(r:ℂ)*Complex.I))
      (Complex.I*(1-complexDefect ε ((q:ℂ)+(y:ℂ)*Complex.I))) y := by
  have ht : (q:ℂ)+(y:ℂ)*Complex.I ∈ targetStrip ε :=
    KFCausalClockFloorFullGaussian.third_strip_subset ε hε _ (by simpa using hy)
  have hd := (clock_derivative ε hε _ ht).comp (y:ℂ)
    (((hasDerivAt_id (y:ℂ)).mul_const Complex.I).const_add (q:ℂ))
  simpa [Function.comp_def,mul_comm] using hd.comp_ofReal

theorem vertical_remainder (ε : ℝ) (hε : 0 < ε) (q y : ℝ)
    (hy : |y| ≤ Real.pi*ε/3) :
    ‖complexClock ε ((q:ℂ)+(y:ℂ)*Complex.I)-complexClock ε (q:ℂ)-
      (y:ℂ)*Complex.I*(1-(realDefect ε hε q:ℂ))‖ ≤
      (4*|y|^2/ε)*(realDefect ε hε q)^2 := by
  let d := realDefect ε hε q
  let f : ℝ → ℂ := fun r => complexClock ε ((q:ℂ)+(r:ℂ)*Complex.I)-complexClock ε (q:ℂ)-
    (r:ℂ)*Complex.I*(1-(d:ℂ))
  have hd (r : ℝ) (hr : |r| ≤ Real.pi*ε/3) :
      HasDerivAt f (Complex.I*((d:ℂ)-complexDefect ε ((q:ℂ)+(r:ℂ)*Complex.I))) r := by
    have hlin := (((hasDerivAt_id r).ofReal_comp.mul_const Complex.I).mul_const (1-(d:ℂ)))
    convert ((vertical_clock_derivative ε hε q r hr).sub_const (complexClock ε (q:ℂ))).sub hlin using 1
    simp only [Complex.ofReal_one,one_mul]
    ring
  have hb (r : ℝ) (hr : r ∈ uIcc 0 y) : |r| ≤ |y| :=
    by simpa only [sub_zero] using abs_sub_left_of_mem_uIcc hr
  have hs := (convex_uIcc (0:ℝ) y).norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun r hr => (hd r ((hb r hr).trans hy)).hasDerivWithinAt)
    (fun r hr => show ‖Complex.I*((d:ℂ)-complexDefect ε ((q:ℂ)+(r:ℂ)*Complex.I))‖ ≤
        (4*|y|/ε)*d^2 by
      rw [norm_mul,Complex.norm_I,one_mul,norm_sub_rev]
      have ht : ‖complexDefect ε ((q:ℂ)+(r:ℂ)*Complex.I)-(d:ℂ)‖ ≤ (4*|r|/ε)*d^2 := by
        simpa [d] using complexDefect_vertical_difference ε hε ((q:ℂ)+(r:ℂ)*Complex.I)
          (by simpa using (hb r hr).trans hy)
      exact ht.trans (mul_le_mul_of_nonneg_right
        (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left (hb r hr) (by norm_num)) hε.le)
        (sq_nonneg d))) left_mem_uIcc right_mem_uIcc
  have h0 : f 0 = 0 := by simp [f]
  rw [h0,sub_zero,sub_zero,Real.norm_eq_abs] at hs
  change ‖f y‖ ≤ _
  convert hs using 1
  ring

theorem real_defect_chart (ε : ℝ) (hε : 0 < ε) (x : Configuration) :
    realDefect ε hε (chart ε x.1) = defect ε x.1 := by
  change defect ε ((chartIso ε hε).symm ((chartIso ε hε) x.1)) = _
  rw [(chartIso ε hε).symm_apply_apply]

theorem difference_first_order_bound (ε : ℝ) (hε : 0 < ε) (h : ℝ)
    (hh : |h| ≤ 2*Real.pi*ε/3) (x : Configuration) :
    ‖difference ε h x-(Complex.I*(h:ℂ)/2)*(response ε x.1:ℂ)‖ ≤
      (h^2/ε)*(defect ε x.1)^2 := by
  have hb := vertical_remainder ε hε (chart ε x.1) (-h/2) (shift_bound ε h hh)
  rw [real_clock_chart ε hε x,real_defect_chart ε hε x] at hb
  have hr : (response ε x.1:ℂ)+(defect ε x.1:ℂ) = 1 := by
    exact_mod_cast response_add_defect ε x.1 hε.le
  have he : difference ε h x-(Complex.I*(h:ℂ)/2)*(response ε x.1:ℂ) =
      -(complexClock ε ((chart ε x.1:ℂ)+(-h/2:ℝ)*Complex.I)-(clock ε x.1:ℂ)-
        ((-h/2:ℝ):ℂ)*Complex.I*(1-(defect ε x.1:ℂ))) := by
    unfold difference shiftedClock
    push_cast
    linear_combination -(Complex.I*(h:ℂ)/2)*hr
  rw [he,norm_neg]
  convert hb using 1
  rw [abs_div,abs_neg,abs_of_pos (by norm_num : (0:ℝ) < 2),div_pow,sq_abs]
  ring

#print axioms clock_derivative
#print axioms vertical_clock_derivative
#print axioms vertical_remainder
#print axioms real_defect_chart
#print axioms difference_first_order_bound

end
end UnifiedTheory.Audit.KFCausalClockFloorClockShiftTaylor
