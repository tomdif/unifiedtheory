/- The exact clock-production multiplier has a quantitative positive sign.
It lies between half the classical clock response and one. -/
import UnifiedTheory.Audit.KFCausalClockFloorClockShiftDifference
import UnifiedTheory.Audit.KFCausalClockFloorStrictDefectSign
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.Real.Pi.Bounds

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1200000

namespace UnifiedTheory.Audit.KFCausalClockFloorClockVelocity
noncomputable section
open UnifiedTheory.Audit.KFCausalCoupledLongitudinalFlow (Configuration)
open UnifiedTheory.Audit.KFCausalClockFloorClockShiftDifference
open UnifiedTheory.Audit.KFCausalClockFloorComplexDefect
open UnifiedTheory.Audit.KFCausalComplexClockChart
open UnifiedTheory.Audit.KFCausalComplexClockInverse
open UnifiedTheory.Audit.KFCausalRegularizedLongitudinalChart (chart chartIso)

theorem sine_ratio_bounds (v : ℝ) (hv : v ≠ 0) (hb : |v| ≤ Real.pi/2) :
    1/2 ≤ Real.sin v/v ∧ Real.sin v/v ≤ 1 := by
  have hp (x : ℝ) (hx : 0 < x) (hxb : x ≤ Real.pi/2) :
      1/2 ≤ Real.sin x/x ∧ Real.sin x/x ≤ 1 := by
    have hπ : (1:ℝ)/2 ≤ 2/Real.pi := (le_div_iff₀ Real.pi_pos).mpr (by linarith [Real.pi_lt_four])
    refine ⟨(le_div_iff₀ hx).mpr ?_,(div_le_one hx).mpr (Real.sin_le hx.le)⟩
    exact (mul_le_mul_of_nonneg_right hπ hx.le).trans (Real.mul_le_sin hx.le hxb)
  rcases lt_or_gt_of_ne hv with hn | hn
  · have ht := hp (-v) (neg_pos.mpr hn) (by linarith [(abs_le.mp hb).1])
    simpa only [Real.sin_neg,neg_div_neg_eq] using ht
  · exact hp v hn ((le_abs_self v).trans hb)

theorem fraction_bounds (ε A B a : ℝ) (hε : 0 < ε) (hB : 0 < B) (hBA : B ≤ A)
    (ha : 1/2 ≤ a) : (1/2)*(B/(B+ε)) ≤ A*a/(A*a+ε) ∧ A*a/(A*a+ε) < 1 := by
  have hA : 0 < A := hB.trans_le hBA
  have haa : 0 < A*a := mul_pos hA (by linarith)
  have hBε : 0 < B+ε := add_pos hB hε
  have hd : 0 < A*a+ε := add_pos haa hε
  have hlow : B ≤ 2*(A*a) := by nlinarith [mul_le_mul_of_nonneg_left ha hA.le]
  refine ⟨?_,(div_lt_one hd).mpr (by linarith)⟩
  apply (le_div_iff₀ hd).mpr
  rw [show (1/2)*(B/(B+ε))*(A*a+ε) = (B*(A*a+ε)/2)/(B+ε) by ring]
  apply (div_le_iff₀ hBε).mpr
  nlinarith [mul_nonneg haa.le hB.le,mul_le_mul_of_nonneg_right hlow hε.le]

def argument (ε h : ℝ) (x : Configuration) : ℂ := (chart ε x.1:ℂ)+(-h/2:ℝ)*Complex.I
def inversePoint (ε h : ℝ) (x : Configuration) : ℂ := complexInverse ε (argument ε h x)
def velocity (ε h : ℝ) (x : Configuration) : ℝ := (2/h)*(difference ε h x).im

variable (ε : ℝ) (hε : 0 < ε) (h : ℝ) (hne : h ≠ 0) (hh : |h| ≤ 2*Real.pi*ε/3)
include hε hh

theorem imaginary_equation (x : Configuration) :
    Real.exp (inversePoint ε h x).re*Real.sin (inversePoint ε h x).im+
      ε*(inversePoint ε h x).im = -h/2 := by
  have he := congrArg Complex.im (complexInverse_right ε hε (argument ε h x) (shift_mem ε hε h hh x))
  simpa only [complexChart_im,argument,Complex.add_im,Complex.ofReal_im,Complex.mul_im,
    Complex.ofReal_re,Complex.I_im,Complex.I_re,mul_one,mul_zero,add_zero,zero_add] using he

include hne in
theorem inverse_im_ne_zero (x : Configuration) : (inversePoint ε h x).im ≠ 0 := by
  intro hz
  have he := imaginary_equation ε hε h hh x
  rw [hz,Real.sin_zero,mul_zero,mul_zero,add_zero] at he
  exact hne (by linarith)

include hne in
theorem inverse_ratio_bounds (x : Configuration) :
    1/2 ≤ Real.sin (inversePoint ε h x).im/(inversePoint ε h x).im ∧
      Real.sin (inversePoint ε h x).im/(inversePoint ε h x).im ≤ 1 :=
  sine_ratio_bounds _ (inverse_im_ne_zero ε hε h hne hh x)
    (complexInverse_mem ε hε _ (shift_mem ε hε h hh x)).le

theorem inverse_real_lower (x : Configuration) : x.1 ≤ (inversePoint ε h x).re := by
  have he := inverse_re_ge_real ε hε (argument ε h x) (shift_mem ε hε h hh x)
  have hr : (argument ε h x).re = chart ε x.1 := by simp [argument]
  rw [hr] at he
  change (chartIso ε hε).symm ((chartIso ε hε) x.1) ≤ _ at he
  simpa only [OrderIso.symm_apply_apply] using he

include hne in
theorem velocity_ratio (x : Configuration) : velocity ε h x =
    (Real.exp (inversePoint ε h x).re*(Real.sin (inversePoint ε h x).im/(inversePoint ε h x).im))/
      (Real.exp (inversePoint ε h x).re*(Real.sin (inversePoint ε h x).im/(inversePoint ε h x).im)+ε) := by
  let A := Real.exp (inversePoint ε h x).re
  let v := (inversePoint ε h x).im
  have hv : v ≠ 0 := inverse_im_ne_zero ε hε h hne hh x
  have he : A*Real.sin v+ε*v = -h/2 := imaginary_equation ε hε h hh x
  simp only [velocity,difference,shiftedClock,complexClock,Complex.sub_im,Complex.add_im,
    Complex.ofReal_im,add_zero,zero_sub,Complex.exp_im]
  change (2/h)*(- (A*Real.sin v)) = (A*(Real.sin v/v))/(A*(Real.sin v/v)+ε)
  have hs : A*(Real.sin v/v)+ε = (-h/2)/v := by
    calc
      _ = (A*Real.sin v+ε*v)/v := by field_simp [hv]
      _ = _ := congrArg (fun r : ℝ => r/v) he
  rw [hs]
  field_simp [hv,hne]

include hne in
theorem velocity_bounds (x : Configuration) :
    (1/2)*KFCausalClockFloorCanonicalDefect.response ε x.1 ≤ velocity ε h x ∧ velocity ε h x < 1 := by
  rw [velocity_ratio ε hε h hne hh]
  exact fraction_bounds ε _ _ _ hε (Real.exp_pos x.1)
    (Real.exp_le_exp.mpr (inverse_real_lower ε hε h hh x))
    (inverse_ratio_bounds ε hε h hne hh x).1

include hne in
theorem velocity_positive (x : Configuration) : 0 < velocity ε h x :=
  (mul_pos (by norm_num : (0:ℝ)<1/2)
    (div_pos (Real.exp_pos _) (KFCausalClockFloorCanonicalDefect.clock_positive ε x.1 hε.le))).trans_le
      (velocity_bounds ε hε h hne hh x).1

theorem velocity_continuous : Continuous (velocity ε h) :=
  continuous_const.mul (Complex.continuous_im.comp (difference_continuous ε hε h hh))

#print axioms sine_ratio_bounds
#print axioms fraction_bounds
#print axioms imaginary_equation
#print axioms inverse_im_ne_zero
#print axioms inverse_ratio_bounds
#print axioms inverse_real_lower
#print axioms velocity_ratio
#print axioms velocity_bounds
#print axioms velocity_positive
#print axioms velocity_continuous
end
end UnifiedTheory.Audit.KFCausalClockFloorClockVelocity
