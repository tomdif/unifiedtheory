/- The imaginary half-exponential shift changes the physical clock by a
bounded multiplier. Its norm is at most |hbar|; no state domain is assumed. -/
import UnifiedTheory.Audit.KFCausalClockFloorShiftedDefectPhysical

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

namespace UnifiedTheory.Audit.KFCausalClockFloorClockShiftDifference
noncomputable section
open MeasureTheory
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalCoupledLongitudinalFlow (Configuration)
open UnifiedTheory.Audit.KFCausalClockFloorFlow (clock)
open UnifiedTheory.Audit.KFCausalRegularizedLongitudinalChart
open UnifiedTheory.Audit.KFCausalComplexClockChart
open UnifiedTheory.Audit.KFCausalComplexClockInverse
open UnifiedTheory.Audit.KFCausalClockFloorComplexDefect
open UnifiedTheory.Audit.KFCausalClockFloorDefectShift
open UnifiedTheory.Audit.KFCausalClockFloorShiftedDefect
open UnifiedTheory.Audit.KFCausalClockFloorShiftedDefectPhysical
open UnifiedTheory.Audit.KFCausalContractiveMultiplier

def shiftedClock (ε h : ℝ) (x : Configuration) : ℂ :=
  complexClock ε ((chart ε x.1:ℂ)+(-h/2:ℝ)*Complex.I)

def difference (ε h : ℝ) (x : Configuration) : ℂ :=
  (clock ε x.1:ℂ)-shiftedClock ε h x

theorem shift_mem (ε : ℝ) (hε : 0 < ε) (h : ℝ)
    (hh : |h| ≤ 2*Real.pi*ε/3) (x : Configuration) :
    (chart ε x.1:ℂ)+(-h/2:ℝ)*Complex.I ∈ targetStrip ε :=
  KFCausalClockFloorFullGaussian.third_strip_subset ε hε _
    (by simpa using shift_bound ε h hh)

theorem real_clock_chart (ε : ℝ) (hε : 0 < ε) (x : Configuration) :
    complexClock ε (chart ε x.1:ℂ) = (clock ε x.1:ℂ) := by
  rw [complexClock_real ε hε]
  change (clock ε ((chartIso ε hε).symm ((chartIso ε hε) x.1)):ℂ) = _
  rw [(chartIso ε hε).symm_apply_apply]

theorem difference_continuous (ε : ℝ) (hε : 0 < ε) (h : ℝ)
    (hh : |h| ≤ 2*Real.pi*ε/3) : Continuous (difference ε h) := by
  have hs : Continuous (shiftedClock ε h) := by
    apply continuous_iff_continuousAt.mpr
    intro x
    have hc : Continuous (chart ε) := by unfold chart; fun_prop
    have ha : AnalyticAt ℂ (complexClock ε)
        ((chart ε x.1:ℂ)+(-h/2:ℝ)*Complex.I) :=
      ((complexInverse_analytic ε hε _ (shift_mem ε hε h hh x)).cexp).add analyticAt_const
    exact ha.continuousAt.comp (f := fun y : Configuration => (chart ε y.1:ℂ)+(-h/2:ℝ)*Complex.I)
      (show ContinuousAt (fun x : Configuration => (chart ε x.1:ℂ)+(-h/2:ℝ)*Complex.I) x by fun_prop)
  exact (show Continuous (fun x : Configuration => (clock ε x.1:ℂ)) by unfold clock; fun_prop).sub hs

theorem difference_bound (ε : ℝ) (hε : 0 < ε) (h : ℝ)
    (hh : |h| ≤ 2*Real.pi*ε/3) (x : Configuration) : ‖difference ε h x‖ ≤ |h| := by
  have hb := complexClock_vertical_difference ε hε _ (shift_mem ε hε h hh x)
  have hr : ((chart ε x.1:ℂ)+(-h/2:ℝ)*Complex.I).re = chart ε x.1 := by simp
  have hi : ((chart ε x.1:ℂ)+(-h/2:ℝ)*Complex.I).im = -h/2 := by simp
  rw [hr,hi,real_clock_chart ε hε x,norm_sub_rev] at hb
  change ‖difference ε h x‖ ≤ _ at hb
  norm_num [abs_div,abs_neg] at hb
  linarith

theorem shiftedClock_defect (ε : ℝ) (hε : 0 < ε) (h : ℝ)
    (hh : |h| ≤ 2*Real.pi*ε/3) (x : Configuration) :
    shiftedClock ε h x*physicalSymbol ε h x = (ε:ℂ) := by
  have hn := complexClock_ne_zero ε hε _ (shift_mem ε hε h hh x)
  unfold shiftedClock physicalSymbol complexDefect
  simpa only [mul_div_assoc] using mul_div_cancel_left₀ (ε:ℂ) hn

theorem difference_normalized_bound (ε : ℝ) (hε : 0 < ε) (h : ℝ)
    (hh : |h| ≤ 2*Real.pi*ε/3) (x : Configuration) :
    ‖difference ε h x / ((|h|+1:ℝ):ℂ)‖ ≤ 1 := by
  rw [norm_div,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (by positivity : 0 < |h|+1)]
  exact (div_le_one (by positivity)).mpr ((difference_bound ε hε h hh x).trans (by linarith))

def differenceOperator (ε : ℝ) (hε : 0 < ε) (h : ℝ)
    (hh : |h| ≤ 2*Real.pi*ε/3) : Hilbert →L[ℂ] Hilbert :=
  ((|h|+1:ℝ):ℂ) • multiplyL (fun x => difference ε h x/((|h|+1:ℝ):ℂ))
    ((difference_continuous ε hε h hh).div_const _).measurable
    (difference_normalized_bound ε hε h hh)

theorem differenceOperator_coe (ε : ℝ) (hε : 0 < ε) (h : ℝ)
    (hh : |h| ≤ 2*Real.pi*ε/3) (f : Hilbert) :
    differenceOperator ε hε h hh f =ᵐ[volume] fun x => difference ε h x*f x := by
  filter_upwards [Lp.coeFn_smul ((|h|+1:ℝ):ℂ)
    (multiplyL (fun x => difference ε h x/((|h|+1:ℝ):ℂ))
      ((difference_continuous ε hε h hh).div_const _).measurable
      (difference_normalized_bound ε hε h hh) f),
    multiplyL_coe (fun x => difference ε h x/((|h|+1:ℝ):ℂ))
      ((difference_continuous ε hε h hh).div_const _).measurable
      (difference_normalized_bound ε hε h hh) f] with x hs hm
  change (((|h|+1:ℝ):ℂ) • multiplyL _ _ _ f) x = _
  rw [hs]
  simp only [Pi.smul_apply,smul_eq_mul,hm]
  have hn : ((|h|+1:ℝ):ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (by positivity)
  field_simp

theorem differenceOperator_norm (ε : ℝ) (hε : 0 < ε) (h : ℝ)
    (hh : |h| ≤ 2*Real.pi*ε/3) (f : Hilbert) :
    ‖differenceOperator ε hε h hh f‖ ≤ |h| * ‖f‖ := by
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [differenceOperator_coe ε hε h hh f] with x hx
  rw [hx,norm_mul]
  exact mul_le_mul_of_nonneg_right (difference_bound ε hε h hh x) (norm_nonneg _)

#print axioms shift_mem
#print axioms real_clock_chart
#print axioms difference_continuous
#print axioms difference_bound
#print axioms shiftedClock_defect
#print axioms difference_normalized_bound
#print axioms differenceOperator_coe
#print axioms differenceOperator_norm

end
end UnifiedTheory.Audit.KFCausalClockFloorClockShiftDifference
