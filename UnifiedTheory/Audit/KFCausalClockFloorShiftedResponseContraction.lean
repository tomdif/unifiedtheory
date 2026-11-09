/- The shifted response is strictly contractive at every clock point.
This is a pointwise strict inequality, not a uniform spectral gap. -/
import UnifiedTheory.Audit.KFCausalClockFloorClockShiftDifference

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

namespace UnifiedTheory.Audit.KFCausalClockFloorShiftedResponseContraction
noncomputable section
open MeasureTheory
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalCoupledLongitudinalFlow (Configuration)
open UnifiedTheory.Audit.KFCausalComplexClockChart
open UnifiedTheory.Audit.KFCausalComplexClockInverse
open UnifiedTheory.Audit.KFCausalClockFloorComplexDefect
open UnifiedTheory.Audit.KFCausalClockFloorClockShiftDifference (shift_mem)
open UnifiedTheory.Audit.KFCausalClockFloorShiftedDefect
open UnifiedTheory.Audit.KFCausalClockFloorShiftedDefectPhysical

theorem norm_lt_add_positive (z : ℂ) (ε : ℝ) (hε : 0 < ε) (hz : 0 ≤ z.re) :
    ‖z‖ < ‖z+(ε:ℂ)‖ := by
  have hs : ‖z‖^2 < ‖z+(ε:ℂ)‖^2 := by
    rw [Complex.sq_norm,Complex.sq_norm,Complex.normSq_apply,Complex.normSq_apply]
    simp only [Complex.add_re,Complex.add_im,Complex.ofReal_re,Complex.ofReal_im,add_zero]
    nlinarith [mul_nonneg hε.le hz]
  nlinarith [norm_nonneg z,norm_nonneg (z+(ε:ℂ))]

theorem complex_response_strict (ε : ℝ) (hε : 0 < ε) (q : ℂ) (hq : q ∈ targetStrip ε) :
    ‖1-complexDefect ε q‖ < 1 := by
  let z := Complex.exp (complexInverse ε q)
  have hz : 0 < z.re := by
    have hi := abs_lt.mp (show |(complexInverse ε q).im| < Real.pi/2 from complexInverse_mem ε hε q hq)
    change 0 < (Complex.exp (complexInverse ε q)).re
    rw [Complex.exp_re]
    exact mul_pos (Real.exp_pos _) (Real.cos_pos_of_mem_Ioo hi)
  have hn : z+(ε:ℂ) ≠ 0 := complexClock_ne_zero ε hε q hq
  have he : 1-complexDefect ε q = z/(z+(ε:ℂ)) := by
    change 1-(ε:ℂ)/(z+(ε:ℂ)) = _
    field_simp
    ring
  rw [he,norm_div]
  exact (div_lt_one (norm_pos_iff.mpr hn)).mpr (norm_lt_add_positive z ε hε hz.le)

theorem physical_response_strict (ε : ℝ) (hε : 0 < ε) (h : ℝ)
    (hh : |h| ≤ 2*Real.pi*ε/3) (x : Configuration) :
    ‖1-physicalSymbol ε h x‖ < 1 :=
  complex_response_strict ε hε _ (shift_mem ε hε h hh x)

def shiftedResponse (ε : ℝ) (hε : 0 < ε) (h : ℝ)
    (hh : |h| ≤ 2*Real.pi*ε/3) : Hilbert →L[ℂ] Hilbert :=
  ContinuousLinearMap.id ℂ Hilbert-shiftedDefect ε hε h hh

theorem shiftedResponse_coe (ε : ℝ) (hε : 0 < ε) (h : ℝ)
    (hh : |h| ≤ 2*Real.pi*ε/3) (f : Hilbert) :
    shiftedResponse ε hε h hh f =ᵐ[volume] fun x => (1-physicalSymbol ε h x)*f x := by
  change f-shiftedDefect ε hε h hh f =ᵐ[volume] _
  filter_upwards [Lp.coeFn_sub f (shiftedDefect ε hε h hh f),
    shiftedDefect_physical_coe ε hε h hh f] with x hs hb
  rw [hs]
  simp only [Pi.sub_apply,hb]
  ring

theorem shiftedResponse_norm (ε : ℝ) (hε : 0 < ε) (h : ℝ)
    (hh : |h| ≤ 2*Real.pi*ε/3) (f : Hilbert) : ‖shiftedResponse ε hε h hh f‖ ≤ ‖f‖ := by
  apply Lp.norm_le_norm_of_ae_le
  filter_upwards [shiftedResponse_coe ε hε h hh f] with x hx
  rw [hx,norm_mul]
  exact mul_le_of_le_one_left (norm_nonneg _) (physical_response_strict ε hε h hh x).le

#print axioms norm_lt_add_positive
#print axioms complex_response_strict
#print axioms physical_response_strict
#print axioms shiftedResponse_coe
#print axioms shiftedResponse_norm

end
end UnifiedTheory.Audit.KFCausalClockFloorShiftedResponseContraction
