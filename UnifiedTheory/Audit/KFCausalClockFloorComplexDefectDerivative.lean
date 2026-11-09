/- The analytic clock defect solves the same polynomial differential
equation as its real restriction. The strip and inverse are the actual
ones used by the longitudinal exponential. -/
import UnifiedTheory.Audit.KFCausalClockFloorDefectShift
import UnifiedTheory.Audit.KFCausalClockFloorDefectTransportScalar

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 800000

namespace UnifiedTheory.Audit.KFCausalClockFloorComplexDefectDerivative
noncomputable section
open Set Filter
open scoped Topology
open UnifiedTheory.Audit.KFCausalComplexClockChart
open UnifiedTheory.Audit.KFCausalComplexClockImage
open UnifiedTheory.Audit.KFCausalComplexClockInverse
open UnifiedTheory.Audit.KFCausalClockFloorComplexDefect
open UnifiedTheory.Audit.KFCausalClockFloorDefectTransportScalar (drift)

def complexDrift (ε : ℝ) (z : ℂ) : ℂ := -(z^2*(1-z))/(ε:ℂ)

theorem complexDrift_real (ε d : ℝ) : complexDrift ε (d:ℂ) = (drift ε d:ℂ) := by
  simp only [complexDrift,drift,Complex.ofReal_div,Complex.ofReal_neg,Complex.ofReal_mul,
    Complex.ofReal_pow,Complex.ofReal_sub,Complex.ofReal_one]

theorem inverse_derivative (ε : ℝ) (hε : 0 < ε) (q : ℂ) (hq : q ∈ targetStrip ε) :
    HasDerivAt (complexInverse ε) (complexClock ε q)⁻¹ q := by
  apply (complexChart_derivative ε (complexInverse ε q)).of_local_left_inverse
    (complexInverse_analytic ε hε q hq).continuousAt (complexClock_ne_zero ε hε q hq)
  filter_upwards [(complexChart_open_image ε hε).mem_nhds (complexChart_surjOn_strip ε hε hq)] with z hz
  apply complexInverse_right_image
  rcases hz with ⟨w,hw,he⟩
  exact ⟨w,(show |w.im| < Real.pi/2 from hw).le,he⟩

theorem defect_derivative (ε : ℝ) (hε : 0 < ε) (q : ℂ) (hq : q ∈ targetStrip ε) :
    HasDerivAt (complexDefect ε) (complexDrift ε (complexDefect ε q)) q := by
  have hc := ((inverse_derivative ε hε q hq).cexp).add_const (ε:ℂ)
  have hd := (hc.inv (complexClock_ne_zero ε hε q hq)).const_mul (ε:ℂ)
  change HasDerivAt (complexDefect ε) _ q at hd
  convert hd using 1
  have hn : complexClock ε q ≠ 0 := complexClock_ne_zero ε hε q hq
  have he : (ε:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hε.ne'
  unfold complexDrift complexDefect complexClock
  unfold complexClock at hn
  field_simp
  ring

theorem vertical_derivative (ε : ℝ) (hε : 0 < ε) (q y : ℝ)
    (hy : |y| ≤ Real.pi*ε/3) :
    HasDerivAt (fun r : ℝ => complexDefect ε ((q:ℂ)+(r:ℂ)*Complex.I))
      (Complex.I*complexDrift ε (complexDefect ε ((q:ℂ)+(y:ℂ)*Complex.I))) y := by
  have ht : ((q:ℂ)+(y:ℂ)*Complex.I) ∈ targetStrip ε := by
    change |(((q:ℂ)+(y:ℂ)*Complex.I):ℂ).im| ≤ Real.pi*ε/2
    simp only [Complex.add_im,Complex.ofReal_im,Complex.mul_im,Complex.ofReal_re,
      Complex.I_im,Complex.I_re,mul_one,mul_zero,add_zero,zero_add]
    nlinarith [Real.pi_pos]
  have hh := (defect_derivative ε hε _ ht).comp ((y:ℂ))
    (((hasDerivAt_id (y:ℂ)).mul_const Complex.I).const_add (q:ℂ))
  simpa [Function.comp_def,mul_comm] using hh.comp_ofReal

#print axioms complexDrift_real
#print axioms inverse_derivative
#print axioms defect_derivative
#print axioms vertical_derivative

end
end UnifiedTheory.Audit.KFCausalClockFloorComplexDefectDerivative
