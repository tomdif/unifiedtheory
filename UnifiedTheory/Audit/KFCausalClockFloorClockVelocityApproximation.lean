/- The exact positive clock velocity approaches the classical response
with a squared-defect error, uniformly over the physical coordinate. -/
import UnifiedTheory.Audit.KFCausalClockFloorClockVelocity
import UnifiedTheory.Audit.KFCausalClockFloorClockShiftTaylor

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1200000

namespace UnifiedTheory.Audit.KFCausalClockFloorClockVelocityApproximation
noncomputable section
open UnifiedTheory.Audit.KFCausalCoupledLongitudinalFlow (Configuration)
open UnifiedTheory.Audit.KFCausalClockFloorClockShiftDifference
open UnifiedTheory.Audit.KFCausalClockFloorClockVelocity
open UnifiedTheory.Audit.KFCausalClockFloorCanonicalDefect (response defect)

variable (ε : ℝ) (hε : 0 < ε) (h : ℝ) (hne : h ≠ 0) (hh : |h| ≤ 2*Real.pi*ε/3)
include hε hne hh

theorem velocity_error (x : Configuration) :
    |velocity ε h x-response ε x.1| ≤ (2*|h|/ε)*(defect ε x.1)^2 := by
  let z := difference ε h x-(Complex.I*(h:ℂ)/2)*(response ε x.1:ℂ)
  have he : velocity ε h x-response ε x.1 = (2/h)*z.im := by
    simp only [velocity,z,Complex.sub_im,Complex.mul_im,Complex.div_ofNat_re,Complex.div_ofNat_im,
      Complex.I_re,Complex.I_im,Complex.ofReal_re,Complex.ofReal_im,mul_zero,one_mul,
      zero_add]
    field_simp [hne]
  rw [he,abs_mul,abs_div,abs_of_pos (by norm_num : (0:ℝ)<2)]
  calc
    _ ≤ (2/|h|)*‖z‖ := mul_le_mul_of_nonneg_left (Complex.abs_im_le_norm z) (by positivity)
    _ ≤ (2/|h|)*((h^2/ε)*(defect ε x.1)^2) :=
      mul_le_mul_of_nonneg_left (KFCausalClockFloorClockShiftTaylor.difference_first_order_bound ε hε h hh x) (by positivity)
    _ = _ := by rw [← sq_abs h]; field_simp [(abs_pos.mpr hne).ne']

#print axioms velocity_error
end
end UnifiedTheory.Audit.KFCausalClockFloorClockVelocityApproximation
