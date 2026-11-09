/- The physical clock controls the field loss associated with the proved
one-sixteenth three-jet coercivity. This is the scalar clock attachment. -/
import UnifiedTheory.Audit.KFCausalTwoWidthPhysicalClockLoss

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1400000

namespace UnifiedTheory.Audit.KFCausalConfluentThreePhysicalClockLoss
noncomputable section
open KFCausalJointFourierDissipationClock
open KFCausalJointClockCoolingCoercivity (imaginaryRate)
open KFCausalClockFloorRelativeShift (scale)
open KFCausalNeutralPlaneNormalizedGeometry (fraction actual_normalized_velocity)

def fieldLoss (α w : ℝ) (r rd : ℂ) (ell : ℝ) : ℝ :=
  16*(-2*(rd.re-ell*r.re)-3*ell)^2/(α*r.re*(rd.re-ell*r.re)*w)

variable (ε y s : ℝ) (hε : 0 < ε) (hy : |y| ≤ Real.pi*ε/3)
local notation "r" => scale ε y s
local notation "rd" => deriv (scale ε y) s
local notation "ell" => imaginaryRate (fraction ε s) r

include hε hy in
theorem actual_loss_identity (α w : ℝ) :
    -4*ell+fieldLoss α w r rd ell =
      KFCausalTwoWidthPhysicalClockLoss.loss (α/4) w (fraction ε s) r := by
  unfold fieldLoss KFCausalTwoWidthPhysicalClockLoss.loss
  rw [(actual_normalized_velocity ε y s hε hy).deriv,real_cooling_identity]
  have hk : -2*(fraction ε s*normalizedRealCooling (fraction ε s) r)-
      3*imaginaryRate (fraction ε s) r =
      fraction ε s*normalizedFieldJet (fraction ε s) r := by
    rw [dilation_identity]
    unfold normalizedFieldJet
    ring
  rw [hk]
  simp only [div_eq_mul_inv,_root_.mul_inv_rev,inv_inv]
  ring

include hε hy in
theorem actual_loss_bound (α w : ℝ) (hα : 0 < α) (hw : 1 ≤ w) :
    -4*ell+fieldLoss α w r rd ell ≤ (48+331776/α)*fraction ε s := by
  rw [actual_loss_identity ε y s hε hy]
  have he : 48+82944/(α/4)=48+331776/α := by ring
  rw [← he]
  exact KFCausalTwoWidthPhysicalClockLoss.actual_loss_bound ε y s hε hy (α/4) w (by positivity) hw

#print axioms actual_loss_identity
#print axioms actual_loss_bound
end
end UnifiedTheory.Audit.KFCausalConfluentThreePhysicalClockLoss
