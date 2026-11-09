/- Second operator-norm time derivatives of the actual common form and
its shifted inverse. All inverse factors are the constructed coercive inverses. -/
import UnifiedTheory.Audit.KFCausalClockFloorAveragedShiftedResolvent

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1500000
set_option maxRecDepth 4096
set_option synthInstance.maxHeartbeats 100000

namespace UnifiedTheory.Audit.KFCausalClockFloorFormSecondDerivative
noncomputable section
open UnifiedTheory.Audit.KFCausalClockFloorAveragedFormTransport
open UnifiedTheory.Audit.KFCausalClockFloorAveragedRegularity
open UnifiedTheory.Audit.KFCausalClockFloorAveragedShiftedResolvent

variable (ε : ℝ) (hε : 0 < ε) (h : ℝ) (hne : h ≠ 0)
  (hh : |h| ≤ 2*Real.pi*ε/3) (m g k : ℝ)
local notation "V" => FormSpace ε hε h hne hh m g k 0
local notation "D" => referenceFormDerivative ε hε h hne hh m g k
local notation "P" => referenceInverse ε hε h hne hh m g k
local notation "P'" => referenceInverseDerivative ε hε h hne hh m g k

theorem form_second_derivative (t : ℝ) : HasDerivAt D ((2:ℝ) • D t) t := by
  have he := (((Real.hasDerivAt_exp (2*t)).comp t ((hasDerivAt_id t).const_mul 2)).const_mul 2)
  have hd : HasDerivAt (fun s : ℝ => 2*Real.exp (2*s)) (2*(2*Real.exp (2*t))) t := by
    convert he using 1
    ring
  simpa only [referenceFormDerivative,smul_smul] using hd.smul_const
    (KFCausalBoundedFormCurve.gram (growingMap ε hε h hne hh m g k))

def inverseSecondDerivative (a t : ℝ) : V →L[ℂ] V :=
  -(P' a t*D t*P a t + P a t*((2:ℝ) • D t)*P a t + P a t*D t*P' a t)

theorem inverse_second_derivative (a t : ℝ) (ha : 0 < a) :
    HasDerivAt (P' a) (inverseSecondDerivative ε hε h hne hh m g k a t) t := by
  have hp := referenceInverse_derivative ε hε h hne hh m g k a t ha
  have hd := form_second_derivative ε hε h hne hh m g k t
  simpa only [referenceInverseDerivative,inverseSecondDerivative,add_mul,add_assoc]
    using ((hp.mul hd).mul hp).neg

theorem inverse_second_continuous (a : ℝ) (ha : 0 < a) :
    Continuous (inverseSecondDerivative ε hε h hne hh m g k a) := by
  have hp := referenceInverse_continuous ε hε h hne hh m g k a ha
  have hd := referenceForm_derivative_continuous ε hε h hne hh m g k
  have hpd := referenceInverse_derivative_continuous ε hε h hne hh m g k a ha
  exact (((hpd.mul hd).mul hp).add ((hp.mul (hd.const_smul (2:ℝ))).mul hp) |>.add
    ((hp.mul hd).mul hpd)).neg

#print axioms form_second_derivative
#print axioms inverse_second_derivative
#print axioms inverse_second_continuous
end
end UnifiedTheory.Audit.KFCausalClockFloorFormSecondDerivative
