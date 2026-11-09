/- Uniform coercivity in fixed coordinates on every compact time interval. -/
import UnifiedTheory.Audit.KFCausalClockFloorFullApproximationStability
import UnifiedTheory.Audit.KFCausalCoerciveCauchyLimit

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
set_option synthInstance.maxHeartbeats 100000

namespace UnifiedTheory.Audit.KFCausalClockFloorUniformNormControl
noncomputable section
open Set
open UnifiedTheory.Audit.KFCausalClockFloorAveragedFormTransport
open UnifiedTheory.Audit.KFCausalClockFloorAveragedShiftedResolvent
open UnifiedTheory.Audit.KFCausalClockFloorFormDomainTransport
open UnifiedTheory.Audit.KFCausalClockFloorFullApproximationStability
open UnifiedTheory.Audit.KFCausalWeightedMassEnergy (energy)
variable (ε : ℝ) (hε : 0 < ε) (h : ℝ) (hne : h ≠ 0)
  (hh : |h| ≤ 2*Real.pi*ε/3) (m g k : ℝ)
local notation "V" => FormSpace ε hε h hne hh m g k 0
local notation "F" => referenceShift ε hε h hne hh m g k
local notation "S" => transport ε hε h hne hh m g k

theorem uniform_norm_control (a s l r : ℝ) (ha : 0 < a) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ t ∈ Icc l r, ∀ x : V,
      ‖x‖^2 ≤ K*energy (F a t) (S a s t x) := by
  have hcont := coefficient_continuity ε hε h hne hh m g k a s ha
  have hd : Continuous (KFCausalShiftedForm.lowerConstant a) :=
    continuous_const.min (continuous_const.min (Real.continuous_exp.comp (continuous_const.mul continuous_id)))
  exact KFCausalCoerciveCauchyLimit.uniform_norm_sq_control (F a) (S a s) (fun t => S a t s)
    (KFCausalShiftedForm.lowerConstant a) l r hcont.2.2.1.continuousOn hd.continuousOn
    (fun t _ => KFCausalShiftedForm.lowerConstant_positive a t ha)
    (fun t _ => KFCausalClockFloorFixedDomainApproximation.transport_inverse ε hε h hne hh m g k a t s ha)
    (fun t _ => KFCausalClockFloorLiftedResolvent.shift_energy_coercive ε hε h hne hh m g k a t)

#print axioms uniform_norm_control
end
end UnifiedTheory.Audit.KFCausalClockFloorUniformNormControl
