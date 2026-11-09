/- Exact charge commutation for the pure-clock coordinate unitary and its
strong unitary transport on all physical L2 states. -/
import UnifiedTheory.Audit.KFCausalClockFloorPureClockChargeCoordinates
import UnifiedTheory.Audit.KFCausalClockFloorPureClockTransport
import UnifiedTheory.Audit.KFCausalCanonicalClockCharge

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1400000

namespace UnifiedTheory.Audit.KFCausalClockFloorPureClockCharge
noncomputable section
open MeasureTheory
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalEuclideanProductCoordinates (Joint JointHilbert)
open UnifiedTheory.Audit.KFCausalClockFloorPureClockChargeCoordinates
open UnifiedTheory.Audit.KFCausalNormalizedChargeFlow
open UnifiedTheory.Audit.KFCausalPhysicalCircleAction (action chargeCoordinates action_coordinates)
open UnifiedTheory.Audit.KFCausalClockFloorPureClockCoordinates (coordinates)
open UnifiedTheory.Audit.KFCausalClockFloorPureClockTransport (transport transport_apply)
open UnifiedTheory.Audit.KFCausalCanonicalClockCharge (translation_charge)

variable (ε : ℝ) (hε : 0 < ε)

theorem jointMap_charge (c : ℝ) (hc : c ≠ 0) (θ : ℝ) (x : Joint 2 4) :
    jointMap ε hε (flowEquiv c hc θ x) = flowEquiv c hc θ (jointMap ε hε x) := by
  ext i
  rcases i with i | i <;> fin_cases i <;>
    simp [jointMap_formula,flow_apply,dilate,KFCausalPairedRotation.rotate]

theorem jointWeight_charge (c : ℝ) (hc : c ≠ 0) (θ : ℝ) (x : Joint 2 4) :
    jointWeight ε (flowEquiv c hc θ x) = jointWeight ε x := by
  rw [jointWeight,flow_clock]
  rfl

theorem jointUnitary_charge (c : ℝ) (hc : c ≠ 0) (θ : ℝ) (f : JointHilbert 2 4) :
    jointUnitary ε hε (KFCausalMixedCircleAction.action c hc θ f) =
      KFCausalMixedCircleAction.action c hc θ (jointUnitary ε hε f) := by
  apply Lp.ext
  filter_upwards [jointUnitary_coe ε hε (KFCausalMixedCircleAction.action c hc θ f),
    (jointMap_quasiMeasurePreserving ε hε).ae (KFCausalMixedCircleAction.action_coe c hc θ f),
    KFCausalMixedCircleAction.action_coe c hc θ (jointUnitary ε hε f),
    (flow_preserves_volume c hc θ).quasiMeasurePreserving.ae (jointUnitary_coe ε hε f)]
    with x hu ha hv hw
  simp only [Function.comp_apply] at ha hv
  rw [hu,ha,hv,hw,jointMap_charge,jointWeight_charge]

theorem coordinates_charge (h : ℝ) (hne : h ≠ 0) (θ : ℝ) (f : Hilbert) :
    coordinates ε hε (action h hne θ f) = action h hne θ (coordinates ε hε f) := by
  apply chargeCoordinates.injective
  rw [charge_unitary_coordinates,action_coordinates,action_coordinates,charge_unitary_coordinates,
    jointUnitary_charge]

theorem inverse_coordinates_charge (h : ℝ) (hne : h ≠ 0) (θ : ℝ) (f : Hilbert) :
    (coordinates ε hε).symm (action h hne θ f) = action h hne θ ((coordinates ε hε).symm f) := by
  apply (coordinates ε hε).injective
  rw [LinearIsometryEquiv.apply_symm_apply,coordinates_charge,LinearIsometryEquiv.apply_symm_apply]

theorem transport_charge (h : ℝ) (hne : h ≠ 0) (t θ : ℝ) (f : Hilbert) :
    transport ε hε t (action h hne θ f) = action h hne θ (transport ε hε t f) := by
  simp only [transport_apply,inverse_coordinates_charge,translation_charge,coordinates_charge]

theorem transport_increment_charge (h : ℝ) (hne : h ≠ 0) (t θ : ℝ) (f : Hilbert) :
    ‖transport ε hε t (action h hne θ f)-action h hne θ f‖ = ‖transport ε hε t f-f‖ := by
  rw [transport_charge,← map_sub,LinearIsometryEquiv.norm_map]

#print axioms jointMap_charge
#print axioms jointWeight_charge
#print axioms jointUnitary_charge
#print axioms coordinates_charge
#print axioms inverse_coordinates_charge
#print axioms transport_charge
#print axioms transport_increment_charge
end
end UnifiedTheory.Audit.KFCausalClockFloorPureClockCharge
