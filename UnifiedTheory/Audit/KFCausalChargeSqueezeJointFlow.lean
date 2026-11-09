/- The paired squeeze in the actual mixed charge coordinates is uniform
dilation of all five transverse coordinates. It commutes with the charge
rotations on the whole physical Hilbert space. -/
import UnifiedTheory.Audit.KFCausalChargeSqueezePartialFourier
import UnifiedTheory.Audit.KFCausalPhysicalCircleAction

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 200000

namespace UnifiedTheory.Audit.KFCausalChargeSqueezeJointFlow
noncomputable section
open MeasureTheory
open UnifiedTheory.Audit.KFCausalEuclideanProductCoordinates
open UnifiedTheory.Audit.KFCausalChargeSqueezePairedFlow (pairFlow pairFlow_zero pairFlow_quasiMeasurePreserving)
open UnifiedTheory.Audit.KFCausalChargeSqueezePartialFourier
open UnifiedTheory.Audit.KFCausalMeasureUnitaryPullback (unitaryPullback_symm_coe)
open UnifiedTheory.Audit.KFCausalPhysicalCircleAction (chargeCoordinates)

abbrev Space := Joint 2 4

def flow (t : ℝ) (x : Space) : Space := (split 2 4).symm (pairFlow (-1) t (split 2 4 x))

theorem flow_first (t : ℝ) (x : Space) (i : Fin 2) :
    flow t x (.inl i) = Real.exp (-t)*x (.inl i) := by
  change Real.exp (-1*t)*x (.inl i) = _
  rw [neg_one_mul]

theorem flow_second (t : ℝ) (x : Space) (i : Fin 4) :
    flow t x (.inr i) =
      if i = 0 then x (.inr i) else Real.exp (-t)*x (.inr i) := rfl

theorem flow_zero (x : Space) : flow 0 x = x := by
  rw [flow,pairFlow_zero,MeasurableEquiv.symm_apply_apply]

theorem flow_quasiMeasurePreserving (t : ℝ) :
    Measure.QuasiMeasurePreserving (flow t) volume volume :=
  (split_preserves_volume 2 4).symm.quasiMeasurePreserving.comp
    ((pairFlow_quasiMeasurePreserving (-1) t).comp (split_preserves_volume 2 4).quasiMeasurePreserving)

def jointTransport (t : ℝ) : JointHilbert 2 4 ≃ₗᵢ[ℂ] JointHilbert 2 4 :=
  (coordinates 2 4).symm.trans ((mixedTransport t).trans (coordinates 2 4))

theorem jointTransport_coe (t : ℝ) (f : JointHilbert 2 4) :
    jointTransport t f =ᵐ[volume] fun x => (Real.exp (-5*t/2):ℂ)*f (flow t x) := by
  filter_upwards [coordinates_coe 2 4 (mixedTransport t ((coordinates 2 4).symm f)),
    (split_preserves_volume 2 4).quasiMeasurePreserving.ae
      (mixedTransport_coe t ((coordinates 2 4).symm f)),
    ((pairFlow_quasiMeasurePreserving (-1) t).comp
      (split_preserves_volume 2 4).quasiMeasurePreserving).ae
      (unitaryPullback_symm_coe (split 2 4) (split_preserves_volume 2 4) f)] with x ha hb hc
  dsimp only [Function.comp_apply] at ha hb hc
  exact ha.trans (hb.trans (congrArg (fun z : ℂ => (Real.exp (-5*t/2):ℂ)*z) hc))

theorem jointTransport_toLp_coe (t : ℝ) (f : Space → ℂ) (hf : MemLp f 2) :
    jointTransport t (hf.toLp f) =ᵐ[volume] fun x => (Real.exp (-5*t/2):ℂ)*f (flow t x) := by
  filter_upwards [jointTransport_coe t (hf.toLp f),
    (flow_quasiMeasurePreserving t).ae hf.coeFn_toLp] with x ha hb
  rw [ha,hb]

private theorem one_coordinate {H K : Type*}
    [SeminormedAddCommGroup H] [NormedSpace ℂ H]
    [SeminormedAddCommGroup K] [NormedSpace ℂ K]
    (P : H ≃ₗᵢ[ℂ] K) (U : H ≃ₗᵢ[ℂ] H) (f : H) :
    P (U f) = (P.symm.trans (U.trans P)) (P f) := by
  simp only [LinearIsometryEquiv.trans_apply,LinearIsometryEquiv.symm_apply_apply]

theorem physical_charge_transport (t : ℝ)
    (f : UnifiedTheory.Audit.KFCausalConfigurationTestSpace.Hilbert) :
    chargeCoordinates (KFCausalPairedSqueezeTransport.transport t f) =
      jointTransport t (chargeCoordinates f) := by
  have h := congrArg (coordinates 2 4) (physical_mixed_transport t f)
  exact h.trans (one_coordinate (coordinates 2 4) (mixedTransport t)
    (KFCausalPhysicalMixedCoordinates.mixedCoordinates f))

theorem flow_charge (a c : ℝ) (hc : c ≠ 0) (θ : ℝ) (x : Space) :
    flow a (KFCausalNormalizedChargeFlow.flowEquiv c hc θ x) =
      KFCausalNormalizedChargeFlow.flowEquiv c hc θ (flow a x) := by
  ext i
  rcases i with i | i <;> fin_cases i <;>
    simp [KFCausalNormalizedChargeFlow.flow_apply,KFCausalNormalizedChargeFlow.dilate,
      KFCausalPairedRotation.rotate,flow_first,flow_second] <;> ring

theorem joint_charge (a c : ℝ) (hc : c ≠ 0) (θ : ℝ) (f : JointHilbert 2 4) :
    jointTransport a (KFCausalMixedCircleAction.action c hc θ f) =
      KFCausalMixedCircleAction.action c hc θ (jointTransport a f) := by
  apply Lp.ext
  filter_upwards [jointTransport_coe a (KFCausalMixedCircleAction.action c hc θ f),
    KFCausalMixedCircleAction.action_coe c hc θ (jointTransport a f),
    (flow_quasiMeasurePreserving a).ae (KFCausalMixedCircleAction.action_coe c hc θ f),
    (KFCausalNormalizedChargeFlow.flow_preserves_volume c hc θ).quasiMeasurePreserving.ae
      (jointTransport_coe a f)] with x hu hv hf hg
  simp only [Function.comp_apply] at hv hf
  rw [hu,hv,hf,hg,flow_charge]

theorem physical_charge (a h : ℝ) (hh : h ≠ 0) (θ : ℝ)
    (f : UnifiedTheory.Audit.KFCausalConfigurationTestSpace.Hilbert) :
    KFCausalPairedSqueezeTransport.transport a (KFCausalPhysicalCircleAction.action h hh θ f) =
      KFCausalPhysicalCircleAction.action h hh θ (KFCausalPairedSqueezeTransport.transport a f) := by
  apply chargeCoordinates.injective
  rw [physical_charge_transport,KFCausalPhysicalCircleAction.action_coordinates,
    KFCausalPhysicalCircleAction.action_coordinates,physical_charge_transport,joint_charge]

#print axioms flow_charge
#print axioms joint_charge
#print axioms physical_charge

#print axioms flow_first
#print axioms flow_second
#print axioms flow_zero
#print axioms flow_quasiMeasurePreserving
#print axioms jointTransport_coe
#print axioms jointTransport_toLp_coe
#print axioms physical_charge_transport
end
end UnifiedTheory.Audit.KFCausalChargeSqueezeJointFlow
