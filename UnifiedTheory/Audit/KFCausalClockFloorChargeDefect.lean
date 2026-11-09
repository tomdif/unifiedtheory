/- The actual physical clock defect commutes with the actual charge circle.
This follows through the paired coordinates and partial Fourier transform;
no charge-invariance premise is imposed on a state or on the defect. -/
import UnifiedTheory.Audit.KFCausalPartialFourierMultiplier
import UnifiedTheory.Audit.KFCausalClockFloorKineticDefect
import UnifiedTheory.Audit.KFCausalPhysicalCircleAction

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 800000

namespace UnifiedTheory.Audit.KFCausalClockFloorChargeDefect
noncomputable section
open MeasureTheory
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalEuclideanProductCoordinates
open UnifiedTheory.Audit.KFCausalEuclideanConfiguration (euclideanPullback)
open UnifiedTheory.Audit.KFCausalPairedModeCoordinates
open UnifiedTheory.Audit.KFCausalPhysicalMixedCoordinates
open UnifiedTheory.Audit.KFCausalPhysicalCircleAction (chargeCoordinates)
open UnifiedTheory.Audit.KFCausalPartialFourier
open UnifiedTheory.Audit.KFCausalPartialFourierMultiplier
open UnifiedTheory.Audit.KFCausalContractiveMultiplier
open UnifiedTheory.Audit.KFCausalClockFloorDefectOperator
open UnifiedTheory.Audit.KFCausalClockFloorCanonicalDefect (defect)
open UnifiedTheory.Audit.KFCausalClockFloorKineticDefect

variable (ε : ℝ) (hε : 0 < ε)

def rightWeight (y : Block 4) : ℂ := (defect ε (y 0) : ℂ)

theorem rightWeight_measurable : Measurable (rightWeight ε) := by
  unfold rightWeight defect KFCausalClockFloorFlow.clock
  fun_prop

include hε in
theorem rightWeight_bound (y : Block 4) : ‖rightWeight ε y‖ ≤ 1 :=
  weight_bound ε hε (y 0,0)

def productDefect : ProductHilbert 2 4 →L[ℂ] ProductHilbert 2 4 :=
  rightMultiplier 2 4 (rightWeight ε) (rightWeight_measurable ε) (rightWeight_bound ε hε)

theorem productDefect_coe (f : ProductHilbert 2 4) :
    productDefect ε hε f =ᵐ[volume] fun z => (defect ε (z.2 0):ℂ)*f z :=
  rightMultiplier_coe _ _ _ _ _ f

def jointDefect : JointHilbert 2 4 →L[ℂ] JointHilbert 2 4 :=
  multiplyL (fun x => (defect ε (x (.inr 0)):ℂ))
    (by unfold defect KFCausalClockFloorFlow.clock; fun_prop)
    (fun x => weight_bound ε hε (x (.inr 0),0))

theorem jointDefect_coe (f : JointHilbert 2 4) :
    jointDefect ε hε f =ᵐ[volume] fun x => (defect ε (x (.inr 0)):ℂ)*f x :=
  multiplyL_coe _ _ _ f

theorem coordinates_defect (f : ProductHilbert 2 4) :
    coordinates 2 4 (productDefect ε hε f) = jointDefect ε hε (coordinates 2 4 f) := by
  apply Lp.ext
  filter_upwards [coordinates_coe 2 4 (productDefect ε hε f),
    coordinates_coe 2 4 f, jointDefect_coe ε hε (coordinates 2 4 f),
    (split_preserves_volume 2 4).quasiMeasurePreserving.ae (productDefect_coe ε hε f)] with x hc hf hd hp
  simp only [Function.comp_apply] at hc hf
  rw [hc,hp,hd,hf,split_snd]

theorem modePullback_defect (f : JointHilbert 2 4) :
    modePullback (jointDefect ε hε f) = euclideanDefect ε hε (modePullback f) := by
  apply Lp.ext
  filter_upwards [modePullback_coe (jointDefect ε hε f), modePullback_coe f,
    euclideanDefect_coe ε hε (modePullback f),
    mode_preserves_volume.quasiMeasurePreserving.ae (jointDefect_coe ε hε f)] with x hc hf hd hj
  simp only [Function.comp_apply] at hc hf
  rw [hc,hj,hd,hf]
  rfl

theorem pairedCoordinates_defect (f : Hilbert) :
    pairedCoordinates (defectOperator ε hε f) = productDefect ε hε (pairedCoordinates f) := by
  apply (coordinates 2 4).injective
  apply modePullback.injective
  rw [coordinates_defect,modePullback_defect]
  have hc (g : Hilbert) : modePullback (coordinates 2 4 (pairedCoordinates g)) =
      euclideanPullback g := by
    simp only [pairedCoordinates,LinearIsometryEquiv.trans_apply,
      LinearIsometryEquiv.apply_symm_apply]
  rw [hc,hc]
  change euclideanPullback (defectOperator ε hε f) =
    euclideanPullback (defectOperator ε hε (euclideanPullback.symm (euclideanPullback f)))
  rw [LinearIsometryEquiv.symm_apply_apply]

theorem mixedCoordinates_defect (f : Hilbert) :
    mixedCoordinates (defectOperator ε hε f) = productDefect ε hε (mixedCoordinates f) := by
  change leftFourier 2 4 (pairedCoordinates (defectOperator ε hε f)) =
    productDefect ε hε (leftFourier 2 4 (pairedCoordinates f))
  rw [pairedCoordinates_defect]
  exact leftFourier_commutes _ _ _ _ _ _

theorem chargeCoordinates_defect (f : Hilbert) :
    chargeCoordinates (defectOperator ε hε f) = jointDefect ε hε (chargeCoordinates f) := by
  change coordinates 2 4 (mixedCoordinates (defectOperator ε hε f)) = _
  rw [mixedCoordinates_defect,coordinates_defect]
  rfl

theorem jointDefect_action (c : ℝ) (hc : c ≠ 0) (θ : ℝ) (f : JointHilbert 2 4) :
    jointDefect ε hε (KFCausalMixedCircleAction.action c hc θ f) =
      KFCausalMixedCircleAction.action c hc θ (jointDefect ε hε f) := by
  apply Lp.ext
  filter_upwards [jointDefect_coe ε hε (KFCausalMixedCircleAction.action c hc θ f),
    KFCausalMixedCircleAction.action_coe c hc θ f,
    KFCausalMixedCircleAction.action_coe c hc θ (jointDefect ε hε f),
    (KFCausalNormalizedChargeFlow.flow_preserves_volume c hc θ).quasiMeasurePreserving.ae
      (jointDefect_coe ε hε f)] with x hd ha hb hj
  simp only [Function.comp_apply] at ha hb
  rw [hd,ha,hb,hj,KFCausalNormalizedChargeFlow.flow_clock]

theorem defect_action (hbar : ℝ) (hh : hbar ≠ 0) (θ : ℝ) (f : Hilbert) :
    defectOperator ε hε (KFCausalPhysicalCircleAction.action hbar hh θ f) =
      KFCausalPhysicalCircleAction.action hbar hh θ (defectOperator ε hε f) := by
  apply chargeCoordinates.injective
  rw [chargeCoordinates_defect,KFCausalPhysicalCircleAction.action_coordinates,
    KFCausalPhysicalCircleAction.action_coordinates,chargeCoordinates_defect,jointDefect_action]

#print axioms rightWeight_measurable
#print axioms rightWeight_bound
#print axioms productDefect_coe
#print axioms jointDefect_coe
#print axioms coordinates_defect
#print axioms modePullback_defect
#print axioms pairedCoordinates_defect
#print axioms mixedCoordinates_defect
#print axioms chargeCoordinates_defect
#print axioms jointDefect_action
#print axioms defect_action

end
end UnifiedTheory.Audit.KFCausalClockFloorChargeDefect
