/- Every measurable contractive multiplier depending only on the physical
clock position commutes with the actual charge action. The statement is on
the entire L2 space and does not require a charge-invariant state. -/
import UnifiedTheory.Audit.KFCausalPartialFourierMultiplier
import UnifiedTheory.Audit.KFCausalEuclideanConfiguration
import UnifiedTheory.Audit.KFCausalPhysicalCircleAction

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 800000

namespace UnifiedTheory.Audit.KFCausalClockChargeMultiplier
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
open UnifiedTheory.Audit.KFCausalEuclideanConfiguration (euclideanPullback_coe)
open UnifiedTheory.Audit.KFCausalCoupledLongitudinalFlow (Configuration)

variable (w : ℝ → ℂ) (hw : Measurable w) (hb : ∀ s, ‖w s‖ ≤ 1)

def clockMultiplier : Hilbert →L[ℂ] Hilbert :=
  multiplyL (fun x : Configuration => w x.1) (hw.comp measurable_fst) (fun x => hb x.1)

theorem clockMultiplier_coe (f : Hilbert) :
    clockMultiplier w hw hb f =ᵐ[volume] fun x => w x.1*f x :=
  multiplyL_coe _ _ _ f

def euclideanMultiplier : KFCausalEuclideanConfiguration.FrequencyHilbert →L[ℂ]
    KFCausalEuclideanConfiguration.FrequencyHilbert :=
  (euclideanPullback : Hilbert →L[ℂ] KFCausalEuclideanConfiguration.FrequencyHilbert).comp
    ((clockMultiplier w hw hb).comp
      (euclideanPullback.symm : KFCausalEuclideanConfiguration.FrequencyHilbert →L[ℂ] Hilbert))

theorem euclideanMultiplier_coe (f : KFCausalEuclideanConfiguration.FrequencyHilbert) :
    euclideanMultiplier w hw hb f =ᵐ[volume] fun x => w (x 0)*f x := by
  have he : euclideanPullback (euclideanPullback.symm f) = f := euclideanPullback.apply_symm_apply f
  filter_upwards [euclideanPullback_coe (clockMultiplier w hw hb (euclideanPullback.symm f)),
    euclideanPullback_coe (euclideanPullback.symm f),
    KFCausalEuclideanConfiguration.split_preserves_volume.quasiMeasurePreserving.ae
      (clockMultiplier_coe w hw hb (euclideanPullback.symm f))] with x hm hf hp
  change (euclideanPullback (clockMultiplier w hw hb (euclideanPullback.symm f))) x = _
  rw [hm]
  change (clockMultiplier w hw hb (euclideanPullback.symm f)) (KFCausalEuclideanConfiguration.split x) = _
  rw [hp]
  rw [he] at hf
  rw [hf,KFCausalEuclideanConfiguration.split_apply]
  rfl

def productMultiplier : ProductHilbert 2 4 →L[ℂ] ProductHilbert 2 4 :=
  rightMultiplier 2 4 (fun y => w (y 0)) (hw.comp (by fun_prop)) (fun y => hb (y 0))

theorem productMultiplier_coe (f : ProductHilbert 2 4) :
    productMultiplier w hw hb f =ᵐ[volume] fun z => w (z.2 0)*f z :=
  rightMultiplier_coe _ _ _ _ _ f

def jointMultiplier : JointHilbert 2 4 →L[ℂ] JointHilbert 2 4 :=
  multiplyL (fun x => w (x (.inr 0)))
    (hw.comp (by fun_prop))
    (fun x => hb (x (.inr 0)))

theorem jointMultiplier_coe (f : JointHilbert 2 4) :
    jointMultiplier w hw hb f =ᵐ[volume] fun x => w (x (.inr 0))*f x :=
  multiplyL_coe _ _ _ f

theorem coordinates_multiplier (f : ProductHilbert 2 4) :
    coordinates 2 4 (productMultiplier w hw hb f) = jointMultiplier w hw hb (coordinates 2 4 f) := by
  apply Lp.ext
  filter_upwards [coordinates_coe 2 4 (productMultiplier w hw hb f),
    coordinates_coe 2 4 f, jointMultiplier_coe w hw hb (coordinates 2 4 f),
    (split_preserves_volume 2 4).quasiMeasurePreserving.ae (productMultiplier_coe w hw hb f)] with x hc hf hd hp
  simp only [Function.comp_apply] at hc hf
  rw [hc,hp,hd,hf,split_snd]

theorem modePullback_multiplier (f : JointHilbert 2 4) :
    modePullback (jointMultiplier w hw hb f) = euclideanMultiplier w hw hb (modePullback f) := by
  apply Lp.ext
  filter_upwards [modePullback_coe (jointMultiplier w hw hb f), modePullback_coe f,
    euclideanMultiplier_coe w hw hb (modePullback f),
    mode_preserves_volume.quasiMeasurePreserving.ae (jointMultiplier_coe w hw hb f)] with x hc hf hd hj
  simp only [Function.comp_apply] at hc hf
  rw [hc,hj,hd,hf]
  rfl

theorem pairedCoordinates_multiplier (f : Hilbert) :
    pairedCoordinates (clockMultiplier w hw hb f) = productMultiplier w hw hb (pairedCoordinates f) := by
  apply (coordinates 2 4).injective
  apply modePullback.injective
  rw [coordinates_multiplier,modePullback_multiplier]
  have hc (g : Hilbert) : modePullback (coordinates 2 4 (pairedCoordinates g)) =
      euclideanPullback g := by
    simp only [pairedCoordinates,LinearIsometryEquiv.trans_apply,
      LinearIsometryEquiv.apply_symm_apply]
  rw [hc,hc]
  change euclideanPullback (clockMultiplier w hw hb f) =
    euclideanPullback (clockMultiplier w hw hb (euclideanPullback.symm (euclideanPullback f)))
  rw [LinearIsometryEquiv.symm_apply_apply]

theorem mixedCoordinates_multiplier (f : Hilbert) :
    mixedCoordinates (clockMultiplier w hw hb f) = productMultiplier w hw hb (mixedCoordinates f) := by
  change leftFourier 2 4 (pairedCoordinates (clockMultiplier w hw hb f)) =
    productMultiplier w hw hb (leftFourier 2 4 (pairedCoordinates f))
  rw [pairedCoordinates_multiplier]
  exact leftFourier_commutes _ _ _ _ _ _

theorem chargeCoordinates_multiplier (f : Hilbert) :
    chargeCoordinates (clockMultiplier w hw hb f) = jointMultiplier w hw hb (chargeCoordinates f) := by
  change coordinates 2 4 (mixedCoordinates (clockMultiplier w hw hb f)) = _
  rw [mixedCoordinates_multiplier,coordinates_multiplier]
  rfl

theorem jointMultiplier_action (c : ℝ) (hc : c ≠ 0) (θ : ℝ) (f : JointHilbert 2 4) :
    jointMultiplier w hw hb (KFCausalMixedCircleAction.action c hc θ f) =
      KFCausalMixedCircleAction.action c hc θ (jointMultiplier w hw hb f) := by
  apply Lp.ext
  filter_upwards [jointMultiplier_coe w hw hb (KFCausalMixedCircleAction.action c hc θ f),
    KFCausalMixedCircleAction.action_coe c hc θ f,
    KFCausalMixedCircleAction.action_coe c hc θ (jointMultiplier w hw hb f),
    (KFCausalNormalizedChargeFlow.flow_preserves_volume c hc θ).quasiMeasurePreserving.ae
      (jointMultiplier_coe w hw hb f)] with x hd ha hb hj
  simp only [Function.comp_apply] at ha hb
  rw [hd,ha,hb,hj,KFCausalNormalizedChargeFlow.flow_clock]

theorem multiplier_action (hbar : ℝ) (hh : hbar ≠ 0) (θ : ℝ) (f : Hilbert) :
    clockMultiplier w hw hb (KFCausalPhysicalCircleAction.action hbar hh θ f) =
      KFCausalPhysicalCircleAction.action hbar hh θ (clockMultiplier w hw hb f) := by
  apply chargeCoordinates.injective
  rw [chargeCoordinates_multiplier,KFCausalPhysicalCircleAction.action_coordinates,
    KFCausalPhysicalCircleAction.action_coordinates,chargeCoordinates_multiplier,jointMultiplier_action]

#print axioms clockMultiplier_coe
#print axioms euclideanMultiplier_coe
#print axioms productMultiplier_coe
#print axioms jointMultiplier_coe
#print axioms coordinates_multiplier
#print axioms modePullback_multiplier
#print axioms pairedCoordinates_multiplier
#print axioms mixedCoordinates_multiplier
#print axioms chargeCoordinates_multiplier
#print axioms jointMultiplier_action
#print axioms multiplier_action

end
end UnifiedTheory.Audit.KFCausalClockChargeMultiplier
