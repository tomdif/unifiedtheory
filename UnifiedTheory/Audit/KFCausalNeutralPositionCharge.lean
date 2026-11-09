/- The bare neutral position phase commutes with the actual charge circle.
This is a whole-L2 identity; it does not assert matter-domain preservation. -/
import UnifiedTheory.Audit.KFCausalChargeSpectatorMultiplier
import UnifiedTheory.Audit.KFCausalPhysicalMomentumModulation
import UnifiedTheory.Audit.KFCausalPhysicalCircleAction

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1200000

namespace UnifiedTheory.Audit.KFCausalNeutralPositionCharge
noncomputable section
open MeasureTheory
open UnifiedTheory.Audit.KFCausalCoupledLongitudinalFlow (Configuration)
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalPhysicalMomentumModulation
open UnifiedTheory.Audit.KFCausalCanonicalWeylAlgebra (scalar scalar_norm)
open UnifiedTheory.Audit.KFCausalEuclideanConfiguration (Space euclideanPullback euclideanPullback_coe)
open UnifiedTheory.Audit.KFCausalEuclideanProductCoordinates
open UnifiedTheory.Audit.KFCausalPairedModeCoordinates
open UnifiedTheory.Audit.KFCausalPairedTranslationCoordinates
open UnifiedTheory.Audit.KFCausalChargeSpectatorMultiplier
open UnifiedTheory.Audit.KFCausalPhysicalCircleAction (chargeCoordinates)

def coordinate : Configuration →L[ℝ] ℝ where
  toFun x := x.2 4
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  cont := by fun_prop

def frequency (v : ℝ) : Configuration →L[ℝ] ℝ := v • coordinate
def action (v : ℝ) : Hilbert ≃ₗᵢ[ℂ] Hilbert := modulation (frequency v)

theorem frequency_apply (v : ℝ) (x : Configuration) : frequency v x = v*x.2 4 := rfl

theorem action_coe (v : ℝ) (f : Hilbert) :
    action v f =ᵐ[volume] fun x => scalar (v*x.2 4)*f x := modulation_coe _ _

theorem action_inverse (v : ℝ) (f : Hilbert) : action (-v) (action v f) = f := by
  have hn : frequency (-v) = -frequency v := by
    apply ContinuousLinearMap.ext
    intro x
    simp [frequency_apply]
  simpa only [action,hn] using modulation_inverse (frequency v) f

def spectatorPhase (v : ℝ) (x : Block 4) : ℂ := scalar (v*x 3)
theorem spectatorPhase_measurable (v : ℝ) : Measurable (spectatorPhase v) := by
  unfold spectatorPhase scalar
  fun_prop
theorem spectatorPhase_norm (v : ℝ) (x : Block 4) : ‖spectatorPhase v x‖ ≤ 1 :=
  (scalar_norm _).le

theorem neutral_position (x : Space) :
    (KFCausalEuclideanConfiguration.split x).2 4 =
      (split 2 4 (modeIsometry x)).2 3 := rfl

theorem euclidean_action (v : ℝ) (f : Hilbert) :
    euclideanPullback (action v f) =
      euclideanMultiplier (spectatorPhase v) (spectatorPhase_measurable v)
        (spectatorPhase_norm v) (euclideanPullback f) := by
  apply Lp.ext
  filter_upwards [euclideanPullback_coe (action v f),
    KFCausalEuclideanConfiguration.split_preserves_volume.quasiMeasurePreserving.ae (action_coe v f),
    euclideanMultiplier_coe (spectatorPhase v) (spectatorPhase_measurable v)
      (spectatorPhase_norm v) (euclideanPullback f),euclideanPullback_coe f] with x he ha hm hf
  simp only [Function.comp_apply] at he hf
  change action v f (KFCausalEuclideanConfiguration.split x) = _ at ha
  rw [he,ha,hm,hf,neutral_position]
  rfl

theorem charge_action_coe (v : ℝ) (f : Hilbert) :
    chargeCoordinates (action v f) =ᵐ[volume] fun x =>
      scalar (v*x (.inr 3))*(chargeCoordinates f) x := by
  rw [← chargeEuclidean_physical,euclidean_action,chargeEuclidean_multiplier,chargeEuclidean_physical]
  exact jointMultiplier_coe (spectatorPhase v) (spectatorPhase_measurable v) (spectatorPhase_norm v) _

theorem action_charge (h : ℝ) (hne : h ≠ 0) (v θ : ℝ) (f : Hilbert) :
    action v (KFCausalPhysicalCircleAction.action h hne θ f) =
      KFCausalPhysicalCircleAction.action h hne θ (action v f) := by
  apply chargeCoordinates.injective
  apply Lp.ext
  let c := KFCausalNormalizedChargeFlow.momentumScale h
  have hc : c ≠ 0 := KFCausalNormalizedChargeFlow.momentumScale_ne_zero h hne
  filter_upwards [charge_action_coe v (KFCausalPhysicalCircleAction.action h hne θ f),
    KFCausalMixedCircleAction.action_coe c hc θ (chargeCoordinates f),
    KFCausalMixedCircleAction.action_coe c hc θ (chargeCoordinates (action v f)),
    (KFCausalNormalizedChargeFlow.flow_preserves_volume c hc θ).quasiMeasurePreserving.ae
      (charge_action_coe v f)] with x hv hu ha hf
  rw [hv,KFCausalPhysicalCircleAction.action_coordinates,hu,
    KFCausalPhysicalCircleAction.action_coordinates,ha]
  exact hf.symm

#print axioms action_inverse
#print axioms charge_action_coe
#print axioms action_charge

end
end UnifiedTheory.Audit.KFCausalNeutralPositionCharge
