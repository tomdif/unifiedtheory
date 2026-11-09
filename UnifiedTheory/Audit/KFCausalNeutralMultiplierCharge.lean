/- Contractive measurable functions of the physical neutral coordinate
commute with the actual charge circle and its zero-charge projection.
The partial Fourier coordinate change is retained throughout. -/
import UnifiedTheory.Audit.KFCausalNeutralPositionCharge
import UnifiedTheory.Audit.KFCausalStandingChargeOperator

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

namespace UnifiedTheory.Audit.KFCausalNeutralMultiplierCharge
noncomputable section
open MeasureTheory
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalCoupledLongitudinalFlow (Configuration)
open UnifiedTheory.Audit.KFCausalEuclideanConfiguration
  (euclideanPullback euclideanPullback_coe)
open UnifiedTheory.Audit.KFCausalEuclideanProductCoordinates
open UnifiedTheory.Audit.KFCausalPairedModeCoordinates
open UnifiedTheory.Audit.KFCausalPairedTranslationCoordinates
open UnifiedTheory.Audit.KFCausalChargeSpectatorMultiplier
open UnifiedTheory.Audit.KFCausalContractiveMultiplier
open UnifiedTheory.Audit.KFCausalPhysicalCircleAction (chargeCoordinates action action_strong_continuous)
open UnifiedTheory.Audit.KFCausalStandingChargeOperator (zeroProjection zeroProjection_integral)

variable (w : ℝ → ℂ) (hw : Measurable w) (hb : ∀ s, ‖w s‖ ≤ 1)

def multiplier : Hilbert →L[ℂ] Hilbert :=
  multiplyL (fun x : Configuration => w (x.2 4)) (hw.comp (by fun_prop)) (fun x => hb _)

theorem multiplier_coe (f : Hilbert) :
    multiplier w hw hb f =ᵐ[volume] fun x => w (x.2 4)*f x :=
  multiplyL_coe _ _ _ f

theorem euclidean_multiplier (f : Hilbert) :
    euclideanPullback (multiplier w hw hb f) =
      euclideanMultiplier (fun x : Block 4 => w (x 3))
        (hw.comp (by fun_prop)) (fun x => hb _) (euclideanPullback f) := by
  apply Lp.ext
  filter_upwards [euclideanPullback_coe (multiplier w hw hb f),
    KFCausalEuclideanConfiguration.split_preserves_volume.quasiMeasurePreserving.ae
      (multiplier_coe w hw hb f),
    euclideanMultiplier_coe (fun x : Block 4 => w (x 3))
      (hw.comp (by fun_prop)) (fun x => hb _) (euclideanPullback f),
    euclideanPullback_coe f] with x he ha hm hf
  simp only [Function.comp_apply] at he hf
  change multiplier w hw hb f (KFCausalEuclideanConfiguration.split x) = _ at ha
  rw [he,ha,hm,hf,KFCausalNeutralPositionCharge.neutral_position]

theorem charge_multiplier_coe (f : Hilbert) :
    chargeCoordinates (multiplier w hw hb f) =ᵐ[volume] fun x =>
      w (x (.inr 3))*chargeCoordinates f x := by
  rw [← chargeEuclidean_physical,euclidean_multiplier,
    chargeEuclidean_multiplier,chargeEuclidean_physical]
  exact jointMultiplier_coe (fun x : Block 4 => w (x 3))
    (hw.comp (by fun_prop)) (fun x => hb _) _

theorem multiplier_action (h : ℝ) (hh : h ≠ 0) (θ : ℝ) (f : Hilbert) :
    multiplier w hw hb (action h hh θ f) = action h hh θ (multiplier w hw hb f) := by
  apply chargeCoordinates.injective
  apply Lp.ext
  let c := KFCausalNormalizedChargeFlow.momentumScale h
  have hc : c ≠ 0 := KFCausalNormalizedChargeFlow.momentumScale_ne_zero h hh
  filter_upwards [charge_multiplier_coe w hw hb (action h hh θ f),
    KFCausalMixedCircleAction.action_coe c hc θ (chargeCoordinates f),
    KFCausalMixedCircleAction.action_coe c hc θ (chargeCoordinates (multiplier w hw hb f)),
    (KFCausalNormalizedChargeFlow.flow_preserves_volume c hc θ).quasiMeasurePreserving.ae
      (charge_multiplier_coe w hw hb f)] with x hv hu ha hf
  rw [hv,KFCausalPhysicalCircleAction.action_coordinates,hu,
    KFCausalPhysicalCircleAction.action_coordinates,ha]
  exact hf.symm

theorem multiplier_projection (h : ℝ) (hh : h ≠ 0) (f : Hilbert) :
    multiplier w hw hb (zeroProjection h hh f) =
      zeroProjection h hh (multiplier w hw hb f) := by
  rw [zeroProjection_integral,zeroProjection_integral,
    (multiplier w hw hb).map_smul_of_tower]
  have hi := (multiplier w hw hb).intervalIntegral_comp_comm
    ((action_strong_continuous h hh f).intervalIntegrable (μ := volume) 0 (2*Real.pi))
  rw [← hi]
  simp_rw [multiplier_action]

#print axioms multiplier_coe
#print axioms euclidean_multiplier
#print axioms charge_multiplier_coe
#print axioms multiplier_action
#print axioms multiplier_projection
end
end UnifiedTheory.Audit.KFCausalNeutralMultiplierCharge
