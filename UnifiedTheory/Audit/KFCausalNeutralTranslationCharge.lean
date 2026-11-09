/- Neutral translation commutes with the actual physical charge circle.
The proof follows the existing partial Fourier and charge coordinates. -/
import UnifiedTheory.Audit.KFCausalNeutralTranslationCoordinates
import UnifiedTheory.Audit.KFCausalSymmetricMomentumCoordinates
import UnifiedTheory.Audit.KFCausalMixedRotationMomentumGraph

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1400000

namespace UnifiedTheory.Audit.KFCausalNeutralTranslationCharge
noncomputable section
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalNeutralTranslationCoordinates
open UnifiedTheory.Audit.KFCausalEuclideanProductCoordinates (Block Joint)
open UnifiedTheory.Audit.KFCausalEuclideanConfiguration (euclideanPullback)
open UnifiedTheory.Audit.KFCausalPhysicalCircleAction (chargeCoordinates)
open UnifiedTheory.Audit.KFCausalPairedModeCoordinates (modeIsometry)
open UnifiedTheory.Audit.KFCausalPairedTranslationCoordinates (chargeEuclidean chargeEuclidean_physical)
open UnifiedTheory.Audit.KFCausalSymmetricMomentumCoordinates (rightVector chargeEuclidean_rightTranslation)
open UnifiedTheory.Audit.KFCausalFourierTranslation (translation)

def neutralBlock (r : ℝ) : Block 4 := WithLp.toLp 2 ![0,0,0,r]
def neutralVector (r : ℝ) : Joint 2 4 := rightVector (neutralBlock r)

theorem mode_neutral (r : ℝ) :
    modeIsometry (KFCausalEuclideanConfiguration.split.symm (vector r)) = neutralVector r := by
  have hs : KFCausalEuclideanConfiguration.split.symm (vector r) =
      WithLp.toLp 2 ![0,0,0,0,0,r] := by
    apply KFCausalEuclideanConfiguration.split.injective
    rw [MeasurableEquiv.apply_symm_apply,KFCausalEuclideanConfiguration.split_apply]
    apply Prod.ext
    · rfl
    · funext i
      fin_cases i <;> simp [vector]
  rw [hs]
  ext i
  rcases i with i | i <;> fin_cases i <;>
    simp [modeIsometry,KFCausalPairedModeCoordinates.modeEquiv,
      KFCausalPairedModeCoordinates.forward,neutralVector,rightVector,neutralBlock]

theorem chargeCoordinates_action (r : ℝ) (f : Hilbert) :
    chargeCoordinates (action r f) = translation (neutralVector r) (chargeCoordinates f) := by
  rw [← chargeEuclidean_physical,euclidean_action,
    chargeEuclidean_rightTranslation _ _ (mode_neutral r),chargeEuclidean_physical]
  rfl

theorem charge_flow_neutral (c : ℝ) (hc : c ≠ 0) (θ r : ℝ) :
    KFCausalNormalizedChargeFlow.flowEquiv c hc θ (neutralVector r) = neutralVector r := by
  ext i
  rcases i with i | i <;> fin_cases i <;>
    simp [KFCausalNormalizedChargeFlow.flow_apply,KFCausalNormalizedChargeFlow.dilate,
      KFCausalPairedRotation.rotate,neutralVector,rightVector,neutralBlock]

theorem action_charge (h : ℝ) (hh : h ≠ 0) (r θ : ℝ) (f : Hilbert) :
    action r (KFCausalPhysicalCircleAction.action h hh θ f) =
      KFCausalPhysicalCircleAction.action h hh θ (action r f) := by
  apply chargeCoordinates.injective
  rw [chargeCoordinates_action,KFCausalPhysicalCircleAction.action_coordinates,
    KFCausalPhysicalCircleAction.action_coordinates,chargeCoordinates_action,
    KFCausalMixedRotationMomentumGraph.translation_action,charge_flow_neutral]

#print axioms mode_neutral
#print axioms chargeCoordinates_action
#print axioms charge_flow_neutral
#print axioms action_charge

end
end UnifiedTheory.Audit.KFCausalNeutralTranslationCharge
