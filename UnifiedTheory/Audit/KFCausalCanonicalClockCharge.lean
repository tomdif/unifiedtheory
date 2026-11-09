/- Canonical clock translation commutes with the actual physical charge
circle on all L2 states, through the actual mixed and paired coordinates.
No charge-zero state or Hamiltonian form invariance is assumed. -/
import UnifiedTheory.Audit.KFCausalSymmetricMomentumCoordinates
import UnifiedTheory.Audit.KFCausalMixedRotationMomentumGraph
import UnifiedTheory.Audit.KFCausalCanonicalClockDerivative

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1200000

namespace UnifiedTheory.Audit.KFCausalCanonicalClockCharge
noncomputable section
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalEuclideanProductCoordinates (Block Joint)
open UnifiedTheory.Audit.KFCausalEuclideanConfiguration (clockVector)
open UnifiedTheory.Audit.KFCausalPhysicalCircleAction (chargeCoordinates)
open UnifiedTheory.Audit.KFCausalPairedModeCoordinates (modeIsometry)
open UnifiedTheory.Audit.KFCausalPairedTranslationCoordinates (chargeEuclidean chargeEuclidean_physical)
open UnifiedTheory.Audit.KFCausalSymmetricMomentumCoordinates (rightVector chargeEuclidean_rightTranslation)
open UnifiedTheory.Audit.KFCausalConfigurationTranslation (translation)
open UnifiedTheory.Audit.KFCausalClockFourierDiagonalization (euclidean_clock_translation)

def clockBlock (r : ℝ) : Block 4 := WithLp.toLp 2 ![r,0,0,0]
def clockJoint (r : ℝ) : Joint 2 4 := rightVector (clockBlock r)

theorem mode_clock (r : ℝ) : modeIsometry (r • clockVector) = clockJoint r := by
  ext i
  rcases i with i | i <;> fin_cases i <;>
    simp [modeIsometry,KFCausalPairedModeCoordinates.modeEquiv,KFCausalPairedModeCoordinates.forward,
      clockJoint,rightVector,clockBlock,clockVector]

theorem chargeCoordinates_translation (r : ℝ) (f : Hilbert) :
    chargeCoordinates (translation r f) =
      KFCausalFourierTranslation.translation (clockJoint r) (chargeCoordinates f) := by
  rw [← chargeEuclidean_physical,euclidean_clock_translation,
    chargeEuclidean_rightTranslation _ _ (mode_clock r),chargeEuclidean_physical]
  rfl

theorem charge_flow_clock (c : ℝ) (hc : c ≠ 0) (θ r : ℝ) :
    KFCausalNormalizedChargeFlow.flowEquiv c hc θ (clockJoint r) = clockJoint r := by
  ext i
  rcases i with i | i <;> fin_cases i <;>
    simp [KFCausalNormalizedChargeFlow.flow_apply,KFCausalNormalizedChargeFlow.dilate,
      KFCausalPairedRotation.rotate,clockJoint,rightVector,clockBlock]

theorem translation_charge (h : ℝ) (hh : h ≠ 0) (r θ : ℝ) (f : Hilbert) :
    translation r (KFCausalPhysicalCircleAction.action h hh θ f) =
      KFCausalPhysicalCircleAction.action h hh θ (translation r f) := by
  apply chargeCoordinates.injective
  rw [chargeCoordinates_translation,KFCausalPhysicalCircleAction.action_coordinates,
    KFCausalPhysicalCircleAction.action_coordinates,chargeCoordinates_translation,
    KFCausalMixedRotationMomentumGraph.translation_action,charge_flow_clock]

theorem translation_increment_charge (h : ℝ) (hh : h ≠ 0) (r θ : ℝ) (f : Hilbert) :
    ‖translation r (KFCausalPhysicalCircleAction.action h hh θ f)-
      KFCausalPhysicalCircleAction.action h hh θ f‖ = ‖translation r f-f‖ := by
  rw [translation_charge,← map_sub,LinearIsometryEquiv.norm_map]

#print axioms mode_clock
#print axioms chargeCoordinates_translation
#print axioms charge_flow_clock
#print axioms translation_charge
#print axioms translation_increment_charge

end
end UnifiedTheory.Audit.KFCausalCanonicalClockCharge
