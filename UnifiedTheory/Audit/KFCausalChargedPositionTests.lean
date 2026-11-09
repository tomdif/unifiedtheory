/- The symmetric position coordinates in the charged Born law give the
actual canonical position-phase tests on every physical L2 state. -/
import UnifiedTheory.Audit.KFCausalChargeSpectatorMultiplier
import UnifiedTheory.Audit.KFCausalComplementaryPositionTests
import UnifiedTheory.Audit.KFCausalClockFloorRotatedAntiSymbol

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1400000

namespace UnifiedTheory.Audit.KFCausalChargedPositionTests
noncomputable section
open MeasureTheory
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalCoupledLongitudinalFlow (Configuration)
open UnifiedTheory.Audit.KFCausalEuclideanConfiguration (Space euclideanPullback euclideanPullback_coe)
open UnifiedTheory.Audit.KFCausalEuclideanProductCoordinates
open UnifiedTheory.Audit.KFCausalPairedModeCoordinates
open UnifiedTheory.Audit.KFCausalPairedTranslationCoordinates
open UnifiedTheory.Audit.KFCausalChargeSpectatorMultiplier
open UnifiedTheory.Audit.KFCausalComplementaryPhysicalMomenta (physicalDirection)
open UnifiedTheory.Audit.KFCausalClockFloorRotatedAntiSymbol (position symmetricIndex)
open UnifiedTheory.Audit.KFCausalPhysicalCircleAction (chargeCoordinates)
open UnifiedTheory.Audit.KFCausalCanonicalWeylAlgebra (operator operator_coe scalar scalar_norm)
open UnifiedTheory.Audit.KFCausalClockFloorEvolvedCharacteristics (positionFrequency)
open UnifiedTheory.Audit.KFCausalLpPhaseTranslation (modulation modulation_coe)

local instance configurationHaar : Measure.IsAddHaarMeasure (volume : Measure Configuration) :=
  Measure.prod.instIsAddHaarMeasure _ _

def positionTest (h u : ℝ) (i : Fin 2) : Hilbert ≃ₗᵢ[ℂ] Hilbert :=
  operator volume h (u • positionFrequency 0 (physicalDirection i.castSucc),0)

def spectatorPhase (u : ℝ) (i : Fin 2) (x : Block 4) : ℂ := scalar (u*x (symmetricIndex i))

theorem spectatorPhase_measurable (u : ℝ) (i : Fin 2) : Measurable (spectatorPhase u i) := by
  unfold spectatorPhase scalar
  fun_prop

theorem spectatorPhase_norm (u : ℝ) (i : Fin 2) (x : Block 4) : ‖spectatorPhase u i x‖ ≤ 1 :=
  (scalar_norm _).le

theorem symmetric_position (i : Fin 2) (x : Space) :
    positionFrequency 0 (physicalDirection i.castSucc) (KFCausalEuclideanConfiguration.split x) =
      (split 2 4 (modeIsometry x)).2 (symmetricIndex i) := by
  fin_cases i <;> simp [positionFrequency,physicalDirection,KFCausalPhysicalGaussianConcentration.dot,
    KFCausalEuclideanConfiguration.split_apply,Fin.sum_univ_succ,split_snd,modeIsometry,modeEquiv,forward,symmetricIndex]
  all_goals ring

theorem euclidean_positionTest (h u : ℝ) (i : Fin 2) (f : Hilbert) :
    euclideanPullback (positionTest h u i f) =
      euclideanMultiplier (spectatorPhase u i) (spectatorPhase_measurable u i)
        (spectatorPhase_norm u i) (euclideanPullback f) := by
  apply Lp.ext
  filter_upwards [euclideanPullback_coe (positionTest h u i f),
    KFCausalEuclideanConfiguration.split_preserves_volume.quasiMeasurePreserving.ae
      (operator_coe volume h (u • positionFrequency 0 (physicalDirection i.castSucc),0) f),
    euclideanMultiplier_coe (spectatorPhase u i) (spectatorPhase_measurable u i)
      (spectatorPhase_norm u i) (euclideanPullback f),euclideanPullback_coe f] with x he ho hm hf
  simp only [Function.comp_apply] at he hf
  change (positionTest h u i f) (KFCausalEuclideanConfiguration.split x) = _ at ho
  rw [he,ho,hm,hf]
  simp only [ContinuousLinearMap.smul_apply,smul_eq_mul,smul_zero,add_zero,
    symmetric_position,spectatorPhase]

theorem positionTest_charge_coe (h u : ℝ) (i : Fin 2) (f : Hilbert) :
    chargeCoordinates (positionTest h u i f) =ᵐ[volume] fun x =>
      Complex.exp (Complex.I*((u*position i x:ℝ):ℂ))*(chargeCoordinates f) x := by
  rw [← chargeEuclidean_physical,euclidean_positionTest,chargeEuclidean_multiplier,chargeEuclidean_physical]
  exact jointMultiplier_coe (spectatorPhase u i) (spectatorPhase_measurable u i) (spectatorPhase_norm u i) _

def chargePositionTest (u : ℝ) (i : Fin 2) : JointHilbert 2 4 ≃ₗᵢ[ℂ] JointHilbert 2 4 :=
  modulation volume (fun x => u*position i x) (by unfold position; fun_prop)

theorem positionTest_charge (h u : ℝ) (i : Fin 2) (f : Hilbert) :
    chargeCoordinates (positionTest h u i f) = chargePositionTest u i (chargeCoordinates f) := by
  apply Lp.ext
  exact (positionTest_charge_coe h u i f).trans
    (modulation_coe volume (fun x => u*position i x) _ (chargeCoordinates f)).symm

#print axioms spectatorPhase_measurable
#print axioms spectatorPhase_norm
#print axioms symmetric_position
#print axioms euclidean_positionTest
#print axioms positionTest_charge_coe
#print axioms positionTest_charge

end
end UnifiedTheory.Audit.KFCausalChargedPositionTests
