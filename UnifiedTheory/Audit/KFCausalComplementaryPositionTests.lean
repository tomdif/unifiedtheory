/- The bounded exponentials of the two identified positions are the
actual canonical Weyl position tests. Their complementary-coordinate
representatives hold for every L2 state, including evolved form states. -/
import UnifiedTheory.Audit.KFCausalComplementaryPhysicalPositions
import UnifiedTheory.Audit.KFCausalClockFloorEvolvedCharacteristics

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1400000

namespace UnifiedTheory.Audit.KFCausalComplementaryPositionTests
noncomputable section
open MeasureTheory
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalCoupledLongitudinalFlow (Configuration)
open UnifiedTheory.Audit.KFCausalTransverseDilationFlow (Transverse)
open UnifiedTheory.Audit.KFCausalEuclideanConfiguration (Space FrequencyHilbert euclideanPullback euclideanPullback_coe)
open UnifiedTheory.Audit.KFCausalEuclideanProductCoordinates
open UnifiedTheory.Audit.KFCausalPairedModeCoordinates
open UnifiedTheory.Audit.KFCausalPairedTranslationCoordinates
open UnifiedTheory.Audit.KFCausalChargePositionPhase
open UnifiedTheory.Audit.KFCausalComplementaryPhysicalPositions
open UnifiedTheory.Audit.KFCausalChargeTransverseSplit
open UnifiedTheory.Audit.KFCausalChargeDualMomentum
open UnifiedTheory.Audit.KFCausalComplementaryChargeSymbol
open UnifiedTheory.Audit.KFCausalPhysicalCircleAction (chargeCoordinates)
open UnifiedTheory.Audit.KFCausalLpPhaseTranslation (modulation modulation_coe)
open UnifiedTheory.Audit.KFCausalCanonicalWeylAlgebra (operator operator_coe scalar)
open UnifiedTheory.Audit.KFCausalClockFloorEvolvedCharacteristics (positionFrequency)

local instance configurationHaar : Measure.IsAddHaarMeasure (volume : Measure Configuration) :=
  Measure.prod.instIsAddHaarMeasure _ _

def positionTest (t : ℝ) (i : Fin 2) : Hilbert ≃ₗᵢ[ℂ] Hilbert :=
  euclideanPullback.trans ((modulation volume (fun x => t*positionSymbol i x)
    (measurable_const.mul (positionSymbol_continuous i).measurable)).trans euclideanPullback.symm)

def antiDirection (i : Fin 2) : Transverse :=
  ![![scale,-scale,0,0,0],![0,0,scale,-scale,0]] i

theorem antiDirection_position (i : Fin 2) (x : Space) :
    positionFrequency 0 (antiDirection i) (KFCausalEuclideanConfiguration.split x) = positionSymbol i x := by
  fin_cases i <;> simp [positionFrequency,antiDirection,positionSymbol,
    KFCausalPhysicalGaussianConcentration.dot,KFCausalEuclideanConfiguration.split_apply,Fin.sum_univ_succ]
  all_goals ring

theorem positionTest_canonical (h t : ℝ) (i : Fin 2) (f : Hilbert) :
    positionTest t i f = operator volume h (t • positionFrequency 0 (antiDirection i),0) f := by
  apply euclideanPullback.injective
  change euclideanPullback (euclideanPullback.symm
    (modulation volume (fun x => t*positionSymbol i x) _ (euclideanPullback f))) = _
  rw [LinearIsometryEquiv.apply_symm_apply]
  apply Lp.ext
  filter_upwards [modulation_coe volume (fun x => t*positionSymbol i x)
      (measurable_const.mul (positionSymbol_continuous i).measurable) (euclideanPullback f),
    euclideanPullback_coe (operator volume h (t • positionFrequency 0 (antiDirection i),0) f),
    KFCausalEuclideanConfiguration.split_preserves_volume.quasiMeasurePreserving.ae
      (operator_coe volume h (t • positionFrequency 0 (antiDirection i),0) f),
    euclideanPullback_coe f] with x hm he ho hf
  simp only [Function.comp_apply] at he hf
  rw [hm,he,ho,hf]
  simp only [smul_zero,add_zero,ContinuousLinearMap.smul_apply,smul_eq_mul,
    antiDirection_position,scalar,KFCausalLpPhaseTranslation.phase]

theorem euclidean_modulation_positionPhase (t : ℝ) (i : Fin 2) (f : FrequencyHilbert) :
    modulation volume (fun x => t*positionSymbol i x) (measurable_const.mul (positionSymbol_continuous i).measurable) f =
      positionPhase ((-t*positionScale) • positionBasis i) f := by
  apply Lp.ext
  filter_upwards [modulation_coe volume (fun x => t*positionSymbol i x)
      (measurable_const.mul (positionSymbol_continuous i).measurable) f,
    positionPhase_coe ((-t*positionScale) • positionBasis i) f] with x hm hp
  rw [hm,hp,KFCausalDirectionalTranslationMomentum.phase_eq]
  unfold KFCausalLpPhaseTranslation.phase
  congr 2
  dsimp only
  rw [← position_basis_symbol i x,inner_neg_right]
  push_cast
  ring

theorem charge_positionTest (t : ℝ) (i : Fin 2) (f : Hilbert) :
    chargeCoordinates (positionTest t i f) =
      KFCausalFourierTranslation.translation ((t*positionScale) • leftVector (positionBasis i)) (chargeCoordinates f) := by
  rw [← chargeEuclidean_physical]
  change chargeEuclidean (euclideanPullback (euclideanPullback.symm
    (modulation volume (fun x => t*positionSymbol i x) _ (euclideanPullback f)))) = _
  rw [LinearIsometryEquiv.apply_symm_apply,euclidean_modulation_positionPhase,chargeEuclidean_positionPhase]
  simp only [neg_mul,neg_smul,neg_neg,leftVector_smul,chargeEuclidean_physical]

theorem positionTest_dual_coe (t : ℝ) (i : Fin 2) (f : Hilbert) :
    dualPhysical (positionTest t i f) =ᵐ[volume] fun x =>
      Complex.exp (Complex.I*((t*complementaryPosition i x:ℝ):ℂ))*(dualPhysical f) x := by
  change dualMixed (chargeCoordinates (positionTest t i f)) =ᵐ[volume] _
  rw [charge_positionTest]
  filter_upwards [dualMixed_directional_coe (leftVector (positionBasis i)) rfl
    (t*positionScale) (chargeCoordinates f)] with x hx
  rw [hx]
  congr 2
  rw [← position_dual_symbol i x]
  unfold dualSymbol
  push_cast
  ring

def dualPositionTest (t : ℝ) (i : Fin 2) : JointHilbert 5 1 ≃ₗᵢ[ℂ] JointHilbert 5 1 :=
  modulation volume (fun x => t*complementaryPosition i x) (by
    unfold complementaryPosition
    fun_prop)

theorem positionTest_dual (t : ℝ) (i : Fin 2) (f : Hilbert) :
    dualPhysical (positionTest t i f) = dualPositionTest t i (dualPhysical f) := by
  apply Lp.ext
  exact (positionTest_dual_coe t i f).trans
    (modulation_coe volume (fun x => t*complementaryPosition i x) _ (dualPhysical f)).symm

#print axioms antiDirection_position
#print axioms positionTest_canonical
#print axioms euclidean_modulation_positionPhase
#print axioms charge_positionTest
#print axioms positionTest_dual_coe
#print axioms positionTest_dual

end
end UnifiedTheory.Audit.KFCausalComplementaryPositionTests
