/- The antisymmetric momentum coordinates in the charged Born law give
the actual canonical transverse translation tests on every L2 state. -/
import UnifiedTheory.Audit.KFCausalChargedPositionTests

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1400000

namespace UnifiedTheory.Audit.KFCausalChargedMomentumTests
noncomputable section
open MeasureTheory
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalCoupledLongitudinalFlow (Configuration)
open UnifiedTheory.Audit.KFCausalEuclideanConfiguration (Space euclideanPullback euclideanPullback_coe)
open UnifiedTheory.Audit.KFCausalEuclideanProductCoordinates
open UnifiedTheory.Audit.KFCausalPairedModeCoordinates
open UnifiedTheory.Audit.KFCausalPairedTranslationCoordinates
open UnifiedTheory.Audit.KFCausalComplementaryPhysicalPositions (positionBasis)
open UnifiedTheory.Audit.KFCausalComplementaryPositionTests (antiDirection)
open UnifiedTheory.Audit.KFCausalPhysicalTransverseMomentum (transverseVector split_transverse_add)
open UnifiedTheory.Audit.KFCausalAntisymmetricMomentumCoordinates (transverseVector_explicit)
open UnifiedTheory.Audit.KFCausalClockFloorRotatedAntiSymbol (momentum)
open UnifiedTheory.Audit.KFCausalNormalizedChargeFlow (momentumScale)
open UnifiedTheory.Audit.KFCausalPhysicalCircleAction (chargeCoordinates)
open UnifiedTheory.Audit.KFCausalCanonicalWeylAlgebra (operator operator_coe scalar)
open UnifiedTheory.Audit.KFCausalLpPhaseTranslation (modulation modulation_coe)
open UnifiedTheory.Audit.KFCausalFourierTranslation (translation translation_coe shift_preserves_volume)

local instance configurationHaar : Measure.IsAddHaarMeasure (volume : Measure Configuration) :=
  Measure.prod.instIsAddHaarMeasure _ _

def momentumTest (h u : ℝ) (i : Fin 2) : Hilbert ≃ₗᵢ[ℂ] Hilbert :=
  operator volume h (0,(0,u • antiDirection i))

theorem direction_mode (i : Fin 2) :
    modeIsometry (transverseVector (antiDirection i)) = leftVector (positionBasis i) := by
  rw [transverseVector_explicit]
  fin_cases i <;> ext k <;> rcases k with k | k <;> fin_cases k <;>
    simp [modeIsometry,modeEquiv,forward,antiDirection,leftVector,positionBasis]
  all_goals ring_nf; rw [scale_square]; norm_num

theorem euclidean_momentumTest (h u : ℝ) (i : Fin 2) (f : Hilbert) :
    euclideanPullback (momentumTest h u i f) =
      translation ((h*u) • transverseVector (antiDirection i)) (euclideanPullback f) := by
  apply Lp.ext
  filter_upwards [euclideanPullback_coe (momentumTest h u i f),
    KFCausalEuclideanConfiguration.split_preserves_volume.quasiMeasurePreserving.ae
      (operator_coe volume h (0,(0,u • antiDirection i)) f),
    translation_coe ((h*u) • transverseVector (antiDirection i)) (euclideanPullback f),
    (shift_preserves_volume ((h*u) • transverseVector (antiDirection i))).quasiMeasurePreserving.ae
      (euclideanPullback_coe f)] with x he ho ht hf
  simp only [Function.comp_apply] at he
  change (euclideanPullback f) (x+(h*u) • transverseVector (antiDirection i)) =
    f (KFCausalEuclideanConfiguration.split (x+(h*u) • transverseVector (antiDirection i))) at hf
  change (momentumTest h u i f) (KFCausalEuclideanConfiguration.split x) = _ at ho
  rw [he,ho,ht,hf,split_transverse_add]
  simp only [ContinuousLinearMap.zero_apply,scalar,Complex.ofReal_zero,mul_zero,Complex.exp_zero,one_mul,
    Prod.smul_mk,smul_zero,smul_smul]
  congr 1
  apply Prod.ext
  · simp
  · rfl

theorem momentumTest_charge_coe (h u : ℝ) (i : Fin 2) (f : Hilbert) :
    chargeCoordinates (momentumTest h u i f) =ᵐ[volume] fun x =>
      Complex.exp (Complex.I*((u*momentum h i x:ℝ):ℂ))*(chargeCoordinates f) x := by
  rw [← chargeEuclidean_physical,euclidean_momentumTest]
  filter_upwards [chargeEuclidean_directional_coe (transverseVector (antiDirection i))
    (positionBasis i) (direction_mode i) (h*u) (euclideanPullback f)] with x hx
  rw [hx,chargeEuclidean_physical]
  congr 2
  have hi : inner ℝ (split 2 4 x).1 (positionBasis i) = x (.inl i) := by
    fin_cases i <;> simp [positionBasis,PiLp.inner_apply,RCLike.inner_apply,split_fst]
  rw [hi]
  unfold momentum momentumScale
  push_cast
  ring

def chargeMomentumTest (h u : ℝ) (i : Fin 2) : JointHilbert 2 4 ≃ₗᵢ[ℂ] JointHilbert 2 4 :=
  modulation volume (fun x => u*momentum h i x) (by unfold momentum; fun_prop)

theorem momentumTest_charge (h u : ℝ) (i : Fin 2) (f : Hilbert) :
    chargeCoordinates (momentumTest h u i f) = chargeMomentumTest h u i (chargeCoordinates f) := by
  apply Lp.ext
  exact (momentumTest_charge_coe h u i f).trans
    (modulation_coe volume (fun x => u*momentum h i x) _ (chargeCoordinates f)).symm

#print axioms direction_mode
#print axioms euclidean_momentumTest
#print axioms momentumTest_charge_coe
#print axioms momentumTest_charge

end
end UnifiedTheory.Audit.KFCausalChargedMomentumTests
