/- Actual canonical translations in the two symmetric directions and
the neutral direction are bounded momentum phases in the complementary
representation. This includes zero hbar and every L2 state. -/
import UnifiedTheory.Audit.KFCausalComplementaryPositionTests

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1400000

namespace UnifiedTheory.Audit.KFCausalComplementaryMomentumTests
noncomputable section
open MeasureTheory
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalCoupledLongitudinalFlow (Configuration)
open UnifiedTheory.Audit.KFCausalEuclideanConfiguration (Space FrequencyHilbert euclideanPullback euclideanPullback_coe)
open UnifiedTheory.Audit.KFCausalEuclideanProductCoordinates
open UnifiedTheory.Audit.KFCausalPairedModeCoordinates
open UnifiedTheory.Audit.KFCausalPairedTranslationCoordinates
open UnifiedTheory.Audit.KFCausalPhysicalTransverseMomentum (transverseVector split_transverse_add)
open UnifiedTheory.Audit.KFCausalComplementaryPhysicalMomenta
open UnifiedTheory.Audit.KFCausalSymmetricMomentumCoordinates
open UnifiedTheory.Audit.KFCausalChargeTransverseSplit
open UnifiedTheory.Audit.KFCausalChargeDualMomentum
open UnifiedTheory.Audit.KFCausalNormalizedChargeFlow (momentumScale)
open UnifiedTheory.Audit.KFCausalPhysicalCircleAction (chargeCoordinates)
open UnifiedTheory.Audit.KFCausalCanonicalWeylAlgebra (operator operator_coe scalar)
open UnifiedTheory.Audit.KFCausalLpPhaseTranslation (modulation modulation_coe)
open UnifiedTheory.Audit.KFCausalFourierTranslation (translation translation_coe shift_preserves_volume)

local instance configurationHaar : Measure.IsAddHaarMeasure (volume : Measure Configuration) :=
  Measure.prod.instIsAddHaarMeasure _ _

def momentumTest (h u : ℝ) (j : Fin 3) : Hilbert ≃ₗᵢ[ℂ] Hilbert :=
  operator volume h (0,(0,u • physicalDirection j))

def momentumSymbol (h : ℝ) (j : Fin 3) (x : Joint 5 1) : ℝ :=
  momentumScale h*x (.inl (momentumIndex j))

theorem euclidean_momentumTest (h u : ℝ) (j : Fin 3) (f : Hilbert) :
    euclideanPullback (momentumTest h u j f) =
      translation ((h*u) • transverseVector (physicalDirection j)) (euclideanPullback f) := by
  apply Lp.ext
  filter_upwards [euclideanPullback_coe (momentumTest h u j f),
    KFCausalEuclideanConfiguration.split_preserves_volume.quasiMeasurePreserving.ae
      (operator_coe volume h (0,(0,u • physicalDirection j)) f),
    translation_coe ((h*u) • transverseVector (physicalDirection j)) (euclideanPullback f),
    (shift_preserves_volume ((h*u) • transverseVector (physicalDirection j))).quasiMeasurePreserving.ae
      (euclideanPullback_coe f)] with x he ho ht hf
  simp only [Function.comp_apply] at he
  change (euclideanPullback f) (x+(h*u) • transverseVector (physicalDirection j)) =
    f (KFCausalEuclideanConfiguration.split (x+(h*u) • transverseVector (physicalDirection j))) at hf
  change (momentumTest h u j f) (KFCausalEuclideanConfiguration.split x) = _ at ho
  rw [he,ho,ht,hf,split_transverse_add]
  simp only [ContinuousLinearMap.zero_apply,scalar,Complex.ofReal_zero,mul_zero,Complex.exp_zero,one_mul,
    Prod.smul_mk,smul_zero,smul_smul]
  congr 1
  apply Prod.ext
  · simp
  · rfl

theorem charge_momentumTest (h u : ℝ) (j : Fin 3) (f : Hilbert) :
    chargeCoordinates (momentumTest h u j f) =
      translation ((h*u) • rightVector (directionBlock j)) (chargeCoordinates f) := by
  rw [← chargeEuclidean_physical,euclidean_momentumTest]
  have hv : modeIsometry ((h*u) • transverseVector (physicalDirection j)) =
      rightVector ((h*u) • directionBlock j) := by
    rw [map_smul,physicalDirection_mode,rightVector_smul]
  rw [chargeEuclidean_rightTranslation _ _ hv,rightVector_smul,chargeEuclidean_physical]

theorem momentumTest_dual_coe (h u : ℝ) (j : Fin 3) (f : Hilbert) :
    dualPhysical (momentumTest h u j f) =ᵐ[volume] fun x =>
      Complex.exp (Complex.I*((u*momentumSymbol h j x:ℝ):ℂ))*(dualPhysical f) x := by
  change dualMixed (chargeCoordinates (momentumTest h u j f)) =ᵐ[volume] _
  rw [charge_momentumTest]
  filter_upwards [dualMixed_directional_coe (rightVector (directionBlock j)) (direction_clock j)
    (h*u) (chargeCoordinates f)] with x hx
  rw [hx]
  congr 2
  change _ = Complex.I*((u*(momentumScale h*x (.inl (momentumIndex j))):ℝ):ℂ)
  rw [← direction_symbol h j x]
  unfold dualSymbol
  push_cast
  ring

def dualMomentumTest (h u : ℝ) (j : Fin 3) : JointHilbert 5 1 ≃ₗᵢ[ℂ] JointHilbert 5 1 :=
  modulation volume (fun x => u*momentumSymbol h j x) (by unfold momentumSymbol; fun_prop)

theorem momentumTest_dual (h u : ℝ) (j : Fin 3) (f : Hilbert) :
    dualPhysical (momentumTest h u j f) = dualMomentumTest h u j (dualPhysical f) := by
  apply Lp.ext
  exact (momentumTest_dual_coe h u j f).trans
    (modulation_coe volume (fun x => u*momentumSymbol h j x) _ (dualPhysical f)).symm

#print axioms euclidean_momentumTest
#print axioms charge_momentumTest
#print axioms momentumTest_dual_coe
#print axioms momentumTest_dual

end
end UnifiedTheory.Audit.KFCausalComplementaryMomentumTests
