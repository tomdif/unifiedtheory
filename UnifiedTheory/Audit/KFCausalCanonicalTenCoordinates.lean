/- The controlled canonical family has ten independent real parameters.
An explicit inverse recovers them from physical test frequencies. Its
omitted directions are neutral position and clock momentum. -/
import UnifiedTheory.Audit.KFCausalCanonicalTenDirections

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1600000

namespace UnifiedTheory.Audit.KFCausalCanonicalTenCoordinates
noncomputable section
open UnifiedTheory.Audit.KFCausalCoupledLongitudinalFlow (Configuration)
open UnifiedTheory.Audit.KFCausalTransverseDilationFlow (Transverse)
open UnifiedTheory.Audit.KFCausalPairedModeCoordinates (scale scale_square)
open UnifiedTheory.Audit.KFCausalCanonicalWeylAlgebra (Frequency)
open UnifiedTheory.Audit.KFCausalCanonicalTenDirections

abbrev Coefficients := (Fin 5 → ℝ) × (Fin 5 → ℝ)

def encode : Coefficients →L[ℝ] Frequency (X := Configuration) where
  toFun z := frequency z.1 z.2
  map_add' x y := by
    apply Prod.ext
    · simp [frequency,add_smul,Finset.sum_add_distrib]
    · change (∑ j, ((0,(x.2 j+y.2 j) • momentumDirection j) : Configuration)) =
        (∑ j, (0,x.2 j • momentumDirection j))+(∑ j, (0,y.2 j • momentumDirection j))
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro j _
      apply Prod.ext
      · simp
      · exact add_smul _ _ _
  map_smul' c x := by
    apply Prod.ext
    · simp [frequency,Finset.smul_sum,smul_smul]
    · simp [frequency,Finset.smul_sum,Prod.smul_mk,smul_smul]
  cont := by unfold frequency; fun_prop

def probe (i : Fin 5) : Transverse := Pi.single i 1

def decode (z : Frequency (X := Configuration)) : Coefficients :=
  (![z.1 (1,0),scale*(z.1 (0,probe 0)-z.1 (0,probe 1)),
      scale*(z.1 (0,probe 2)-z.1 (0,probe 3)),
      scale*(z.1 (0,probe 0)+z.1 (0,probe 1)),scale*(z.1 (0,probe 2)+z.1 (0,probe 3))],
    ![scale*(z.2.2 0+z.2.2 1),scale*(z.2.2 2+z.2.2 3),z.2.2 4,
      scale*(z.2.2 0-z.2.2 1),scale*(z.2.2 2-z.2.2 3)])

theorem decode_encode (z : Coefficients) : decode (encode z) = z := by
  apply Prod.ext
  all_goals funext i; fin_cases i
  all_goals simp [encode,decode,frequency,positionLinear,momentumDirection,probe,
    KFCausalClockFloorEvolvedCharacteristics.positionFrequency,
    KFCausalPhysicalGaussianConcentration.dot,KFCausalComplementaryPositionTests.antiDirection,
    KFCausalComplementaryPhysicalMomenta.physicalDirection,Fin.sum_univ_succ]
  all_goals ring_nf; rw [scale_square]; ring

theorem encode_injective : Function.Injective encode := Function.LeftInverse.injective decode_encode

theorem omitted_coordinates (z : Coefficients) : (encode z).1 (0,probe 4) = 0 ∧ (encode z).2.1 = 0 := by
  simp [encode,frequency,positionLinear,momentumDirection,probe,
    KFCausalClockFloorEvolvedCharacteristics.positionFrequency,
    KFCausalPhysicalGaussianConcentration.dot,KFCausalComplementaryPositionTests.antiDirection,
    KFCausalComplementaryPhysicalMomenta.physicalDirection,Fin.sum_univ_succ]

#print axioms decode_encode
#print axioms encode_injective
#print axioms omitted_coordinates

end
end UnifiedTheory.Audit.KFCausalCanonicalTenCoordinates
