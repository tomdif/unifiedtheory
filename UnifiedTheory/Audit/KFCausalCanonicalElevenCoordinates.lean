/- Add neutral position to the ten controlled canonical coordinates.
The eleven coefficients are independent. Clock momentum is still absent.
The exact ordered product adds no phase error in this ordering. -/
import UnifiedTheory.Audit.KFCausalCanonicalTenCoordinates
import UnifiedTheory.Audit.KFCausalNeutralPositionFrequencyControl

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 800000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalCanonicalElevenCoordinates
noncomputable section
open MeasureTheory
open UnifiedTheory.Audit.KFCausalCoupledLongitudinalFlow (Configuration)
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalCanonicalWeylAlgebra (Frequency operator scalar)
open UnifiedTheory.Audit.KFCausalNeutralPositionCharge (frequency action coordinate)
open UnifiedTheory.Audit.KFCausalCanonicalTenCoordinates (probe)

local instance configurationHaar : Measure.IsAddHaarMeasure (volume : Measure Configuration) :=
  Measure.prod.instIsAddHaarMeasure _ _

abbrev Coefficients := KFCausalCanonicalTenCoordinates.Coefficients × ℝ

def encode : Coefficients →L[ℝ] Frequency (X := Configuration) where
  toFun z := (frequency z.2,0)+KFCausalCanonicalTenCoordinates.encode z.1
  map_add' x y := by
    simp only [Prod.fst_add,Prod.snd_add,map_add,frequency,add_smul]
    (apply Prod.ext <;> simp)
    abel
  map_smul' c x := by
    change (frequency (c*x.2),0)+KFCausalCanonicalTenCoordinates.encode (c • x.1) =
      c • ((frequency x.2,0)+KFCausalCanonicalTenCoordinates.encode x.1)
    rw [map_smul,smul_add]
    congr 1
    apply Prod.ext <;> simp [frequency,smul_smul]
  cont := by unfold frequency; fun_prop

def decode (z : Frequency (X := Configuration)) : Coefficients :=
  (KFCausalCanonicalTenCoordinates.decode z,z.1 (0,probe 4))

theorem decode_neutral (z : Frequency (X := Configuration)) (v : ℝ) :
    KFCausalCanonicalTenCoordinates.decode ((frequency v,0)+z) =
      KFCausalCanonicalTenCoordinates.decode z := by
  simp [KFCausalCanonicalTenCoordinates.decode,frequency,coordinate,probe]

theorem decode_encode (z : Coefficients) : decode (encode z) = z := by
  apply Prod.ext
  · exact (decode_neutral (KFCausalCanonicalTenCoordinates.encode z.1) z.2).trans
      (KFCausalCanonicalTenCoordinates.decode_encode z.1)
  · change (frequency z.2+(KFCausalCanonicalTenCoordinates.encode z.1).1) (0,probe 4) = z.2
    rw [ContinuousLinearMap.add_apply,(KFCausalCanonicalTenCoordinates.omitted_coordinates z.1).1,add_zero]
    simp [frequency,coordinate,probe]

theorem encode_injective : Function.Injective encode := Function.LeftInverse.injective decode_encode

theorem omitted_clock_momentum (z : Coefficients) : (encode z).2.1 = 0 := by
  change (0+(KFCausalCanonicalTenCoordinates.encode z.1).2).1 = 0
  rw [zero_add]
  exact (KFCausalCanonicalTenCoordinates.omitted_coordinates z.1).2

theorem neutral_axis (v : ℝ) : encode (0,v) = (frequency v,0) := by
  change (frequency v,0)+KFCausalCanonicalTenCoordinates.encode 0 = _
  rw [map_zero,add_zero]

theorem operator_product (h : ℝ) (z : Coefficients) (f : Hilbert) :
    operator volume h (encode z) f =
      action z.2 (operator volume h (KFCausalCanonicalTenCoordinates.encode z.1) f) := by
  have he := KFCausalCanonicalWeylAlgebra.operator_product volume h
    (frequency z.2,(0:Configuration)) (KFCausalCanonicalTenCoordinates.encode z.1) f
  rw [map_zero,mul_zero] at he
  simp only [scalar,Complex.ofReal_zero,mul_zero,Complex.exp_zero,one_smul] at he
  rw [KFCausalNeutralPositionCutoffCharacteristic.operator_phase] at he
  exact he.symm

theorem displacement_bound (h : ℝ) (z : Coefficients) (f : Hilbert) :
    ‖operator volume h (encode z) f-f‖ ≤
      ‖operator volume h (KFCausalCanonicalTenCoordinates.encode z.1) f-f‖+‖action z.2 f-f‖ := by
  rw [operator_product]
  have ht := norm_sub_le_norm_sub_add_norm_sub
    (action z.2 (operator volume h (KFCausalCanonicalTenCoordinates.encode z.1) f)) (action z.2 f) f
  rw [← map_sub,(action z.2).norm_map] at ht
  exact ht

#print axioms decode_neutral
#print axioms decode_encode
#print axioms encode_injective
#print axioms omitted_clock_momentum
#print axioms neutral_axis
#print axioms operator_product
#print axioms displacement_bound

end
end UnifiedTheory.Audit.KFCausalCanonicalElevenCoordinates
