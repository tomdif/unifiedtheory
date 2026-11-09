/- Neutral momentum is an exact coordinate marginal of the represented
eleven-coordinate probability. Its canonical test is the existing physical
neutral-momentum test, so independently extracted curves can be identified. -/
import UnifiedTheory.Audit.KFCausalElevenMarginals
import UnifiedTheory.Audit.KFCausalNeutralTemporalCompactness
import UnifiedTheory.Audit.KFCausalNeutralMomentumProbability

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 600000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalElevenMomentumMarginal
noncomputable section
open MeasureTheory
open UnifiedTheory.Audit.KFCausalCoupledLongitudinalFlow (Configuration)
open UnifiedTheory.Audit.KFCausalCanonicalElevenCoordinates (Coefficients encode)
open UnifiedTheory.Audit.KFCausalElevenPhaseProjection
open UnifiedTheory.Audit.KFCausalElevenCountableCharacteristics (ClassicalKernel)
open UnifiedTheory.Audit.KFCausalCanonicalWeylAlgebra (characteristic)
open UnifiedTheory.Audit.KFCausalClockFloorDisplacedClockRightTail (evolvedState)
open UnifiedTheory.Audit.KFCausalNeutralTemporalCompactness (curve)

local instance configurationHaar : Measure.IsAddHaarMeasure (volume : Measure Configuration) :=
  Measure.prod.instIsAddHaarMeasure _ _

def axis (v : ℝ) : Coefficients := ((0,Pi.single 2 v),0)

def momentumProjection : ElevenSpace →L[ℝ] ℝ where
  toFun x := x (.inl (.inr 2))
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  cont := by fun_prop

theorem axis_encode (v : ℝ) : encode (axis v) = KFCausalNeutralCanonicalForm.frequency v := by
  rw [axis,KFCausalElevenMarginals.ten_encode,KFCausalNeutralCharacteristicControl.frequency_momentum]
  simp [KFCausalCanonicalTenCoordinates.encode,KFCausalCanonicalTenDirections.frequency,
    KFCausalCanonicalTenDirections.momentumDirection,Fin.sum_univ_succ]

theorem axis_inner (x : ElevenSpace) (v : ℝ) :
    inner ℝ x (coefficientVector (axis v)) = v*momentumProjection x := by
  simp [PiLp.inner_apply,coefficientVector,axis,momentumProjection,RCLike.inner_apply,Fin.sum_univ_succ]

def marginal (ν : ProbabilityMeasure ElevenSpace) : ProbabilityMeasure ℝ :=
  ⟨(ν : Measure ElevenSpace).map momentumProjection,
    Measure.isProbabilityMeasure_map momentumProjection.continuous.measurable.aemeasurable⟩

theorem marginal_characteristic (ν : ProbabilityMeasure ElevenSpace) (v : ℝ) :
    charFun (marginal ν : Measure ℝ) v = charFun (ν : Measure ElevenSpace) (coefficientVector (axis v)) := by
  rw [charFun_apply_real,charFun_apply]
  simp only [← Complex.ofReal_mul]
  change (∫ x, Complex.exp ((v*x:ℝ)*Complex.I) ∂(ν : Measure ElevenSpace).map momentumProjection) = _
  rw [integral_map momentumProjection.continuous.measurable.aemeasurable (by fun_prop)]
  simp only [axis_inner]

theorem marginal_eq (ν : ProbabilityMeasure ElevenSpace) (χ : ClassicalKernel)
    (hν : ∀ z, charFun (ν : Measure ElevenSpace) (coefficientVector z) = χ.value z)
    (ρ : ProbabilityMeasure ℝ) (hρ : ∀ v, χ.value (axis v) = charFun (ρ : Measure ℝ) v) :
    marginal ν = ρ := by
  apply ProbabilityMeasure.toMeasure_injective
  apply Measure.ext_of_charFun
  funext v
  rw [marginal_characteristic,hν,hρ]

theorem physical_characteristic (ε a h : ℝ) (hε : 0 < ε) (ha : 0 < a) (hne : h ≠ 0)
    (hh : |h| ≤ 2*Real.pi*ε/3) (m g k s : ℝ) (p : Configuration) (t v : ℝ) :
    characteristic volume h (evolvedState ε a h hε ha hne hh m g k s p t) (encode (axis v)) =
      curve ε a h hε ha hne hh m g k s p (t,v) := by
  rw [axis_encode]
  rfl

#print axioms axis_encode
#print axioms axis_inner
#print axioms marginal_characteristic
#print axioms marginal_eq
#print axioms physical_characteristic

end
end UnifiedTheory.Audit.KFCausalElevenMomentumMarginal
