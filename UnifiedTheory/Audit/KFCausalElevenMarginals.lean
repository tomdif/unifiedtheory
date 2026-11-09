/- Physical projections and probability marginals of the eleven-coordinate
law. The old ten coordinates and the actual neutral position are retained. -/
import UnifiedTheory.Audit.KFCausalElevenProbabilityRepresentation
import UnifiedTheory.Audit.KFCausalTenProbabilityLimit

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 600000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalElevenMarginals
noncomputable section
open MeasureTheory
open UnifiedTheory.Audit.KFCausalElevenPhaseProjection
open UnifiedTheory.Audit.KFCausalCanonicalElevenCoordinates (Coefficients encode neutral_axis)
open UnifiedTheory.Audit.KFCausalElevenCountableCharacteristics (ClassicalKernel)
open UnifiedTheory.Audit.KFCausalTenPhaseProjection (TenSpace)

def neutralProjection : ElevenSpace →L[ℝ] ℝ where
  toFun x := x (.inr ())
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  cont := by fun_prop

def tenProjection : ElevenSpace →L[ℝ] TenSpace where
  toFun x := WithLp.toLp 2 (fun i => x (.inl i))
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  cont := by fun_prop

theorem neutral_inner (x : ElevenSpace) (v : ℝ) :
    inner ℝ x (coefficientVector (0,v)) = v*neutralProjection x := by
  simp [PiLp.inner_apply,coefficientVector,neutralProjection,RCLike.inner_apply]

theorem ten_inner (x : ElevenSpace) (z : KFCausalCanonicalTenCoordinates.Coefficients) :
    inner ℝ (tenProjection x) (KFCausalTenPhaseProjection.coefficientVector z) =
      inner ℝ x (coefficientVector (z,0)) := by
  simp [PiLp.inner_apply,coefficientVector,KFCausalTenPhaseProjection.coefficientVector,
    tenProjection,RCLike.inner_apply]

theorem ten_encode (z : KFCausalCanonicalTenCoordinates.Coefficients) :
    encode (z,0) = KFCausalCanonicalTenCoordinates.encode z := by
  simp [encode,KFCausalNeutralPositionCharge.frequency]

theorem ten_project (x : FullSpace) : tenProjection (project x) = KFCausalTenPhaseProjection.project x := by
  apply ext_inner_right ℝ
  intro z
  have hz : KFCausalTenPhaseProjection.coefficientVector (KFCausalTenPhaseProjection.coefficients z) = z := by
    apply PiLp.ext
    intro i
    cases i <;> rfl
  rw [← hz,ten_inner,project_inner,coefficients_vector,ten_encode,
    KFCausalTenPhaseProjection.project_inner,KFCausalTenPhaseProjection.coefficients_vector]

theorem neutral_project (x : FullSpace) : neutralProjection (project x) =
    KFCausalNeutralPositionCharge.coordinate (KFCausalPhysicalCanonicalCoordinates.coordinateMap x.1) := by
  have hp := project_inner x (coefficientVector (0,1))
  rw [neutral_inner,coefficients_vector,neutral_axis] at hp
  simpa only [one_mul,KFCausalNeutralPositionCharge.frequency,one_smul,map_zero,inner_zero_left,add_zero] using hp

def neutralMarginal (ν : ProbabilityMeasure ElevenSpace) : ProbabilityMeasure ℝ :=
  ⟨(ν : Measure ElevenSpace).map neutralProjection,
    Measure.isProbabilityMeasure_map neutralProjection.continuous.measurable.aemeasurable⟩

def tenMarginal (ν : ProbabilityMeasure ElevenSpace) : ProbabilityMeasure TenSpace :=
  ⟨(ν : Measure ElevenSpace).map tenProjection,
    Measure.isProbabilityMeasure_map tenProjection.continuous.measurable.aemeasurable⟩

theorem neutral_marginal_characteristic (ν : ProbabilityMeasure ElevenSpace) (v : ℝ) :
    charFun (neutralMarginal ν : Measure ℝ) v =
      charFun (ν : Measure ElevenSpace) (coefficientVector (0,v)) := by
  rw [charFun_apply_real,charFun_apply]
  simp only [← Complex.ofReal_mul]
  change (∫ x, Complex.exp ((v*x:ℝ)*Complex.I) ∂(ν : Measure ElevenSpace).map neutralProjection) = _
  rw [integral_map neutralProjection.continuous.measurable.aemeasurable (by fun_prop)]
  simp only [neutral_inner]

theorem ten_marginal_characteristic (ν : ProbabilityMeasure ElevenSpace)
    (z : KFCausalCanonicalTenCoordinates.Coefficients) :
    charFun (tenMarginal ν : Measure TenSpace) (KFCausalTenPhaseProjection.coefficientVector z) =
      charFun (ν : Measure ElevenSpace) (coefficientVector (z,0)) := by
  rw [charFun_apply,charFun_apply]
  change (∫ x, Complex.exp ((inner ℝ x (KFCausalTenPhaseProjection.coefficientVector z):ℂ)*Complex.I)
    ∂(ν : Measure ElevenSpace).map tenProjection) = _
  rw [integral_map tenProjection.continuous.measurable.aemeasurable (by fun_prop)]
  simp only [ten_inner]

theorem neutral_marginal_eq (ν : ProbabilityMeasure ElevenSpace) (χ : ClassicalKernel)
    (hν : ∀ z, charFun (ν : Measure ElevenSpace) (coefficientVector z) = χ.value z)
    (ρ : ProbabilityMeasure ℝ) (hρ : ∀ v, χ.value (0,v) = charFun (ρ : Measure ℝ) v) :
    neutralMarginal ν = ρ := by
  apply ProbabilityMeasure.toMeasure_injective
  apply Measure.ext_of_charFun
  funext v
  rw [neutral_marginal_characteristic,hν,hρ]

def restrictKernel (χ : ClassicalKernel) : KFCausalClockFloorCountableCharacteristics.ClassicalKernel where
  value z := χ.value (z,0)
  continuous_value := χ.continuous_value.comp (continuous_id.prodMk continuous_const)
  value_zero := χ.value_zero
  norm_le_one z := χ.norm_le_one (z,0)
  value_neg z := by simpa only [Prod.neg_mk,neg_zero] using χ.value_neg (z,0)
  positive N z c := by
    simpa only [Prod.mk_sub_mk,sub_zero] using χ.positive N (fun i => (z i,0)) c

theorem ten_marginal_represents (ν : ProbabilityMeasure ElevenSpace) (χ : ClassicalKernel)
    (hν : ∀ z, charFun (ν : Measure ElevenSpace) (coefficientVector z) = χ.value z)
    (z : KFCausalCanonicalTenCoordinates.Coefficients) :
    charFun (tenMarginal ν : Measure TenSpace) (KFCausalTenPhaseProjection.coefficientVector z) =
      (restrictKernel χ).value z := (ten_marginal_characteristic ν z).trans (hν (z,0))

#print axioms neutral_inner
#print axioms ten_inner
#print axioms ten_encode
#print axioms ten_project
#print axioms neutral_project
#print axioms neutral_marginal_characteristic
#print axioms ten_marginal_characteristic
#print axioms neutral_marginal_eq
#print axioms ten_marginal_represents

end
end UnifiedTheory.Audit.KFCausalElevenMarginals
