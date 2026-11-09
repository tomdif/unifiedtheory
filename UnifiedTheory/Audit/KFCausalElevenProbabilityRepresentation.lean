/- The eleven controlled physical characteristic limits are represented by
actual probability measures. The projected approximants are tight and
converge weakly to the unique representing probability. -/
import UnifiedTheory.Audit.KFCausalElevenPhaseProjection
import UnifiedTheory.Audit.KFCausalCharacteristicRepresentation
import UnifiedTheory.Audit.KFCausalElevenCountableCharacteristics

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1400000

namespace UnifiedTheory.Audit.KFCausalElevenProbabilityRepresentation
noncomputable section
open MeasureTheory Filter
open scoped Topology
open UnifiedTheory.Audit.KFCausalElevenPhaseProjection
open UnifiedTheory.Audit.KFCausalCanonicalElevenCoordinates (Coefficients encode)
open UnifiedTheory.Audit.KFCausalPhysicalWindowedLaw (phase)
open UnifiedTheory.Audit.KFCausalElevenCountableCharacteristics (ClassicalKernel)

def projectedProbability (μ : Measure FullSpace) (hμ : IsProbabilityMeasure μ) :
    ProbabilityMeasure ElevenSpace := by
  letI := hμ
  exact ⟨μ.map project,Measure.isProbabilityMeasure_map project.continuous.measurable.aemeasurable⟩

 theorem tight_and_represented (μ : ℕ → Measure FullSpace) (hμ : ∀ n, IsProbabilityMeasure (μ n))
    (χ : ClassicalKernel)
    (hc : ∀ z : Coefficients, Tendsto (fun n => ∫ x, phase (encode z) x ∂μ n)
      atTop (𝓝 (χ.value z))) :
    IsTightMeasureSet (Set.range (fun n => (μ n).map project)) ∧
    ∃ ν : ProbabilityMeasure ElevenSpace,
      (∀ z : Coefficients, charFun (ν : Measure ElevenSpace) (coefficientVector z) = χ.value z) ∧
      Tendsto (fun n => projectedProbability (μ n) (hμ n)) atTop (𝓝 ν) := by
  let p n := projectedProbability (μ n) (hμ n)
  let f : ElevenSpace → ℂ := fun z => χ.value (coefficients z)
  have hf : Continuous f := χ.continuous_value.comp coefficients.continuous
  have h0 : f 0 = 1 := by simp only [f,map_zero,χ.value_zero]
  have hp : ∀ z, Tendsto (fun n => charFun (p n : Measure ElevenSpace) z) atTop (𝓝 (f z)) := by
    intro z
    simpa only [p,projectedProbability,ProbabilityMeasure.coe_mk,projected_characteristic,f]
      using hc (coefficients z)
  refine ⟨KFCausalCharacteristicTightness.tight_of_characteristic_limit p f hf h0 hp,?_⟩
  obtain ⟨ν,hν,_⟩ := KFCausalCharacteristicRepresentation.exists_probability_limit p f hf h0 hp
  refine ⟨ν,?_,KFCausalCharacteristicRepresentation.weak_convergence p f hf h0 hp ν hν⟩
  intro z
  simpa only [f,coefficients_vector] using hν (coefficientVector z)

 theorem representation_unique (ν ρ : ProbabilityMeasure ElevenSpace) (χ : ClassicalKernel)
    (hν : ∀ z : Coefficients, charFun (ν : Measure ElevenSpace) (coefficientVector z) = χ.value z)
    (hρ : ∀ z : Coefficients, charFun (ρ : Measure ElevenSpace) (coefficientVector z) = χ.value z) : ν = ρ := by
  apply ProbabilityMeasure.toMeasure_injective
  apply Measure.ext_of_charFun (μ := (ν : Measure ElevenSpace)) (ν := (ρ : Measure ElevenSpace))
  funext z
  have he := vector_coefficients z
  rw [← he]
  exact (hν (coefficients z)).trans (hρ (coefficients z)).symm

#print axioms tight_and_represented
#print axioms representation_unique

end
end UnifiedTheory.Audit.KFCausalElevenProbabilityRepresentation
