/- The ten controlled physical characteristic limits are represented by
actual probability measures. The projected approximants are tight and
converge weakly to the unique representing probability. -/
import UnifiedTheory.Audit.KFCausalTenPhaseProjection
import UnifiedTheory.Audit.KFCausalCharacteristicRepresentation
import UnifiedTheory.Audit.KFCausalClockFloorCountableCharacteristics

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1400000

namespace UnifiedTheory.Audit.KFCausalTenProbabilityLimit
noncomputable section
open MeasureTheory Filter
open scoped Topology
open UnifiedTheory.Audit.KFCausalTenPhaseProjection
open UnifiedTheory.Audit.KFCausalCanonicalTenCoordinates (Coefficients encode)
open UnifiedTheory.Audit.KFCausalPhysicalWindowedLaw (phase)
open UnifiedTheory.Audit.KFCausalClockFloorCountableCharacteristics (ClassicalKernel)

def projectedProbability (μ : Measure FullSpace) (hμ : IsProbabilityMeasure μ) :
    ProbabilityMeasure TenSpace := by
  letI := hμ
  exact ⟨μ.map project,Measure.isProbabilityMeasure_map project.continuous.measurable.aemeasurable⟩

 theorem tight_and_represented (μ : ℕ → Measure FullSpace) (hμ : ∀ n, IsProbabilityMeasure (μ n))
    (χ : ClassicalKernel)
    (hc : ∀ z : Coefficients, Tendsto (fun n => ∫ x, phase (encode z) x ∂μ n)
      atTop (𝓝 (χ.value z))) :
    IsTightMeasureSet (Set.range (fun n => (μ n).map project)) ∧
    ∃ ν : ProbabilityMeasure TenSpace,
      (∀ z : Coefficients, charFun (ν : Measure TenSpace) (coefficientVector z) = χ.value z) ∧
      Tendsto (fun n => projectedProbability (μ n) (hμ n)) atTop (𝓝 ν) := by
  let p n := projectedProbability (μ n) (hμ n)
  let f : TenSpace → ℂ := fun z => χ.value (coefficients z)
  have hf : Continuous f := χ.continuous_value.comp coefficients.continuous
  have h0 : f 0 = 1 := by simp only [f,map_zero,χ.value_zero]
  have hp : ∀ z, Tendsto (fun n => charFun (p n : Measure TenSpace) z) atTop (𝓝 (f z)) := by
    intro z
    simpa only [p,projectedProbability,ProbabilityMeasure.coe_mk,projected_characteristic,f]
      using hc (coefficients z)
  refine ⟨KFCausalCharacteristicTightness.tight_of_characteristic_limit p f hf h0 hp,?_⟩
  obtain ⟨ν,hν,_⟩ := KFCausalCharacteristicRepresentation.exists_probability_limit p f hf h0 hp
  refine ⟨ν,?_,KFCausalCharacteristicRepresentation.weak_convergence p f hf h0 hp ν hν⟩
  intro z
  simpa only [f,coefficients_vector] using hν (coefficientVector z)

 theorem representation_unique (ν ρ : ProbabilityMeasure TenSpace) (χ : ClassicalKernel)
    (hν : ∀ z : Coefficients, charFun (ν : Measure TenSpace) (coefficientVector z) = χ.value z)
    (hρ : ∀ z : Coefficients, charFun (ρ : Measure TenSpace) (coefficientVector z) = χ.value z) : ν = ρ := by
  apply ProbabilityMeasure.toMeasure_injective
  apply Measure.ext_of_charFun (μ := (ν : Measure TenSpace)) (ν := (ρ : Measure TenSpace))
  funext z
  have he : coefficientVector (coefficients z) = z := by
    apply PiLp.ext
    intro i
    cases i <;> rfl
  rw [← he]
  exact (hν (coefficients z)).trans (hρ (coefficients z)).symm

#print axioms tight_and_represented
#print axioms representation_unique

end
end UnifiedTheory.Audit.KFCausalTenProbabilityLimit
