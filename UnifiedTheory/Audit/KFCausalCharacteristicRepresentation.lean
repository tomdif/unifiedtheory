/- A continuous normalized characteristic limit of positive probabilities
has a unique representing probability measure. Tightness is derived from
characteristics before applying Prokhorov and testing the weak limit. -/
import UnifiedTheory.Audit.KFCausalCharacteristicTightness

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1200000

namespace UnifiedTheory.Audit.KFCausalCharacteristicRepresentation
noncomputable section
open MeasureTheory Filter BoundedContinuousFunction
open scoped Topology

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  [FiniteDimensional ℝ E]

 theorem exists_probability_limit (μ : ℕ → ProbabilityMeasure E) (f : E → ℂ)
    (hf : Continuous f) (hf0 : f 0 = 1)
    (hc : ∀ z, Tendsto (fun n => charFun (μ n : Measure E) z) atTop (𝓝 (f z))) :
    ∃ ν : ProbabilityMeasure E, (∀ z, charFun (ν : Measure E) z = f z) ∧
      ∃ φ : ℕ → ℕ, StrictMono φ ∧ Tendsto (fun n => μ (φ n)) atTop (𝓝 ν) := by
  obtain ⟨ν,φ,hφ,hlim⟩ := KFCausalCharacteristicTightness.exists_weak_subsequence μ f hf hf0 hc
  refine ⟨ν,?_,φ,hφ,hlim⟩
  intro z
  have hp := (ProbabilityMeasure.tendsto_iff_forall_integral_rclike_tendsto ℂ).mp hlim (innerProbChar z)
  simp only [← charFun_eq_integral_innerProbChar] at hp
  exact tendsto_nhds_unique hp ((hc z).comp hφ.tendsto_atTop)

 theorem unique_probability_limit (μ : ℕ → ProbabilityMeasure E) (f : E → ℂ)
    (hf : Continuous f) (hf0 : f 0 = 1)
    (hc : ∀ z, Tendsto (fun n => charFun (μ n : Measure E) z) atTop (𝓝 (f z))) :
    ∃! ν : ProbabilityMeasure E, ∀ z, charFun (ν : Measure E) z = f z := by
  obtain ⟨ν,hν,_⟩ := exists_probability_limit μ f hf hf0 hc
  refine ⟨ν,hν,?_⟩
  intro ρ hρ
  apply ProbabilityMeasure.toMeasure_injective
  exact Measure.ext_of_charFun (μ := (ρ : Measure E)) (ν := (ν : Measure E))
    (funext (fun z => (hρ z).trans (hν z).symm))

 theorem weak_convergence (μ : ℕ → ProbabilityMeasure E) (f : E → ℂ)
    (hf : Continuous f) (hf0 : f 0 = 1)
    (hc : ∀ z, Tendsto (fun n => charFun (μ n : Measure E) z) atTop (𝓝 (f z)))
    (ν : ProbabilityMeasure E) (hν : ∀ z, charFun (ν : Measure E) z = f z) :
    Tendsto μ atTop (𝓝 ν) := by
  apply tendsto_of_subseq_tendsto
  intro ns hns
  obtain ⟨ρ,hρ,φ,_,hlim⟩ := exists_probability_limit (fun n => μ (ns n)) f hf hf0
    (fun z => (hc z).comp hns)
  have he : ρ = ν := ProbabilityMeasure.toMeasure_injective
    (Measure.ext_of_charFun (μ := (ρ : Measure E)) (ν := (ν : Measure E))
      (funext (fun z => (hρ z).trans (hν z).symm)))
  subst ρ
  exact ⟨φ,hlim⟩

#print axioms exists_probability_limit
#print axioms unique_probability_limit
#print axioms weak_convergence

end
end UnifiedTheory.Audit.KFCausalCharacteristicRepresentation
