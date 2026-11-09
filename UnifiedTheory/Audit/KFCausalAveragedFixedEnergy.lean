/- A fixed physical vector has exactly its original energy after circle
averaging, whenever its base form lift exists. -/
import UnifiedTheory.Audit.KFCausalAveragedEnergyGraph

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 800000

namespace UnifiedTheory.Audit.KFCausalAveragedFixedEnergy
noncomputable section
open MeasureTheory
open UnifiedTheory.Audit.KFCausalUnitaryOrbitAverage (StrongUnitaryGroup)
open UnifiedTheory.Audit.KFCausalPeriodicUnitaryMean (fixedSpace)
open UnifiedTheory.Audit.KFCausalUnitIntervalOrbit (angleMeasure)
open UnifiedTheory.Audit.KFCausalAveragedFormSpace
open UnifiedTheory.Audit.KFCausalAveragedFormProjection
open UnifiedTheory.Audit.KFCausalAveragedEnergyGraph (output_energy_integral)

variable {H E K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K]
  (U : StrongUnitaryGroup H) (T : ℝ) (J : E →L[ℂ] H) (A : E →L[ℂ] K)
  (hJ : Function.Injective J)

include hJ

theorem fixed_energy (u : FormSpace U T J) (v : E)
    (he : embedding U T J u = J v) (hf : J v ∈ fixedSpace U) :
    ‖averagedOutput U T J A u‖^2 = ‖A v‖^2 := by
  have hs : ∀ᵐ θ ∂angleMeasure, sectionMap U T J u θ = v := by
    filter_upwards [compatibility_ae U T J u] with θ hθ
    exact hJ (hθ.trans ((congrArg (U.action (T*θ)) he).trans (hf (T*θ))))
  calc
    _ = ∫ θ, ‖A (sectionMap U T J u θ)‖^2 ∂angleMeasure := output_energy_integral U T J A u
    _ = ∫ _θ : ℝ, ‖A v‖^2 ∂angleMeasure := integral_congr_ae (hs.mono (fun _ h => congrArg (fun z => ‖A z‖^2) h))
    _ = _ := by simp

variable [CompleteSpace H] [CompleteSpace E]

theorem exists_fixed_lift (hT : T ≠ 0) (v : E) (hf : J v ∈ fixedSpace U) :
    ∃ u : FormSpace U T J, embedding U T J u = J v ∧ ‖averagedOutput U T J A u‖^2 = ‖A v‖^2 := by
  have hd := (fixed_mem_domain_iff U T J hT (J v) hf).mpr ⟨v,rfl⟩
  obtain ⟨u,hu⟩ := hd
  exact ⟨u,hu,fixed_energy U T J A hJ u v hu hf⟩

#print axioms fixed_energy
#print axioms exists_fixed_lift

end
end UnifiedTheory.Audit.KFCausalAveragedFixedEnergy
