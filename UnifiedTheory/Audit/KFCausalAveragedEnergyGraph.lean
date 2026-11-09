/- The orbit-averaged energy has an actual closed, single-valued operator
graph. Density of its domain is deliberately not a premise or conclusion.
The original form's graph norm supplies the closed-range estimate. -/
import UnifiedTheory.Audit.KFCausalAveragedFormProjection
import Mathlib.Analysis.InnerProductSpace.LinearPMap

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 800000

namespace UnifiedTheory.Audit.KFCausalAveragedEnergyGraph
noncomputable section
open MeasureTheory
open UnifiedTheory.Audit.KFCausalUnitaryOrbitAverage
open UnifiedTheory.Audit.KFCausalUnitIntervalOrbit
open UnifiedTheory.Audit.KFCausalAveragedFormSpace
open UnifiedTheory.Audit.KFCausalAveragedFormProjection

variable {H E K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K]

theorem l2_norm_square {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (v : Lp E 2 μ) :
    ‖v‖^2 = ∫ θ, ‖v θ‖^2 ∂μ := by
  apply Complex.ofReal_injective
  rw [← integral_complex_ofReal]
  calc
    _ = inner ℂ v v := by
      simpa only [Complex.ofReal_pow] using (inner_self_eq_norm_sq_to_K (𝕜 := ℂ) v).symm
    _ = _ := by
      rw [L2.inner_def]
      apply integral_congr_ae
      filter_upwards [] with θ
      rw [inner_self_eq_norm_sq_to_K]
      norm_cast

variable (U : StrongUnitaryGroup H) (T : ℝ) (J : E →L[ℂ] H) (A : E →L[ℂ] K)

theorem output_energy_integral (u : FormSpace U T J) :
    ‖averagedOutput U T J A u‖^2 = ∫ θ, ‖A (sectionMap U T J u θ)‖^2 ∂angleMeasure := by
  rw [l2_norm_square]
  apply integral_congr_ae
  filter_upwards [A.coeFn_compLp (sectionMap U T J u)] with θ hθ
  change ‖A.compLp (sectionMap U T J u) θ‖^2 = _
  rw [hθ]

theorem section_energy_identity
    (hJA : ∀ v : E, ‖v‖^2 = ‖J v‖^2 + ‖A v‖^2) (u : FormSpace U T J) :
    ‖sectionMap U T J u‖^2 = ‖embedding U T J u‖^2 + ‖averagedOutput U T J A u‖^2 := by
  let v := sectionMap U T J u
  have he : (fun θ => ‖v θ‖^2) =ᵐ[angleMeasure]
      fun θ => ‖J.compLp v θ‖^2 + ‖A.compLp v θ‖^2 := by
    filter_upwards [J.coeFn_compLp v, A.coeFn_compLp v] with θ hJ hA
    rw [hJ, hA, hJA]
  have hJ : Integrable (fun θ => ‖J.compLp v θ‖^2) angleMeasure :=
    (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable _)).mp (Lp.memLp _)
  have hA : Integrable (fun θ => ‖A.compLp v θ‖^2) angleMeasure :=
    (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable _)).mp (Lp.memLp _)
  have hn : ‖v‖^2 = ‖J.compLp v‖^2 + ‖A.compLp v‖^2 := by
    rw [l2_norm_square angleMeasure v, integral_congr_ae he, integral_add hJ hA,
      ← l2_norm_square, ← l2_norm_square]
  change ‖sectionMap U T J u‖^2 =
    ‖J.compLp (sectionMap U T J u)‖^2 + ‖averagedOutput U T J A u‖^2 at hn
  rwa [compatibility, (orbit U T).norm_map] at hn

theorem form_energy_identity
    (hJA : ∀ v : E, ‖v‖^2 = ‖J v‖^2 + ‖A v‖^2) (u : FormSpace U T J) :
    ‖u‖^2 = 2*‖embedding U T J u‖^2 + ‖averagedOutput U T J A u‖^2 := by
  rw [norm_identity, section_energy_identity U T J A hJA]
  ring

def graphMap : FormSpace U T J →L[ℂ] (H × Lp K 2 angleMeasure) :=
  (embedding U T J).prod (averagedOutput U T J A)

theorem graphMap_bound
    (hJA : ∀ v : E, ‖v‖^2 = ‖J v‖^2 + ‖A v‖^2) (u : FormSpace U T J) :
    ‖u‖ ≤ 2*‖graphMap U T J A u‖ := by
  have h1 : ‖embedding U T J u‖ ≤ ‖graphMap U T J A u‖ := norm_fst_le (graphMap U T J A u)
  have h2 : ‖averagedOutput U T J A u‖ ≤ ‖graphMap U T J A u‖ := norm_snd_le (graphMap U T J A u)
  have h1s := (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr h1
  have h2s := (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr h2
  have hn := form_energy_identity U T J A hJA u
  nlinarith [norm_nonneg u, norm_nonneg (graphMap U T J A u)]

theorem graphMap_closed_range [CompleteSpace H] [CompleteSpace E]
    (hJA : ∀ v : E, ‖v‖^2 = ‖J v‖^2 + ‖A v‖^2) :
    IsClosed (Set.range (graphMap U T J A)) := by
  have ha : AntilipschitzWith 2 (graphMap U T J A) :=
    (graphMap U T J A).antilipschitz_of_bound (graphMap_bound U T J A hJA)
  exact ha.isClosed_range (graphMap U T J A).uniformContinuous

def averagedOperator : H →ₗ.[ℂ] Lp K 2 angleMeasure :=
  (graphMap U T J A).range.toLinearPMap

theorem averagedOperator_graph (hJ : Function.Injective J) :
    (averagedOperator U T J A).graph = (graphMap U T J A).range := by
  apply Submodule.toLinearPMap_graph_eq
  rintro z ⟨u, rfl⟩ hu
  have hz : u = 0 := embedding_injective U T J hJ (by simpa using hu)
  change averagedOutput U T J A u = 0
  rw [hz, map_zero]

theorem averagedOperator_closed [CompleteSpace H] [CompleteSpace E] (hJ : Function.Injective J)
    (hJA : ∀ v : E, ‖v‖^2 = ‖J v‖^2 + ‖A v‖^2) :
    (averagedOperator U T J A).IsClosed := by
  rw [LinearPMap.IsClosed, averagedOperator_graph U T J A hJ]
  exact graphMap_closed_range U T J A hJA

theorem averagedOperator_domain (hJ : Function.Injective J) (f : H) :
    f ∈ (averagedOperator U T J A).domain ↔ f ∈ domain U T J := by
  rw [LinearPMap.mem_domain_iff, averagedOperator_graph U T J A hJ]
  constructor
  · rintro ⟨g, u, hu⟩
    exact ⟨u, congrArg Prod.fst hu⟩
  · rintro ⟨u, rfl⟩
    exact ⟨averagedOutput U T J A u, u, rfl⟩

theorem averagedOperator_form_graph (hJ : Function.Injective J) (u : FormSpace U T J) :
    (embedding U T J u, averagedOutput U T J A u) ∈ (averagedOperator U T J A).graph := by
  rw [averagedOperator_graph U T J A hJ]
  exact ⟨u, rfl⟩

#print axioms l2_norm_square
#print axioms output_energy_integral
#print axioms section_energy_identity
#print axioms form_energy_identity
#print axioms graphMap_bound
#print axioms graphMap_closed_range
#print axioms averagedOperator_graph
#print axioms averagedOperator_closed
#print axioms averagedOperator_domain
#print axioms averagedOperator_form_graph

end
end UnifiedTheory.Audit.KFCausalAveragedEnergyGraph
