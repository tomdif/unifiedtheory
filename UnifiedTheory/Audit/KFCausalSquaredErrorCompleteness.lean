/- A vanishing two-parameter squared-error bound yields an actual
one-sided vector limit in a complete normed space. -/
import UnifiedTheory.Audit.KFCausalCorrelatedClusteredL2Error

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Audit.KFCausalSquaredErrorCompleteness
noncomputable section
open Filter
open scoped Topology

theorem exists_limit {E : Type*} [NormedAddCommGroup E] [CompleteSpace E]
    (u : ℝ → E) (g : ℝ → ℝ) (hg : Tendsto g (𝓝[>] 0) (𝓝 0))
    (hb : ∀ δ η : ℝ, 0 < δ → 0 < η → ‖u δ-u η‖^2 ≤ g δ+g η) :
    ∃ v : E, Tendsto u (𝓝[>] 0) (𝓝 v) := by
  apply cauchy_map_iff_exists_tendsto.mp
  rw [cauchy_map_iff',tendsto_uniformity_iff_dist_tendsto_zero]
  have hsum : Tendsto (fun z : ℝ × ℝ => g z.1+g z.2) ((𝓝[>] 0) ×ˢ (𝓝[>] 0)) (𝓝 0) := by
    simpa only [add_zero] using (hg.comp tendsto_fst).add (hg.comp tendsto_snd)
  have hs : Tendsto (fun z : ℝ × ℝ => ‖u z.1-u z.2‖^2) ((𝓝[>] 0) ×ˢ (𝓝[>] 0)) (𝓝 0) := by
    apply squeeze_zero' (Eventually.of_forall (fun z => sq_nonneg ‖u z.1-u z.2‖)) _ hsum
    filter_upwards [tendsto_fst.eventually (self_mem_nhdsWithin : ∀ᶠ δ : ℝ in 𝓝[>] 0, δ ∈ Set.Ioi 0),
      tendsto_snd.eventually (self_mem_nhdsWithin : ∀ᶠ η : ℝ in 𝓝[>] 0, η ∈ Set.Ioi 0)] with z hδ hη
    exact hb z.1 z.2 hδ hη
  have hn := Real.continuous_sqrt.continuousAt.tendsto.comp hs
  simpa only [Function.comp_def,Real.sqrt_sq_eq_abs,abs_norm,Real.sqrt_zero,dist_eq_norm] using hn

#print axioms exists_limit
end
end UnifiedTheory.Audit.KFCausalSquaredErrorCompleteness
