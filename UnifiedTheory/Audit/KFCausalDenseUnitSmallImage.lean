/- A strict bounded-observable estimate on a unit vector transfers to a
dense linear domain by continuous normalization. -/
import Mathlib.Analysis.Normed.Module.RCLike.Basic
import Mathlib.Topology.Algebra.Module.Basic
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Audit.KFCausalDenseUnitSmallImage
noncomputable section
open Filter
open scoped Topology

variable {H K : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]
  [NormedAddCommGroup K] [NormedSpace ℂ K]

theorem exists_unit_small_image (E : Submodule ℂ H) (D : H →L[ℂ] K)
    (f : H) (hf : ‖f‖ = 1) (hclosure : f ∈ E.topologicalClosure)
    (δ : ℝ) (hδ : ‖D f‖ < δ) :
    ∃ u : H, u ∈ E ∧ ‖u‖ = 1 ∧ ‖D u‖ < δ := by
  let unit : H → H := fun v => ((‖v‖⁻¹ : ℝ) : ℂ) • v
  have hf0 : f ≠ 0 := by intro h; simp [h] at hf
  have hu : unit f = f := by simp [unit, hf]
  have hc : ContinuousAt unit f := by
    apply ContinuousAt.smul
    · exact Complex.continuous_ofReal.continuousAt.comp
        (continuous_norm.continuousAt.inv₀ (norm_ne_zero_iff.mpr hf0))
    · exact continuousAt_id
  have ht : ‖D (unit f)‖ < δ := by rwa [hu]
  have hev : ∀ᶠ v in 𝓝 f, ‖D (unit v)‖ < δ :=
    (D.continuous.continuousAt.comp hc).norm.tendsto.eventually (gt_mem_nhds ht)
  have hfreq : ∃ᶠ v in 𝓝 f, v ∈ E := mem_closure_iff_frequently.mp hclosure
  obtain ⟨v, hv, hv0, hvδ⟩ :=
    (hfreq.and_eventually ((eventually_ne_nhds hf0).and hev)).exists
  have hn : ‖unit v‖ = 1 := by
    simpa only [unit, Complex.ofReal_inv] using (norm_smul_inv_norm (𝕜 := ℂ) hv0)
  exact ⟨unit v, E.smul_mem _ hv, hn, hvδ⟩

#print axioms exists_unit_small_image

end
end UnifiedTheory.Audit.KFCausalDenseUnitSmallImage
