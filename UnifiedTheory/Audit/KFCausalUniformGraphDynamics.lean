/- Uniform graph operators give a compact-time physical output bound.
The exact strong equation then supplies a trajectory Lipschitz estimate. -/
import UnifiedTheory.Audit.KFCausalEmbeddedGraphExtension
import Mathlib.Analysis.Calculus.MeanValue

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Audit.KFCausalUniformGraphDynamics
noncomputable section
open Set
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

theorem output_bound (T₀ : H →ₗ.[ℂ] H) (T : ℝ → H →ₗ.[ℂ] H)
    (U : ℝ → H →L[ℂ] H) (R : H →L[ℂ] H) (I : Set ℝ)
    (hleft : ∀ x : T₀.domain, R ((x:H)+T₀ x) = (x:H))
    (hE : ∃ C : ℝ, 0 ≤ C ∧ ∃ E : I → H →L[ℂ] H,
      (∀ t, ‖E t‖ ≤ C) ∧ ∀ t : I, ∀ v, (U t (R v),E t v) ∈ (T t).graph) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ I, ∀ x : T₀.domain, ∃ hx : U t x ∈ (T t).domain,
      ‖T t ⟨U t x,hx⟩‖ ≤ C*(‖(x:H)‖+‖T₀ x‖) := by
  obtain ⟨C,hC,E,hN,hg⟩ := hE
  refine ⟨C,hC,fun t ht x => ?_⟩
  have hp : (U t x,E ⟨t,ht⟩ ((x:H)+T₀ x)) ∈ (T t).graph := by
    simpa only [hleft] using hg ⟨t,ht⟩ ((x:H)+T₀ x)
  have hx : U t x ∈ (T t).domain := LinearPMap.mem_domain_of_mem_graph hp
  refine ⟨hx,?_⟩
  have he : T t ⟨U t x,hx⟩ = E ⟨t,ht⟩ ((x:H)+T₀ x) :=
    (T t).mem_graph_snd_inj' ((T t).mem_graph ⟨U t x,hx⟩) hp rfl
  rw [he]
  exact ((E ⟨t,ht⟩).le_opNorm _).trans (mul_le_mul (hN ⟨t,ht⟩)
    (norm_add_le _ _) (norm_nonneg _) hC)

theorem lipschitz_bound (T₀ : H →ₗ.[ℂ] H) (T : ℝ → H →ₗ.[ℂ] H)
    (U : ℝ → H →L[ℂ] H) (c : ℂ) (I : Set ℝ) (hI : Convex ℝ I)
    (hd : ∀ t ∈ I, ∀ x : T₀.domain, ∃ hx : U t x ∈ (T t).domain,
      HasDerivAt (fun r => U r x) (c • T t ⟨U t x,hx⟩) t)
    (hb : ∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ I, ∀ x : T₀.domain, ∃ hx : U t x ∈ (T t).domain,
      ‖T t ⟨U t x,hx⟩‖ ≤ C*(‖(x:H)‖+‖T₀ x‖)) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ x : T₀.domain, ∀ u ∈ I, ∀ v ∈ I,
      ‖U v x-U u x‖ ≤ K*(‖(x:H)‖+‖T₀ x‖)*‖v-u‖ := by
  obtain ⟨C,hC,hb⟩ := hb
  refine ⟨‖c‖*C,mul_nonneg (norm_nonneg _) hC,fun x u hu v hv => ?_⟩
  have hdiff (t : ℝ) (ht : t ∈ I) : DifferentiableAt ℝ (fun r => U r x) t := by
    obtain ⟨hx,hdx⟩ := hd t ht x
    exact hdx.differentiableAt
  have hder (t : ℝ) (ht : t ∈ I) :
      ‖deriv (fun r => U r x) t‖ ≤ (‖c‖*C)*(‖(x:H)‖+‖T₀ x‖) := by
    obtain ⟨hx,hdx⟩ := hd t ht x
    obtain ⟨_,hbx⟩ := hb t ht x
    rw [hdx.deriv,norm_smul]
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hbx (norm_nonneg c)
  exact hI.norm_image_sub_le_of_norm_deriv_le hdiff hder hu hv

#print axioms output_bound
#print axioms lipschitz_bound
end
end UnifiedTheory.Audit.KFCausalUniformGraphDynamics
