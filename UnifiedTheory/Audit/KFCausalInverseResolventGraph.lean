/- Exact graph characterization for the inverse of an injective bounded
resolvent. The condition is an equation in the original Hilbert space. -/
import UnifiedTheory.Audit.KFCausalResolventHamiltonian

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Audit.KFCausalInverseResolventGraph
noncomputable section
open UnifiedTheory.Audit.KFCausalResolventHamiltonian

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

theorem inverseShift_graph_iff (R : H →L[ℂ] H) (hi : Function.Injective R) (f g : H) :
    (f,g) ∈ (inverseShift R hi).graph ↔ R (g+f)=f := by
  constructor
  · intro hp
    obtain ⟨v,hv,hg⟩ := (LinearPMap.mem_graph_iff _).mp hp
    simpa only [hv,hg] using inverseShift_resolvent R hi v
  · intro hr
    have hf : f ∈ (inverseShift R hi).domain := ⟨g+f,hr⟩
    have he : inverseShift R hi ⟨f,hf⟩ = g := by
      apply add_right_cancel (b := f)
      apply hi
      exact (inverseShift_resolvent R hi ⟨f,hf⟩).trans hr.symm
    exact (LinearPMap.mem_graph_iff _).mpr ⟨⟨f,hf⟩,rfl,he⟩

theorem symmetric_injective_dense [CompleteSpace H] (R : H →L[ℂ] H)
    (hi : Function.Injective R) (hs : ∀ f g, inner ℂ (R f) g = inner ℂ f (R g)) :
    DenseRange R := by
  have hsym : R.toLinearMap.IsSymmetric := hs
  change Dense (R.range : Set H)
  apply Submodule.dense_iff_topologicalClosure_eq_top.mpr
  apply Submodule.topologicalClosure_eq_top_iff.mpr
  rw [hsym.orthogonal_range]
  exact LinearMap.ker_eq_bot.mpr hi

#print axioms inverseShift_graph_iff
#print axioms symmetric_injective_dense

end
end UnifiedTheory.Audit.KFCausalInverseResolventGraph
