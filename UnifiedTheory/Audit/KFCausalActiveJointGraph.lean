/- Closedness of a weighted joint graph needs closedness only of its active
factors. A factor with coefficient zero imposes exactly a zero output. -/
import UnifiedTheory.Audit.KFCausalFiniteJointGraph

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Audit.KFCausalActiveJointGraph
noncomputable section
open KFCausalFiniteJointGraph

variable {H ι : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [Fintype ι]

theorem jointGraph_closed (T : ι → H →ₗ.[ℂ] H) (c : ι → ℂ)
    (hc : ∀ i, c i ≠ 0 → (T i).IsClosed) :
    IsClosed (jointGraph T c : Set (H × Output ι H)) := by
  change IsClosed {z : H × Output ι H | ∀ i, (c i • z.1,z.2 i) ∈ (T i).graph}
  simp only [Set.setOf_forall]
  apply isClosed_iInter
  intro i
  by_cases hi : c i = 0
  · have he : {z : H × Output ι H | (c i • z.1,z.2 i) ∈ (T i).graph} =
        {z : H × Output ι H | z.2 i = 0} := by
      ext z
      simp only [Set.mem_setOf_eq,hi,zero_smul]
      constructor
      · intro hz
        exact (T i).graph_fst_eq_zero_snd hz rfl
      · intro hz
        rw [hz]
        exact (T i).graph.zero_mem
    rw [he]
    exact isClosed_eq ((PiLp.continuous_apply 2 _ i).comp continuous_snd) continuous_const
  · exact (show IsClosed ((T i).graph : Set (H × H)) from hc i hi).preimage
      ((continuous_const.smul continuous_fst).prodMk
      ((PiLp.continuous_apply 2 _ i).comp continuous_snd))

theorem jointClosed_eq_initial (T : ι → H →ₗ.[ℂ] H) (c : ι → ℂ)
    (hc : ∀ i, c i ≠ 0 → (T i).IsClosed) : jointClosed T c = jointInitial T c := by
  unfold jointClosed jointInitial
  congr 1
  exact (jointGraph_closed T c hc).submodule_topologicalClosure_eq

#print axioms jointGraph_closed
#print axioms jointClosed_eq_initial
end
end UnifiedTheory.Audit.KFCausalActiveJointGraph
