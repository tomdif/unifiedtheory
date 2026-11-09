/- Transport the full natural weighted joint graph, then its closure.
No restriction to a trial family and no graph-core assumption is used. -/
import UnifiedTheory.Audit.KFCausalFiniteOutputRescaling

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 800000

namespace UnifiedTheory.Audit.KFCausalJointGraphRescaling
noncomputable section
open UnifiedTheory.Audit.KFCausalFiniteJointGraph
open UnifiedTheory.Audit.KFCausalFiniteOutputRescaling
variable {H ι : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [Fintype ι]

theorem graph_rescale (T : ι → H →ₗ.[ℂ] H) (c c' d : ι → ℂ)
    (hc : ∀ i, c' i=d i*c i) (z : H × Output ι H) (hz : z ∈ jointGraph T c) :
    (z.1,diagonal d z.2) ∈ jointGraph T c' := by
  intro i
  have h := (T i).graph.smul_mem (d i) (hz i)
  change (d i • (c i • z.1),d i • z.2 i) ∈ (T i).graph at h
  change (c' i • z.1,diagonal d z.2 i) ∈ (T i).graph
  simpa only [hc i,diagonal_apply,smul_smul] using h

theorem closure_rescale (T : ι → H →ₗ.[ℂ] H) (c c' d : ι → ℂ)
    (hc : ∀ i, c' i=d i*c i) (z : H × Output ι H)
    (hz : z ∈ (jointGraph T c).topologicalClosure) :
    (z.1,diagonal d z.2) ∈ (jointGraph T c').topologicalClosure := by
  have hclosed : IsClosed {w : H × Output ι H | (w.1,diagonal d w.2) ∈ (jointGraph T c').topologicalClosure} :=
    (jointGraph T c').isClosed_topologicalClosure.preimage
      (continuous_fst.prodMk ((diagonal d).continuous.comp continuous_snd))
  apply closure_minimal (t := {w : H × Output ι H | (w.1,diagonal d w.2) ∈ (jointGraph T c').topologicalClosure})
    ?_ hclosed (by simpa only [Submodule.topologicalClosure_coe] using hz)
  intro w hw
  exact (jointGraph T c').le_topologicalClosure (graph_rescale T c c' d hc w hw)

theorem initial_graph_rescale (T : ι → H →ₗ.[ℂ] H) (c c' d : ι → ℂ)
    (hc : ∀ i, c' i=d i*c i) (z : H × Output ι H) (hz : z ∈ (jointInitial T c).graph) :
    (z.1,diagonal d z.2) ∈ (jointInitial T c').graph := by
  rw [joint_initial_graph] at hz ⊢
  exact graph_rescale T c c' d hc z hz

theorem closed_graph_rescale (T : ι → H →ₗ.[ℂ] H) (c c' d : ι → ℂ)
    (hT : ∀ i, (T i).IsClosable) (hc : ∀ i, c' i=d i*c i)
    (z : H × Output ι H) (hz : z ∈ (jointClosed T c).graph) :
    (z.1,diagonal d z.2) ∈ (jointClosed T c').graph := by
  rw [joint_closed_graph T c hT] at hz
  rw [joint_closed_graph T c' hT]
  exact closure_rescale T c c' d hc z hz

theorem initial_domain_eq (T : ι → H →ₗ.[ℂ] H) (c c' d e : ι → ℂ)
    (hd : ∀ i, c' i=d i*c i) (he : ∀ i, c i=e i*c' i) :
    (jointInitial T c).domain=(jointInitial T c').domain := by
  apply le_antisymm
  · intro x hx
    exact LinearPMap.mem_domain_of_mem_graph
      (initial_graph_rescale T c c' d hd _ ((jointInitial T c).mem_graph ⟨x,hx⟩))
  · intro x hx
    exact LinearPMap.mem_domain_of_mem_graph
      (initial_graph_rescale T c' c e he _ ((jointInitial T c').mem_graph ⟨x,hx⟩))

theorem closed_domain_eq (T : ι → H →ₗ.[ℂ] H) (c c' d e : ι → ℂ)
    (hT : ∀ i, (T i).IsClosable) (hd : ∀ i, c' i=d i*c i) (he : ∀ i, c i=e i*c' i) :
    (jointClosed T c).domain=(jointClosed T c').domain := by
  apply le_antisymm
  · intro x hx
    exact LinearPMap.mem_domain_of_mem_graph
      (closed_graph_rescale T c c' d hT hd _ ((jointClosed T c).mem_graph ⟨x,hx⟩))
  · intro x hx
    exact LinearPMap.mem_domain_of_mem_graph
      (closed_graph_rescale T c' c e hT he _ ((jointClosed T c').mem_graph ⟨x,hx⟩))

#print axioms graph_rescale
#print axioms closure_rescale
#print axioms initial_graph_rescale
#print axioms closed_graph_rescale
#print axioms initial_domain_eq
#print axioms closed_domain_eq

end
end UnifiedTheory.Audit.KFCausalJointGraphRescaling
