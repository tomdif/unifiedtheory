/- Joint closure of finitely many actual closable factors. The natural
weighted graph uses (c_i*f,y_i) in graph(T_i), so zero coefficients impose
no domain restrictions. No graph-core or equality of closure domains is
assumed. -/
import Mathlib.Analysis.InnerProductSpace.LinearPMap
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 800000

namespace UnifiedTheory.Audit.KFCausalFiniteJointGraph
noncomputable section
open Set

variable {H ι : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [Fintype ι]
abbrev Output (ι H : Type*) [Fintype ι] := PiLp 2 (fun _ : ι => H)

def jointGraph (T : ι → H →ₗ.[ℂ] H) (c : ι → ℂ) : Submodule ℂ (H × Output ι H) where
  carrier := {z | ∀ i, (c i • z.1,z.2 i) ∈ (T i).graph}
  zero_mem' := by intro i; simp
  add_mem' := by
    intro x y hx hy i
    simpa only [Prod.fst_add,Prod.snd_add,PiLp.add_apply,smul_add] using (T i).graph.add_mem (hx i) (hy i)
  smul_mem' := by
    intro a x hx i
    have h := (T i).graph.smul_mem a (hx i)
    change (a • (c i • x.1),a • x.2 i) ∈ (T i).graph at h
    change (c i • (a • x.1),a • x.2 i) ∈ (T i).graph
    simpa only [smul_smul,mul_comm] using h

def jointInitial (T : ι → H →ₗ.[ℂ] H) (c : ι → ℂ) : H →ₗ.[ℂ] Output ι H :=
  (jointGraph T c).toLinearPMap
def jointClosed (T : ι → H →ₗ.[ℂ] H) (c : ι → ℂ) : H →ₗ.[ℂ] Output ι H :=
  (jointGraph T c).topologicalClosure.toLinearPMap

theorem joint_initial_graph (T : ι → H →ₗ.[ℂ] H) (c : ι → ℂ) :
    (jointInitial T c).graph=jointGraph T c := by
  apply Submodule.toLinearPMap_graph_eq
  intro z hz hx
  apply PiLp.ext
  intro i
  exact (T i).mem_graph_snd_inj (hz i) (T i).graph.zero_mem (by simp [hx])

theorem joint_domain (T : ι → H →ₗ.[ℂ] H) (c : ι → ℂ) (f : H) :
    f ∈ (jointInitial T c).domain ↔ ∀ i, c i • f ∈ (T i).domain := by
  constructor
  · intro hf i
    have hg := (jointInitial T c).mem_graph ⟨f,hf⟩
    rw [joint_initial_graph] at hg
    exact LinearPMap.mem_domain_of_mem_graph (hg i)
  · intro hf
    apply LinearPMap.mem_domain_of_mem_graph
      (y := WithLp.toLp 2 (fun i => T i ⟨c i • f,hf i⟩))
    rw [joint_initial_graph]
    intro i
    exact (T i).mem_graph ⟨c i • f,hf i⟩

theorem closure_component_graph (T : ι → H →ₗ.[ℂ] H) (c : ι → ℂ)
    (hT : ∀ i, (T i).IsClosable) (z : H × Output ι H)
    (hz : z ∈ (jointGraph T c).topologicalClosure) (i : ι) :
    (c i • z.1,z.2 i) ∈ (T i).closure.graph := by
  have hcT : IsClosed ((T i).closure.graph : Set (H × H)) := (hT i).closure_isClosed
  have hc : IsClosed {z : H × Output ι H | (c i • z.1,z.2 i) ∈ (T i).closure.graph} :=
    hcT.preimage
      ((continuous_const.smul continuous_fst).prodMk ((PiLp.continuous_apply 2 _ i).comp continuous_snd))
  apply closure_minimal (t := {z : H × Output ι H | (c i • z.1,z.2 i) ∈ (T i).closure.graph}) ?_ hc
    (by simpa only [Submodule.topologicalClosure_coe] using hz)
  intro w hw
  exact LinearPMap.le_graph_of_le (T i).le_closure (hw i)

theorem joint_closure_vertical_zero (T : ι → H →ₗ.[ℂ] H) (c : ι → ℂ)
    (hT : ∀ i, (T i).IsClosable) (z : H × Output ι H)
    (hz : z ∈ (jointGraph T c).topologicalClosure) (hx : z.1=0) : z.2=0 := by
  apply PiLp.ext
  intro i
  exact (T i).closure.mem_graph_snd_inj (closure_component_graph T c hT z hz i)
    (T i).closure.graph.zero_mem (by simp [hx])

theorem joint_closed_graph (T : ι → H →ₗ.[ℂ] H) (c : ι → ℂ) (hT : ∀ i, (T i).IsClosable) :
    (jointClosed T c).graph=(jointGraph T c).topologicalClosure :=
  Submodule.toLinearPMap_graph_eq _ (joint_closure_vertical_zero T c hT)

theorem joint_closable (T : ι → H →ₗ.[ℂ] H) (c : ι → ℂ) (hT : ∀ i, (T i).IsClosable) :
    (jointInitial T c).IsClosable := by
  refine ⟨jointClosed T c,?_⟩
  rw [joint_initial_graph,joint_closed_graph T c hT]

theorem joint_closed (T : ι → H →ₗ.[ℂ] H) (c : ι → ℂ) (hT : ∀ i, (T i).IsClosable) :
    (jointClosed T c).IsClosed := by
  rw [LinearPMap.IsClosed,joint_closed_graph T c hT]
  exact (jointGraph T c).isClosed_topologicalClosure

theorem joint_initial_le_closed (T : ι → H →ₗ.[ℂ] H) (c : ι → ℂ)
    (hT : ∀ i, (T i).IsClosable) : jointInitial T c ≤ jointClosed T c := by
  rw [← LinearPMap.le_graph_iff,joint_initial_graph,joint_closed_graph T c hT]
  exact (jointGraph T c).le_topologicalClosure

def commonDomain (T : ι → H →ₗ.[ℂ] H) : Submodule ℂ H := ⨅ i, (T i).domain

def commonOutput (T : ι → H →ₗ.[ℂ] H) (c : ι → ℂ) (f : commonDomain T) : Output ι H :=
  WithLp.toLp 2 (fun i => c i • T i ⟨f,(Submodule.mem_iInf _).mp f.property i⟩)

theorem commonOutput_graph (T : ι → H →ₗ.[ℂ] H) (c : ι → ℂ) (f : commonDomain T) :
    ((f:H),commonOutput T c f) ∈ (jointInitial T c).graph := by
  rw [joint_initial_graph]
  intro i
  exact (T i).graph.smul_mem (c i) ((T i).mem_graph ⟨f,(Submodule.mem_iInf _).mp f.property i⟩)

theorem commonOutput_norm (T : ι → H →ₗ.[ℂ] H) (c : ι → ℂ) (f : commonDomain T) :
    ‖commonOutput T c f‖^2 =
      ∑ i, ‖c i‖^2*‖T i ⟨f,(Submodule.mem_iInf _).mp f.property i⟩‖^2 := by
  rw [PiLp.norm_sq_eq_of_L2]
  simp only [commonOutput,PiLp.toLp_apply,norm_smul,mul_pow]

theorem joint_dense (T : ι → H →ₗ.[ℂ] H) (c : ι → ℂ)
    (hd : Dense (commonDomain T : Set H)) : Dense ((jointInitial T c).domain : Set H) := by
  apply hd.mono
  intro f hf
  exact LinearPMap.mem_domain_of_mem_graph (commonOutput_graph T c ⟨f,hf⟩)

theorem joint_closed_dense (T : ι → H →ₗ.[ℂ] H) (c : ι → ℂ) (hT : ∀ i, (T i).IsClosable)
    (hd : Dense (commonDomain T : Set H)) : Dense ((jointClosed T c).domain : Set H) :=
  (joint_dense T c hd).mono (joint_initial_le_closed T c hT).1

#print axioms joint_initial_graph
#print axioms joint_domain
#print axioms closure_component_graph
#print axioms joint_closure_vertical_zero
#print axioms joint_closed_graph
#print axioms joint_closable
#print axioms joint_closed
#print axioms joint_initial_le_closed
#print axioms commonOutput_graph
#print axioms commonOutput_norm
#print axioms joint_dense
#print axioms joint_closed_dense

end
end UnifiedTheory.Audit.KFCausalFiniteJointGraph
