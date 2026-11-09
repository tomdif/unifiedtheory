/- Weak inner-product data on a proved graph core determine the actual
 selfadjoint operator graph. This is a transfer lemma, with its core
 equality supplied by a separate construction in each application. -/
import Mathlib.Analysis.InnerProductSpace.LinearPMap

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 800000

namespace UnifiedTheory.Audit.KFCausalSelfAdjointCoreWeakGraph
noncomputable section
open Set

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

def weakKernel (f g : H) : Submodule ℂ (H × H) where
  carrier := {p | inner ℂ p.2 f = inner ℂ p.1 g}
  zero_mem' := by simp
  add_mem' := by
    intro p q hp hq
    change inner ℂ (p.2+q.2) f = inner ℂ (p.1+q.1) g
    rw [inner_add_left,inner_add_left,hp,hq]
  smul_mem' := by
    intro c p hp
    change inner ℂ (c • p.2) f = inner ℂ (c • p.1) g
    rw [inner_smul_left,inner_smul_left,hp]

theorem weakKernel_closed (f g : H) : IsClosed (weakKernel f g : Set (H × H)) :=
  isClosed_eq (continuous_snd.inner continuous_const) (continuous_fst.inner continuous_const)

variable [CompleteSpace H]

theorem graph_iff_weak (A : H →ₗ.[ℂ] H) (hA : IsSelfAdjoint A) (f g : H) :
    (f,g) ∈ A.graph ↔ ∀ v w : H, (v,w) ∈ A.graph → inner ℂ w f = inner ℂ v g := by
  have he : A.graph.adjoint = A.graph := by
    rw [← LinearPMap.adjoint_graph_eq_graph_adjoint hA.dense_domain,LinearPMap.isSelfAdjoint_def.mp hA]
  have hi := Submodule.mem_adjoint_iff A.graph (f,g)
  rw [he] at hi
  simpa only [sub_eq_zero] using hi

theorem graph_iff_core_weak (A : H →ₗ.[ℂ] H) (hA : IsSelfAdjoint A)
    (G : Set (H × H)) (hG : (Submodule.span ℂ G).topologicalClosure = A.graph) (f g : H) :
    (f,g) ∈ A.graph ↔ ∀ p ∈ G, inner ℂ p.2 f = inner ℂ p.1 g := by
  constructor
  · intro hfg p hp
    have hpA : p ∈ A.graph := by
      rw [← hG]
      exact (Submodule.span ℂ G).le_topologicalClosure (Submodule.subset_span hp)
    exact (graph_iff_weak A hA f g).mp hfg p.1 p.2 hpA
  · intro hw
    have hs : Submodule.span ℂ G ≤ weakKernel f g := Submodule.span_le.mpr hw
    have hc := Submodule.topologicalClosure_minimal _ hs (weakKernel_closed f g)
    rw [hG] at hc
    exact (graph_iff_weak A hA f g).mpr (fun v w hvw => hc hvw)

#print axioms weakKernel_closed
#print axioms graph_iff_weak
#print axioms graph_iff_core_weak
end
end UnifiedTheory.Audit.KFCausalSelfAdjointCoreWeakGraph
