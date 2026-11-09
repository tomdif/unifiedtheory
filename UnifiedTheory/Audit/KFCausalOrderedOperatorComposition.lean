/- Exact composition on its natural domain. A dense reversed composition
of two self-adjoint operators supplies a closed adjoint extension, proving
closability without assuming that a composition of closed operators is closed. -/
import Mathlib.Analysis.InnerProductSpace.LinearPMap
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 800000

namespace UnifiedTheory.Audit.KFCausalOrderedOperatorComposition
noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

def compositionGraph (A B : H →ₗ.[ℂ] H) : Submodule ℂ (H × H) where
  carrier := {z | ∃ y, (z.1,y) ∈ B.graph ∧ (y,z.2) ∈ A.graph}
  zero_mem' := ⟨0,B.graph.zero_mem,A.graph.zero_mem⟩
  add_mem' := by
    rintro f g ⟨y,hy,hf⟩ ⟨z,hz,hg⟩
    exact ⟨y+z,B.graph.add_mem hy hz,A.graph.add_mem hf hg⟩
  smul_mem' := by
    rintro c f ⟨y,hy,hf⟩
    exact ⟨c • y,B.graph.smul_mem c hy,A.graph.smul_mem c hf⟩

def composition (A B : H →ₗ.[ℂ] H) : H →ₗ.[ℂ] H := (compositionGraph A B).toLinearPMap

theorem composition_graph_eq (A B : H →ₗ.[ℂ] H) :
    (composition A B).graph=compositionGraph A B := by
  apply Submodule.toLinearPMap_graph_eq
  rintro z ⟨y,hy,hz⟩ hx
  have hy0 : y=0 := B.mem_graph_snd_inj hy B.graph.zero_mem hx
  exact A.mem_graph_snd_inj hz A.graph.zero_mem hy0

theorem composition_graph (A B : H →ₗ.[ℂ] H) (f g : H) :
    (f,g) ∈ (composition A B).graph ↔ ∃ y, (f,y) ∈ B.graph ∧ (y,g) ∈ A.graph := by
  rw [composition_graph_eq]
  rfl

theorem composition_domain (A B : H →ₗ.[ℂ] H) (f : H) :
    f ∈ (composition A B).domain ↔ ∃ y, (f,y) ∈ B.graph ∧ y ∈ A.domain := by
  constructor
  · intro hf
    obtain ⟨y,hy,hg⟩ := (composition_graph A B f _).mp ((composition A B).mem_graph ⟨f,hf⟩)
    exact ⟨y,hy,LinearPMap.mem_domain_of_mem_graph hg⟩
  · rintro ⟨y,hy,hA⟩
    apply LinearPMap.mem_domain_of_mem_graph (y := A ⟨y,hA⟩)
    exact (composition_graph A B f _).mpr ⟨y,hy,A.mem_graph ⟨y,hA⟩⟩

variable [CompleteSpace H]

theorem selfAdjoint_graph_pairing (A : H →ₗ.[ℂ] H) (hA : IsSelfAdjoint A)
    (f g u v : H) (hf : (f,g) ∈ A.graph) (hu : (u,v) ∈ A.graph) :
    inner ℂ g u=inner ℂ f v := by
  have h := LinearPMap.adjoint_isFormalAdjoint hA.dense_domain
  rw [LinearPMap.isSelfAdjoint_def.mp hA] at h
  obtain ⟨x,hx,hg⟩ := (LinearPMap.mem_graph_iff A).mp hf
  obtain ⟨y,hy,hv⟩ := (LinearPMap.mem_graph_iff A).mp hu
  simpa only [hx,hg,hy,hv] using h x y

theorem composition_formalAdjoint (A B : H →ₗ.[ℂ] H)
    (hA : IsSelfAdjoint A) (hB : IsSelfAdjoint B) :
    (composition A B).IsFormalAdjoint (composition B A) := by
  intro f g
  obtain ⟨y,hy,hf⟩ := (composition_graph A B (f:H) _).mp ((composition A B).mem_graph f)
  obtain ⟨z,hz,hg⟩ := (composition_graph B A (g:H) _).mp ((composition B A).mem_graph g)
  exact (selfAdjoint_graph_pairing A hA y _ g z hf hz).trans
    (selfAdjoint_graph_pairing B hB f y z _ hy hg)

theorem composition_closable (A B : H →ₗ.[ℂ] H)
    (hA : IsSelfAdjoint A) (hB : IsSelfAdjoint B)
    (hd : Dense ((composition B A).domain : Set H)) : (composition A B).IsClosable :=
  (LinearPMap.adjoint_isClosed hd).isClosable.leIsClosable
    ((composition_formalAdjoint B A hB hA).le_adjoint hd)

#print axioms composition_graph_eq
#print axioms composition_graph
#print axioms composition_domain
#print axioms selfAdjoint_graph_pairing
#print axioms composition_formalAdjoint
#print axioms composition_closable

end
end UnifiedTheory.Audit.KFCausalOrderedOperatorComposition
