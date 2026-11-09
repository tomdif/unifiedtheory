/- Formal adjointness reverses all three factors on their exact natural
composition domains. Density of the reversed domain implies closability;
no composition is presumed closed or self-adjoint. -/
import UnifiedTheory.Audit.KFCausalOrderedOperatorComposition

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 800000

namespace UnifiedTheory.Audit.KFCausalTripleOperatorComposition
noncomputable section
open UnifiedTheory.Audit.KFCausalOrderedOperatorComposition
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem triple_formalAdjoint (A B C : H →ₗ.[ℂ] H)
    (hA : IsSelfAdjoint A) (hB : IsSelfAdjoint B) (hC : IsSelfAdjoint C) :
    (composition A (composition B C)).IsFormalAdjoint (composition (composition C B) A) := by
  intro f g
  obtain ⟨y,hy,hf⟩ := (composition_graph A (composition B C) (f:H) _).mp
    ((composition A (composition B C)).mem_graph f)
  obtain ⟨x,hx,hxy⟩ := (composition_graph B C (f:H) y).mp hy
  obtain ⟨v,hv,hg⟩ := (composition_graph (composition C B) A (g:H) _).mp
    ((composition (composition C B) A).mem_graph g)
  obtain ⟨u,hu,hug⟩ := (composition_graph C B v _).mp hg
  exact (selfAdjoint_graph_pairing A hA y _ g v hf hv).trans
    ((selfAdjoint_graph_pairing B hB x y v u hxy hu).trans
      (selfAdjoint_graph_pairing C hC f x u _ hx hug))

theorem triple_closable (A B C : H →ₗ.[ℂ] H)
    (hA : IsSelfAdjoint A) (hB : IsSelfAdjoint B) (hC : IsSelfAdjoint C)
    (hd : Dense ((composition (composition C B) A).domain : Set H)) :
    (composition A (composition B C)).IsClosable :=
  (LinearPMap.adjoint_isClosed hd).isClosable.leIsClosable
    ((triple_formalAdjoint A B C hA hB hC).symm.le_adjoint hd)

#print axioms triple_formalAdjoint
#print axioms triple_closable

end
end UnifiedTheory.Audit.KFCausalTripleOperatorComposition
