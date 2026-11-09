/- A surjective transformation of complete energy forms gives an exact
unitary correspondence of the representing operator graphs. Applications
must prove the form transformation, its surjectivity and its pairing. -/
import UnifiedTheory.Audit.KFCausalClosedGraphForm

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 800000

namespace UnifiedTheory.Audit.KFCausalClosedFormUnitaryGraph
noncomputable section
open KFCausalClosedGraphForm

variable {H K E : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

theorem graph_iff (D : Data H K) (U : H ≃ₗᵢ[ℂ] H) (J : E → H)
    (F : E → FormSpace D) (hs : Function.Surjective F)
    (hJ : ∀ u, embedding D (F u) = U (J u))
    (b : E → E → ℂ)
    (hb : ∀ u v, inner ℂ (energyOutput D (F u)) (energyOutput D (F v)) = b u v)
    (f g : H) :
    (U f,U g) ∈ (hamiltonian D).graph ↔
      ∃ u, J u = f ∧ ∀ v, b u v = inner ℂ g (J v) := by
  constructor
  · intro hfg
    have hf := LinearPMap.mem_domain_of_mem_graph hfg
    let x : (hamiltonian D).domain := ⟨U f,hf⟩
    have hx : hamiltonian D x = U g :=
      (hamiltonian D).mem_graph_snd_inj' ((hamiltonian D).mem_graph x) hfg rfl
    obtain ⟨u,hu⟩ := hs (formLift D x)
    have huf : J u = f := U.injective
      ((hJ u).symm.trans ((congrArg (embedding D) hu).trans (embedding_formLift D x)))
    refine ⟨u,huf,?_⟩
    intro v
    exact (hb u v).symm.trans
      ((congrArg (fun w => inner ℂ (energyOutput D w) (energyOutput D (F v))) hu).trans
        ((hamiltonian_represents_form D x (F v)).trans
          ((congrArg₂ (inner ℂ) hx (hJ v)).trans (U.inner_map_map g (J v)))))
  · rintro ⟨u,huf,hpair⟩
    have hp : ∀ w : FormSpace D,
        inner ℂ (energyOutput D (F u)) (energyOutput D w) = inner ℂ (U g) (embedding D w) := by
      intro w
      obtain ⟨v,rfl⟩ := hs w
      exact (hb u v).trans ((hpair v).trans ((U.inner_map_map g (J v)).symm.trans
        (congrArg (inner ℂ (U g)) (hJ v).symm)))
    obtain ⟨hd,he⟩ := (hamiltonian_domain_characterization D (F u) (U g)).mpr hp
    have hg : (embedding D (F u),U g) ∈ (hamiltonian D).graph :=
      (LinearPMap.mem_graph_iff (hamiltonian D)).mpr ⟨⟨_,hd⟩,rfl,he⟩
    exact (congrArg (fun z => (z,U g) ∈ (hamiltonian D).graph)
      ((hJ u).trans (congrArg U huf))).mp hg

#print axioms graph_iff
end
end UnifiedTheory.Audit.KFCausalClosedFormUnitaryGraph
