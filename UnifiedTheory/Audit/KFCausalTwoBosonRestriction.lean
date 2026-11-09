/- Exact equality, including full domains, between the two-boson
Friedrichs operator and the symmetric restriction of the tensor sum. -/
import UnifiedTheory.Audit.KFCausalTwoBosonFormBridge

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Audit.KFCausalTwoBosonRestriction
noncomputable section
open KFCausalClosedGraphForm KFCausalCompletedTensor KFCausalTensorSumHamiltonian
open KFCausalTwoBosonHamiltonian

variable {H K : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

def GraphIdentification (D : Data H K) : Prop :=
  ∀ x y : symmetric H, (x, y) ∈ (bosonHamiltonian D).graph ↔
    ((x : Space H H), (y : Space H H)) ∈ (tensorHamiltonian D D).graph

theorem graph_iff (D : Data H K) : GraphIdentification D := by
  intro x y
  constructor
  · intro hg
    obtain ⟨u, hu, hv⟩ := (bosonHamiltonian D).mem_graph_iff.mp hg
    have hi := KFCausalTwoBosonFormBridge.hamiltonian_inclusion D u
    simpa only [hu, hv] using hi
  · intro hg
    have hf : (tensorHamiltonian D D).IsFormalAdjoint (tensorHamiltonian D D) := by
      have h := LinearPMap.adjoint_isFormalAdjoint
        (KFCausalTensorSumHamiltonian.selfAdjoint D D).dense_domain
      rwa [LinearPMap.isSelfAdjoint_def.mp (KFCausalTensorSumHamiltonian.selfAdjoint D D)] at h
    have hp (v : (bosonHamiltonian D).domain) :
        inner ℂ y (v : symmetric H) = inner ℂ x (bosonHamiltonian D v) := by
      obtain ⟨a, ha, hay⟩ := (tensorHamiltonian D D).mem_graph_iff.mp hg
      obtain ⟨b, hb, hby⟩ := (tensorHamiltonian D D).mem_graph_iff.mp
        (KFCausalTwoBosonFormBridge.hamiltonian_inclusion D v)
      have hh := hf a b
      dsimp only at ha hay hb hby
      rw [ha, hay, hb, hby] at hh
      exact hh
    have hx : x ∈ (bosonHamiltonian D).adjoint.domain :=
      LinearPMap.mem_adjoint_domain_of_exists _ ⟨y, hp⟩
    have hy := LinearPMap.adjoint_apply_eq (KFCausalTwoBosonHamiltonian.selfAdjoint D).dense_domain
      ⟨x, hx⟩ hp
    have he : (x, y) ∈ (bosonHamiltonian D).adjoint.graph := by
      rw [LinearPMap.mem_graph_iff]
      exact ⟨⟨x, hx⟩, rfl, hy⟩
    rwa [LinearPMap.isSelfAdjoint_def.mp (KFCausalTwoBosonHamiltonian.selfAdjoint D)] at he

def DomainIdentification (D : Data H K) : Prop :=
  ∀ x : symmetric H, x ∈ (bosonHamiltonian D).domain ↔
    (x : Space H H) ∈ (tensorHamiltonian D D).domain

theorem domain_iff (D : Data H K) : DomainIdentification D := by
  intro x
  constructor
  · intro hx
    exact LinearPMap.mem_domain_of_mem_graph (KFCausalTwoBosonFormBridge.hamiltonian_inclusion D ⟨x, hx⟩)
  · intro hx
    let u : (tensorHamiltonian D D).domain := ⟨x, hx⟩
    have he := KFCausalTensorExchange.hamiltonian_exchange H K D u
    have hy : swap H (tensorHamiltonian D D u) = tensorHamiltonian D D u :=
      (tensorHamiltonian D D).mem_graph_snd_inj' he ((tensorHamiltonian D D).mem_graph u)
        ((mem_symmetric H x).mp x.property)
    let y : symmetric H := ⟨tensorHamiltonian D D u, (mem_symmetric H _).mpr hy⟩
    exact LinearPMap.mem_domain_of_mem_graph
      ((graph_iff D x y).mpr ((tensorHamiltonian D D).mem_graph u))

end
end UnifiedTheory.Audit.KFCausalTwoBosonRestriction
