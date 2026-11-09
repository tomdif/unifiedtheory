/- Exact full-graph and full-domain recovery of the original Hamiltonian
in the one-particle Bose sector. -/
import UnifiedTheory.Audit.KFCausalBosonicSectorHamiltonian

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Audit.KFCausalBosonicSectorOneParticle
noncomputable section
open KFCausalClosedGraphForm KFCausalBosonicSectorProjection KFCausalBosonicSectorHamiltonian

variable {H K : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

theorem all_invariant (D : Data H K) (x : H) : x ∈ invariant D 0 := by
  intro σ
  have hσ : σ = 1 := by
    apply Equiv.ext
    intro i
    exact (Fin.eq_zero _).trans (Fin.eq_zero _).symm
  rw [hσ, KFCausalParticlePermutations.action_one]


def identification (D : Data H K) : invariant D 0 ≃ₗᵢ[ℂ] H :=
  LinearIsometryEquiv.ofSurjective (invariant D 0).subtypeₗᵢ
    (fun x => ⟨⟨x, all_invariant D x⟩, rfl⟩)

theorem average_one (D : Data H K) (x : H) : average D 0 x = x :=
  average_on_invariant D 0 ⟨x, all_invariant D x⟩

theorem original_core_graph (D : Data H K) (v : (hamiltonian D).domain) :
    (projection D 0 (v : H), projection D 0 (hamiltonian D v)) ∈
      (bosonHamiltonian D 0).graph := by
  have he := core_graph D 0 (Finsupp.single (fun _ : Fin 1 => v) 1)
  simpa only [bosonInput, bosonAction, LinearMap.comp_apply,
    KFCausalParticleDomainTensors.input, KFCausalParticleDomainTensors.output,
    Finsupp.linearCombination_single, one_smul, KFCausalParticleDomainTensors.inputTuple,
    KFCausalParticlePureTensors.pureTuple, KFCausalParticleDomainTensors.actionTuple] using he

theorem hamiltonian_inclusion (D : Data H K) (x : (bosonHamiltonian D 0).domain) :
    ((x : invariant D 0).val, (bosonHamiltonian D 0 x).val) ∈ (hamiltonian D).graph := by
  have hf : (bosonHamiltonian D 0).IsFormalAdjoint (bosonHamiltonian D 0) := by
    have hh := LinearPMap.adjoint_isFormalAdjoint (selfAdjoint D 0).dense_domain
    rwa [LinearPMap.isSelfAdjoint_def.mp (selfAdjoint D 0)] at hh
  have hp (v : (hamiltonian D).domain) :
      inner ℂ (bosonHamiltonian D 0 x).val (v : H) =
        inner ℂ (x : invariant D 0).val (hamiltonian D v) := by
    obtain ⟨b, hb, hby⟩ := (bosonHamiltonian D 0).mem_graph_iff.mp (original_core_graph D v)
    have he := hf x b
    dsimp only at hb hby
    rw [hb, hby] at he
    change inner ℂ (bosonHamiltonian D 0 x).val (average D 0 (v : H)) =
      inner ℂ (x : invariant D 0).val (average D 0 (hamiltonian D v)) at he
    simpa only [average_one] using he
  have hx : (x : invariant D 0).val ∈ (hamiltonian D).adjoint.domain :=
    LinearPMap.mem_adjoint_domain_of_exists _ ⟨(bosonHamiltonian D 0 x).val, hp⟩
  have hy := LinearPMap.adjoint_apply_eq (hamiltonian_selfAdjoint D).dense_domain
    ⟨(x : invariant D 0).val, hx⟩ hp
  have he : ((x : invariant D 0).val, (bosonHamiltonian D 0 x).val) ∈
      (hamiltonian D).adjoint.graph := by
    rw [LinearPMap.mem_graph_iff]
    exact ⟨⟨_, hx⟩, rfl, hy⟩
  rwa [LinearPMap.isSelfAdjoint_def.mp (hamiltonian_selfAdjoint D)] at he

def GraphIdentification (D : Data H K) : Prop :=
  ∀ x y : invariant D 0, (x, y) ∈ (bosonHamiltonian D 0).graph ↔
    (x.val, y.val) ∈ (hamiltonian D).graph

theorem graph_iff (D : Data H K) : GraphIdentification D := by
  intro x y
  constructor
  · intro hg
    obtain ⟨u, hu, hv⟩ := (bosonHamiltonian D 0).mem_graph_iff.mp hg
    simpa only [hu, hv] using hamiltonian_inclusion D u
  · intro hg
    have hf : (hamiltonian D).IsFormalAdjoint (hamiltonian D) := by
      have hh := LinearPMap.adjoint_isFormalAdjoint (hamiltonian_selfAdjoint D).dense_domain
      rwa [LinearPMap.isSelfAdjoint_def.mp (hamiltonian_selfAdjoint D)] at hh
    have hp (v : (bosonHamiltonian D 0).domain) :
        inner ℂ y (v : invariant D 0) = inner ℂ x (bosonHamiltonian D 0 v) := by
      obtain ⟨a, ha, hay⟩ := (hamiltonian D).mem_graph_iff.mp hg
      obtain ⟨b, hb, hby⟩ := (hamiltonian D).mem_graph_iff.mp (hamiltonian_inclusion D v)
      have hh := hf a b
      dsimp only at ha hay hb hby
      rw [ha, hay, hb, hby] at hh
      exact hh
    have hx : x ∈ (bosonHamiltonian D 0).adjoint.domain :=
      LinearPMap.mem_adjoint_domain_of_exists _ ⟨y, hp⟩
    have hy := LinearPMap.adjoint_apply_eq (selfAdjoint D 0).dense_domain ⟨x, hx⟩ hp
    have he : (x, y) ∈ (bosonHamiltonian D 0).adjoint.graph := by
      rw [LinearPMap.mem_graph_iff]
      exact ⟨⟨x, hx⟩, rfl, hy⟩
    rwa [LinearPMap.isSelfAdjoint_def.mp (selfAdjoint D 0)] at he

def DomainIdentification (D : Data H K) : Prop :=
  ∀ x : invariant D 0, x ∈ (bosonHamiltonian D 0).domain ↔ x.val ∈ (hamiltonian D).domain

theorem domain_iff (D : Data H K) : DomainIdentification D := by
  intro x
  constructor
  · intro hx
    exact LinearPMap.mem_domain_of_mem_graph (hamiltonian_inclusion D ⟨x, hx⟩)
  · intro hx
    let y : invariant D 0 := ⟨hamiltonian D ⟨x.val, hx⟩, all_invariant D _⟩
    exact LinearPMap.mem_domain_of_mem_graph
      ((graph_iff D x y).mpr ((hamiltonian D).mem_graph ⟨x.val, hx⟩))

end
end UnifiedTheory.Audit.KFCausalBosonicSectorOneParticle
