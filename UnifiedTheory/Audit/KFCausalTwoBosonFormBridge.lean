/- Continuous graph maps connect the independently closed two-boson form
with the full tensor-sum form. -/
import UnifiedTheory.Audit.KFCausalTensorExchange

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Audit.KFCausalTwoBosonFormBridge
noncomputable section
open KFCausalClosedGraphForm KFCausalCompletedTensor KFCausalTensorSumHamiltonian
open KFCausalTwoBosonHamiltonian KFCausalTensorExchange

variable {H K : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

private theorem map_closure {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F] (S : Submodule ℂ E) (T : Submodule ℂ F)
    (hc : IsClosed (T : Set F)) (L : E →L[ℂ] F) (hL : ∀ x ∈ S, L x ∈ T)
    (x : E) (hx : x ∈ S.topologicalClosure) : L x ∈ T :=
  closure_minimal hL (hc.preimage L.continuous)
    (by simpa only [Submodule.topologicalClosure_coe] using hx)

theorem include_graph (D : Data H K)
    (z : symmetric H × EnergySpace (H := H) (K := K) (X := H) (Y := K))
    (hz : z ∈ (bosonForm D).operator.graph) :
    ((z.1 : Space H H), z.2) ∈ (tensorForm D D).operator.graph := by
  have he : (bosonForm D).operator.graph =
      (KFCausalSeparatedGraphClosure.graphRange (bosonInput D) (bosonOutput D)).topologicalClosure :=
    KFCausalEnergyCoreClosure.closedOperator_graph _ _ _ (boson_factorization D)
  rw [he] at hz
  let L := (symmetric H).subtypeL.prodMap
    (ContinuousLinearMap.id ℂ (EnergySpace (H := H) (K := K) (X := H) (Y := K)))
  apply map_closure _ _ (tensorForm D D).closed L _ z hz
  rintro w ⟨u, rfl⟩
  change ((bosonInput D u : Space H H), bosonOutput D u) ∈ (tensorForm D D).operator.graph
  rw [bosonInput_coe]
  exact KFCausalEnergyCoreClosure.core_energy_graph _ _ _ (factorization D D) (coreSym D u)

theorem output_symmetrize (D : Data H K) (u : Core D D) :
    bosonOutput D u = output D D u + energySwap H K (output D D u) := by
  change output D D (u + TensorProduct.comm ℂ _ _ u) = _
  rw [map_add, ← output_exchange]

theorem project_graph (D : Data H K)
    (z : Space H H × EnergySpace (H := H) (K := K) (X := H) (Y := K))
    (hz : z ∈ (tensorForm D D).operator.graph) :
    (symmetrize H z.1, z.2 + energySwap H K z.2) ∈ (bosonForm D).operator.graph := by
  have he : (tensorForm D D).operator.graph =
      (KFCausalSeparatedGraphClosure.graphRange (input D D) (output D D)).topologicalClosure :=
    KFCausalEnergyCoreClosure.closedOperator_graph _ _ _ (factorization D D)
  rw [he] at hz
  let L := (symmetrize H).prodMap
    (ContinuousLinearMap.id ℂ _ + (energySwap H K).toContinuousLinearEquiv.toContinuousLinearMap)
  apply map_closure _ _ (bosonForm D).closed L _ z hz
  rintro w ⟨u, rfl⟩
  change (bosonInput D u, output D D u + energySwap H K (output D D u)) ∈
    (bosonForm D).operator.graph
  rw [← output_symmetrize]
  exact KFCausalEnergyCoreClosure.core_energy_graph _ _ _ (boson_factorization D) u

def lift (D : Data H K) (u : FormSpace (bosonForm D)) : FormSpace (tensorForm D D) :=
  ⟨WithLp.toLp 2 ((embedding (bosonForm D) u : Space H H), energyOutput (bosonForm D) u),
    include_graph D _ u.property⟩

def project (D : Data H K) (u : FormSpace (tensorForm D D)) : FormSpace (bosonForm D) :=
  ⟨WithLp.toLp 2 (symmetrize H (embedding (tensorForm D D) u),
    energyOutput (tensorForm D D) u + energySwap H K (energyOutput (tensorForm D D) u)),
    project_graph D _ u.property⟩

theorem output_fixed (D : Data H K) (u : FormSpace (bosonForm D)) :
    energySwap H K (energyOutput (bosonForm D) u) = energyOutput (bosonForm D) u := by
  have hi := include_graph D _ u.property
  exact (tensorForm D D).operator.mem_graph_snd_inj'
    (energy_graph_exchange H K D _ hi) hi
    ((mem_symmetric H _).mp (embedding (bosonForm D) u).property)

set_option maxHeartbeats 800000 in
-- The two completed forms have nested subtype domains.
theorem hamiltonian_inclusion (D : Data H K) (x : (bosonHamiltonian D).domain) :
    (((x : symmetric H) : Space H H), (bosonHamiltonian D x : Space H H)) ∈
      (tensorHamiltonian D D).graph := by
  let u := formLift (bosonForm D) x
  have hq : ∀ v : FormSpace (tensorForm D D),
      inner ℂ (energyOutput (tensorForm D D) (lift D u)) (energyOutput (tensorForm D D) v) =
      inner ℂ (bosonHamiltonian D x : Space H H) (embedding (tensorForm D D) v) := by
    intro v
    have hp := hamiltonian_represents_form (bosonForm D) x (project D v)
    change inner ℂ (energyOutput (bosonForm D) u)
        (energyOutput (tensorForm D D) v + energySwap H K (energyOutput (tensorForm D D) v)) =
      inner ℂ (bosonHamiltonian D x : Space H H)
        (embedding (tensorForm D D) v + swap H (embedding (tensorForm D D) v)) at hp
    have he := KFCausalFormInvolution.inner_involution (energySwap H K)
      (energySwap_involutive H K) (energyOutput (bosonForm D) u) (energyOutput (tensorForm D D) v)
    rw [output_fixed D u] at he
    have hy := KFCausalFormInvolution.inner_involution (swap H) (swap_involutive H)
      (bosonHamiltonian D x : Space H H) (embedding (tensorForm D D) v)
    rw [(mem_symmetric H _).mp (bosonHamiltonian D x).property] at hy
    rw [inner_add_right, inner_add_right, ← he, ← hy] at hp
    change inner ℂ (energyOutput (bosonForm D) u) (energyOutput (tensorForm D D) v) = _
    linear_combination (1 / 2 : ℂ) * hp
  obtain ⟨hx, hy⟩ := (hamiltonian_domain_characterization (tensorForm D D) (lift D u)
    (bosonHamiltonian D x : Space H H)).mpr hq
  rw [LinearPMap.mem_graph_iff]
  refine ⟨⟨_, hx⟩, ?_, hy⟩
  change (embedding (bosonForm D) (formLift (bosonForm D) x) : Space H H) = _
  rw [embedding_formLift]

end
end UnifiedTheory.Audit.KFCausalTwoBosonFormBridge
