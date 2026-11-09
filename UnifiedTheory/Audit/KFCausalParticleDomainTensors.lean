/- Tensors of actual one-particle domain vectors form a Hilbert-dense domain and
have the iterated sum action in the labelled particle Hamiltonian graph. -/
import UnifiedTheory.Audit.KFCausalParticlePureTensors

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Audit.KFCausalParticleDomainTensors
noncomputable section
open scoped TensorProduct
open KFCausalClosedGraphForm KFCausalCompletedTensor KFCausalTensorParticleSectors
open KFCausalParticlePureTensors

variable {H K : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

abbrev Tuple (D : Data H K) (n : ℕ) := Fin (n + 1) → (hamiltonian D).domain

def inputTuple (D : Data H K) (n : ℕ) (v : Tuple D n) : (nonemptySector D n).State :=
  pureTuple D n (fun i => (v i : H))

def actionTuple (D : Data H K) : (n : ℕ) → Tuple D n → (nonemptySector D n).State
  | 0, v => hamiltonian D (v 0)
  | n + 1, v =>
      pure (nonemptySector D n).State H (actionTuple D n (fun i => v i.castSucc))
        (v (Fin.last (n + 1)) : H) +
      pure (nonemptySector D n).State H (inputTuple D n (fun i => v i.castSucc))
        (hamiltonian D (v (Fin.last (n + 1))))

theorem tuple_graph (D : Data H K) (n : ℕ) (v : Tuple D n) :
    (inputTuple D n v, actionTuple D n v) ∈ (hamiltonian (nonemptySector D n).form).graph := by
  induction n with
  | zero => exact (hamiltonian D).mem_graph (v 0)
  | succ n hn =>
    obtain ⟨a, ha, hb⟩ := (hamiltonian (nonemptySector D n).form).mem_graph_iff.mp
      (hn (fun i => v i.castSucc))
    dsimp only at ha hb
    have he := product_pure_graph (nonemptySector D n) (fromForm D) a
      (v (Fin.last (n + 1)))
    dsimp only [fromForm] at he
    rw [ha, hb] at he
    dsimp only [nonemptySector, product, fromForm, inputTuple, pureTuple, actionTuple] at he ⊢
    exact he

theorem total_domain (D : Data H K) (n : ℕ) (S : Submodule ℂ (nonemptySector D n).State)
    (hc : IsClosed (S : Set (nonemptySector D n).State))
    (hp : ∀ v : Tuple D n, inputTuple D n v ∈ S) : ∀ x, x ∈ S := by
  have hd : DenseRange (hamiltonian D).domain.subtype := by simpa using hamiltonian_dense D
  induction n with
  | zero =>
    intro x
    exact hd.induction_on x hc (fun a => hp (fun _ => a))
  | succ n hn =>
    have ht (x : (nonemptySector D n).State) (y : H) : pure _ H x y ∈ S := by
      refine hd.induction_on y (hc.preimage (right _ H x).continuous) ?_
      intro b
      let L := left (nonemptySector D n).State H (b : H)
      apply hn (S.comap L.toLinearMap) (hc.preimage L.continuous) _ x
      intro v
      change pure _ H (inputTuple D n v) (b : H) ∈ S
      have he := hp (Fin.snoc v b)
      simpa [inputTuple, pureTuple] using he
    have ha (u : (nonemptySector D n).State ⊗[ℂ] H) : includeTensor _ H u ∈ S := by
      induction u using TensorProduct.induction_on with
      | zero => exact S.zero_mem
      | tmul x y => exact ht x y
      | add u v hu hv => simpa only [map_add] using S.add_mem hu hv
    intro x
    exact UniformSpace.Completion.denseRange_coe.induction_on x hc ha

abbrev Core (D : Data H K) (n : ℕ) := Tuple D n →₀ ℂ

def input (D : Data H K) (n : ℕ) : Core D n →ₗ[ℂ] (nonemptySector D n).State :=
  Finsupp.linearCombination ℂ (inputTuple D n)

def output (D : Data H K) (n : ℕ) : Core D n →ₗ[ℂ] (nonemptySector D n).State :=
  Finsupp.linearCombination ℂ (actionTuple D n)

theorem input_dense (D : Data H K) (n : ℕ) : DenseRange (input D n) := by
  apply total_domain D n (input D n).range.topologicalClosure
    (input D n).range.isClosed_topologicalClosure
  intro v
  apply (input D n).range.le_topologicalClosure
  exact ⟨Finsupp.single v 1, by simp [input]⟩

theorem core_graph (D : Data H K) (n : ℕ) (u : Core D n) :
    (input D n u, output D n u) ∈ (hamiltonian (nonemptySector D n).form).graph := by
  induction u using Finsupp.induction_linear with
  | zero => simpa using (hamiltonian (nonemptySector D n).form).graph.zero_mem
  | add u v hu hv => simpa only [map_add] using
      (hamiltonian (nonemptySector D n).form).graph.add_mem hu hv
  | single v c => simpa only [input, output, Finsupp.linearCombination_single] using
      (hamiltonian (nonemptySector D n).form).graph.smul_mem c (tuple_graph D n v)

def coreDomain (D : Data H K) (n : ℕ) :
    Core D n →ₗ[ℂ] (hamiltonian (nonemptySector D n).form).domain :=
  (input D n).codRestrict _ (fun u => LinearPMap.mem_domain_of_mem_graph (core_graph D n u))

theorem coreDomain_value (D : Data H K) (n : ℕ) (u : Core D n) :
    hamiltonian (nonemptySector D n).form (coreDomain D n u) = output D n u :=
  (hamiltonian (nonemptySector D n).form).mem_graph_snd_inj'
    ((hamiltonian (nonemptySector D n).form).mem_graph _) (core_graph D n u) rfl

end
end UnifiedTheory.Audit.KFCausalParticleDomainTensors
