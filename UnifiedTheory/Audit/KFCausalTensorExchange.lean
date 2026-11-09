/- Particle exchange preserves the full closed tensor energy graph and
the full domain of the two-particle Hamiltonian. -/
import UnifiedTheory.Audit.KFCausalFormInvolution
import UnifiedTheory.Audit.KFCausalTwoBosonHamiltonian

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Audit.KFCausalTensorExchange
noncomputable section
open scoped TensorProduct
open KFCausalClosedGraphForm KFCausalCompletedTensor KFCausalTensorSumHamiltonian

variable (H K : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K]

def flip : Space H K ≃ₗᵢ[ℂ] Space K H :=
  (TensorProduct.comm ℂ H K).extendOfIsometry
    (includeTensor H K).toLinearMap (includeTensor K H).toLinearMap
    UniformSpace.Completion.denseRange_coe UniformSpace.Completion.denseRange_coe
    (by intro u; simp)

theorem flip_include (u : H ⊗[ℂ] K) :
    flip H K (includeTensor H K u) = includeTensor K H (TensorProduct.comm ℂ H K u) :=
  (TensorProduct.comm ℂ H K).extendOfIsometry_eq _ _ _ _ _ u

theorem flip_pure (x : H) (y : K) : flip H K (pure H K x y) = pure K H y x :=
  flip_include H K (x ⊗ₜ[ℂ] y)

theorem flip_flip (x : Space H K) : flip K H (flip H K x) = x := by
  refine UniformSpace.Completion.denseRange_coe.induction_on x
    (isClosed_eq ((flip K H).continuous.comp (flip H K).continuous) continuous_id) ?_
  intro u
  change flip K H (flip H K (includeTensor H K u)) = includeTensor H K u
  rw [flip_include, flip_include]
  congr 1
  exact (TensorProduct.comm ℂ H K).symm_apply_apply u

def energySwap : EnergySpace (H := H) (K := K) (X := H) (Y := K) ≃ₗᵢ[ℂ]
    EnergySpace (H := H) (K := K) (X := H) (Y := K) :=
  ((flip K H).withLpProdCongr 2 (flip H K)).trans
    (LinearIsometryEquiv.withLpProdComm 2 ℂ (Space H K) (Space K H))

theorem energySwap_involutive : Function.Involutive (energySwap H K) := by
  intro x
  apply WithLp.ofLp_injective 2
  apply Prod.ext
  · exact flip_flip K H _
  · exact flip_flip H K _

variable [CompleteSpace H] [CompleteSpace K]

theorem output_exchange (D : Data H K) (u : Core D D) :
    energySwap H K (output D D u) = output D D (TensorProduct.comm ℂ _ _ u) := by
  induction u using TensorProduct.induction_on with
  | zero => simp
  | add u v hu hv => simp only [map_add, hu, hv]
  | tmul a b =>
    apply WithLp.ofLp_injective 2
    apply Prod.ext
    · exact flip_pure H K (a : H) (domainEnergy D b)
    · exact flip_pure K H (domainEnergy D a) (b : H)

theorem energy_graph_exchange (D : Data H K)
    (z : Space H H × EnergySpace (H := H) (K := K) (X := H) (Y := K))
    (hz : z ∈ (tensorForm D D).operator.graph) :
    (swap H z.1, energySwap H K z.2) ∈ (tensorForm D D).operator.graph := by
  let S := KFCausalSeparatedGraphClosure.graphRange (input D D) (output D D)
  have he : (tensorForm D D).operator.graph = S.topologicalClosure :=
    KFCausalEnergyCoreClosure.closedOperator_graph _ _ _ (factorization D D)
  rw [he] at hz ⊢
  have hc : IsClosed {w : Space H H × EnergySpace (H := H) (K := K) (X := H) (Y := K) |
      (swap H w.1, energySwap H K w.2) ∈ S.topologicalClosure} :=
    S.isClosed_topologicalClosure.preimage
      (((swap H).continuous.comp continuous_fst).prodMk
        ((energySwap H K).continuous.comp continuous_snd))
  have hi : (S : Set (Space H H × EnergySpace (H := H) (K := K) (X := H) (Y := K))) ⊆
      {w | (swap H w.1, energySwap H K w.2) ∈ S.topologicalClosure} := by
    rintro w ⟨u, rfl⟩
    change (swap H (input D D u), energySwap H K (output D D u)) ∈ S.topologicalClosure
    rw [KFCausalTwoBosonHamiltonian.input_swap, output_exchange]
    exact S.le_topologicalClosure ⟨TensorProduct.comm ℂ _ _ u, rfl⟩
  exact closure_minimal hi hc (by simpa only [Submodule.topologicalClosure_coe] using hz)

theorem hamiltonian_exchange (D : Data H K) (x : (tensorHamiltonian D D).domain) :
    (swap H (x : Space H H), swap H (tensorHamiltonian D D x)) ∈ (tensorHamiltonian D D).graph :=
  KFCausalFormInvolution.hamiltonian_graph (tensorForm D D) (swap H) (energySwap H K)
    (energy_graph_exchange H K D) (swap_involutive H) (energySwap_involutive H K) x

end
end UnifiedTheory.Audit.KFCausalTensorExchange
