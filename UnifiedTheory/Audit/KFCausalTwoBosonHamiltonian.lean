/- The symmetric two-particle sector and its positive self-adjoint
Hamiltonian, constructed from the actual one-particle closed form. -/
import UnifiedTheory.Audit.KFCausalTensorSumHamiltonian

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Audit.KFCausalTwoBosonHamiltonian
noncomputable section
open scoped TensorProduct
open KFCausalClosedGraphForm KFCausalCompletedTensor KFCausalTensorSumHamiltonian

variable {H K : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

def coreSym (D : Data H K) : Core D D →ₗ[ℂ] Core D D :=
  LinearMap.id + (TensorProduct.comm ℂ (hamiltonian D).domain (hamiltonian D).domain).toLinearMap

theorem input_swap (D : Data H K) (u : Core D D) :
    swap H (input D D u) = input D D (TensorProduct.comm ℂ _ _ u) := by
  induction u using TensorProduct.induction_on with
  | zero => simp
  | add u v hu hv => simp only [map_add, hu, hv]
  | tmul a b => exact swap_pure H (a : H) (b : H)

theorem action_swap (D : Data H K) (u : Core D D) :
    swap H (action D D u) = action D D (TensorProduct.comm ℂ _ _ u) := by
  induction u using TensorProduct.induction_on with
  | zero => simp
  | add u v hu hv => simp only [map_add, hu, hv]
  | tmul a b =>
    change swap H (pure H H (hamiltonian D a) (b : H) +
      pure H H (a : H) (hamiltonian D b)) =
      pure H H (hamiltonian D b) (a : H) + pure H H (b : H) (hamiltonian D a)
    rw [map_add, swap_pure, swap_pure, add_comm]

theorem coreSym_fixed (D : Data H K) (u : Core D D) :
    TensorProduct.comm ℂ _ _ (coreSym D u) = coreSym D u := by
  change TensorProduct.comm ℂ _ _ (u + TensorProduct.comm ℂ _ _ u) = _
  rw [map_add]
  have hh := (TensorProduct.comm ℂ (hamiltonian D).domain
    (hamiltonian D).domain).symm_apply_apply u
  change TensorProduct.comm ℂ _ _ (TensorProduct.comm ℂ _ _ u) = u at hh
  rw [hh]
  exact add_comm _ _

def bosonInput (D : Data H K) : Core D D →ₗ[ℂ] symmetric H :=
  (symmetrize H).toLinearMap.comp (input D D)

theorem bosonInput_coe (D : Data H K) (u : Core D D) :
    (bosonInput D u : Space H H) = input D D (coreSym D u) := by
  change input D D u + swap H (input D D u) = input D D (u + TensorProduct.comm ℂ _ _ u)
  rw [map_add, input_swap]

def bosonOutput (D : Data H K) : Core D D →ₗ[ℂ]
    EnergySpace (H := H) (K := K) (X := H) (Y := K) := (output D D).comp (coreSym D)

def bosonAction (D : Data H K) : Core D D →ₗ[ℂ] symmetric H :=
  ((action D D).comp (coreSym D)).codRestrict (symmetric H) (by
    intro u
    rw [mem_symmetric]
    exact (action_swap D (coreSym D u)).trans (congrArg (action D D) (coreSym_fixed D u)))

theorem bosonInput_dense (D : Data H K) : DenseRange (bosonInput D) :=
  (symmetrize_surjective H).denseRange.comp (input_dense D D) (symmetrize H).continuous

theorem boson_factorization (D : Data H K) (u v : Core D D) :
    inner ℂ (bosonOutput D u) (bosonOutput D v) =
      inner ℂ (bosonAction D u) (bosonInput D v) := by
  change inner ℂ (output D D (coreSym D u)) (output D D (coreSym D v)) =
    inner ℂ (action D D (coreSym D u)) (bosonInput D v : Space H H)
  rw [bosonInput_coe, factorization]

def bosonForm (D : Data H K) :
    Data (symmetric H) (EnergySpace (H := H) (K := K) (X := H) (Y := K)) :=
  KFCausalEnergyCoreClosure.formData (bosonInput D) (bosonOutput D) (bosonAction D)
    (bosonInput_dense D) (boson_factorization D)

def bosonHamiltonian (D : Data H K) : symmetric H →ₗ.[ℂ] symmetric H :=
  hamiltonian (bosonForm D)

theorem selfAdjoint (D : Data H K) : IsSelfAdjoint (bosonHamiltonian D) :=
  hamiltonian_selfAdjoint _

def CoreGraph (D : Data H K) : Prop :=
  ∀ u : Core D D, (bosonInput D u, bosonAction D u) ∈ (bosonHamiltonian D).graph

theorem core_graph (D : Data H K) : CoreGraph D :=
  fun u => KFCausalEnergyCoreClosure.core_graph _ _ _ (bosonInput_dense D)
    (boson_factorization D) u

theorem core_action_coe (D : Data H K) (a b : (hamiltonian D).domain) :
    (bosonAction D (a ⊗ₜ[ℂ] b) : Space H H) =
      pure H H (hamiltonian D a) (b : H) + pure H H (a : H) (hamiltonian D b) +
      (pure H H (hamiltonian D b) (a : H) + pure H H (b : H) (hamiltonian D a)) := by
  change action D D (a ⊗ₜ[ℂ] b + b ⊗ₜ[ℂ] a) = _
  rw [map_add]
  rfl

theorem positive (D : Data H K) (u : (bosonHamiltonian D).domain) :
    0 ≤ (inner ℂ (bosonHamiltonian D u) (u : symmetric H)).re :=
  hamiltonian_positive _ u

theorem variational_domain (D : Data H K)
    (u : FormSpace (bosonForm D)) (y : symmetric H) :
    (∃ hx : embedding (bosonForm D) u ∈ (bosonHamiltonian D).domain,
      bosonHamiltonian D ⟨embedding (bosonForm D) u, hx⟩ = y) ↔
    ∀ v, inner ℂ (energyOutput (bosonForm D) u) (energyOutput (bosonForm D) v) =
      inner ℂ y (embedding (bosonForm D) v) :=
  hamiltonian_domain_characterization _ _ _

end
end UnifiedTheory.Audit.KFCausalTwoBosonHamiltonian
