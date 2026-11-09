/- A positive self-adjoint tensor sum from two closed graph forms.
No eigenbasis or pure-point spectrum is assumed. -/
import UnifiedTheory.Audit.KFCausalEnergyCoreClosure
import UnifiedTheory.Audit.KFCausalCompletedTensor

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Audit.KFCausalTensorSumHamiltonian
noncomputable section
open scoped TensorProduct
open KFCausalClosedGraphForm KFCausalCompletedTensor

variable {H K X Y : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  [NormedAddCommGroup X] [InnerProductSpace ℂ X] [CompleteSpace X]
  [NormedAddCommGroup Y] [InnerProductSpace ℂ Y] [CompleteSpace Y]

def domainEnergy (D : Data H K) : (hamiltonian D).domain →ₗ[ℂ] K :=
  (energyOutput D).toLinearMap.comp ((embedding D).adjoint.toLinearMap.comp
    ((hamiltonian D).toFun + (hamiltonian D).domain.subtype))

theorem domainEnergy_pairing (D : Data H K) (u v : (hamiltonian D).domain) :
    inner ℂ (domainEnergy D u) (domainEnergy D v) = inner ℂ (hamiltonian D u) (v : H) := by
  change inner ℂ (energyOutput D (formLift D u)) (energyOutput D (formLift D v)) = _
  rw [hamiltonian_represents_form, embedding_formLift]

abbrev Core (D : Data H K) (F : Data X Y) :=
  (hamiltonian D).domain ⊗[ℂ] (hamiltonian F).domain

abbrev EnergySpace := WithLp 2 (Space K X × Space H Y)

def input (D : Data H K) (F : Data X Y) : Core D F →ₗ[ℂ] Space H X :=
  coreEmbedding H X (hamiltonian D).domain.subtype (hamiltonian F).domain.subtype

def output (D : Data H K) (F : Data X Y) :
    Core D F →ₗ[ℂ] EnergySpace (H := H) (K := K) (X := X) (Y := Y) :=
  (WithLp.prodContinuousLinearEquiv 2 ℂ (Space K X) (Space H Y)).symm.toLinearMap.comp
    ((coreEmbedding K X (domainEnergy D) (hamiltonian F).domain.subtype).prod
      (coreEmbedding H Y (hamiltonian D).domain.subtype (domainEnergy F)))

def action (D : Data H K) (F : Data X Y) : Core D F →ₗ[ℂ] Space H X :=
  coreEmbedding H X (hamiltonian D).toFun (hamiltonian F).domain.subtype +
    coreEmbedding H X (hamiltonian D).domain.subtype (hamiltonian F).toFun

theorem input_dense (D : Data H K) (F : Data X Y) : DenseRange (input D F) :=
  coreEmbedding_dense H X _ _ (by simpa using hamiltonian_dense D)
    (by simpa using hamiltonian_dense F)

theorem factorization (D : Data H K) (F : Data X Y) (u v : Core D F) :
    inner ℂ (output D F u) (output D F v) = inner ℂ (action D F u) (input D F v) := by
  induction u using TensorProduct.induction_on with
  | zero => simp
  | add u w hu hw => simp only [map_add, inner_add_left, hu, hw]
  | tmul a b =>
    induction v using TensorProduct.induction_on with
    | zero => simp
    | add v w hv hw => simp only [map_add, inner_add_right, hv, hw]
    | tmul c d =>
      change inner ℂ (pure K X (domainEnergy D a) (b : X))
          (pure K X (domainEnergy D c) (d : X)) +
        inner ℂ (pure H Y (a : H) (domainEnergy F b))
          (pure H Y (c : H) (domainEnergy F d)) =
        inner ℂ (pure H X (hamiltonian D a) (b : X) +
          pure H X (a : H) (hamiltonian F b)) (pure H X (c : H) (d : X))
      rw [inner_add_left, pure_inner, pure_inner, pure_inner, pure_inner,
        domainEnergy_pairing, domainEnergy_pairing]

def tensorForm (D : Data H K) (F : Data X Y) :
    Data (Space H X) (EnergySpace (H := H) (K := K) (X := X) (Y := Y)) :=
  KFCausalEnergyCoreClosure.formData (input D F) (output D F) (action D F)
    (input_dense D F) (factorization D F)

def tensorHamiltonian (D : Data H K) (F : Data X Y) : Space H X →ₗ.[ℂ] Space H X :=
  hamiltonian (tensorForm D F)

theorem selfAdjoint (D : Data H K) (F : Data X Y) : IsSelfAdjoint (tensorHamiltonian D F) :=
  hamiltonian_selfAdjoint _

def CoreGraph (D : Data H K) (F : Data X Y) : Prop :=
  ∀ u : Core D F, (input D F u, action D F u) ∈ (tensorHamiltonian D F).graph

theorem core_graph (D : Data H K) (F : Data X Y) : CoreGraph D F :=
  fun u => KFCausalEnergyCoreClosure.core_graph _ _ _ (input_dense D F) (factorization D F) u

theorem pure_graph (D : Data H K) (F : Data X Y)
    (a : (hamiltonian D).domain) (b : (hamiltonian F).domain) :
    (pure H X (a : H) (b : X), pure H X (hamiltonian D a) (b : X) +
      pure H X (a : H) (hamiltonian F b)) ∈ (tensorHamiltonian D F).graph :=
  core_graph D F (a ⊗ₜ[ℂ] b)

theorem positive (D : Data H K) (F : Data X Y) (u : (tensorHamiltonian D F).domain) :
    0 ≤ (inner ℂ (tensorHamiltonian D F u) (u : Space H X)).re :=
  hamiltonian_positive _ u

theorem variational_domain (D : Data H K) (F : Data X Y)
    (u : FormSpace (tensorForm D F)) (y : Space H X) :
    (∃ hx : embedding (tensorForm D F) u ∈ (tensorHamiltonian D F).domain,
      tensorHamiltonian D F ⟨embedding (tensorForm D F) u, hx⟩ = y) ↔
    ∀ v, inner ℂ (energyOutput (tensorForm D F) u) (energyOutput (tensorForm D F) v) =
      inner ℂ y (embedding (tensorForm D F) v) :=
  hamiltonian_domain_characterization _ _ _

end
end UnifiedTheory.Audit.KFCausalTensorSumHamiltonian
