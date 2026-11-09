/- Positive self-adjoint Hamiltonians on every completed Bose-symmetric
sector, from the symmetrized actual tensor-domain energy core. -/
import UnifiedTheory.Audit.KFCausalParticleCoreCovariance
import UnifiedTheory.Audit.KFCausalBosonicSectorProjection
import UnifiedTheory.Audit.KFCausalParticleEnergyGap

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Audit.KFCausalBosonicSectorHamiltonian
noncomputable section
open KFCausalClosedGraphForm KFCausalTensorParticleSectors KFCausalParticlePermutations
open KFCausalParticleDomainTensors KFCausalParticleCoreCovariance KFCausalBosonicSectorProjection

variable {H K : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

def averageCore (D : Data H K) (n : ℕ) : Core D n →ₗ[ℂ] Core D n :=
  (Fintype.card (Equiv.Perm (Fin (n + 1))) : ℂ)⁻¹ •
    ∑ σ : Equiv.Perm (Fin (n + 1)), (domainPerm D n σ).toLinearMap

theorem input_average (D : Data H K) (n : ℕ) (u : Core D n) :
    input D n (averageCore D n u) = average D n (input D n u) := by
  simp only [averageCore, LinearMap.smul_apply, LinearMap.sum_apply, map_smul, map_sum,
    average_apply, ← input_permute, LinearEquiv.coe_coe]

theorem output_average (D : Data H K) (n : ℕ) (u : Core D n) :
    output D n (averageCore D n u) = average D n (output D n u) := by
  simp only [averageCore, LinearMap.smul_apply, LinearMap.sum_apply, map_smul, map_sum,
    average_apply, ← output_permute, LinearEquiv.coe_coe]

def bosonInput (D : Data H K) (n : ℕ) : Core D n →ₗ[ℂ] invariant D n :=
  (projection D n).toLinearMap.comp (input D n)

def bosonAction (D : Data H K) (n : ℕ) : Core D n →ₗ[ℂ] invariant D n :=
  (projection D n).toLinearMap.comp (output D n)

def bosonEnergy (D : Data H K) (n : ℕ) : Core D n →ₗ[ℂ] (nonemptySector D n).Energy :=
  (KFCausalTensorSumHamiltonian.domainEnergy (nonemptySector D n).form).comp
    ((coreDomain D n).comp (averageCore D n))

theorem input_coe (D : Data H K) (n : ℕ) (u : Core D n) :
    (bosonInput D n u : (nonemptySector D n).State) = input D n (averageCore D n u) :=
  (input_average D n u).symm

theorem action_coe (D : Data H K) (n : ℕ) (u : Core D n) :
    (bosonAction D n u : (nonemptySector D n).State) = output D n (averageCore D n u) :=
  (output_average D n u).symm

theorem bosonInput_dense (D : Data H K) (n : ℕ) : DenseRange (bosonInput D n) :=
  (projection_surjective D n).denseRange.comp (input_dense D n) (projection D n).continuous

theorem factorization (D : Data H K) (n : ℕ) (u v : Core D n) :
    inner ℂ (bosonEnergy D n u) (bosonEnergy D n v) =
      inner ℂ (bosonAction D n u) (bosonInput D n v) := by
  change inner ℂ (KFCausalTensorSumHamiltonian.domainEnergy (nonemptySector D n).form
      (coreDomain D n (averageCore D n u)))
    (KFCausalTensorSumHamiltonian.domainEnergy (nonemptySector D n).form
      (coreDomain D n (averageCore D n v))) =
    inner ℂ (bosonAction D n u : (nonemptySector D n).State)
      (bosonInput D n v : (nonemptySector D n).State)
  rw [KFCausalTensorSumHamiltonian.domainEnergy_pairing, coreDomain_value, action_coe, input_coe]
  rfl

def bosonForm (D : Data H K) (n : ℕ) : Data (invariant D n) (nonemptySector D n).Energy :=
  KFCausalEnergyCoreClosure.formData (bosonInput D n) (bosonEnergy D n) (bosonAction D n)
    (bosonInput_dense D n) (factorization D n)

def bosonHamiltonian (D : Data H K) (n : ℕ) : invariant D n →ₗ.[ℂ] invariant D n :=
  hamiltonian (bosonForm D n)

theorem selfAdjoint (D : Data H K) (n : ℕ) : IsSelfAdjoint (bosonHamiltonian D n) :=
  hamiltonian_selfAdjoint _

def CoreGraph (D : Data H K) (n : ℕ) : Prop :=
  ∀ u : Core D n, (bosonInput D n u, bosonAction D n u) ∈ (bosonHamiltonian D n).graph

theorem core_graph (D : Data H K) (n : ℕ) : CoreGraph D n :=
  KFCausalEnergyCoreClosure.core_graph _ _ _ (bosonInput_dense D n) (factorization D n)

theorem lower_bound (D : Data H K) (n : ℕ) (δ : ℝ)
    (hD : KFCausalTensorSumEnergyFloor.LowerBound D δ) :
    KFCausalTensorSumEnergyFloor.LowerBound (bosonForm D n) (((n : ℝ) + 1) * δ) := by
  apply KFCausalEnergyCoreFloor.hamiltonian_lower
  intro u
  have he := KFCausalTensorSumEnergyFloor.domainEnergy_lower (nonemptySector D n).form
    (((n : ℝ) + 1) * δ) (KFCausalParticleEnergyGap.nonempty_lower D δ hD n)
      (coreDomain D n (averageCore D n u))
  change (((n : ℝ) + 1) * δ) * ‖(bosonInput D n u : (nonemptySector D n).State)‖ ^ 2 ≤ _
  rw [input_coe]
  exact he

theorem variational_domain (D : Data H K) (n : ℕ)
    (u : FormSpace (bosonForm D n)) (y : invariant D n) :
    (∃ hx : KFCausalClosedGraphForm.embedding (bosonForm D n) u ∈ (bosonHamiltonian D n).domain,
      bosonHamiltonian D n ⟨KFCausalClosedGraphForm.embedding (bosonForm D n) u, hx⟩ = y) ↔
    ∀ v, inner ℂ (energyOutput (bosonForm D n) u) (energyOutput (bosonForm D n) v) =
      inner ℂ y (KFCausalClosedGraphForm.embedding (bosonForm D n) v) :=
  hamiltonian_domain_characterization _ _ _

end
end UnifiedTheory.Audit.KFCausalBosonicSectorHamiltonian
