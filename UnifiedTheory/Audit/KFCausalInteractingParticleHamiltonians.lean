/- Tensor-particle and two-boson Hamiltonians for the actual full H(t).
The all-sector tensor sum retains particle labels. Bose symmetry in every
sector and a Pauli--Fierz coupling are not inferred from this construction. -/
import UnifiedTheory.Audit.KFCausalTensorParticleSectors
import UnifiedTheory.Audit.KFCausalTwoBosonHamiltonian
import UnifiedTheory.Audit.KFCausalClockFloorAveragedHamiltonian

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false

namespace UnifiedTheory.Audit.KFCausalInteractingParticleHamiltonians
noncomputable section
open KFCausalConfigurationTestSpace (Hilbert)
open KFCausalCompletedTensor

variable (ε : ℝ) (hε : 0 < ε) (h : ℝ) (hh : h ≠ 0)
  (hb : |h| ≤ 2 * Real.pi * ε / 3) (m g k t : ℝ)

local notation "D" => KFCausalClockFloorAveragedHamiltonian.formData ε hε h hh hb m g k t
local notation "H" => KFCausalClockFloorAveragedHamiltonian.hamiltonian ε hε h hh hb m g k t

def twoParticle : Space Hilbert Hilbert →ₗ.[ℂ] Space Hilbert Hilbert :=
  KFCausalTensorSumHamiltonian.tensorHamiltonian D D

theorem twoParticle_selfAdjoint : IsSelfAdjoint (twoParticle ε hε h hh hb m g k t) :=
  KFCausalTensorSumHamiltonian.selfAdjoint D D

theorem twoParticle_core : KFCausalTensorSumHamiltonian.CoreGraph D D :=
  KFCausalTensorSumHamiltonian.core_graph D D

def twoBoson : symmetric Hilbert →ₗ.[ℂ] symmetric Hilbert :=
  KFCausalTwoBosonHamiltonian.bosonHamiltonian D

theorem twoBoson_selfAdjoint : IsSelfAdjoint (twoBoson ε hε h hh hb m g k t) :=
  KFCausalTwoBosonHamiltonian.selfAdjoint D

theorem twoBoson_core : KFCausalTwoBosonHamiltonian.CoreGraph D :=
  KFCausalTwoBosonHamiltonian.core_graph D

abbrev ParticleSpace := KFCausalTensorParticleSectors.TensorFock D

def particleHamiltonian : ParticleSpace ε hε h hh hb m g k t →ₗ.[ℂ]
    ParticleSpace ε hε h hh hb m g k t := KFCausalTensorParticleSectors.fullHamiltonian D

theorem particle_selfAdjoint : IsSelfAdjoint (particleHamiltonian ε hε h hh hb m g k t) :=
  KFCausalTensorParticleSectors.full_selfAdjoint D

theorem particle_positive (u : (particleHamiltonian ε hε h hh hb m g k t).domain) :
    0 ≤ (inner ℂ (particleHamiltonian ε hε h hh hb m g k t u)
      (u : ParticleSpace ε hε h hh hb m g k t)).re :=
  KFCausalTensorParticleSectors.full_positive D u

theorem particle_domain (x : ParticleSpace ε hε h hh hb m g k t) :
    x ∈ (particleHamiltonian ε hε h hh hb m g k t).domain ↔
      ∃ (hx : ∀ n, x n ∈ (KFCausalTensorParticleSectors.sectorHamiltonian D n).domain),
        Memℓp (fun n => KFCausalTensorParticleSectors.sectorHamiltonian D n ⟨x n, hx n⟩) 2 :=
  KFCausalTensorParticleSectors.full_domain D x

theorem one_particle_recovers_full_interaction :
    KFCausalTensorParticleSectors.sectorHamiltonian D 1 = H := rfl

def vacuum : ParticleSpace ε hε h hh hb m g k t := KFCausalTensorParticleSectors.vacuum D

theorem vacuum_norm : ‖vacuum ε hε h hh hb m g k t‖ = 1 :=
  KFCausalTensorParticleSectors.vacuum_norm D

theorem vacuum_stationary :
    (vacuum ε hε h hh hb m g k t, 0) ∈ (particleHamiltonian ε hε h hh hb m g k t).graph :=
  KFCausalTensorParticleSectors.vacuum_stationary D

end
end UnifiedTheory.Audit.KFCausalInteractingParticleHamiltonians
