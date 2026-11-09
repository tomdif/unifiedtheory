/- Bose-symmetric sectors for all particle numbers of the actual H(t).
The gap here belongs to the uncoupled particle sum, not the Pauli--Fierz model. -/
import UnifiedTheory.Audit.KFCausalBosonicEnergyGap
import UnifiedTheory.Audit.KFCausalBosonicSectorOneParticle
import UnifiedTheory.Audit.KFCausalInteractingParticleEnergyGap

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false

namespace UnifiedTheory.Audit.KFCausalInteractingBosonicHamiltonian
noncomputable section
open KFCausalTensorSumEnergyFloor KFCausalBosonicFock

variable (ε : ℝ) (hε : 0 < ε) (h : ℝ) (hpos : 0 < h)
  (hb : |h| ≤ Real.pi * ε / 3) (m g k : ℝ) (hk : 0 < k) (t : ℝ)
local notation "hw" => KFCausalClockFloorRadialYosidaReference.wide_bound ε hε h hb
local notation "D" => KFCausalClockFloorAveragedHamiltonian.formData ε hε h hpos.ne' hw m g k t

theorem sector_selfAdjoint (n : ℕ) : IsSelfAdjoint (sectorHamiltonian D n) :=
  KFCausalBosonicFock.sector_selfAdjoint D n

theorem core_graph (n : ℕ) : KFCausalBosonicSectorHamiltonian.CoreGraph D n :=
  KFCausalBosonicSectorHamiltonian.core_graph D n

theorem one_particle_graph_identification : KFCausalBosonicSectorOneParticle.GraphIdentification D :=
  KFCausalBosonicSectorOneParticle.graph_iff D

theorem one_particle_domain_identification : KFCausalBosonicSectorOneParticle.DomainIdentification D :=
  KFCausalBosonicSectorOneParticle.domain_iff D

theorem full_selfAdjoint : IsSelfAdjoint (fullHamiltonian D) :=
  KFCausalBosonicFock.full_selfAdjoint D

theorem vacuum_stationary : (vacuum D, 0) ∈ (fullHamiltonian D).graph :=
  KFCausalBosonicFock.vacuum_stationary D

include hk in
theorem sector_energy_lower (n : ℕ) : LowerBound (sector D n).form ((n : ℝ) * (ε / 2)) :=
  KFCausalBosonicEnergyGap.sector_lower D (ε / 2)
    (KFCausalInteractingParticleEnergyGap.original_lower ε hε h hpos hb m g k hk t) n

include hk in
theorem number_energy_lower (x : (fullHamiltonian D).domain) :
    (∑' n : ℕ, ((n : ℝ) * (ε / 2)) * ‖(x : BosonFock D) n‖ ^ 2) ≤
      (inner ℂ (fullHamiltonian D x) (x : BosonFock D)).re :=
  KFCausalBosonicEnergyGap.number_energy_lower D (ε / 2) (by positivity)
    (KFCausalInteractingParticleEnergyGap.original_lower ε hε h hpos hb m g k hk t) x

include hk in
theorem excitation_energy_gap (x : (fullHamiltonian D).domain)
    (hx : inner ℂ (vacuum D) (x : BosonFock D) = 0) :
    (ε / 2) * ‖(x : BosonFock D)‖ ^ 2 ≤
      (inner ℂ (fullHamiltonian D x) (x : BosonFock D)).re :=
  KFCausalBosonicEnergyGap.orthogonal_energy_gap D (ε / 2) (by positivity)
    (KFCausalInteractingParticleEnergyGap.original_lower ε hε h hpos hb m g k hk t) x hx

include hk in
theorem vacuum_kernel_unique (x : BosonFock D) (hx : (x, 0) ∈ (fullHamiltonian D).graph) :
    x = KFCausalBosonicEnergyGap.vacuumCoefficient D x • vacuum D :=
  KFCausalBosonicEnergyGap.zero_energy_kernel D (ε / 2) (by positivity)
    (KFCausalInteractingParticleEnergyGap.original_lower ε hε h hpos hb m g k hk t) x hx

end
end UnifiedTheory.Audit.KFCausalInteractingBosonicHamiltonian
