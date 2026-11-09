/- The original epsilon/2 floor gives an n*epsilon/2 tensor-sector floor,
a number-weighted lower bound, and a one-dimensional zero-energy kernel
for the uncoupled labelled particle sum. This is not a Pauli--Fierz gap. -/
import UnifiedTheory.Audit.KFCausalParticleEnergyGap
import UnifiedTheory.Audit.KFCausalInteractingParticleHamiltonians
import UnifiedTheory.Audit.KFCausalInteractingEnergyFloor
import UnifiedTheory.Audit.KFCausalTwoBosonRestriction

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false

namespace UnifiedTheory.Audit.KFCausalInteractingParticleEnergyGap
noncomputable section
open KFCausalConfigurationTestSpace (Hilbert)
open KFCausalTensorSumEnergyFloor KFCausalTensorParticleSectors

variable (ε : ℝ) (hε : 0 < ε) (h : ℝ) (hpos : 0 < h)
  (hb : |h| ≤ Real.pi * ε / 3) (m g k : ℝ) (hk : 0 < k) (t : ℝ)
local notation "hw" => KFCausalClockFloorRadialYosidaReference.wide_bound ε hε h hb
local notation "D" => KFCausalClockFloorAveragedHamiltonian.formData ε hε h hpos.ne' hw m g k t
local notation "H" => KFCausalClockFloorAveragedHamiltonian.hamiltonian ε hε h hpos.ne' hw m g k t

theorem two_boson_graph_identification : KFCausalTwoBosonRestriction.GraphIdentification D :=
  KFCausalTwoBosonRestriction.graph_iff D

theorem two_boson_domain_identification : KFCausalTwoBosonRestriction.DomainIdentification D :=
  KFCausalTwoBosonRestriction.domain_iff D

include hk in
theorem original_lower : LowerBound D (ε / 2) := by
  intro x
  exact KFCausalInteractingEnergyFloor.graph_energy_lower ε hε h hpos hb m g k hk t x (H x)
    ((H).mem_graph x)

include hk in
theorem sector_energy_lower (n : ℕ) : LowerBound (sector D n).form ((n : ℝ) * (ε / 2)) :=
  KFCausalParticleEnergyGap.sector_lower D (ε / 2)
    (original_lower ε hε h hpos hb m g k hk t) n

include hk in
theorem two_boson_lower : LowerBound (KFCausalTwoBosonHamiltonian.bosonForm D) (ε / 2 + ε / 2) :=
  boson_lower D (ε / 2) (original_lower ε hε h hpos hb m g k hk t)

include hk in
theorem number_energy_lower (x : (fullHamiltonian D).domain) :
    (∑' n : ℕ, ((n : ℝ) * (ε / 2)) * ‖(x : TensorFock D) n‖ ^ 2) ≤
      (inner ℂ (fullHamiltonian D x) (x : TensorFock D)).re :=
  KFCausalParticleEnergyGap.number_energy_lower D (ε / 2) (by positivity)
    (original_lower ε hε h hpos hb m g k hk t) x

include hk in
theorem excitation_energy_gap (x : (fullHamiltonian D).domain)
    (hx : inner ℂ (vacuum D) (x : TensorFock D) = 0) :
    (ε / 2) * ‖(x : TensorFock D)‖ ^ 2 ≤
      (inner ℂ (fullHamiltonian D x) (x : TensorFock D)).re :=
  KFCausalParticleEnergyGap.orthogonal_energy_gap D (ε / 2) (by positivity)
    (original_lower ε hε h hpos hb m g k hk t) x hx

include hk in
theorem vacuum_kernel_unique (x : TensorFock D) (hx : (x, 0) ∈ (fullHamiltonian D).graph) :
    x = KFCausalParticleEnergyGap.vacuumCoefficient D x • vacuum D :=
  KFCausalParticleEnergyGap.zero_energy_kernel D (ε / 2) (by positivity)
    (original_lower ε hε h hpos hb m g k hk t) x hx

end
end UnifiedTheory.Audit.KFCausalInteractingParticleEnergyGap
