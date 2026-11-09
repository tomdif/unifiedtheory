/- The full interacting H(t), acting on one factor of the completed space
L2(Omega; X). Its self-adjointness, exact full domain, and energy floor are
proved from the actual resolvent. This is one tensor-factor action, not
the sum over all particle factors or its bosonic restriction. -/
import UnifiedTheory.Audit.KFCausalLpHamiltonianAmplification
import UnifiedTheory.Audit.KFCausalInteractingCorrelationReconstruction

set_option autoImplicit false
set_option Elab.async false

namespace UnifiedTheory.Audit.KFCausalInteractingTensorFactor
noncomputable section
open MeasureTheory
open KFCausalConfigurationTestSpace (Hilbert)
open KFCausalInteractingCorrelationReconstruction

variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
variable (ε : ℝ) (hε : 0 < ε) (h : ℝ) (hpos : 0 < h)
  (hb : |h| ≤ Real.pi*ε/3) (m g k t : ℝ)
local notation "hw" => KFCausalClockFloorRadialYosidaReference.wide_bound ε hε h hb
local notation "H" => KFCausalClockFloorAveragedHamiltonian.hamiltonian ε hε h hpos.ne' hw m g k t
local notation "R" => physicalResolvent ε hε h hpos hb m g k t

def hamiltonian : Lp Hilbert 2 μ →ₗ.[ℂ] Lp Hilbert 2 μ :=
  KFCausalLpHamiltonianAmplification.hamiltonian μ R
    (resolvent_injective ε hε h hpos hb m g k t)

theorem hamiltonian_selfAdjoint : IsSelfAdjoint (hamiltonian μ ε hε h hpos hb m g k t) :=
  KFCausalLpHamiltonianAmplification.hamiltonian_selfAdjoint μ R
    (resolvent_injective ε hε h hpos hb m g k t)
    (resolvent_symmetric ε hε h hpos hb m g k t)

theorem hamiltonian_graph (f y : Lp Hilbert 2 μ) :
    (f,y) ∈ (hamiltonian μ ε hε h hpos hb m g k t).graph ↔
      ∀ᵐ x ∂μ, (f x,y x) ∈ (H).graph := by
  rw [hamiltonian, KFCausalLpHamiltonianAmplification.hamiltonian_graph]
  simp only [KFCausalLpHamiltonianAmplification.inverseShift_graph_iff,
    hamiltonian_graph_iff ε hε h hpos hb m g k t]

theorem hamiltonian_domain (f : Lp Hilbert 2 μ) :
    f ∈ (hamiltonian μ ε hε h hpos hb m g k t).domain ↔
      ∃ y : Lp Hilbert 2 μ, ∀ᵐ x ∂μ, (f x,y x) ∈ (H).graph := by
  rw [hamiltonian, KFCausalLpHamiltonianAmplification.hamiltonian_domain]
  simp only [KFCausalLpHamiltonianAmplification.inverseShift_graph_iff,
    hamiltonian_graph_iff ε hε h hpos hb m g k t]

theorem energy_lower (hk : 0 < k) (f y : Lp Hilbert 2 μ)
    (hfy : (f,y) ∈ (hamiltonian μ ε hε h hpos hb m g k t).graph) :
    (ε/2)*‖f‖^2 ≤ (inner ℂ y f).re := by
  have he := (hamiltonian_graph μ ε hε h hpos hb m g k t f y).mp hfy
  have hsq : Integrable (fun x => ‖f x‖^2) μ :=
    (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable f)).mp (Lp.memLp f)
  rw [KFCausalAveragedEnergyGraph.l2_norm_square, ← integral_const_mul, L2.inner_def]
  have hr : (∫ x, inner ℂ (y x) (f x) ∂μ).re = ∫ x, (inner ℂ (y x) (f x)).re ∂μ :=
    (integral_re (L2.integrable_inner (𝕜 := ℂ) y f)).symm
  rw [hr]
  apply integral_mono_ae (hsq.const_mul (ε/2)) (L2.integrable_inner (𝕜 := ℂ) y f).re
  filter_upwards [he] with x hx
  exact KFCausalInteractingEnergyFloor.graph_energy_lower ε hε h hpos hb m g k hk t _ _ hx

end
end UnifiedTheory.Audit.KFCausalInteractingTensorFactor
