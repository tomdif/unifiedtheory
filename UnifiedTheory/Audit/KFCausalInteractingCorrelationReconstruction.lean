/- Constructive operator-to-correlation bridge for the actual interacting H(t).
For each fixed physical parameter t, the integer index below is a new discrete
resolvent-time index. It is not the physical parameter and does not assert a
continuous Euclidean semigroup. Reflection quotient, transfer, and the entire
Hamiltonian graph are identified without adding a model-matching hypothesis.
Spacetime-local fields, a gauge measure, and a physical vacuum remain open. -/
import UnifiedTheory.Audit.KFCausalResolventStationaryCovariance
import UnifiedTheory.Audit.KFCausalInteractingEnergyFloor

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalInteractingCorrelationReconstruction
noncomputable section
open scoped InnerProduct BigOperators
open KFCausalConfigurationTestSpace (Hilbert)
open KFCausalResolventReflectionKernel

variable (ε : ℝ) (hε : 0 < ε) (h : ℝ) (hpos : 0 < h)
  (hb : |h| ≤ Real.pi*ε/3) (m g k t : ℝ)
local notation "hw" => KFCausalClockFloorRadialYosidaReference.wide_bound ε hε h hb
local notation "H" => KFCausalClockFloorAveragedHamiltonian.hamiltonian ε hε h hpos.ne' hw m g k t

def physicalResolvent : Hilbert →L[ℂ] Hilbert :=
  KFCausalClockFloorHamiltonianClockCore.resolvent ε hε h hpos.ne' hw m g k t 1
local notation "R" => physicalResolvent ε hε h hpos hb m g k t

theorem resolvent_symmetric (f z : Hilbert) : inner ℂ (R f) z = inner ℂ f (R z) :=
  KFCausalPositiveResolventBounds.resolvent_inner_symm H R 1
    (KFCausalClockFloorHamiltonianClockCore.resolves ε hε h hpos.ne' hw m g k t 1 zero_lt_one)
    (KFCausalClockFloorAveragedHamiltonian.hamiltonian_selfAdjoint ε hε h hpos.ne' hw m g k t) f z

theorem resolvent_contraction (f : Hilbert) : ‖R f‖ ≤ ‖f‖ := by
  simpa only [inv_one, one_mul] using
    KFCausalPositiveResolventBounds.resolvent_apply_norm_bound H R 1 zero_lt_one
      (KFCausalClockFloorHamiltonianClockCore.resolves ε hε h hpos.ne' hw m g k t 1 zero_lt_one)
      (KFCausalClockFloorAveragedHamiltonian.hamiltonian_positive ε hε h hpos.ne' hw m g k t) f

theorem resolvent_injective : Function.Injective R :=
  KFCausalPositiveResolventBounds.resolvent_injective H R 1
    (KFCausalClockFloorHamiltonianClockCore.resolves ε hε h hpos.ne' hw m g k t 1 zero_lt_one)

theorem physical_reflection_positive (u : History Hilbert) :
    0 ≤ (reflectionPairing R u u).re :=
  reflection_positive R (resolvent_symmetric ε hε h hpos hb m g k t) u

theorem physical_bond_reflection_positive (u : History Hilbert) :
    0 ≤ (reflectionPairing R u (shift u)).re := by
  rw [pairing_reconstruction R (resolvent_symmetric ε hε h hpos hb m g k t),
    shift_reconstruct]
  have hp := KFCausalPositiveResolventBounds.resolvent_positive H R 1 zero_lt_one
    (KFCausalClockFloorHamiltonianClockCore.resolves ε hε h hpos.ne' hw m g k t 1 zero_lt_one)
    (KFCausalClockFloorAveragedHamiltonian.hamiltonian_selfAdjoint ε hε h hpos.ne' hw m g k t)
    (KFCausalClockFloorAveragedHamiltonian.hamiltonian_positive ε hε h hpos.ne' hw m g k t)
    (reconstruct R u)
  rwa [resolvent_symmetric ε hε h hpos hb m g k t] at hp

theorem physical_covariance_positive (u : ℕ → Hilbert) (N : ℕ) :
    0 ≤ (KFCausalResolventStationaryCovariance.covariance R u N).re :=
  KFCausalResolventStationaryCovariance.covariance_nonnegative R
    (resolvent_symmetric ε hε h hpos hb m g k t)
    (resolvent_contraction ε hε h hpos hb m g k t) u N

theorem physical_quotient_pairing (u v : History Hilbert) :
    @inner ℂ (Reconstructed R) _ (Submodule.Quotient.mk u) (Submodule.Quotient.mk v) =
      reflectionPairing R u v :=
  quotient_inner R (resolvent_symmetric ε hε h hpos hb m g k t) u v

theorem physical_transfer_positive (x : Reconstructed R) :
    0 ≤ (inner ℂ (transfer R x) x).re := by
  change 0 ≤ (inner ℂ (reconstructionIsometry R (transfer R x))
    (reconstructionIsometry R x)).re
  rw [transfer_intertwines]
  exact KFCausalPositiveResolventBounds.resolvent_positive H R 1 zero_lt_one
    (KFCausalClockFloorHamiltonianClockCore.resolves ε hε h hpos.ne' hw m g k t 1 zero_lt_one)
    (KFCausalClockFloorAveragedHamiltonian.hamiltonian_selfAdjoint ε hε h hpos.ne' hw m g k t)
    (KFCausalClockFloorAveragedHamiltonian.hamiltonian_positive ε hε h hpos.ne' hw m g k t)
    (reconstructionIsometry R x)

/-- The transfer determines the entire original operator graph, including its domain. -/
theorem hamiltonian_graph_iff (f y : Hilbert) :
    (f,y) ∈ (H).graph ↔ R (y+f) = f := by
  constructor
  · intro hg
    obtain ⟨x, rfl, rfl⟩ := (H).mem_graph_iff.mp hg
    simpa only [one_smul] using
      KFCausalClockFloorHamiltonianClockCore.left_inverse ε hε h hpos.ne' hw m g k t
        1 zero_lt_one x
  · intro he
    have hr := KFCausalClockFloorHamiltonianClockCore.resolves ε hε h hpos.ne' hw m g k t
      1 zero_lt_one (y+f)
    have hg : (R (y+f), (y+f) - (1:ℝ) • R (y+f)) ∈ (H).graph :=
      (H).mem_graph_iff.mpr ⟨⟨R (y+f),hr.1⟩,rfl,hr.2⟩
    simpa only [he, one_smul, add_sub_cancel_right] using hg

theorem hamiltonian_domain_iff (f : Hilbert) :
    f ∈ (H).domain ↔ ∃ z, R z = f := by
  constructor
  · intro hf
    exact ⟨H ⟨f,hf⟩+f, (hamiltonian_graph_iff ε hε h hpos hb m g k t f _).mp
      ((H).mem_graph ⟨f,hf⟩)⟩
  · rintro ⟨z,rfl⟩
    exact (KFCausalClockFloorHamiltonianClockCore.resolves ε hε h hpos.ne' hw m g k t
      1 zero_lt_one z).1

/-- A graph built only from the reconstructed bounded transfer. -/
def inverseTransferGraph : Submodule ℂ (Reconstructed R × Reconstructed R) where
  carrier := {p | transfer R (p.2+p.1) = p.1}
  zero_mem' := by simp
  add_mem' := by
    intro p q hp hq
    change transfer R ((p.2+q.2)+(p.1+q.1)) = p.1+q.1
    rw [show (p.2+q.2)+(p.1+q.1) = (p.2+p.1)+(q.2+q.1) by abel, map_add, hp, hq]
  smul_mem' := by
    intro c p hp
    change transfer R (c • p.2+c • p.1) = c • p.1
    rw [← smul_add, map_smul, hp]

private theorem inverseTransferGraph_singleValued
    (p : Reconstructed R × Reconstructed R)
    (hp : p ∈ inverseTransferGraph ε hε h hpos hb m g k t) (hz : p.1 = 0) : p.2 = 0 := by
  change transfer R (p.2+p.1) = p.1 at hp
  rw [hz, add_zero] at hp
  have he := congrArg (reconstructionIsometry R) hp
  rw [transfer_intertwines, map_zero] at he
  have hi := resolvent_injective ε hε h hpos hb m g k t
  have hx : reconstructionIsometry R p.2 = 0 := hi (by simpa only [map_zero] using he)
  exact (reconstructionIsometry R).injective (by simpa only [map_zero] using hx)

def reconstructedHamiltonian : Reconstructed R →ₗ.[ℂ] Reconstructed R :=
  (inverseTransferGraph ε hε h hpos hb m g k t).toLinearPMap

theorem reconstructed_graph (x y : Reconstructed R) :
    (x,y) ∈ (reconstructedHamiltonian ε hε h hpos hb m g k t).graph ↔
      transfer R (y+x) = x := by
  rw [reconstructedHamiltonian, Submodule.toLinearPMap_graph_eq _
    (inverseTransferGraph_singleValued ε hε h hpos hb m g k t)]
  rfl

theorem full_hamiltonian_identification (x y : Reconstructed R) :
    (x,y) ∈ (reconstructedHamiltonian ε hε h hpos hb m g k t).graph ↔
      (reconstructionIsometry R x, reconstructionIsometry R y) ∈ (H).graph := by
  rw [reconstructed_graph, hamiltonian_graph_iff]
  constructor
  · intro he
    have hh := congrArg (reconstructionIsometry R) he
    simpa only [transfer_intertwines, map_add] using hh
  · intro he
    apply (reconstructionIsometry R).injective
    simpa only [transfer_intertwines, map_add] using he

theorem physical_transfer_strict_bound (hk : 0 < k) (x : Reconstructed R) :
    ‖transfer R x‖ ≤ (1+ε/2)⁻¹*‖x‖ := by
  apply transfer_bound R
  intro f
  simpa only [div_eq_mul_inv, mul_comm] using
    KFCausalInteractingEnergyFloor.resolvent_norm_le ε hε h hpos hb m g k hk t 1 zero_lt_one f

/-- The unshifted resolvent construction has no nonzero fixed vacuum vector. -/
theorem no_nonzero_transfer_fixed_vector (hk : 0 < k) (x : Reconstructed R)
    (hx : transfer R x = x) : x = 0 := by
  have he := physical_transfer_strict_bound ε hε h hpos hb m g k t hk x
  rw [hx] at he
  have hq : (1+ε/2)⁻¹ < 1 := (inv_lt_one₀ (by positivity)).mpr (by linarith)
  have hn := norm_nonneg x
  have hz : ‖x‖ = 0 := by nlinarith
  exact norm_eq_zero.mp hz

#print axioms full_hamiltonian_identification
#print axioms no_nonzero_transfer_fixed_vector

end
end UnifiedTheory.Audit.KFCausalInteractingCorrelationReconstruction
