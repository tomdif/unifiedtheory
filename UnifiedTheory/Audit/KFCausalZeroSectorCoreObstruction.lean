/- A family confined to zero charge cannot be an operator core for the
full physical Hamiltonian. This does not exclude a core for its zero sector. -/
import UnifiedTheory.Audit.KFCausalCircularChargeDomain
import UnifiedTheory.Audit.KFCausalClockFloorAveragedHamiltonian

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000

namespace UnifiedTheory.Audit.KFCausalZeroSectorCoreObstruction
noncomputable section
open KFCausalConfigurationTestSpace (Hilbert)
open KFCausalStandingChargeOperator (zeroSector zeroSector_closed)
open KFCausalCircularChargeTransform (packet transform_packet)

theorem exists_nonzero_charge (h : ℝ) (hh : h ≠ 0) :
    ∃ f : Hilbert, f ∉ zeroSector h hh := by
  let B := KFCausalHermiteProductBasis.planeBasis 1 1 (by norm_num) (by norm_num)
  let g := B (0,0)
  let i : KFCausalHermiteProductBasis.Index := ((1,0),(0,0))
  refine ⟨packet h hh 1 (by norm_num) i g, ?_⟩
  intro hf
  have he := (KFCausalCircularChargeDomain.zero_sector_iff h hh 1 (by norm_num) _).mp hf i
    (by norm_num [i,KFCausalFourCircularChargeBasis.charge])
  rw [transform_packet] at he
  have hz : g = 0 := by simpa [lp.single_apply] using he
  have hn : ‖g‖ = 1 := B.orthonormal.norm_eq_one (0,0)
  rw [hz,norm_zero] at hn
  norm_num at hn

private theorem graph_closure_ne_of_closed_set {X : Type*}
    [NormedAddCommGroup X] [NormedSpace ℂ X]
    (T : X →ₗ.[ℂ] X) (hd : Dense (T.domain : Set X))
    (Z : Set X) (hZ : IsClosed Z) (hne : ∃ f, f ∉ Z)
    (S : Set (X × X)) (hS : ∀ p ∈ S, p.1 ∈ Z) :
    closure S ≠ (T.graph : Set (X × X)) := by
  intro he
  have hc : closure S ⊆ {p : X × X | p.1 ∈ Z} :=
    closure_minimal hS (hZ.preimage continuous_fst)
  have ht : (T.domain : Set X) ⊆ Z := by
    intro f hf
    have hp : (f,T ⟨f,hf⟩) ∈ closure S := by
      rw [he]
      exact T.mem_graph ⟨f,hf⟩
    exact @hc (f,T ⟨f,hf⟩) hp
  obtain ⟨f,hf⟩ := hne
  exact hf ((closure_minimal ht hZ) (hd f))

/-- Applies to every densely defined operator, without any spectral assumption. -/
theorem graph_closure_ne_of_zero_sector (h : ℝ) (hh : h ≠ 0)
    (T : Hilbert →ₗ.[ℂ] Hilbert) (hd : Dense (T.domain : Set Hilbert))
    (S : Set (Hilbert × Hilbert)) (hS : ∀ p ∈ S, p.1 ∈ zeroSector h hh) :
    closure S ≠ (T.graph : Set (Hilbert × Hilbert)) :=
  graph_closure_ne_of_closed_set T hd (zeroSector h hh) (zeroSector_closed h hh)
    (exists_nonzero_charge h hh) S hS

theorem hamiltonian_graph_closure_ne (ε : ℝ) (hε : 0 < ε) (h : ℝ) (hh : h ≠ 0)
    (hb : |h| ≤ 2*Real.pi*ε/3) (m g k t : ℝ)
    (S : Set (Hilbert × Hilbert)) (hS : ∀ p ∈ S, p.1 ∈ zeroSector h hh) :
    closure S ≠ ((KFCausalClockFloorAveragedHamiltonian.hamiltonian
      ε hε h hh hb m g k t).graph : Set (Hilbert × Hilbert)) :=
  graph_closure_ne_of_zero_sector h hh _
    (KFCausalClockFloorAveragedHamiltonian.hamiltonian_dense ε hε h hh hb m g k t) S hS

/-- Even allowing arbitrary second coordinates cannot repair the missing charged states. -/
theorem zero_charge_family_not_core (ε h : ℝ) (hε : 0 < ε) (hh : h ≠ 0)
    (hb : |h| ≤ 2*Real.pi*ε/3) (m g k t : ℝ)
    {ι : Type*} (f y : ι → Hilbert) (hf : ∀ j, f j ∈ zeroSector h hh) :
    closure (Set.range (fun j => (f j,y j))) ≠
      ((KFCausalClockFloorAveragedHamiltonian.hamiltonian
        ε hε h hh hb m g k t).graph : Set (Hilbert × Hilbert)) := by
  apply hamiltonian_graph_closure_ne ε hε h hh hb m g k t
  rintro _ ⟨j,rfl⟩
  exact hf j

#print axioms exists_nonzero_charge
#print axioms graph_closure_ne_of_zero_sector
#print axioms hamiltonian_graph_closure_ne
#print axioms zero_charge_family_not_core
end
end UnifiedTheory.Audit.KFCausalZeroSectorCoreObstruction
