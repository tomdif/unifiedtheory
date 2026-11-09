/- Charge rotations preserve the FULL maximal pure-clock momentum graph.
This follows from proved all-L2 group commutation, with no compact-state
core premise, charge-zero condition or Hamiltonian-domain assumption. -/
import UnifiedTheory.Audit.KFCausalClockFloorPureClockCharge
import UnifiedTheory.Audit.KFCausalClockFloorPureClockMomentum

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 800000

namespace UnifiedTheory.Audit.KFCausalClockFloorPureClockChargeGraph
noncomputable section
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalClockFloorPureClockTransport (transport)
open UnifiedTheory.Audit.KFCausalPhysicalCircleAction (action action_reverse)
open UnifiedTheory.Audit.KFCausalClockFloorPureClockMomentum (pureGroup pureMomentum)
open UnifiedTheory.Audit.KFCausalUnitaryMomentumEvolution (momentum_graph_iff)
open UnifiedTheory.Audit.KFCausalClockFloorPureClockCharge (transport_charge)

variable (ε : ℝ) (hε : 0 < ε)

theorem graph_charge (h : ℝ) (hh : h ≠ 0) (θ : ℝ) (f g : Hilbert)
    (hfg : (f,g) ∈ (pureMomentum ε hε h).graph) :
    (action h hh θ f,action h hh θ g) ∈ (pureMomentum ε hε h).graph := by
  apply (momentum_graph_iff (pureGroup ε hε) h hh _ _).mpr
  have hd := (((action h hh θ : Hilbert →L[ℂ] Hilbert).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt 0
    ((momentum_graph_iff (pureGroup ε hε) h hh f g).mp hfg))
  change HasDerivAt (fun t : ℝ => action h hh θ (transport ε hε t f))
    (action h hh θ ((Complex.I/(h:ℂ)) • g)) 0 at hd
  change HasDerivAt (fun t : ℝ => transport ε hε t (action h hh θ f))
    ((Complex.I/(h:ℂ)) • action h hh θ g) 0
  simpa only [← transport_charge,map_smul] using hd

theorem graph_charge_iff (h : ℝ) (hh : h ≠ 0) (θ : ℝ) (f g : Hilbert) :
    (action h hh θ f,action h hh θ g) ∈ (pureMomentum ε hε h).graph ↔
      (f,g) ∈ (pureMomentum ε hε h).graph := by
  constructor
  · intro hfg
    simpa only [action_reverse] using graph_charge ε hε h hh (-θ) _ _ hfg
  · exact graph_charge ε hε h hh θ f g

theorem domain_charge_iff (h : ℝ) (hh : h ≠ 0) (θ : ℝ) (f : Hilbert) :
    action h hh θ f ∈ (pureMomentum ε hε h).domain ↔ f ∈ (pureMomentum ε hε h).domain := by
  constructor
  · intro hf
    obtain ⟨g,hg⟩ := LinearPMap.mem_domain_iff.mp hf
    have he := graph_charge ε hε h hh (-θ) _ _ hg
    rw [action_reverse] at he
    exact LinearPMap.mem_domain_of_mem_graph he
  · intro hf
    obtain ⟨g,hg⟩ := LinearPMap.mem_domain_iff.mp hf
    exact LinearPMap.mem_domain_of_mem_graph (graph_charge ε hε h hh θ f g hg)

theorem graph_output_norm (h : ℝ) (hh : h ≠ 0) (θ : ℝ) (f g q : Hilbert)
    (hg : (f,g) ∈ (pureMomentum ε hε h).graph)
    (hq : (action h hh θ f,q) ∈ (pureMomentum ε hε h).graph) : ‖q‖ = ‖g‖ := by
  have he := (pureMomentum ε hε h).mem_graph_snd_inj' hq (graph_charge ε hε h hh θ f g hg) rfl
  dsimp only at he
  rw [he,LinearIsometryEquiv.norm_map]

theorem characteristic_charge (h : ℝ) (hh : h ≠ 0) (r θ : ℝ) (f : Hilbert) :
    inner ℂ (action h hh θ f) (transport ε hε r (action h hh θ f)) =
      inner ℂ f (transport ε hε r f) := by
  rw [transport_charge,LinearIsometryEquiv.inner_map_map]

#print axioms graph_charge
#print axioms graph_charge_iff
#print axioms domain_charge_iff
#print axioms graph_output_norm
#print axioms characteristic_charge

end
end UnifiedTheory.Audit.KFCausalClockFloorPureClockChargeGraph
