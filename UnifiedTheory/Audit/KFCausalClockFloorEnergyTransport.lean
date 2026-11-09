/- The clock-floor model's full weighted joint graph and its closure
transport exactly between Hamiltonian times. This acts on the whole
operator graph, without assuming that a trial family is a form core. -/
import UnifiedTheory.Audit.KFCausalPhysicalEnergyTransport
import UnifiedTheory.Audit.KFCausalClockFloorJointEnergy

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 800000

namespace UnifiedTheory.Audit.KFCausalClockFloorEnergyTransport
noncomputable section
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalTransverseDilationFlow (Transverse)
open UnifiedTheory.Audit.KFCausalFiniteJointGraph (Output)
open UnifiedTheory.Audit.KFCausalJointGraphRescaling
open UnifiedTheory.Audit.KFCausalPhysicalEnergyTransport (timeOutput weight_transition)
open UnifiedTheory.Audit.KFCausalClockFloorJointEnergy
open UnifiedTheory.Audit.KFCausalClockFloorMatterClosure (energyFactor_closable)

variable (ε : ℝ) (hε : 0 < ε) (hbar : ℝ)
  (v : Fin 4 → Transverse) (l : Transverse →L[ℝ] ℝ) (mass2 quartic vacuum s t : ℝ)

theorem initialEnergy_graph_transport (z : Hilbert × Output (Fin 8) Hilbert)
    (hz : z ∈ (initialEnergy ε hε hbar v l mass2 quartic vacuum s).graph) :
    (z.1,timeOutput s t z.2) ∈ (initialEnergy ε hε hbar v l mass2 quartic vacuum t).graph :=
  initial_graph_rescale _ _ _ _ (weight_transition mass2 quartic vacuum s t) z hz

theorem initialEnergy_domain_independent :
    (initialEnergy ε hε hbar v l mass2 quartic vacuum s).domain =
      (initialEnergy ε hε hbar v l mass2 quartic vacuum t).domain :=
  initial_domain_eq _ _ _ _ _ (weight_transition mass2 quartic vacuum s t)
    (weight_transition mass2 quartic vacuum t s)

theorem closedEnergy_graph_transport (hh : |hbar| ≤ Real.pi*ε)
    (z : Hilbert × Output (Fin 8) Hilbert)
    (hz : z ∈ (closedEnergy ε hε hbar v l mass2 quartic vacuum s).graph) :
    (z.1,timeOutput s t z.2) ∈ (closedEnergy ε hε hbar v l mass2 quartic vacuum t).graph :=
  closed_graph_rescale _ _ _ _ (energyFactor_closable ε hbar hε hh v l)
    (weight_transition mass2 quartic vacuum s t) z hz

theorem common_form_domain (hh : |hbar| ≤ Real.pi*ε) :
    (closedEnergy ε hε hbar v l mass2 quartic vacuum s).domain =
      (closedEnergy ε hε hbar v l mass2 quartic vacuum t).domain :=
  closed_domain_eq _ _ _ _ _ (energyFactor_closable ε hbar hε hh v l)
    (weight_transition mass2 quartic vacuum s t) (weight_transition mass2 quartic vacuum t s)

#print axioms initialEnergy_graph_transport
#print axioms initialEnergy_domain_independent
#print axioms closedEnergy_graph_transport
#print axioms common_form_domain

end
end UnifiedTheory.Audit.KFCausalClockFloorEnergyTransport
