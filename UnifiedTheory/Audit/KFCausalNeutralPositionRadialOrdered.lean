/- The actual radial test preserves the ordered clock exponential graph,
including the inverse-clock factor in its prescribed order. All input
domain identities are derived from the natural clock and exponential graphs. -/
import UnifiedTheory.Audit.KFCausalNeutralPositionRadialExponential
import UnifiedTheory.Audit.KFCausalNeutralPositionRadialKinetics

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 400000

namespace UnifiedTheory.Audit.KFCausalNeutralPositionRadialOrdered
noncomputable section
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalClockFloorClockHalf (inverseClockHalf half_inverse_graph)
open UnifiedTheory.Audit.KFCausalClockFloorExponential (longitudinalExponential)
open UnifiedTheory.Audit.KFCausalClockFloorTrialSpectralDomain (orderedExponential)
open UnifiedTheory.Audit.KFCausalOrderedOperatorComposition (composition_graph)
open UnifiedTheory.Audit.KFCausalNeutralPositionRadialCutoff (action)
open UnifiedTheory.Audit.KFCausalNeutralPositionRadialExponential (shifted exponential_graph_action)
open UnifiedTheory.Audit.KFCausalClockFloorShiftedDefect (shift_bound)

variable (ε h δ v : ℝ) (hε : 0 < ε) (hδ : 0 < δ)

include hε in
theorem inverseHalf_graph_action (f g : Hilbert) (hfg : (f,g) ∈ (inverseClockHalf ε).graph) :
    (action h δ v hδ f,action h δ v hδ g) ∈ (inverseClockHalf ε).graph :=
  (half_inverse_graph ε hε _ _).mp
    (KFCausalNeutralPositionRadialKinetics.clock_graph ε hε h δ v hδ g f
      ((half_inverse_graph ε hε g f).mpr hfg))

variable (hh : |h| ≤ 2*Real.pi*ε/3)

theorem ordered_graph_action (f g : Hilbert) (hfg : (f,g) ∈ (orderedExponential ε hε h).graph) :
    (action h δ v hδ f,shifted ε h δ v hε hδ (-h/2) (shift_bound ε h hh) g) ∈
      (orderedExponential ε hε h).graph := by
  rw [orderedExponential,composition_graph] at hfg ⊢
  obtain ⟨u,hu,hg⟩ := hfg
  exact ⟨action h δ v hδ u,inverseHalf_graph_action ε h δ v hε hδ f u hu,
    exponential_graph_action ε h δ v hε hδ hh u g hg⟩

include hh in
theorem exponential_domain_action (f : Hilbert)
    (hf : f ∈ (longitudinalExponential ε hε h (1/2)).domain) :
    action h δ v hδ f ∈ (longitudinalExponential ε hε h (1/2)).domain :=
  LinearPMap.mem_domain_of_mem_graph (exponential_graph_action ε h δ v hε hδ hh f _
    ((longitudinalExponential ε hε h (1/2)).mem_graph ⟨f,hf⟩))

include hh in
theorem ordered_domain_action (f : Hilbert) (hf : f ∈ (orderedExponential ε hε h).domain) :
    action h δ v hδ f ∈ (orderedExponential ε hε h).domain :=
  LinearPMap.mem_domain_of_mem_graph (ordered_graph_action ε h δ v hε hδ hh f _
    ((orderedExponential ε hε h).mem_graph ⟨f,hf⟩))

#print axioms inverseHalf_graph_action
#print axioms ordered_graph_action
#print axioms exponential_domain_action
#print axioms ordered_domain_action

end
end UnifiedTheory.Audit.KFCausalNeutralPositionRadialOrdered
