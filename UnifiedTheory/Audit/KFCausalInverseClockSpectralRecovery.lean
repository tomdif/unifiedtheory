/- The bounded inverse half-clock is injective. Consequently an exact
second output D z identifies the unbounded spectral endpoint z inside
an already proved natural reverse graph. -/
import UnifiedTheory.Audit.KFCausalClockFloorVacuumSquare
import UnifiedTheory.Audit.KFCausalClockFloorMatterClosure

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

namespace UnifiedTheory.Audit.KFCausalInverseClockSpectralRecovery
noncomputable section
open KFCausalConfigurationTestSpace (Hilbert)
open KFCausalClockFloorBoundedInverse (inverseL inverseL_graph)
open KFCausalClockFloorClockHalf (clockHalf half_inverse_graph)
open KFCausalClockFloorExponential (longitudinalExponential)
open KFCausalClockFloorTrialSpectralDomain (reversedExponential)
open KFCausalClockFloorMatterClosure (reversedMatterFactor)
open KFCausalOrderedOperatorComposition (composition_graph)

theorem inverseL_injective (ε : ℝ) (hε : 0 < ε) : Function.Injective (inverseL ε hε) := by
  intro f g he
  have hf := (half_inverse_graph ε hε _ _).mpr ((inverseL_graph ε hε f _).mpr rfl)
  have hg := (half_inverse_graph ε hε _ _).mpr ((inverseL_graph ε hε g _).mpr rfl)
  exact (clockHalf ε).mem_graph_snd_inj' hf hg he

theorem exponential_graph_of_reversed (ε : ℝ) (hε : 0 < ε) (h : ℝ) (u z : Hilbert)
    (hu : (u,inverseL ε hε z) ∈ (reversedExponential ε hε h).graph) :
    (u,z) ∈ (longitudinalExponential ε hε h (1/2)).graph := by
  obtain ⟨v,hv,he⟩ := (KFCausalClockFloorVacuumSquare.reversed_graph ε hε h _ _).mp hu
  have hz : v = z := inverseL_injective ε hε he.symm
  simpa only [hz] using hv

theorem matter_exponential_graph (ε : ℝ) (hε : 0 < ε) (h : ℝ)
    (T : Hilbert →ₗ.[ℂ] Hilbert) (u v z : Hilbert)
    (hv : (u,v) ∈ T.graph)
    (hz : (u,inverseL ε hε z) ∈ (reversedMatterFactor ε hε h T).graph) :
    (v,z) ∈ (longitudinalExponential ε hε h (1/2)).graph := by
  obtain ⟨w,hw,hr⟩ := (composition_graph _ _ _ _).mp hz
  have he : w = v := T.mem_graph_snd_inj' hw hv rfl
  rw [he] at hr
  exact exponential_graph_of_reversed ε hε h v z hr

#print axioms inverseL_injective
#print axioms exponential_graph_of_reversed
#print axioms matter_exponential_graph
end
end UnifiedTheory.Audit.KFCausalInverseClockSpectralRecovery
