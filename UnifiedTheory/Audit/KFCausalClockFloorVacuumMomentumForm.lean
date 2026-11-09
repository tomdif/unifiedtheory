/- The positive weak longitudinal-momentum response extends uniquely
from the constructed common-composition core to the full ordered vacuum
form domain. No full averaged-Hamiltonian momentum law is asserted. -/
import UnifiedTheory.Audit.KFCausalClockFloorOrderedMomentumCore
import UnifiedTheory.Audit.KFCausalClockFloorVacuumMomentumResponse
import UnifiedTheory.Audit.KFCausalClockFloorVacuumOutputFaithful

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1200000

namespace UnifiedTheory.Audit.KFCausalClockFloorVacuumMomentumForm
noncomputable section
open Filter
open scoped Topology
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalClockFloorLongitudinalMomentum (longitudinalMomentum)
open UnifiedTheory.Audit.KFCausalClockFloorTrialSpectralDomain (orderedExponential)
open UnifiedTheory.Audit.KFCausalClockFloorOrderedMomentumCommutator
open UnifiedTheory.Audit.KFCausalClockFloorOrderedMomentumCore
open UnifiedTheory.Audit.KFCausalClockFloorVacuumMomentumResponse

variable (ε : ℝ) (hε : 0 < ε) (h : ℝ) (hh : |h| ≤ 2*Real.pi*ε/3)
local notation "L" => longitudinalMomentum ε hε h
local notation "T" => orderedExponential ε hε h
local notation "𝒦" => regularGraph ε hε h

def inputMomentum (z : 𝒦) : Hilbert := (L) ⟨z.val.1,z.property.2.1⟩
def outputMomentum (z : 𝒦) : Hilbert := (L) ⟨z.val.2,z.property.2.2⟩
def orderedMomentum (z : 𝒦) : Hilbert := outputMomentum ε hε h z-correction ε hε h hh z.val.2
def weakRate (z : 𝒦) : ℝ := (-2/h)*(inner ℂ z.val.2 (orderedMomentum ε hε h hh z)).im
def graphResponse (z : Hilbert × Hilbert) : ℝ := response ε hε h hh z.2

theorem orderedMomentum_graph (hne : h ≠ 0) (z : 𝒦) :
    (inputMomentum ε hε h z,orderedMomentum ε hε h hh z) ∈ (T).graph :=
  momentum_ordered_graph ε hε h hne hh z.val.1 (inputMomentum ε hε h z) z.val.2
    (outputMomentum ε hε h z) ((L).mem_graph ⟨z.val.1,z.property.2.1⟩)
      z.property.1 ((L).mem_graph ⟨z.val.2,z.property.2.2⟩)

theorem weakRate_eq (hne : h ≠ 0) (z : 𝒦) : weakRate ε hε h hh z = graphResponse ε hε h hh z.val :=
  weak_momentum_response ε hε h hh hne z.val.1 (inputMomentum ε hε h z) z.val.2
    (orderedMomentum ε hε h hh z) ((L).mem_graph ⟨z.val.1,z.property.2.1⟩)
      z.property.1 (orderedMomentum_graph ε hε h hh hne z)

theorem graphResponse_continuous : Continuous (graphResponse ε hε h hh) :=
  (response_continuous ε hε h hh).comp continuous_snd

theorem graphResponse_positive (f tf : Hilbert) (hf : (f,tf) ∈ (T).graph) (hn : f ≠ 0) :
    0 < graphResponse ε hε h hh (f,tf) := by
  apply response_positive ε hε h hh tf
  intro ht
  rw [ht] at hf
  exact hn (KFCausalClockFloorVacuumOutputFaithful.ordered_graph_zero ε hε h f hf)

theorem core_rate_approximation (hne : h ≠ 0) (f tf : Hilbert) (hf : (f,tf) ∈ (T).graph) :
    ∃ z : ℕ → 𝒦,
      Tendsto (fun n => (z n).val) atTop (𝓝 (f,tf)) ∧
        Tendsto (fun n => weakRate ε hε h hh (z n)) atTop (𝓝 (graphResponse ε hε h hh (f,tf))) := by
  obtain ⟨w,hw,ht⟩ := graph_approximation ε hε h hne hh f tf hf
  let z : ℕ → 𝒦 := fun n => ⟨w n,hw n⟩
  refine ⟨z,ht,?_⟩
  have hc := (graphResponse_continuous ε hε h hh).continuousAt.tendsto.comp ht
  exact hc.congr' (Filter.Eventually.of_forall (fun n => (weakRate_eq ε hε h hh hne (z n)).symm))

theorem extension_unique (hne : h ≠ 0) (F : Hilbert × Hilbert → ℝ)
    (hF : ContinuousOn F ((T).graph : Set (Hilbert × Hilbert)))
    (hagree : ∀ z : 𝒦, F z.val = weakRate ε hε h hh z) :
    ∀ z ∈ (T).graph, F z = graphResponse ε hε h hh z := by
  rintro ⟨f,tf⟩ hf
  obtain ⟨z,hz,hr⟩ := core_rate_approximation ε hε h hh hne f tf hf
  have ht : Tendsto (fun n => (z n).val) atTop (𝓝[((T).graph : Set (Hilbert × Hilbert))] (f,tf)) :=
    tendsto_nhdsWithin_iff.mpr ⟨hz,Filter.Eventually.of_forall (fun n => (z n).property.1)⟩
  have hl := (hF (f,tf) hf).tendsto.comp ht
  exact tendsto_nhds_unique hl (hr.congr' (Filter.Eventually.of_forall (fun n => (hagree (z n)).symm)))

#print axioms orderedMomentum_graph
#print axioms weakRate_eq
#print axioms graphResponse_continuous
#print axioms graphResponse_positive
#print axioms core_rate_approximation
#print axioms extension_unique
end
end UnifiedTheory.Audit.KFCausalClockFloorVacuumMomentumForm
