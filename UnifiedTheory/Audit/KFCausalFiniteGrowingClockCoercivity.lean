/- The original finite sourced family satisfies the mixed clock/growing
form requirement by its actual clock-output Hamiltonian graph. Thus the
clock term cannot cancel the growing Hamiltonian output on this family.
The two static kinetic rows remain outside this estimate. -/
import UnifiedTheory.Audit.KFCausalClockFloorGrowingClockAccretivity
import UnifiedTheory.Audit.KFCausalFiniteGrowingHamiltonianOutput
import UnifiedTheory.Audit.KFCausalClockWeightedOriginalHamiltonian

set_option Elab.async false
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalFiniteGrowingClockCoercivity
noncomputable section
open KFCausalConfigurationTestSpace (Hilbert)
open KFCausalFinitePotentialHamiltonianDomain (hamiltonian_strip)
open KFCausalFiniteGrowingHamiltonianOutput (growingOutput growing_domain growing_graph)

variable (n : ℕ) (ε h : ℝ) (a w p : Fin n → ℝ) (C b : Fin n → ℂ)
  (P : Fin n → Polynomial ℂ) (hε : 0 < ε) (ha : ∀ i, 0 < a i)
  (hh : h ≠ 0) (hw : ∀ i, 1 ≤ w i) (hb : |h| ≤ ε/10)
  (mass2 quartic vacuum : ℝ)
local notation "hs" => hamiltonian_strip ε h hε hb
local notation "ψ" => KFCausalReciprocalNeutralSuperposition.state n ε h a w p C b P hε ha hh hw
local notation "cψ" => KFCausalClockWeightedOriginalHamiltonian.state ε h hε hh hb n a w p C b P ha hw false
local notation "gψ" => growingOutput n ε h a w p C b P hε ha hh hw hb mass2 quartic vacuum
local notation "G" => KFCausalClockFloorGrowingHamiltonian.hamiltonian ε hε h hh hs mass2 quartic vacuum
local notation "GD" => KFCausalClockFloorGrowingHamiltonian.formData ε hε h hh hs mass2 quartic vacuum
local notation "GJ" => KFCausalClosedGraphForm.embedding GD

private def statePoint : (G).domain :=
  ⟨ψ,growing_domain n ε h a w p C b P hε ha hh hw hb mass2 quartic vacuum⟩

private theorem statePoint_output :
    G (statePoint n ε h a w p C b P hε ha hh hw hb mass2 quartic vacuum)=gψ := by
  exact (G).mem_graph_snd_inj'
    ((G).mem_graph (statePoint n ε h a w p C b P hε ha hh hw hb mass2 quartic vacuum))
    (growing_graph n ε h a w p C b P hε ha hh hw hb mass2 quartic vacuum) rfl

def clockFormVector : KFCausalClockFloorGrowingHamiltonian.GrowingForm ε hε h hh hs mass2 quartic vacuum :=
  KFCausalClockFloorGrowingHamiltonian.referenceLift ε hε h hh hs mass2 quartic vacuum
    (KFCausalClockFloorAveragedHamiltonianBridge.referenceLift ε hε h hh hs mass2 quartic vacuum 0
      ⟨cψ,LinearPMap.mem_domain_of_mem_graph
        (KFCausalClockWeightedOriginalHamiltonian.hamiltonian_graph
          ε h hε hh hb n a w p C b P ha hw false mass2 quartic vacuum 0 hs)⟩)

theorem clockFormVector_embedding :
    GJ (clockFormVector n ε h a w p C b P hε ha hh hw hb mass2 quartic vacuum)=cψ := by
  unfold clockFormVector
  rw [KFCausalClockFloorGrowingHamiltonian.referenceLift_embedding,
    KFCausalClockFloorAveragedHamiltonianBridge.embedding_referenceLift]

theorem clock_growing_pairing_nonnegative : 0 ≤ (inner ℂ gψ cψ).re := by
  have hc : (ψ,GJ (clockFormVector n ε h a w p C b P hε ha hh hw hb mass2 quartic vacuum)) ∈
      (KFCausalClockFloorClockOperator.clockOperator ε hε).graph := by
    rw [clockFormVector_embedding]
    exact KFCausalClockWeightedOriginalHamiltonian.clock_graph ε h hε hh hb n a w p C b P ha hw
  have hp := KFCausalClockFloorGrowingClockAccretivity.clock_form_accretive
    ε hε h hh hs mass2 quartic vacuum
    (statePoint n ε h a w p C b P hε ha hh hw hb mass2 quartic vacuum)
    (clockFormVector n ε h a w p C b P hε ha hh hw hb mass2 quartic vacuum) hc
  simpa only [statePoint_output,clockFormVector_embedding] using hp

theorem clock_growing_norm_bound (r : ℝ) (hr : 0 ≤ r) :
    ‖gψ‖ ≤ ‖gψ+r • cψ‖ := by
  have hc : (ψ,GJ (clockFormVector n ε h a w p C b P hε ha hh hw hb mass2 quartic vacuum)) ∈
      (KFCausalClockFloorClockOperator.clockOperator ε hε).graph := by
    rw [clockFormVector_embedding]
    exact KFCausalClockWeightedOriginalHamiltonian.clock_graph ε h hε hh hb n a w p C b P ha hw
  have hp := KFCausalClockFloorGrowingClockAccretivity.clock_growing_norm_bound
    ε hε h hh hs mass2 quartic vacuum
    (statePoint n ε h a w p C b P hε ha hh hw hb mass2 quartic vacuum)
    (clockFormVector n ε h a w p C b P hε ha hh hw hb mass2 quartic vacuum) hc r hr
  simpa only [statePoint_output,clockFormVector_embedding] using hp

#print axioms clockFormVector_embedding
#print axioms clock_growing_pairing_nonnegative
#print axioms clock_growing_norm_bound
end
end UnifiedTheory.Audit.KFCausalFiniteGrowingClockCoercivity
