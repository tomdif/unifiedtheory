/- The actual zero-charge projection preserves the full pure-clock
momentum graph. Closed-graph integration justifies the unbounded operator
interchange; no finite-packet membership of the projected state is assumed. -/
import UnifiedTheory.Audit.KFCausalClockFloorPureClockChargeGraph
import UnifiedTheory.Audit.KFCausalClosedOperatorUnitaryCommutation
import UnifiedTheory.Audit.KFCausalStandingChargeOperator

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 800000

namespace UnifiedTheory.Audit.KFCausalPureClockZeroProjection
noncomputable section
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalClockFloorPureClockMomentum (pureMomentum pure_selfAdjoint)
open UnifiedTheory.Audit.KFCausalPhysicalCircleAction (group action)
open UnifiedTheory.Audit.KFCausalStandingChargeOperator (zeroProjection zeroProjection_fixes zeroSector)
open UnifiedTheory.Audit.KFCausalClockFloorPureClockChargeGraph (graph_charge)

variable (ε : ℝ) (hε : 0 < ε) (h : ℝ) (hh : h ≠ 0)
local notation "B" => pureMomentum ε hε h
local notation "P" => zeroProjection h hh

theorem projected_graph (f b : Hilbert) (hB : (f,b) ∈ (B).graph) :
    (P f,P b) ∈ (B).graph :=
  KFCausalClosedOperatorUnitaryCommutation.average_graph (group h hh) B
    (pure_selfAdjoint ε hε h hh).isClosed (graph_charge ε hε h hh) f b hB (2*Real.pi)

theorem complementary_graph (f b : Hilbert) (hB : (f,b) ∈ (B).graph) :
    (f-P f,b-P b) ∈ (B).graph := (B).graph.sub_mem hB (projected_graph ε hε h hh f b hB)

theorem output_zeroSector (f b : Hilbert) (hB : (f,b) ∈ (B).graph) (hf : f ∈ zeroSector h hh) :
    b ∈ zeroSector h hh := by
  have hg := projected_graph ε hε h hh f b hB
  rw [zeroProjection_fixes h hh f hf] at hg
  have he : P b = b := (B).mem_graph_snd_inj' hg hB rfl
  rw [← he]
  exact KFCausalStandingChargeOperator.zeroProjection_mem h hh b

#print axioms projected_graph
#print axioms complementary_graph
#print axioms output_zeroSector
end
end UnifiedTheory.Audit.KFCausalPureClockZeroProjection
