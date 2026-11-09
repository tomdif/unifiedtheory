/- Pure-clock transport preserves the full physical field graphs.
The resulting momentum compositions and graph cores use actual closed
operators; no field-domain regularity is postulated. -/
import UnifiedTheory.Audit.KFCausalClockFloorPureClockMomentum
import UnifiedTheory.Audit.KFCausalClosedOperatorUnitaryCommutation
import UnifiedTheory.Audit.KFCausalPhysicalField

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 800000

namespace UnifiedTheory.Audit.KFCausalClockFloorPureClockFields
noncomputable section
open MeasureTheory
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalTransverseDilationFlow (Transverse)
open UnifiedTheory.Audit.KFCausalPhysicalField
open UnifiedTheory.Audit.KFCausalTransverseFieldSquare
open UnifiedTheory.Audit.KFCausalClockFloorPureClockTransport
open UnifiedTheory.Audit.KFCausalClockFloorPureClockMomentum
open UnifiedTheory.Audit.KFCausalClosedOperatorUnitaryCommutation

variable (ε : ℝ) (hε : 0 < ε) (l : Transverse →L[ℝ] ℝ)

theorem field_transport (t : ℝ) (f g : Hilbert) (hg : (f,g) ∈ (physicalField l).graph) :
    (transport ε hε t f,transport ε hε t g) ∈ (physicalField l).graph := by
  apply (physicalField_graph l _ _).mpr
  filter_upwards [transport_coe ε hε t f,transport_coe ε hε t g,
    (flow_quasiMeasurePreserving ε hε t).ae ((physicalField_graph l f g).mp hg)] with x hf ht hx
  rw [hf,ht]
  dsimp only [transportFunction]
  rw [hx]
  dsimp only [pureFlow]
  ring

theorem square_transport (t : ℝ) (f g : Hilbert) (hg : (f,g) ∈ (fieldSquare l).graph) :
    (transport ε hε t f,transport ε hε t g) ∈ (fieldSquare l).graph := by
  apply (fieldSquare_graph l _ _).mpr
  filter_upwards [transport_coe ε hε t f,transport_coe ε hε t g,
    (flow_quasiMeasurePreserving ε hε t).ae ((fieldSquare_graph l f g).mp hg)] with x hf ht hx
  rw [hf,ht]
  dsimp only [transportFunction]
  rw [hx]
  dsimp only [pureFlow]
  ring

theorem field_interchange (h : ℝ) (hh : h ≠ 0) (f g b k : Hilbert)
    (hg : (f,g) ∈ (physicalField l).graph) (hb : (f,b) ∈ (pureMomentum ε hε h).graph) :
    (b,k) ∈ (physicalField l).graph ↔ (g,k) ∈ (pureMomentum ε hε h).graph :=
  graph_interchange (pureGroup ε hε) (physicalField l) (physicalField_closed l)
    (field_transport ε hε l) h hh f g b k hg hb

theorem square_interchange (h : ℝ) (hh : h ≠ 0) (f g b k : Hilbert)
    (hg : (f,g) ∈ (fieldSquare l).graph) (hb : (f,b) ∈ (pureMomentum ε hε h).graph) :
    (b,k) ∈ (fieldSquare l).graph ↔ (g,k) ∈ (pureMomentum ε hε h).graph :=
  graph_interchange (pureGroup ε hε) (fieldSquare l) (fieldSquare_selfAdjoint l).isClosed
    (square_transport ε hε l) h hh f g b k hg hb

theorem field_core (h : ℝ) :
    (regularGraph (pureGroup ε hε) (physicalField l) h).topologicalClosure = (physicalField l).graph :=
  regular_graph_core (pureGroup ε hε) (physicalField l) (physicalField_closed l) (field_transport ε hε l) h

theorem square_core (h : ℝ) :
    (regularGraph (pureGroup ε hε) (fieldSquare l) h).topologicalClosure = (fieldSquare l).graph :=
  regular_graph_core (pureGroup ε hε) (fieldSquare l) (fieldSquare_selfAdjoint l).isClosed
    (square_transport ε hε l) h

#print axioms field_transport
#print axioms square_transport
#print axioms field_interchange
#print axioms square_interchange
#print axioms field_core
#print axioms square_core
end
end UnifiedTheory.Audit.KFCausalClockFloorPureClockFields
