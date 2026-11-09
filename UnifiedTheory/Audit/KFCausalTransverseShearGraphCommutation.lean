/- Strongly commuting clock and shear flows preserve their full maximal
momentum graphs. Bounded clock weights also preserve the shear graph. -/
import UnifiedTheory.Audit.KFCausalTransverseShearMomentum
import UnifiedTheory.Audit.KFCausalTransverseShearClockCommutation
import UnifiedTheory.Audit.KFCausalClockFloorPureClockMomentum

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

namespace UnifiedTheory.Audit.KFCausalTransverseShearGraphCommutation
noncomputable section
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalTransverseShearTransport
open UnifiedTheory.Audit.KFCausalTransverseShearMomentum
open UnifiedTheory.Audit.KFCausalTransverseShearClockCommutation
open UnifiedTheory.Audit.KFCausalClockFloorPureClockMomentum (pureGroup pureMomentum)
open UnifiedTheory.Audit.KFCausalClockFloorLongitudinalMomentum (coupledGroup longitudinalMomentum)
open UnifiedTheory.Audit.KFCausalStrongUnitaryProductDerivative (graph_of_commutes)

variable (ε : ℝ) (hε : 0 < ε) (h : ℝ) (hh : h ≠ 0)
include hh

theorem pure_graph_shear (t : ℝ) (f g : Hilbert)
    (hfg : (f,g) ∈ (pureMomentum ε hε h).graph) :
    (transport t f,transport t g) ∈ (pureMomentum ε hε h).graph :=
  graph_of_commutes (pureGroup ε hε) h hh (transport t)
    (fun u x => (pure_transport ε hε t u x).symm) f g hfg

theorem coupled_graph_shear (t : ℝ) (f g : Hilbert)
    (hfg : (f,g) ∈ (longitudinalMomentum ε hε h).graph) :
    (transport t f,transport t g) ∈ (longitudinalMomentum ε hε h).graph :=
  graph_of_commutes (coupledGroup ε hε) h hh (transport t)
    (fun u x => (coupled_transport ε hε t u x).symm) f g hfg

theorem pure_graph_shear_iff (t : ℝ) (f g : Hilbert) :
    (transport t f,transport t g) ∈ (pureMomentum ε hε h).graph ↔
      (f,g) ∈ (pureMomentum ε hε h).graph := by
  constructor
  · intro hfg
    simpa only [transport_reverse] using pure_graph_shear ε hε h hh (-t) _ _ hfg
  · exact pure_graph_shear ε hε h hh t f g

theorem coupled_graph_shear_iff (t : ℝ) (f g : Hilbert) :
    (transport t f,transport t g) ∈ (longitudinalMomentum ε hε h).graph ↔
      (f,g) ∈ (longitudinalMomentum ε hε h).graph := by
  constructor
  · intro hfg
    simpa only [transport_reverse] using coupled_graph_shear ε hε h hh (-t) _ _ hfg
  · exact coupled_graph_shear ε hε h hh t f g

theorem shear_graph_pure (t : ℝ) (f g : Hilbert)
    (hfg : (f,g) ∈ (shearMomentum h).graph) :
    (KFCausalClockFloorPureClockTransport.transport ε hε t f,
      KFCausalClockFloorPureClockTransport.transport ε hε t g) ∈ (shearMomentum h).graph :=
  graph_of_commutes shearGroup h hh (KFCausalClockFloorPureClockTransport.transport ε hε t)
    (fun u x => pure_transport ε hε u t x) f g hfg

theorem shear_graph_coupled (t : ℝ) (f g : Hilbert)
    (hfg : (f,g) ∈ (shearMomentum h).graph) :
    (KFCausalClockFloorUnitaryTransport.transport ε hε t f,
      KFCausalClockFloorUnitaryTransport.transport ε hε t g) ∈ (shearMomentum h).graph :=
  graph_of_commutes shearGroup h hh (KFCausalClockFloorUnitaryTransport.transport ε hε t)
    (fun u x => coupled_transport ε hε u t x) f g hfg

theorem shear_graph_pure_iff (t : ℝ) (f g : Hilbert) :
    (KFCausalClockFloorPureClockTransport.transport ε hε t f,
      KFCausalClockFloorPureClockTransport.transport ε hε t g) ∈ (shearMomentum h).graph ↔
      (f,g) ∈ (shearMomentum h).graph := by
  constructor
  · intro hfg
    simpa only [KFCausalClockFloorPureClockTransport.transport_reverse] using
      shear_graph_pure ε hε h hh (-t) _ _ hfg
  · exact shear_graph_pure ε hε h hh t f g

theorem shear_graph_coupled_iff (t : ℝ) (f g : Hilbert) :
    (KFCausalClockFloorUnitaryTransport.transport ε hε t f,
      KFCausalClockFloorUnitaryTransport.transport ε hε t g) ∈ (shearMomentum h).graph ↔
      (f,g) ∈ (shearMomentum h).graph := by
  constructor
  · intro hfg
    simpa only [KFCausalClockFloorUnitaryTransport.transport_reverse] using
      shear_graph_coupled ε hε h hh (-t) _ _ hfg
  · exact shear_graph_coupled ε hε h hh t f g

theorem defect_shear_graph (f g : Hilbert) (hfg : (f,g) ∈ (shearMomentum h).graph) :
    (KFCausalClockFloorDefectOperator.defectOperator ε hε f,
      KFCausalClockFloorDefectOperator.defectOperator ε hε g) ∈ (shearMomentum h).graph :=
  graph_of_commutes shearGroup h hh (KFCausalClockFloorDefectOperator.defectOperator ε hε)
    (defect_commutes ε hε) f g hfg

theorem inverse_half_shear_graph (f g : Hilbert) (hfg : (f,g) ∈ (shearMomentum h).graph) :
    (KFCausalClockFloorBoundedInverse.inverseL ε hε f,
      KFCausalClockFloorBoundedInverse.inverseL ε hε g) ∈ (shearMomentum h).graph :=
  graph_of_commutes shearGroup h hh (KFCausalClockFloorBoundedInverse.inverseL ε hε)
    (inverse_half_commutes ε hε) f g hfg

#print axioms pure_graph_shear
#print axioms coupled_graph_shear
#print axioms pure_graph_shear_iff
#print axioms coupled_graph_shear_iff
#print axioms shear_graph_pure
#print axioms shear_graph_coupled
#print axioms shear_graph_pure_iff
#print axioms shear_graph_coupled_iff
#print axioms defect_shear_graph
#print axioms inverse_half_shear_graph
end
end UnifiedTheory.Audit.KFCausalTransverseShearGraphCommutation
