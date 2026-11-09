/- Actual linear and quadratic ordered matter outputs of B on each
coherent state, with norm-continuous charge orbits. The T B reduction
derives the weighted domains without a higher-moment assumption. -/
import UnifiedTheory.Audit.KFCausalBoundedClockMatterGraphs

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 800000

namespace UnifiedTheory.Audit.KFCausalCoherentMomentumMatterOrbit
noncomputable section
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalEuclideanProductCoordinates (Joint)
open UnifiedTheory.Audit.KFCausalTransverseDilationFlow (Transverse)
open UnifiedTheory.Audit.KFCausalClockFloorCoherentStates (state)
open UnifiedTheory.Audit.KFCausalClockFloorCoherentUnitary (clockFrequency)
open UnifiedTheory.Audit.KFCausalClockFloorCoherentParameters (clockFrequency_parameter)
open UnifiedTheory.Audit.KFCausalChargeModulationFlow (parameter)
open UnifiedTheory.Audit.KFCausalClockFloorShiftedOutput (shift_bound)
open UnifiedTheory.Audit.KFCausalClockFloorCoherentMatterOrbit
open UnifiedTheory.Audit.KFCausalClockFloorCoherentShiftedOrbit (shiftedOutput_eq_scalarOutput)
open UnifiedTheory.Audit.KFCausalCoherentMomentumOutputReduction
open UnifiedTheory.Audit.KFCausalBoundedClockMatterGraphs
open UnifiedTheory.Audit.KFCausalCoherentVacuumCompositionOrbit (orderedMomentumOutput orderedMomentumOutput_graph)
open UnifiedTheory.Audit.KFCausalClockFloorPureClockMomentum (pureMomentum)
open UnifiedTheory.Audit.KFCausalClockFloorTrialMatter (matterFactor)
open UnifiedTheory.Audit.KFCausalPhysicalField (physicalField)
open UnifiedTheory.Audit.KFCausalTransverseFieldSquare (fieldSquare)
open UnifiedTheory.Audit.KFCausalOrderedOperatorComposition (composition_graph)

variable (ε a h : ℝ) (hε : 0 < ε) (ha : 0 < a) (hh : h ≠ 0) (hb : |h| ≤ 2*Real.pi*ε/3)

def linearMomentumOutput (k : Joint 2 4) (l : Transverse →L[ℝ] ℝ) : Hilbert :=
  reducedOutput ε a h hε ha hb (clockFrequency k)
    (linearOutput ε a h hε ha hh (-h/2) (shift_bound ε h hb) k l)
    (linearOutput ε (a/2) h hε (by positivity) hh (-h/2) (shift_bound ε h hb) k l)

def quadraticMomentumOutput (k : Joint 2 4) (l : Transverse →L[ℝ] ℝ) : Hilbert :=
  reducedOutput ε a h hε ha hb (clockFrequency k)
    (quadraticOutput ε a h hε ha hh (-h/2) (shift_bound ε h hb) k l)
    (quadraticOutput ε (a/2) h hε (by positivity) hh (-h/2) (shift_bound ε h hb) k l)

theorem linearMomentumOutput_field_graph (k : Joint 2 4) (l : Transverse →L[ℝ] ℝ) :
    (orderedMomentumOutput ε a h hε ha hh hb k,linearMomentumOutput ε a h hε ha hh hb k l) ∈
      (physicalField l).graph := by
  rw [orderedMomentumOutput_eq]
  apply reducedOutput_field_graph
  · rw [shiftedOutput_eq_scalarOutput]
    exact linearOutput_graph ε a h hε ha hh (-h/2) (shift_bound ε h hb) k l
  · rw [shiftedOutput_eq_scalarOutput]
    exact linearOutput_graph ε (a/2) h hε (by positivity) hh (-h/2) (shift_bound ε h hb) k l

theorem quadraticMomentumOutput_field_graph (k : Joint 2 4) (l : Transverse →L[ℝ] ℝ) :
    (orderedMomentumOutput ε a h hε ha hh hb k,quadraticMomentumOutput ε a h hε ha hh hb k l) ∈
      (fieldSquare l).graph := by
  rw [orderedMomentumOutput_eq]
  apply reducedOutput_square_graph
  · rw [shiftedOutput_eq_scalarOutput]
    exact quadraticOutput_graph ε a h hε ha hh (-h/2) (shift_bound ε h hb) k l
  · rw [shiftedOutput_eq_scalarOutput]
    exact quadraticOutput_graph ε (a/2) h hε (by positivity) hh (-h/2) (shift_bound ε h hb) k l

theorem linearMomentumOutput_matter_graph (k : Joint 2 4) (l : Transverse →L[ℝ] ℝ)
    (b : Hilbert) (hB : (state ε a h hε ha hh k,b) ∈ (pureMomentum ε hε h).graph) :
    (b,linearMomentumOutput ε a h hε ha hh hb k l) ∈ (matterFactor ε hε h (physicalField l)).graph :=
  (composition_graph _ _ _ _).mpr ⟨_,orderedMomentumOutput_graph ε a h hε ha hh hb k b hB,
    linearMomentumOutput_field_graph ε a h hε ha hh hb k l⟩

theorem quadraticMomentumOutput_matter_graph (k : Joint 2 4) (l : Transverse →L[ℝ] ℝ)
    (b : Hilbert) (hB : (state ε a h hε ha hh k,b) ∈ (pureMomentum ε hε h).graph) :
    (b,quadraticMomentumOutput ε a h hε ha hh hb k l) ∈ (matterFactor ε hε h (fieldSquare l)).graph :=
  (composition_graph _ _ _ _).mpr ⟨_,orderedMomentumOutput_graph ε a h hε ha hh hb k b hB,
    quadraticMomentumOutput_field_graph ε a h hε ha hh hb k l⟩

theorem linearMomentumOutput_orbit_continuous (k : Joint 2 4) (l : Transverse →L[ℝ] ℝ) :
    Continuous (fun θ => linearMomentumOutput ε a h hε ha hh hb (parameter θ k) l) := by
  unfold linearMomentumOutput
  simp_rw [clockFrequency_parameter]
  exact reducedOutput_continuous ε a h hε ha hb _ _ _
    (linearOutput_orbit_continuous ε a h hε ha hh (-h/2) (shift_bound ε h hb) k l)
    (linearOutput_orbit_continuous ε (a/2) h hε (by positivity) hh (-h/2) (shift_bound ε h hb) k l)

theorem quadraticMomentumOutput_orbit_continuous (k : Joint 2 4) (l : Transverse →L[ℝ] ℝ) :
    Continuous (fun θ => quadraticMomentumOutput ε a h hε ha hh hb (parameter θ k) l) := by
  unfold quadraticMomentumOutput
  simp_rw [clockFrequency_parameter]
  exact reducedOutput_continuous ε a h hε ha hb _ _ _
    (quadraticOutput_orbit_continuous ε a h hε ha hh (-h/2) (shift_bound ε h hb) k l)
    (quadraticOutput_orbit_continuous ε (a/2) h hε (by positivity) hh (-h/2) (shift_bound ε h hb) k l)

#print axioms linearMomentumOutput_field_graph
#print axioms quadraticMomentumOutput_field_graph
#print axioms linearMomentumOutput_matter_graph
#print axioms quadraticMomentumOutput_matter_graph
#print axioms linearMomentumOutput_orbit_continuous
#print axioms quadraticMomentumOutput_orbit_continuous
end
end UnifiedTheory.Audit.KFCausalCoherentMomentumMatterOrbit
