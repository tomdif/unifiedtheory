/- Actual clock-half and every transverse kinetic output of B applied to
an original coherent state. Their charge orbits are norm continuous. -/
import UnifiedTheory.Audit.KFCausalOriginalPureClockOutput
import UnifiedTheory.Audit.KFCausalClockFloorPureClockChargeGraph

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 800000

namespace UnifiedTheory.Audit.KFCausalCoherentMomentumFactorOrbit
noncomputable section
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalEuclideanProductCoordinates (Joint)
open UnifiedTheory.Audit.KFCausalTransverseDilationFlow (Transverse)
open UnifiedTheory.Audit.KFCausalClockFloorCoherentStates (state action_state)
open UnifiedTheory.Audit.KFCausalClockFloorCoherentUnitary (clockFrequency)
open UnifiedTheory.Audit.KFCausalClockFloorCoherentParameters (clockFrequency_parameter)
open UnifiedTheory.Audit.KFCausalChargeModulationFlow (parameter)
open UnifiedTheory.Audit.KFCausalPhysicalCircleAction (action)
open UnifiedTheory.Audit.KFCausalPureClockOutputMultipliers
open UnifiedTheory.Audit.KFCausalClockFloorCoherentOrbitContinuity
  (clockOutput clockOutput_graph clockOutput_orbit_continuous)
open UnifiedTheory.Audit.KFCausalClockFloorCoherentClockMomentum (momentumOutput state_clockMomentum_graph)
open UnifiedTheory.Audit.KFCausalClockFloorCoherentMomentumOrbit (momentumOutput_orbit_continuous)
open UnifiedTheory.Audit.KFCausalClockFloorPureClockMomentum (pureMomentum)
open UnifiedTheory.Audit.KFCausalClockFloorClockHalf (clockHalf)
open UnifiedTheory.Audit.KFCausalClockFloorTrialMomentum (clockMomentum)

variable (ε a h : ℝ) (hε : 0 < ε) (ha : 0 < a) (hh : h ≠ 0)
local notation "B" => pureMomentum ε hε h

def pureOutput (k : Joint 2 4) : Hilbert :=
  outputMap ε a h hε ha (clockFrequency k)
    (state ε a h hε ha hh k) (state ε (a/2) h hε (by positivity) hh k)

theorem pureOutput_graph (k : Joint 2 4) :
    (state ε a h hε ha hh k,pureOutput ε a h hε ha hh k) ∈ (B).graph := by
  unfold pureOutput
  rw [KFCausalCoherentShearDomain.state_eq_toLp ε a h hε ha hh k,
    KFCausalCoherentShearDomain.state_eq_toLp ε (a/2) h hε (by positivity) hh k]
  exact KFCausalOriginalPureClockOutput.profile_graph ε a hε ha _ _ _ _
    (KFCausalChargeGaussianGeometry.groundWidth_positive h hh)
    (KFCausalClockFloorInvariantTrial.neutralWidth_positive h hh)
    (KFCausalClockFloorInvariantTrial.neutralWidth_bound h) _ h hh

theorem pureOutput_action (θ : ℝ) (k : Joint 2 4) :
    pureOutput ε a h hε ha hh (parameter θ k) = action h hh θ (pureOutput ε a h hε ha hh k) := by
  have hg := KFCausalClockFloorPureClockChargeGraph.graph_charge ε hε h hh θ _ _
    (pureOutput_graph ε a h hε ha hh k)
  rw [action_state] at hg
  exact (B).mem_graph_snd_inj' (pureOutput_graph ε a h hε ha hh _) hg rfl

def clockMomentumOutput (k : Joint 2 4) : Hilbert :=
  outputMap ε a h hε ha (clockFrequency k)
    (clockOutput ε a h hε ha hh k) (clockOutput ε (a/2) h hε (by positivity) hh k)

def kineticMomentumOutput (k : Joint 2 4) (v : Transverse) : Hilbert :=
  outputMap ε a h hε ha (clockFrequency k)
    (momentumOutput ε a h hε ha hh k v) (momentumOutput ε (a/2) h hε (by positivity) hh k v)

theorem clockMomentumOutput_graph (k : Joint 2 4) :
    (pureOutput ε a h hε ha hh k,clockMomentumOutput ε a h hε ha hh k) ∈ (clockHalf ε).graph :=
  outputMap_half_graph ε a h hε ha _ _ _ _ _ (clockOutput_graph ε a h hε ha hh k)
    (clockOutput_graph ε (a/2) h hε (by positivity) hh k)

theorem kineticMomentumOutput_graph (k : Joint 2 4) (v : Transverse) :
    (pureOutput ε a h hε ha hh k,kineticMomentumOutput ε a h hε ha hh k v) ∈
      (clockMomentum ε h v).graph :=
  outputMap_kinetic_graph ε a h hε ha hh v _ _ _ _ _ (state_clockMomentum_graph ε a h hε ha hh k v)
    (state_clockMomentum_graph ε (a/2) h hε (by positivity) hh k v)

theorem clockMomentumOutput_orbit_continuous (k : Joint 2 4) :
    Continuous (fun θ => clockMomentumOutput ε a h hε ha hh (parameter θ k)) := by
  unfold clockMomentumOutput
  simp_rw [clockFrequency_parameter]
  exact outputMap_continuous ε a h hε ha _ _ _
    (clockOutput_orbit_continuous ε a h hε ha hh k)
    (clockOutput_orbit_continuous ε (a/2) h hε (by positivity) hh k)

theorem kineticMomentumOutput_orbit_continuous (k : Joint 2 4) (v : Transverse) :
    Continuous (fun θ => kineticMomentumOutput ε a h hε ha hh (parameter θ k) v) := by
  unfold kineticMomentumOutput
  simp_rw [clockFrequency_parameter]
  exact outputMap_continuous ε a h hε ha _ _ _
    (momentumOutput_orbit_continuous ε a h hε ha hh k v)
    (momentumOutput_orbit_continuous ε (a/2) h hε (by positivity) hh k v)

theorem clockMomentumOutput_action_graph (θ : ℝ) (k : Joint 2 4) :
    (action h hh θ (pureOutput ε a h hε ha hh k),
      clockMomentumOutput ε a h hε ha hh (parameter θ k)) ∈ (clockHalf ε).graph := by
  rw [← pureOutput_action]
  exact clockMomentumOutput_graph ε a h hε ha hh _

theorem kineticMomentumOutput_action_graph (θ : ℝ) (k : Joint 2 4) (v : Transverse) :
    (action h hh θ (pureOutput ε a h hε ha hh k),
      kineticMomentumOutput ε a h hε ha hh (parameter θ k) v) ∈ (clockMomentum ε h v).graph := by
  rw [← pureOutput_action]
  exact kineticMomentumOutput_graph ε a h hε ha hh _ v

#print axioms pureOutput_graph
#print axioms pureOutput_action
#print axioms clockMomentumOutput_graph
#print axioms kineticMomentumOutput_graph
#print axioms clockMomentumOutput_orbit_continuous
#print axioms kineticMomentumOutput_orbit_continuous
#print axioms clockMomentumOutput_action_graph
#print axioms kineticMomentumOutput_action_graph
end
end UnifiedTheory.Audit.KFCausalCoherentMomentumFactorOrbit
