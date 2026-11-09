/- Actual boosted initial states in the reference completed energy form
used by the quantum propagator. Their evolved form trajectory retains the
proved initial energy and the existing energy-growth estimate. -/
import UnifiedTheory.Audit.KFCausalClockFloorDisplacedInitialEnergy
import UnifiedTheory.Audit.KFCausalClockFloorStrongFormEvolution

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1600000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalClockFloorDisplacedReferenceState
noncomputable section
open UnifiedTheory.Audit.KFCausalCoupledLongitudinalFlow (Configuration)
open UnifiedTheory.Audit.KFCausalClockFloorAveragedFormTransport
open UnifiedTheory.Audit.KFCausalClockFloorAveragedTimeControl
open UnifiedTheory.Audit.KFCausalClockFloorAveragedFormFlow (formFlow formFlow_physical_norm)
open UnifiedTheory.Audit.KFCausalClockFloorAveragedEvolution (evolution evolution_embedding)
open UnifiedTheory.Audit.KFCausalClockFloorStrongFormEvolution (formFlow_energy_bound formFlow_continuous)
open UnifiedTheory.Audit.KFCausalClockFloorAveragedHamiltonian (graphFormVector)
open UnifiedTheory.Audit.KFCausalClockFloorDisplacedAveragedDomain (averagedVector)
open UnifiedTheory.Audit.KFCausalClockFloorDisplacedBoostOrbit (state_boost)
open UnifiedTheory.Audit.KFCausalClockFloorDisplacedInitialEnergy (boostedEnergy)
open UnifiedTheory.Audit.KFCausalClockFloorBoostedKineticLimit (boostedState boostedState_norm)
open UnifiedTheory.Audit.KFCausalClockFloorEvolvedCharacteristics (positionFrequency)
open UnifiedTheory.Audit.KFCausalDisplacedBoostParameters (boostQ boostK)

variable (ε a h : ℝ) (hε : 0 < ε) (ha : 0 < a) (hh : h ≠ 0)
  (hb : |h| ≤ 2*Real.pi*ε/3) (m g κ s : ℝ) (p : Configuration)
local notation "V₀" => FormSpace ε hε h hh hb m g κ 0
local notation "J" => embedding ε hε h hh hb m g κ 0
local notation "E" => timeEnergy ε hε h hh hb m g κ

def referenceState : V₀ :=
  formTransfer ε hε h hh hb m g κ s 0
    (graphFormVector ε hε h hh hb m g κ s
      (averagedVector ε a h hε ha hh hb m g κ s (boostQ h (h⁻¹ • p)) (boostK (h⁻¹ • p)) rfl))

theorem referenceState_embedding :
    J (referenceState ε a h hε ha hh hb m g κ s p) =
      boostedState ε a h hε ha hh (positionFrequency p.1 p.2) := by
  rw [referenceState,transfer_embedding]
  exact state_boost ε a h hε ha hh p

theorem referenceState_energy :
    E s (referenceState ε a h hε ha hh hb m g κ s p) =
      boostedEnergy ε a h hε ha hh hb m g κ s p := by
  rw [← timeEnergy_actual,referenceState,transfer_inverse]
  rfl

theorem referenceState_norm : ‖J (referenceState ε a h hε ha hh hb m g κ s p)‖ = 1 := by
  rw [referenceState_embedding]
  exact boostedState_norm ε a h hε ha hh _

def trajectory (t : ℝ) : V₀ := formFlow ε hε h hh hb m g κ s t (referenceState ε a h hε ha hh hb m g κ s p)

theorem trajectory_embedding (t : ℝ) :
    J (trajectory ε a h hε ha hh hb m g κ s p t) =
      evolution ε hε h hh hb m g κ s t (boostedState ε a h hε ha hh (positionFrequency p.1 p.2)) := by
  rw [← referenceState_embedding ε a h hε ha hh hb m g κ s p,evolution_embedding]
  rfl

theorem trajectory_norm (t : ℝ) : ‖J (trajectory ε a h hε ha hh hb m g κ s p t)‖ = 1 :=
  (formFlow_physical_norm ε hε h hh hb m g κ s t _).trans (referenceState_norm ε a h hε ha hh hb m g κ s p)

theorem trajectory_energy_bound (t : ℝ) :
    E t (trajectory ε a h hε ha hh hb m g κ s p t) ≤
      Real.exp (2*|t-s|)*boostedEnergy ε a h hε ha hh hb m g κ s p := by
  simpa only [referenceState_energy] using
    formFlow_energy_bound ε hε h hh hb m g κ s t (referenceState ε a h hε ha hh hb m g κ s p)

theorem trajectory_continuous : Continuous (trajectory ε a h hε ha hh hb m g κ s p) :=
  formFlow_continuous ε hε h hh hb m g κ s _

#print axioms referenceState_embedding
#print axioms referenceState_energy
#print axioms referenceState_norm
#print axioms trajectory_embedding
#print axioms trajectory_norm
#print axioms trajectory_energy_bound
#print axioms trajectory_continuous

end
end UnifiedTheory.Audit.KFCausalClockFloorDisplacedReferenceState
