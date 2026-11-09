/- Every canonical momentum boost is an actual member of the normalized
displacement family. Its whole physical charge orbit is identified, with
no assumption that the charge circle preserves the pure-boost slice. -/
import UnifiedTheory.Audit.KFCausalDisplacedBoostParameters

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1200000

namespace UnifiedTheory.Audit.KFCausalClockFloorDisplacedBoostOrbit
noncomputable section
open UnifiedTheory.Audit.KFCausalCoupledLongitudinalFlow (Configuration)
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalEuclideanProductCoordinates (Joint)
open UnifiedTheory.Audit.KFCausalPairedRotation
open UnifiedTheory.Audit.KFCausalNormalizedChargeFlow
open UnifiedTheory.Audit.KFCausalChargeModulationFlow
open UnifiedTheory.Audit.KFCausalClockFloorDisplacedStates
open UnifiedTheory.Audit.KFCausalDisplacedPairedCoordinates
open UnifiedTheory.Audit.KFCausalDisplacedBoostParameters
open UnifiedTheory.Audit.KFCausalPhysicalMomentumModulation (modulation)
open UnifiedTheory.Audit.KFCausalClockFloorEvolvedCharacteristics (positionFrequency)
open UnifiedTheory.Audit.KFCausalClockFloorInvariantTrial (trialState)
open UnifiedTheory.Audit.KFCausalClockFloorSemiclassicalStates (unitTrial)
open UnifiedTheory.Audit.KFCausalClockFloorBoostedKineticLimit (boostedState)
open UnifiedTheory.Audit.KFCausalClockFloorBoostedSpectral (positionFrequency_smul)

theorem rawState_boost (ε a h : ℝ) (hε : 0 < ε) (ha : 0 < a) (hh : h ≠ 0) (p : Configuration) :
    rawState ε a h hε ha hh (boostQ h p) (boostK p) =
      modulation (positionFrequency p.1 p.2) (trialState ε a h hε ha hh) := by
  rw [rawState_packetState,packetState_boost h hh]
  rfl

theorem state_boost (ε a h : ℝ) (hε : 0 < ε) (ha : 0 < a) (hh : h ≠ 0) (p : Configuration) :
    state ε a h hε ha hh (boostQ h (h⁻¹ • p)) (boostK (h⁻¹ • p)) =
      boostedState ε a h hε ha hh (positionFrequency p.1 p.2) := by
  rw [state_normalization,rawState_boost,positionFrequency_smul]
  exact ((modulation (h⁻¹ • positionFrequency p.1 p.2) : Hilbert →L[ℂ] Hilbert).map_smul_of_tower
    (‖trialState ε a h hε ha hh‖⁻¹ : ℝ) (trialState ε a h hε ha hh)).symm

theorem action_boostedState (ε a h : ℝ) (hε : 0 < ε) (ha : 0 < a) (hh : h ≠ 0)
    (p : Configuration) (θ : ℝ) :
    KFCausalPhysicalCircleAction.action h hh θ
      (boostedState ε a h hε ha hh (positionFrequency p.1 p.2)) =
      state ε a h hε ha hh (parameter θ (boostQ h (h⁻¹ • p))) (parameter θ (boostK (h⁻¹ • p))) := by
  rw [← state_boost ε a h hε ha hh,action_state]

theorem parameter_clock (θ : ℝ) (q : Joint 2 4) : (parameter θ q) (.inr 0) = q (.inr 0) := rfl

theorem parameter_neutral (θ : ℝ) (q : Joint 2 4) : (parameter θ q) (.inr 3) = q (.inr 3) := rfl

theorem boost_orbit_clock_displacement (h : ℝ) (p : Configuration) (θ : ℝ) :
    (parameter θ (boostQ h (h⁻¹ • p))) (.inr 0) = 0 := rfl

theorem boost_orbit_neutral_displacement (h : ℝ) (p : Configuration) (θ : ℝ) :
    (parameter θ (boostQ h (h⁻¹ • p))) (.inr 3) = 0 := rfl

theorem boost_orbit_first_displacement (h : ℝ) (hh : h ≠ 0) (p : Configuration) (θ : ℝ) :
    (parameter θ (boostQ h (h⁻¹ • p))) (.inr 1) =
      Real.sin θ*KFCausalPairedModeCoordinates.scale*(p.2 0-p.2 1) := by
  simp only [parameter,rotate,boostQ,antisymmetricFrequency,momentumScale,
    Real.sin_neg,Real.cos_neg]
  dsimp
  field_simp
  ring

theorem boost_orbit_second_displacement (h : ℝ) (hh : h ≠ 0) (p : Configuration) (θ : ℝ) :
    (parameter θ (boostQ h (h⁻¹ • p))) (.inr 2) =
      Real.sin θ*KFCausalPairedModeCoordinates.scale*(p.2 2-p.2 3) := by
  simp only [parameter,rotate,boostQ,antisymmetricFrequency,momentumScale,
    Real.sin_neg,Real.cos_neg]
  dsimp
  field_simp
  ring

#print axioms rawState_boost
#print axioms state_boost
#print axioms action_boostedState
#print axioms parameter_clock
#print axioms parameter_neutral
#print axioms boost_orbit_clock_displacement
#print axioms boost_orbit_neutral_displacement
#print axioms boost_orbit_first_displacement
#print axioms boost_orbit_second_displacement

end
end UnifiedTheory.Audit.KFCausalClockFloorDisplacedBoostOrbit
