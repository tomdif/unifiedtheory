/- Threshold monotonicity for the bounded localized spectral observation,
including its complete physical charge orbit. -/
import UnifiedTheory.Audit.KFCausalClockFloorLocalizedSpectralSplit

set_option Elab.async false
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1200000

namespace UnifiedTheory.Audit.KFCausalClockFloorSpectralThresholds
noncomputable section
open MeasureTheory
open KFCausalConfigurationTestSpace (Hilbert)
open KFCausalClockFloorLocalizedSpectrum (observation orbitObservation)
open KFCausalClockFloorWeightedClockControl (weighted)
open KFCausalClockFloorFourierCoordinates (coupledFourier)
open KFCausalClockFloorFourierMultiplier (symbol)
open KFCausalClockFloorExponential (symbol_measurable)
open KFCausalClockFloorOrbitVacuumGraph (physicalOrbit physicalOrbit_coe)
open KFCausalUnitIntervalOrbit (angleMeasure)

variable (ε : ℝ) (hε : 0 < ε) (h : ℝ)

theorem upper_antitone (R S : ℝ) (hRS : R ≤ S) (f : Hilbert) :
    ‖observation ε hε h S f‖^2 ≤ ‖observation ε hε h R f‖^2 := by
  rw [KFCausalClockFloorLocalizedSpectrum.observation_norm_square,
    KFCausalClockFloorLocalizedSpectrum.observation_norm_square]
  unfold KFCausalClockFloorLongitudinalTails.positiveTail
  apply setIntegral_mono_set
    ((memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable
      (coupledFourier ε hε (weighted ε hε f)))).mp (Lp.memLp _)).integrableOn
    (Filter.Eventually.of_forall (fun _ => sq_nonneg _))
  exact Filter.Eventually.of_forall (fun p hp => hRS.trans hp)

theorem orbit_antitone (hne : h ≠ 0) (R S : ℝ) (hRS : R ≤ S) (f : Hilbert) :
    ‖orbitObservation ε hε h hne S f‖^2 ≤ ‖orbitObservation ε hε h hne R f‖^2 := by
  rw [KFCausalAveragedEnergyGraph.l2_norm_square,KFCausalAveragedEnergyGraph.l2_norm_square]
  apply integral_mono_ae
    ((memLp_two_iff_integrable_sq_norm
      (Lp.aestronglyMeasurable (orbitObservation ε hε h hne S f))).mp (Lp.memLp _))
    ((memLp_two_iff_integrable_sq_norm
      (Lp.aestronglyMeasurable (orbitObservation ε hε h hne R f))).mp (Lp.memLp _))
  filter_upwards [(observation ε hε h S).coeFn_compLp (physicalOrbit h hne f),
    (observation ε hε h R).coeFn_compLp (physicalOrbit h hne f)] with θ hS hR
  change ‖(observation ε hε h S).compLp (physicalOrbit h hne f) θ‖^2 ≤
    ‖(observation ε hε h R).compLp (physicalOrbit h hne f) θ‖^2
  rw [hS,hR]
  exact upper_antitone ε hε h R S hRS _

#print axioms upper_antitone
#print axioms orbit_antitone
end
end UnifiedTheory.Audit.KFCausalClockFloorSpectralThresholds
