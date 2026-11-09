/- Actual drift-operator pairings for each boosted ordered output.
These are exact identities before taking the semiclassical limit. -/
import UnifiedTheory.Audit.KFCausalClockFloorDriftCoordinates
import UnifiedTheory.Audit.KFCausalClockFloorDisplacedFieldIntegral
import UnifiedTheory.Audit.KFCausalClockFloorInitialDriftSeed

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1800000

namespace UnifiedTheory.Audit.KFCausalClockFloorDisplacedDriftIntegral
noncomputable section
open MeasureTheory
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalCoupledLongitudinalFlow (Configuration)
open UnifiedTheory.Audit.KFCausalEuclideanProductCoordinates (Joint)
open UnifiedTheory.Audit.KFCausalTransverseDilationFlow (Transverse)
open UnifiedTheory.Audit.KFCausalClockFloorRecenteredFields
open UnifiedTheory.Audit.KFCausalClockFloorDisplacedEnergyIntegral (rawLine gaussianMass_scale)
open UnifiedTheory.Audit.KFCausalClockFloorDisplacedLineDensity (recenter boostedLine)
open UnifiedTheory.Audit.KFCausalClockFloorDisplacedPhaseLimit (rescaledPosition)
open UnifiedTheory.Audit.KFCausalClockFloorRecenteredJacobian
open UnifiedTheory.Audit.KFCausalClockFloorCoherentMatterOrbit
  (pulledField pulledField_continuous linear_base_memLp quadratic_base_memLp)
open UnifiedTheory.Audit.KFCausalClockFloorSourcedMultiplierContinuity
open UnifiedTheory.Audit.KFCausalClockFloorFieldMoments (fieldLine)
open UnifiedTheory.Audit.KFCausalClockFloorTrialMatter (fieldLine_grouping)
open UnifiedTheory.Audit.KFCausalClockFloorGroupedCoordinates
open UnifiedTheory.Audit.KFCausalClockFloorUnitaryCoordinates (coordinates)
open UnifiedTheory.Audit.KFCausalClockFloorShearBounds (Grouped)
open UnifiedTheory.Audit.KFCausalClockFloorDisplacedSources (amplitude source clockFrequency)
open UnifiedTheory.Audit.KFCausalClockFloorInvariantTrial
  (trialState neutralWidth neutralWidth_positive neutralWidth_bound)
open UnifiedTheory.Audit.KFCausalChargeGaussianGeometry (groundWidth groundWidth_positive)
open UnifiedTheory.Audit.KFCausalClockFloorShiftedOutput (shift_bound)
open UnifiedTheory.Audit.KFCausalClockFloorTrialEnergyNorms (clockMass trial_norm_square)
open UnifiedTheory.Audit.KFCausalPhysicalGaussianNormalization (gaussianMass)
open UnifiedTheory.Audit.KFCausalClockFloorBoostedRescaling (scale scale_positive)
open UnifiedTheory.Audit.KFCausalClassicalChargePhase (physicalTail)
open UnifiedTheory.Audit.KFCausalChargeModulationFlow (parameter)
open UnifiedTheory.Audit.KFCausalDisplacedBoostParameters (boostQ boostK)
open UnifiedTheory.Audit.KFCausalPhysicalEnergyFactors (modelDirections)

open UnifiedTheory.Audit.KFCausalClockFloorDisplacedFieldIntegral
open UnifiedTheory.Audit.KFCausalClockFloorDisplacedEnergyIntegral
open UnifiedTheory.Audit.KFCausalClockFloorDriftCoordinates
open UnifiedTheory.Audit.KFCausalClockFloorDefectTransportOperator (driftOperator)
open UnifiedTheory.Audit.KFCausalClockFloorInitialDriftPairing (pairing_real_smul)
open UnifiedTheory.Audit.KFCausalClockFloorInitialDriftSeed (pairing_complex_smul)

def driftPair (ε : ℝ) (hε : 0 < ε) (f : Hilbert) : ℝ :=
  (inner ℂ f (driftOperator ε hε f)).re

theorem sourcedField_pairing (ε a h : ℝ) (hε : 0 < ε) (ha : 0 < a) (hh : h ≠ 0)
    (hb : |h| ≤ 2*Real.pi*ε/3) (q k : Joint 2 4) (l : Transverse →L[ℝ] ℝ) (j : Fin 2) :
    driftPair ε hε (KFCausalClockFloorSourcedCommonDomain.factorOutput ε a (groundWidth h) (neutralWidth h)
      hε ha (groundWidth_positive h hh) (neutralWidth_positive h hh) (neutralWidth_bound h)
      (amplitude h q k) (clockFrequency h k) (source h q k) h hb modelDirections l (fieldIndex j)) =
        ∫ z, realDrift ε hε z.1*‖weightedLine ε a h hε q k l j z‖^2 := by
  have he : KFCausalClockFloorSourcedCommonDomain.factorOutput ε a (groundWidth h) (neutralWidth h)
      hε ha (groundWidth_positive h hh) (neutralWidth_positive h hh) (neutralWidth_bound h)
      (amplitude h q k) (clockFrequency h k) (source h q k) h hb modelDirections l (fieldIndex j) =
    outputState ε a (groundWidth h) (neutralWidth h) (-h/2) hε ha
      (groundWidth_positive h hh) (neutralWidth_positive h hh) (neutralWidth_bound h) (shift_bound ε h hb)
      (fieldMultiplier ε hε l j) (fieldMultiplier_measurable ε hε l j) (fieldBase ε a h hε ha hh hb l j)
      (amplitude h q k) (clockFrequency h k) (source h q k) := by
    fin_cases j
    · unfold fieldMultiplier
      simp only [zero_add,pow_one]
      exact (KFCausalClockFloorSourcedFieldContinuity.linearOutput_eq ε a h hε ha hh hb
        (amplitude h q k) (clockFrequency h k) (source h q k) l).symm
    · exact (KFCausalClockFloorSourcedFieldContinuity.quadraticOutput_eq ε a h hε ha hh hb _ _ _ l).symm
  rw [he,driftPair,outputState,coordinates_toLp_pairing]
  simp_rw [weightedLine_grouping]
  exact grouping_preserves_volume.integral_comp grouping.measurableEmbedding
    (fun z => realDrift ε hε z.1*‖weightedLine ε a h hε q k l j z‖^2)

theorem sourcedExponential_pairing (ε a h : ℝ) (hε : 0 < ε) (ha : 0 < a) (hh : h ≠ 0)
    (hb : |h| ≤ 2*Real.pi*ε/3) (q k : Joint 2 4) :
    driftPair ε hε (KFCausalClockFloorSourcedSpectral.shiftedOutput ε a (groundWidth h) (neutralWidth h)
      hε ha (groundWidth_positive h hh) (neutralWidth_positive h hh) (neutralWidth_bound h)
      (amplitude h q k) (clockFrequency h k) (source h q k) h hb) =
        ∫ z, realDrift ε hε z.1*‖rawLine ε a h q k z‖^2 := by
  rw [driftPair,KFCausalClockFloorSourcedSpectral.shiftedOutput,pairing_complex_smul,
    KFCausalClockFloorCoherentSpectral.gaussianState,coordinates_toLp_pairing]
  rw [← integral_const_mul]
  calc
    _ = ∫ x : Configuration, realDrift ε hε (grouping x).1*‖rawLine ε a h q k (grouping x)‖^2 := by
      apply integral_congr_ae
      filter_upwards [] with x
      simp only [rawLine,norm_mul,mul_pow,KFCausalClockFloorCoherentSpectral.configurationLine]
      change _ = realDrift ε hε x.1*_
      ring
    _ = _ := grouping_preserves_volume.integral_comp grouping.measurableEmbedding
      (fun z => realDrift ε hε z.1*‖rawLine ε a h q k z‖^2)

theorem rawLine_memLp (ε a h : ℝ) (hε : 0 < ε) (ha : 0 < a) (hh : h ≠ 0)
    (hb : |h| ≤ 2*Real.pi*ε/3) (q k : Joint 2 4) : MemLp (rawLine ε a h q k) 2 :=
  (KFCausalClockFloorCoherentStrip.line_memLp ε a (groundWidth h) (neutralWidth h) (clockFrequency h k)
    (source h q k) (-h/2) hε ha (groundWidth_positive h hh)
    (neutralWidth_positive h hh) (neutralWidth_bound h) (shift_bound ε h hb)).const_mul (amplitude h q k)

theorem exponentialOutput_pairing (ε a h : ℝ) (hε : 0 < ε) (ha : 0 < a) (hh : h ≠ 0)
    (hb : |h| ≤ 2*Real.pi*ε/3) (q k : Joint 2 4) :
    driftPair ε hε (exponentialOutput ε a h hε ha hh hb q k) =
      (∫ u : ℝ, realDrift ε hε u*clockJacobian ε hε u*∫ ξ : Transverse,
        ‖rawLine ε a h q k (u,recenter ε hε u h
          (physicalTail (KFCausalDisplacedPhysicalPhase.phase h q k).1) ξ)‖^2) /
            (clockMass ε a*gaussianMass (groundWidth 1) (neutralWidth 1)) := by
  change (inner ℂ ((‖trialState ε a h hε ha hh‖⁻¹ : ℝ) • _)
    (driftOperator ε hε ((‖trialState ε a h hε ha hh‖⁻¹ : ℝ) • _))).re = _
  rw [pairing_real_smul,inv_pow,← div_eq_inv_mul,trial_norm_square]
  change driftPair ε hε (KFCausalClockFloorSourcedSpectral.shiftedOutput ε a (groundWidth h) (neutralWidth h)
    hε ha (groundWidth_positive h hh) (neutralWidth_positive h hh) (neutralWidth_bound h)
    (amplitude h q k) (clockFrequency h k) (source h q k) h hb) / _ = _
  rw [sourcedExponential_pairing ε a h hε ha hh hb q k]
  rw [recentered_drift_integral ε h hε hh _ _ (rawLine_memLp ε a h hε ha hh hb q k),gaussianMass_scale h hh]
  rw [mul_left_comm (clockMass ε a) ((scale h)^5)]
  exact mul_div_mul_left _ _ (pow_ne_zero 5 (scale_positive h hh).ne')

theorem fieldOutput_pairing (ε a h : ℝ) (hε : 0 < ε) (ha : 0 < a) (hh : h ≠ 0)
    (hb : |h| ≤ 2*Real.pi*ε/3) (q k : Joint 2 4) (l : Transverse →L[ℝ] ℝ) (j : Fin 2) :
    driftPair ε hε (fieldOutput ε a h hε ha hh hb q k l j) =
      (∫ u : ℝ, realDrift ε hε u*clockJacobian ε hε u*∫ ξ : Transverse,
        (fieldPower j l (rescaledPosition h (physicalTail (KFCausalDisplacedPhysicalPhase.phase h q k).1) ξ))^2*
          ‖rawLine ε a h q k (u,recenter ε hε u h
            (physicalTail (KFCausalDisplacedPhysicalPhase.phase h q k).1) ξ)‖^2) /
              (clockMass ε a*gaussianMass (groundWidth 1) (neutralWidth 1)) := by
  unfold driftPair fieldOutput KFCausalClockFloorDisplacedCommonDomain.factorOutput
  rw [pairing_real_smul,inv_pow,← div_eq_inv_mul,trial_norm_square]
  rw [show (inner ℂ _ (driftOperator ε hε _)).re = _ from
    sourcedField_pairing ε a h hε ha hh hb q k l j]
  rw [recentered_drift_integral ε h hε hh _ _ (weightedLine_memLp ε a h hε ha hh hb q k l j)]
  simp_rw [weightedLine_recenter_square]
  rw [gaussianMass_scale h hh,mul_left_comm (clockMass ε a) ((scale h)^5)]
  exact mul_div_mul_left _ _ (pow_ne_zero 5 (scale_positive h hh).ne')

theorem boostedOutput_pairing (ε a h : ℝ) (hε : 0 < ε) (ha : 0 < a) (hh : h ≠ 0)
    (hb : |h| ≤ 2*Real.pi*ε/3) (p : Configuration) (θ : ℝ) :
    driftPair ε hε (boostedOutput ε a h hε ha hh hb p θ) =
      (∫ u : ℝ, realDrift ε hε u*clockJacobian ε hε u*
        ∫ ξ : Transverse, ‖boostedLine ε a hε u h p θ ξ‖^2) /
          (clockMass ε a*gaussianMass (groundWidth 1) (neutralWidth 1)) :=
  exponentialOutput_pairing ε a h hε ha hh hb _ _

theorem boostedFieldOutput_pairing (ε a h : ℝ) (hε : 0 < ε) (ha : 0 < a) (hh : h ≠ 0)
    (hb : |h| ≤ 2*Real.pi*ε/3) (p : Configuration) (θ : ℝ) (l : Transverse →L[ℝ] ℝ) (j : Fin 2) :
    driftPair ε hε (boostedFieldOutput ε a h hε ha hh hb p θ l j) =
      (∫ u : ℝ, realDrift ε hε u*clockJacobian ε hε u*∫ ξ : Transverse,
        (fieldPower j l (rescaledPosition h (orbitCentre p θ) ξ))^2 * ‖boostedLine ε a hε u h p θ ξ‖^2) /
          (clockMass ε a*gaussianMass (groundWidth 1) (neutralWidth 1)) := by
  rw [boostedFieldOutput,fieldOutput_pairing]
  unfold boostedLine rawLine
  dsimp only
  simp_rw [KFCausalDisplacedPhysicalPhase.phase_boost_orbit h hh]
  rfl

#print axioms sourcedField_pairing
#print axioms sourcedExponential_pairing
#print axioms rawLine_memLp
#print axioms exponentialOutput_pairing
#print axioms fieldOutput_pairing
#print axioms boostedOutput_pairing
#print axioms boostedFieldOutput_pairing

end
end UnifiedTheory.Audit.KFCausalClockFloorDisplacedDriftIntegral
