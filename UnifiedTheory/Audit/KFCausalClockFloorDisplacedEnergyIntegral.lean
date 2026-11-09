/- The actual normalized ordered exponential energy equals its recentered
integral. The concentration Jacobian cancels the trial Gaussian mass exactly;
the real clock Jacobian remains. These identities precede passage to a limit. -/
import UnifiedTheory.Audit.KFCausalClockFloorRecenteredJacobian
import UnifiedTheory.Audit.KFCausalClockFloorDisplacedCommonDomain

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1800000

namespace UnifiedTheory.Audit.KFCausalClockFloorDisplacedEnergyIntegral
noncomputable section
open MeasureTheory
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalTransverseDilationFlow (Transverse)
open UnifiedTheory.Audit.KFCausalCoupledLongitudinalFlow (Configuration)
open UnifiedTheory.Audit.KFCausalEuclideanProductCoordinates (Joint)
open UnifiedTheory.Audit.KFCausalClassicalChargePhase (physicalTail)
open UnifiedTheory.Audit.KFCausalClockFloorDisplacedLineDensity
open UnifiedTheory.Audit.KFCausalClockFloorRecenteredJacobian
open UnifiedTheory.Audit.KFCausalClockFloorDisplacedSources (amplitude source clockFrequency)
open UnifiedTheory.Audit.KFCausalClockFloorCoherentStrip (line line_memLp)
open UnifiedTheory.Audit.KFCausalClockFloorBoostedRescaling
  (scale scale_positive scale_groundWidth scale_neutralWidth)
open UnifiedTheory.Audit.KFCausalClockFloorInvariantTrial
  (neutralWidth neutralWidth_positive neutralWidth_bound trialState)
open UnifiedTheory.Audit.KFCausalChargeGaussianGeometry (groundWidth groundWidth_positive)
open UnifiedTheory.Audit.KFCausalClockFloorTrialEnergyNorms (clockMass trial_norm_square)
open UnifiedTheory.Audit.KFCausalPhysicalGaussianNormalization (gaussianMass)
open UnifiedTheory.Audit.KFCausalClockFloorShiftedOutput (shift_bound)
open UnifiedTheory.Audit.KFCausalChargeModulationFlow (parameter)
open UnifiedTheory.Audit.KFCausalDisplacedBoostParameters (boostQ boostK)
open UnifiedTheory.Audit.KFCausalPhysicalEnergyFactors (modelDirections)
open UnifiedTheory.Audit.KFCausalMatterOrderedDomain (pointField)

def rawLine (ε a h : ℝ) (q k : Joint 2 4) (z : ℝ × KFCausalClockFloorShearBounds.Grouped) : ℂ :=
  amplitude h q k * line ε a (groundWidth h) (neutralWidth h)
    (clockFrequency h k) (source h q k) (-h/2) z

def recenteredMass (ε a : ℝ) (hε : 0 < ε) (h : ℝ) (q k : Joint 2 4) : ℝ :=
  ∫ u : ℝ, clockJacobian ε hε u * ∫ ξ : Transverse,
    ‖rawLine ε a h q k
      (u,recenter ε hε u h (physicalTail (KFCausalDisplacedPhysicalPhase.phase h q k).1) ξ)‖^2

theorem rawLine_mass (ε a h : ℝ) (hε : 0 < ε) (ha : 0 < a)
    (hh : h ≠ 0) (hb : |h| ≤ 2*Real.pi*ε/3) (q k : Joint 2 4) :
    (∫ z, ‖rawLine ε a h q k z‖^2) = (scale h)^5*recenteredMass ε a hε h q k := by
  have hm := (line_memLp ε a (groundWidth h) (neutralWidth h) (clockFrequency h k)
    (source h q k) (-h/2) hε ha (groundWidth_positive h hh)
    (neutralWidth_positive h hh) (neutralWidth_bound h) (shift_bound ε h hb)).const_mul (amplitude h q k)
  have hi := (memLp_two_iff_integrable_sq_norm hm.1).mp hm
  change Integrable (fun z => ‖rawLine ε a h q k z‖^2) at hi
  rw [Measure.volume_eq_prod ℝ KFCausalClockFloorShearBounds.Grouped] at hi ⊢
  rw [integral_prod _ hi,recenteredMass,← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with u
  rw [recenter_integral ε hε u h hh (physicalTail (KFCausalDisplacedPhysicalPhase.phase h q k).1)]
  ring

theorem gaussianMass_scale (h : ℝ) (hh : h ≠ 0) :
    gaussianMass (groundWidth h) (neutralWidth h) =
      (scale h)^5*gaussianMass (groundWidth 1) (neutralWidth 1) := by
  have he := KFCausalClockFloorGaussianRescaling.gaussianMass_smul
    (groundWidth h) (neutralWidth h) (scale h) (groundWidth_positive h hh)
    (neutralWidth_positive h hh) (scale_positive h hh)
  rw [scale_groundWidth h hh,scale_neutralWidth h hh] at he
  rw [he,mul_inv_cancel_left₀ (pow_ne_zero 5 (scale_positive h hh).ne')]

def exponentialOutput (ε a h : ℝ) (hε : 0 < ε) (ha : 0 < a)
    (hh : h ≠ 0) (hb : |h| ≤ 2*Real.pi*ε/3) (q k : Joint 2 4) : Hilbert :=
  KFCausalClockFloorDisplacedCommonDomain.factorOutput ε a h hε ha hh hb q k modelDirections pointField 7

theorem exponentialOutput_mass (ε a h : ℝ) (hε : 0 < ε) (ha : 0 < a)
    (hh : h ≠ 0) (hb : |h| ≤ 2*Real.pi*ε/3) (q k : Joint 2 4) :
    ‖exponentialOutput ε a h hε ha hh hb q k‖^2 =
      recenteredMass ε a hε h q k /
        (clockMass ε a*gaussianMass (groundWidth 1) (neutralWidth 1)) := by
  change ‖(‖trialState ε a h hε ha hh‖⁻¹ : ℝ) •
    KFCausalClockFloorSourcedSpectral.shiftedOutput ε a (groundWidth h) (neutralWidth h)
      hε ha (groundWidth_positive h hh) (neutralWidth_positive h hh) (neutralWidth_bound h)
      (amplitude h q k) (clockFrequency h k) (source h q k) h hb‖^2 = _
  rw [norm_smul,mul_pow,Real.norm_eq_abs,abs_inv,abs_of_nonneg (norm_nonneg _),
    inv_pow,← div_eq_inv_mul,trial_norm_square]
  have he : ‖KFCausalClockFloorSourcedSpectral.shiftedOutput ε a (groundWidth h) (neutralWidth h)
      hε ha (groundWidth_positive h hh) (neutralWidth_positive h hh) (neutralWidth_bound h)
      (amplitude h q k) (clockFrequency h k) (source h q k) h hb‖^2 =
      ∫ z, ‖rawLine ε a h q k z‖^2 := by
    simp only [KFCausalClockFloorSourcedSpectral.shiftedOutput,norm_smul,mul_pow,
      KFCausalClockFloorBoostedExponentialBound.gaussianState_mass,rawLine,norm_mul,integral_const_mul]
  rw [he,rawLine_mass ε a h hε ha hh hb q k,gaussianMass_scale h hh]
  rw [mul_left_comm (clockMass ε a) ((scale h)^5)]
  exact mul_div_mul_left _ _ (pow_ne_zero 5 (scale_positive h hh).ne')

def boostedOutput (ε a h : ℝ) (hε : 0 < ε) (ha : 0 < a)
    (hh : h ≠ 0) (hb : |h| ≤ 2*Real.pi*ε/3) (p : Configuration) (θ : ℝ) : Hilbert :=
  exponentialOutput ε a h hε ha hh hb
    (parameter θ (boostQ h (h⁻¹ • p))) (parameter θ (boostK (h⁻¹ • p)))

theorem boostedOutput_mass (ε a h : ℝ) (hε : 0 < ε) (ha : 0 < a)
    (hh : h ≠ 0) (hb : |h| ≤ 2*Real.pi*ε/3) (p : Configuration) (θ : ℝ) :
    ‖boostedOutput ε a h hε ha hh hb p θ‖^2 =
      (∫ u : ℝ, clockJacobian ε hε u * ∫ ξ : Transverse, ‖boostedLine ε a hε u h p θ ξ‖^2) /
        (clockMass ε a*gaussianMass (groundWidth 1) (neutralWidth 1)) :=
  exponentialOutput_mass ε a h hε ha hh hb _ _

#print axioms rawLine_mass
#print axioms gaussianMass_scale
#print axioms exponentialOutput_mass
#print axioms boostedOutput_mass

end
end UnifiedTheory.Audit.KFCausalClockFloorDisplacedEnergyIntegral
