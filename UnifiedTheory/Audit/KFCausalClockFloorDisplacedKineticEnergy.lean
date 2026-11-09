/- Exact normalized clock and kinetic energies on displaced boosted
orbits. The clock term is unchanged; each kinetic energy is its phase
momentum term plus an explicit nonnegative abs(hbar) correction. -/
import UnifiedTheory.Audit.KFCausalClockFloorDisplacedProfileMass

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1800000

namespace UnifiedTheory.Audit.KFCausalClockFloorDisplacedKineticEnergy
noncomputable section
open MeasureTheory Filter
open scoped Topology
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalTransverseDilationFlow (Transverse)
open UnifiedTheory.Audit.KFCausalCoupledLongitudinalFlow (Configuration)
open UnifiedTheory.Audit.KFCausalEuclideanProductCoordinates (Joint)
open UnifiedTheory.Audit.KFCausalClockFloorDisplacedProfileMass
open UnifiedTheory.Audit.KFCausalClockFloorDisplacedMomentumDensity (pairing)
open UnifiedTheory.Audit.KFCausalClockFloorDisplacedPhysicalPackets (phaseMomentum)
open UnifiedTheory.Audit.KFCausalClockFloorDisplacedSources (amplitude source clockFrequency)
open UnifiedTheory.Audit.KFCausalClockFloorTrialEnergyNorms (clockMass clockMass_positive halfMass dampedMass trial_norm_square)
open UnifiedTheory.Audit.KFCausalClockFloorInvariantTrial (trialState neutralWidth neutralWidth_positive neutralWidth_bound)
open UnifiedTheory.Audit.KFCausalChargeGaussianGeometry (groundWidth groundWidth_positive)
open UnifiedTheory.Audit.KFCausalPhysicalGaussianNormalization (gaussianMass gaussianMass_positive)
open UnifiedTheory.Audit.KFCausalClockFloorBoostedRescaling (scale scale_positive)
open UnifiedTheory.Audit.KFCausalChargeModulationFlow (parameter)
open UnifiedTheory.Audit.KFCausalDisplacedBoostParameters (boostQ boostK)
open UnifiedTheory.Audit.KFCausalClassicalChargePhase (rotate physicalTail)
open UnifiedTheory.Audit.KFCausalPhysicalEnergyFactors (modelDirections)
open UnifiedTheory.Audit.KFCausalMatterOrderedDomain (pointField)

def clockOutput (ε a h : ℝ) (hε : 0 < ε) (ha : 0 < a) (hh : h ≠ 0) (q k : Joint 2 4) : Hilbert :=
  (‖trialState ε a h hε ha hh‖⁻¹ : ℝ) • KFCausalClockFloorSourcedClockMomentum.clockOutput ε a
    (groundWidth h) (neutralWidth h) hε ha (groundWidth_positive h hh) (neutralWidth_positive h hh)
    (neutralWidth_bound h) (amplitude h q k) (clockFrequency h k) (source h q k)

def momentumOutput (ε a h : ℝ) (hε : 0 < ε) (ha : 0 < a) (hh : h ≠ 0)
    (q k : Joint 2 4) (v : Transverse) : Hilbert :=
  (‖trialState ε a h hε ha hh‖⁻¹ : ℝ) • KFCausalClockFloorSourcedClockMomentum.momentumOutput ε a
    (groundWidth h) (neutralWidth h) hε ha (groundWidth_positive h hh) (neutralWidth_positive h hh)
    (neutralWidth_bound h) (amplitude h q k) (clockFrequency h k) (source h q k) h v

def kineticCorrection (v : Transverse) : ℝ := 4*momentMass v/gaussianMass (groundWidth 1) (neutralWidth 1)

theorem kineticCorrection_nonnegative (v : Transverse) : 0 ≤ kineticCorrection v := by
  unfold kineticCorrection
  exact div_nonneg (mul_nonneg (by norm_num) (momentMass_nonnegative v))
    (gaussianMass_positive _ _ (groundWidth_positive 1 one_ne_zero) (neutralWidth_positive 1 one_ne_zero)).le

theorem clockOutput_square (ε a h : ℝ) (hε : 0 < ε) (ha : 0 < a) (hh : h ≠ 0) (q k : Joint 2 4) :
    ‖clockOutput ε a h hε ha hh q k‖^2 = halfMass ε a/clockMass ε a := by
  unfold clockOutput KFCausalClockFloorSourcedClockMomentum.clockOutput
  rw [norm_smul,mul_pow,Real.norm_eq_abs,abs_inv,abs_of_nonneg (norm_nonneg _),
    inv_pow,← div_eq_inv_mul,trial_norm_square,profileState_mass h hh]
  exact mul_div_mul_right _ _ (gaussianMass_positive _ _ (groundWidth_positive h hh) (neutralWidth_positive h hh)).ne'

theorem momentumOutput_square (ε a h : ℝ) (hε : 0 < ε) (ha : 0 < a) (hh : h ≠ 0)
    (q k : Joint 2 4) (v : Transverse) :
    ‖momentumOutput ε a h hε ha hh q k v‖^2 =
      (dampedMass ε a/clockMass ε a)*((pairing v (phaseMomentum h q k))^2+|h| *kineticCorrection v) := by
  unfold momentumOutput
  rw [norm_smul,mul_pow,Real.norm_eq_abs,abs_inv,abs_of_nonneg (norm_nonneg _),inv_pow,
    ← div_eq_inv_mul,trial_norm_square,sourcedMomentum_mass ε a h hε ha hh,KFCausalClockFloorDisplacedEnergyIntegral.gaussianMass_scale h hh]
  have hs := (scale_positive h hh).ne'
  have hG := (gaussianMass_positive _ _ (groundWidth_positive 1 one_ne_zero) (neutralWidth_positive 1 one_ne_zero)).ne'
  have hC := (clockMass_positive ε a hε ha).ne'
  unfold kineticCorrection
  field_simp

def orbitMomentum (p : Configuration) (θ : ℝ) : Transverse :=
  physicalTail (rotate (-θ) (0,KFCausalClassicalPhysicalPhase.toPaired p)).2

def boostedClockOutput (ε a h : ℝ) (hε : 0 < ε) (ha : 0 < a) (hh : h ≠ 0) (p : Configuration) (θ : ℝ) : Hilbert :=
  clockOutput ε a h hε ha hh (parameter θ (boostQ h (h⁻¹ • p))) (parameter θ (boostK (h⁻¹ • p)))

def boostedMomentumOutput (ε a h : ℝ) (hε : 0 < ε) (ha : 0 < a) (hh : h ≠ 0)
    (p : Configuration) (θ : ℝ) (v : Transverse) : Hilbert :=
  momentumOutput ε a h hε ha hh (parameter θ (boostQ h (h⁻¹ • p))) (parameter θ (boostK (h⁻¹ • p))) v

theorem boostedClockOutput_square (ε a h : ℝ) (hε : 0 < ε) (ha : 0 < a) (hh : h ≠ 0)
    (p : Configuration) (θ : ℝ) :
    ‖boostedClockOutput ε a h hε ha hh p θ‖^2 = halfMass ε a/clockMass ε a := clockOutput_square _ _ _ _ _ _ _ _

theorem boostedMomentumOutput_square (ε a h : ℝ) (hε : 0 < ε) (ha : 0 < a) (hh : h ≠ 0)
    (p : Configuration) (θ : ℝ) (v : Transverse) :
    ‖boostedMomentumOutput ε a h hε ha hh p θ v‖^2 =
      (dampedMass ε a/clockMass ε a)*((pairing v (orbitMomentum p θ))^2+|h| *kineticCorrection v) := by
  rw [boostedMomentumOutput,momentumOutput_square,phaseMomentum,KFCausalDisplacedPhysicalPhase.phase_boost_orbit h hh]
  rfl

theorem boostedMomentumOutput_tendsto (ε a : ℝ) (hε : 0 < ε) (ha : 0 < a)
    (p : Configuration) (θ : ℝ) (v : Transverse) (h : ℕ → ℝ) (hh : ∀ n, h n ≠ 0)
    (hz : Tendsto h atTop (𝓝 0)) :
    Tendsto (fun n => ‖boostedMomentumOutput ε a (h n) hε ha (hh n) p θ v‖^2) atTop
      (𝓝 ((dampedMass ε a/clockMass ε a)*(pairing v (orbitMomentum p θ))^2)) := by
  simp_rw [boostedMomentumOutput_square]
  simpa only [abs_zero,zero_mul,add_zero] using
    ((hz.abs.mul_const (kineticCorrection v)).const_add ((pairing v (orbitMomentum p θ))^2)).const_mul
      (dampedMass ε a/clockMass ε a)

def kineticIndex (i : Fin 4) : Fin 8 := ⟨i.val+1,by omega⟩

theorem clockOutput_factor (ε a h : ℝ) (hε : 0 < ε) (ha : 0 < a) (hh : h ≠ 0)
    (hb : |h| ≤ 2*Real.pi*ε/3) (q k : Joint 2 4) :
    KFCausalClockFloorDisplacedCommonDomain.factorOutput ε a h hε ha hh hb q k modelDirections pointField 0 =
      clockOutput ε a h hε ha hh q k := rfl

theorem momentumOutput_factor (ε a h : ℝ) (hε : 0 < ε) (ha : 0 < a) (hh : h ≠ 0)
    (hb : |h| ≤ 2*Real.pi*ε/3) (q k : Joint 2 4) (i : Fin 4) :
    KFCausalClockFloorDisplacedCommonDomain.factorOutput ε a h hε ha hh hb q k modelDirections pointField (kineticIndex i) =
      momentumOutput ε a h hε ha hh q k (modelDirections i) := by fin_cases i <;> rfl

#print axioms kineticCorrection_nonnegative
#print axioms clockOutput_square
#print axioms momentumOutput_square
#print axioms boostedClockOutput_square
#print axioms boostedMomentumOutput_square
#print axioms boostedMomentumOutput_tendsto
#print axioms clockOutput_factor
#print axioms momentumOutput_factor

end
end UnifiedTheory.Audit.KFCausalClockFloorDisplacedKineticEnergy
