/- Exact integral formulas for both actual ordered field outputs on the
displaced family. The field acts after the longitudinal exponential, and
the same concentration normalization cancels for both field powers. -/
import UnifiedTheory.Audit.KFCausalClockFloorRecenteredFields

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1800000

namespace UnifiedTheory.Audit.KFCausalClockFloorDisplacedFieldIntegral
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

def fieldIndex (j : Fin 2) : Fin 8 := if j=0 then 5 else 6

def fieldMultiplier (ε : ℝ) (hε : 0 < ε) (l : Transverse →L[ℝ] ℝ) (j : Fin 2) (x : Configuration) : ℂ :=
  (pulledField ε hε l x:ℂ)^(j.val+1)

theorem fieldMultiplier_measurable (ε : ℝ) (hε : 0 < ε) (l : Transverse →L[ℝ] ℝ) (j : Fin 2) :
    AEStronglyMeasurable (fieldMultiplier ε hε l j) volume :=
  ((Complex.continuous_ofReal.comp (pulledField_continuous ε hε l)).pow (j.val+1)).aestronglyMeasurable

def fieldBase (ε a h : ℝ) (hε : 0 < ε) (ha : 0 < a) (hh : h ≠ 0)
    (hb : |h| ≤ 2*Real.pi*ε/3) (l : Transverse →L[ℝ] ℝ) (j : Fin 2) :
    MemLp (fun x => fieldMultiplier ε hε l j x*baseLine ε a (groundWidth h) (neutralWidth h) (-h/2) x) 2 := by
  fin_cases j
  · simpa only [fieldMultiplier,zero_add,pow_one] using
      linear_base_memLp ε a h hε ha hh (-h/2) (shift_bound ε h hb) l
  · exact quadratic_base_memLp ε a h hε ha hh (-h/2) (shift_bound ε h hb) l

def weightedLine (ε a h : ℝ) (hε : 0 < ε) (q k : Joint 2 4)
    (l : Transverse →L[ℝ] ℝ) (j : Fin 2) (z : ℝ × Grouped) : ℂ :=
  (fieldLine ε hε l z:ℂ)^(j.val+1)*rawLine ε a h q k z

theorem weightedLine_grouping (ε a h : ℝ) (hε : 0 < ε) (q k : Joint 2 4)
    (l : Transverse →L[ℝ] ℝ) (j : Fin 2) (x : Configuration) :
    modifiedLine ε a (groundWidth h) (neutralWidth h) (-h/2) (fieldMultiplier ε hε l j)
      (amplitude h q k) (clockFrequency h k) (source h q k) x =
        weightedLine ε a h hε q k l j (grouping x) := by
  rw [weightedLine,fieldLine_grouping]
  rfl

theorem weightedLine_memLp (ε a h : ℝ) (hε : 0 < ε) (ha : 0 < a) (hh : h ≠ 0)
    (hb : |h| ≤ 2*Real.pi*ε/3) (q k : Joint 2 4) (l : Transverse →L[ℝ] ℝ) (j : Fin 2) :
    MemLp (weightedLine ε a h hε q k l j) 2 := by
  have hm := modifiedLine_memLp ε a (groundWidth h) (neutralWidth h) (-h/2) hε ha
    (groundWidth_positive h hh) (neutralWidth_positive h hh) (neutralWidth_bound h) (shift_bound ε h hb)
    (fieldMultiplier ε hε l j) (fieldMultiplier_measurable ε hε l j) (fieldBase ε a h hε ha hh hb l j)
    (amplitude h q k) (clockFrequency h k) (source h q k)
  have ht := hm.comp_measurePreserving grouping_preserves_volume.symm
  simpa only [Function.comp_def,weightedLine_grouping,MeasurableEquiv.apply_symm_apply] using ht

theorem sourcedField_mass (ε a h : ℝ) (hε : 0 < ε) (ha : 0 < a) (hh : h ≠ 0)
    (hb : |h| ≤ 2*Real.pi*ε/3) (q k : Joint 2 4) (l : Transverse →L[ℝ] ℝ) (j : Fin 2) :
    ‖KFCausalClockFloorSourcedCommonDomain.factorOutput ε a (groundWidth h) (neutralWidth h)
      hε ha (groundWidth_positive h hh) (neutralWidth_positive h hh) (neutralWidth_bound h)
      (amplitude h q k) (clockFrequency h k) (source h q k) h hb modelDirections l (fieldIndex j)‖^2 =
        ∫ z, ‖weightedLine ε a h hε q k l j z‖^2 := by
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
  rw [he,outputState,(coordinates ε hε).norm_map,KFCausalCoupledFunctionEnergy.toLp_square_integral]
  simp_rw [weightedLine_grouping]
  exact grouping_preserves_volume.integral_comp grouping.measurableEmbedding
    (fun z => ‖weightedLine ε a h hε q k l j z‖^2)

theorem weightedLine_recenter_square (ε a u h : ℝ) (hε : 0 < ε) (q k : Joint 2 4)
    (Q ξ : Transverse) (l : Transverse →L[ℝ] ℝ) (j : Fin 2) :
    ‖weightedLine ε a h hε q k l j (u,recenter ε hε u h Q ξ)‖^2 =
      (fieldPower j l (rescaledPosition h Q ξ))^2 *
        ‖rawLine ε a h q k (u,recenter ε hε u h Q ξ)‖^2 := by
  rw [weightedLine,fieldLine_recenter,← Complex.ofReal_pow,norm_mul,mul_pow,
    Complex.norm_real,Real.norm_eq_abs,sq_abs]
  rfl

def recenteredFieldMass (ε a : ℝ) (hε : 0 < ε) (h : ℝ) (q k : Joint 2 4)
    (l : Transverse →L[ℝ] ℝ) (j : Fin 2) : ℝ :=
  let Q := physicalTail (KFCausalDisplacedPhysicalPhase.phase h q k).1
  ∫ u : ℝ, clockJacobian ε hε u * ∫ ξ : Transverse,
    (fieldPower j l (rescaledPosition h Q ξ))^2 * ‖rawLine ε a h q k (u,recenter ε hε u h Q ξ)‖^2

theorem weightedLine_mass (ε a h : ℝ) (hε : 0 < ε) (ha : 0 < a) (hh : h ≠ 0)
    (hb : |h| ≤ 2*Real.pi*ε/3) (q k : Joint 2 4) (l : Transverse →L[ℝ] ℝ) (j : Fin 2) :
    (∫ z, ‖weightedLine ε a h hε q k l j z‖^2) = (scale h)^5*recenteredFieldMass ε a hε h q k l j := by
  have hm := weightedLine_memLp ε a h hε ha hh hb q k l j
  have hi := (memLp_two_iff_integrable_sq_norm hm.1).mp hm
  rw [Measure.volume_eq_prod ℝ Grouped] at hi ⊢
  rw [integral_prod _ hi,recenteredFieldMass,← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with u
  rw [recenter_integral ε hε u h hh (physicalTail (KFCausalDisplacedPhysicalPhase.phase h q k).1)]
  simp_rw [weightedLine_recenter_square]
  ring

def fieldOutput (ε a h : ℝ) (hε : 0 < ε) (ha : 0 < a) (hh : h ≠ 0)
    (hb : |h| ≤ 2*Real.pi*ε/3) (q k : Joint 2 4) (l : Transverse →L[ℝ] ℝ) (j : Fin 2) : Hilbert :=
  KFCausalClockFloorDisplacedCommonDomain.factorOutput ε a h hε ha hh hb q k modelDirections l (fieldIndex j)

theorem fieldOutput_mass (ε a h : ℝ) (hε : 0 < ε) (ha : 0 < a) (hh : h ≠ 0)
    (hb : |h| ≤ 2*Real.pi*ε/3) (q k : Joint 2 4) (l : Transverse →L[ℝ] ℝ) (j : Fin 2) :
    ‖fieldOutput ε a h hε ha hh hb q k l j‖^2 = recenteredFieldMass ε a hε h q k l j /
      (clockMass ε a*gaussianMass (groundWidth 1) (neutralWidth 1)) := by
  unfold fieldOutput KFCausalClockFloorDisplacedCommonDomain.factorOutput
  rw [norm_smul,mul_pow,Real.norm_eq_abs,abs_inv,abs_of_nonneg (norm_nonneg _),
    inv_pow,← div_eq_inv_mul,trial_norm_square,sourcedField_mass ε a h hε ha hh hb q k l j,
    weightedLine_mass ε a h hε ha hh hb q k l j,gaussianMass_scale h hh]
  rw [mul_left_comm (clockMass ε a) ((scale h)^5)]
  exact mul_div_mul_left _ _ (pow_ne_zero 5 (scale_positive h hh).ne')

def boostedFieldOutput (ε a h : ℝ) (hε : 0 < ε) (ha : 0 < a) (hh : h ≠ 0)
    (hb : |h| ≤ 2*Real.pi*ε/3) (p : Configuration) (θ : ℝ) (l : Transverse →L[ℝ] ℝ) (j : Fin 2) : Hilbert :=
  fieldOutput ε a h hε ha hh hb (parameter θ (boostQ h (h⁻¹ • p)))
    (parameter θ (boostK (h⁻¹ • p))) l j

theorem boostedFieldOutput_mass (ε a h : ℝ) (hε : 0 < ε) (ha : 0 < a) (hh : h ≠ 0)
    (hb : |h| ≤ 2*Real.pi*ε/3) (p : Configuration) (θ : ℝ) (l : Transverse →L[ℝ] ℝ) (j : Fin 2) :
    ‖boostedFieldOutput ε a h hε ha hh hb p θ l j‖^2 =
      (∫ u : ℝ, clockJacobian ε hε u * ∫ ξ : Transverse,
        (fieldPower j l (rescaledPosition h (orbitCentre p θ) ξ))^2 * ‖boostedLine ε a hε u h p θ ξ‖^2) /
          (clockMass ε a*gaussianMass (groundWidth 1) (neutralWidth 1)) := by
  rw [boostedFieldOutput,fieldOutput_mass]
  unfold recenteredFieldMass
  dsimp only
  unfold boostedLine rawLine
  dsimp only
  simp_rw [KFCausalDisplacedPhysicalPhase.phase_boost_orbit h hh]
  rfl

#print axioms fieldMultiplier_measurable
#print axioms weightedLine_grouping
#print axioms weightedLine_memLp
#print axioms sourcedField_mass
#print axioms weightedLine_recenter_square
#print axioms weightedLine_mass
#print axioms fieldOutput_mass
#print axioms boostedFieldOutput_mass

end
end UnifiedTheory.Audit.KFCausalClockFloorDisplacedFieldIntegral
