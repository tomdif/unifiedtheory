/- The explicit classical initial probability law: the fixed clock density,
zero transverse position, and zero canonical momentum. This identifies
initial data only; it does not assert propagation by classical dynamics. -/
import UnifiedTheory.Audit.KFCausalClockFloorInitialProduct
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

namespace UnifiedTheory.Audit.KFCausalClockFloorInitialClassicalLaw
noncomputable section
open MeasureTheory MeasureTheory.Measure
open scoped ENNReal
open UnifiedTheory.Audit.KFCausalCoupledLongitudinalFlow (Configuration)
open UnifiedTheory.Audit.KFCausalTransverseDilationFlow (Transverse)
open UnifiedTheory.Audit.KFCausalClockFloorInvariantTrial
open UnifiedTheory.Audit.KFCausalClockFloorTrialEnergyNorms
open UnifiedTheory.Audit.KFCausalClockFloorInitialProduct
open UnifiedTheory.Audit.KFCausalPhysicalGaussianConcentration
open UnifiedTheory.Audit.KFCausalLpPhaseTranslation

variable (ε a : ℝ) (hε : 0 < ε) (ha : 0 < a)

def clockDensity (s : ℝ) : ℝ := ‖clockFunction ε a s‖^2/clockMass ε a

omit hε ha in
theorem clockDensity_continuous : Continuous (clockDensity ε a) :=
  ((clockFunction_continuous ε a).norm.pow 2).div_const _

include hε ha in
theorem clockDensity_nonnegative (s : ℝ) : 0 ≤ clockDensity ε a s :=
  div_nonneg (sq_nonneg _) (clockMass_positive ε a hε ha).le

include hε ha in
theorem clockDensity_integrable : Integrable (clockDensity ε a) volume :=
  ((memLp_two_iff_integrable_sq_norm (clockFunction_continuous ε a).aestronglyMeasurable).mp
    (clockFunction_memLp ε a hε ha)).div_const _

include hε ha in
theorem clockDensity_integral : ∫ s, clockDensity ε a s = 1 := by
  change (∫ s, ‖clockFunction ε a s‖^2/clockMass ε a) = 1
  rw [integral_div]
  exact div_self (clockMass_positive ε a hε ha).ne'

def clockLaw : Measure ℝ := volume.withDensity (fun s => ENNReal.ofReal (clockDensity ε a s))

include hε ha in
theorem clockLaw_probability : IsProbabilityMeasure (clockLaw ε a) := by
  constructor
  rw [clockLaw,withDensity_apply _ MeasurableSet.univ,Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal (clockDensity_integrable ε a hε ha)
      (Filter.Eventually.of_forall (clockDensity_nonnegative ε a hε ha)),
    clockDensity_integral ε a hε ha,ENNReal.ofReal_one]

theorem unitClock_density :
    (fun s => ‖unitClock ε a hε ha s‖^2) =ᵐ[volume] clockDensity ε a := by
  filter_upwards [Lp.coeFn_smul (‖clockState ε a hε ha‖⁻¹:ℝ) (clockState ε a hε ha),
    (clockFunction_memLp ε a hε ha).coeFn_toLp] with s hs hc
  change unitClock ε a hε ha s = _ at hs
  change clockState ε a hε ha s = clockFunction ε a s at hc
  rw [hs,Pi.smul_apply,hc,norm_smul,mul_pow,Real.norm_eq_abs,abs_inv,
    abs_of_nonneg (norm_nonneg _),inv_pow,clockState_norm_square]
  exact (div_eq_inv_mul _ _).symm

def clockCharacteristic (r : ℝ) : ℂ :=
  inner ℂ (unitClock ε a hε ha)
    (modulation volume (fun s : ℝ => r*s) (measurable_const.mul measurable_id) (unitClock ε a hε ha))

theorem clockCharacteristic_integral (r : ℝ) :
    clockCharacteristic ε a hε ha r =
      ∫ s, phase (fun t : ℝ => r*t) s * (clockDensity ε a s:ℂ) := by
  rw [clockCharacteristic,L2.inner_def]
  apply integral_congr_ae
  filter_upwards [modulation_coe volume (fun s : ℝ => r*s) (measurable_const.mul measurable_id)
    (unitClock ε a hε ha),unitClock_density ε a hε ha] with s hs hd
  rw [hs,RCLike.inner_apply']
  calc
    _ = phase (fun t : ℝ => r*t) s *
        (inner ℂ (unitClock ε a hε ha s) (unitClock ε a hε ha s)) := by
      rw [RCLike.inner_apply']; ring
    _ = _ := by rw [inner_self_eq_norm_sq_to_K,RCLike.ofReal_eq_complex_ofReal,← Complex.ofReal_pow,hd]

theorem clockCharacteristic_law (r : ℝ) :
    clockCharacteristic ε a hε ha r = ∫ s, phase (fun t : ℝ => r*t) s ∂clockLaw ε a := by
  rw [clockLaw,integral_withDensity_eq_integral_toReal_smul
    (clockDensity_continuous ε a).measurable.ennreal_ofReal
    (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
  rw [clockCharacteristic_integral]
  apply integral_congr_ae
  filter_upwards [] with s
  rw [ENNReal.toReal_ofReal (clockDensity_nonnegative ε a hε ha s)]
  change _ = (clockDensity ε a s:ℂ)*_
  exact mul_comm _ _

abbrev PhaseSpace := Configuration × Configuration

def clockAxis (s : ℝ) : PhaseSpace := ((s,0),(0,0))

theorem clockAxis_continuous : Continuous clockAxis := by unfold clockAxis; fun_prop

def classicalLaw : Measure PhaseSpace := (clockLaw ε a).map clockAxis

include hε ha in
theorem classicalLaw_probability : IsProbabilityMeasure (classicalLaw ε a) := by
  letI := clockLaw_probability ε a hε ha
  exact Measure.isProbabilityMeasure_map clockAxis_continuous.measurable.aemeasurable

def classicalPhase (r u : ℝ) (ξ η : Transverse) (z : PhaseSpace) : ℂ :=
  Complex.exp (Complex.I*((r*z.1.1+dot ξ z.1.2+u*z.2.1+dot η z.2.2:ℝ):ℂ))

theorem classicalPhase_continuous (r u : ℝ) (ξ η : Transverse) : Continuous (classicalPhase r u ξ η) := by
  unfold classicalPhase
  exact Complex.continuous_exp.comp (continuous_const.mul (Complex.continuous_ofReal.comp
    (((continuous_const.mul continuous_fst.fst).add ((dot_continuous ξ).comp continuous_fst.snd)).add
      (continuous_const.mul continuous_snd.fst) |>.add ((dot_continuous η).comp continuous_snd.snd))))

theorem classicalLaw_characteristic (r u : ℝ) (ξ η : Transverse) :
    ∫ z, classicalPhase r u ξ η z ∂classicalLaw ε a = clockCharacteristic ε a hε ha r := by
  rw [classicalLaw,integral_map clockAxis_continuous.measurable.aemeasurable
    (classicalPhase_continuous r u ξ η).aestronglyMeasurable,clockCharacteristic_law]
  apply integral_congr_ae
  filter_upwards [] with s
  simp only [classicalPhase,clockAxis,dot,Pi.zero_apply,mul_zero,Finset.sum_const_zero,
    add_zero,phase]

#print axioms clockDensity_continuous
#print axioms clockDensity_nonnegative
#print axioms clockDensity_integrable
#print axioms clockDensity_integral
#print axioms clockLaw_probability
#print axioms unitClock_density
#print axioms clockCharacteristic_integral
#print axioms clockCharacteristic_law
#print axioms clockAxis_continuous
#print axioms classicalLaw_probability
#print axioms classicalPhase_continuous
#print axioms classicalLaw_characteristic

end
end UnifiedTheory.Audit.KFCausalClockFloorInitialClassicalLaw
