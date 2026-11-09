/- Exact clock moments of the initial boosted family and a physical
left-tail bound for arbitrary L2 states. -/
import UnifiedTheory.Audit.KFCausalClockFloorPowerVelocityPairing
import UnifiedTheory.Audit.KFCausalClockFloorInitialClassicalLaw
import UnifiedTheory.Audit.KFCausalClockFloorBoostedKineticLimit

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1600000

namespace UnifiedTheory.Audit.KFCausalClockFloorClockMomentLaw
noncomputable section
open MeasureTheory MeasureTheory.Measure Filter
open scoped Topology
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalCoupledLongitudinalFlow (Configuration)
open UnifiedTheory.Audit.KFCausalTransverseDilationFlow (Transverse)
open UnifiedTheory.Audit.KFCausalClockFloorCanonicalDefect
open UnifiedTheory.Audit.KFCausalClockFloorFlow (clock)
open UnifiedTheory.Audit.KFCausalClockFloorDefectOperator (defectOperator)
open UnifiedTheory.Audit.KFCausalClockFloorPowerVelocityPairing (defect_power_coe)
open UnifiedTheory.Audit.KFCausalClockFloorInitialDriftPairing (real_multiplier_pairing)
open UnifiedTheory.Audit.KFCausalClockFloorInitialClassicalLaw
open UnifiedTheory.Audit.KFCausalClockFloorInitialProduct (unitClock unitTrial_product)
open UnifiedTheory.Audit.KFCausalGaussianPhaseSpaceLimit (unitGaussian unitGaussian_norm)
open UnifiedTheory.Audit.KFCausalL2TensorEmbedding (productState_coe)
open UnifiedTheory.Audit.KFCausalPhysicalMomentumModulation (modulation_coe)
open UnifiedTheory.Audit.KFCausalClockFloorSemiclassicalStates (unitTrial)
open UnifiedTheory.Audit.KFCausalClockFloorBoostedKineticLimit (boostedState)

def moment (ε : ℝ) (hε : 0 < ε) (n : ℕ) (f : Hilbert) : ℝ :=
  (inner ℂ f (((defectOperator ε hε)^(n+1)) f)).re

def initialMoment (ε a : ℝ) (n : ℕ) : ℝ := ∫ s, (defect ε s)^(n+1) ∂clockLaw ε a

theorem defect_strict_bounds (ε : ℝ) (hε : 0 < ε) (s : ℝ) : 0 < defect ε s ∧ defect ε s < 1 := by
  refine ⟨defect_positive ε s hε,?_⟩
  rw [defect,div_lt_one (clock_positive ε s hε.le)]
  unfold clock
  linarith [Real.exp_pos s]

theorem defect_continuous (ε : ℝ) (hε : 0 < ε) : Continuous (defect ε) :=
  continuous_const.div (Real.continuous_exp.add continuous_const) (fun s => (clock_positive ε s hε.le).ne')

theorem moment_integrable (ε : ℝ) (hε : 0 < ε) (n : ℕ) (f : Hilbert) :
    Integrable (fun x : Configuration => (defect ε x.1)^(n+1)*‖f x‖^2) := by
  have hi := (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable f)).mp (Lp.memLp f)
  apply hi.bdd_mul (c := 1) (((defect_continuous ε hε).comp continuous_fst).pow (n+1)).aestronglyMeasurable
  filter_upwards [] with x
  dsimp only [Function.comp_def]
  rw [Real.norm_eq_abs,abs_of_nonneg (pow_nonneg (defect_strict_bounds ε hε x.1).1.le _)]
  exact pow_le_one₀ (defect_strict_bounds ε hε x.1).1.le (defect_strict_bounds ε hε x.1).2.le

theorem moment_integral (ε : ℝ) (hε : 0 < ε) (n : ℕ) (f : Hilbert) :
    moment ε hε n f = ∫ x : Configuration, (defect ε x.1)^(n+1)*‖f x‖^2 :=
  real_multiplier_pairing volume _ _ _ (defect_power_coe ε hε (n+1) f)

theorem boostedState_density (ε a h : ℝ) (hε : 0 < ε) (ha : 0 < a) (hh : h ≠ 0)
    (l : Configuration →L[ℝ] ℝ) :
    (fun x => ‖boostedState ε a h hε ha hh l x‖^2) =ᵐ[volume]
      fun x => clockDensity ε a x.1*‖unitGaussian h hh x.2‖^2 := by
  have hp := productState_coe volume volume (unitClock ε a hε ha) (unitGaussian h hh)
  rw [← unitTrial_product ε a h hε ha hh] at hp
  filter_upwards [modulation_coe (h⁻¹ • l) (unitTrial ε a h hε ha hh),hp,
    quasiMeasurePreserving_fst.ae (unitClock_density ε a hε ha)] with x hm hp hc
  change ‖KFCausalPhysicalMomentumModulation.modulation (h⁻¹ • l) (unitTrial ε a h hε ha hh) x‖^2 = _
  rw [hm,hp,norm_mul,KFCausalCanonicalWeylAlgebra.scalar_norm,one_mul,norm_mul,mul_pow,hc]

theorem boosted_initial_moment (ε a h : ℝ) (hε : 0 < ε) (ha : 0 < a) (hh : h ≠ 0)
    (l : Configuration →L[ℝ] ℝ) (n : ℕ) :
    moment ε hε n (boostedState ε a h hε ha hh l) = initialMoment ε a n := by
  rw [moment_integral]
  calc
    _ = ∫ x : Configuration, ((defect ε x.1)^(n+1)*clockDensity ε a x.1)*‖unitGaussian h hh x.2‖^2 := by
      apply integral_congr_ae
      filter_upwards [boostedState_density ε a h hε ha hh l] with x hx
      rw [hx,mul_assoc]
    _ = (∫ s, (defect ε s)^(n+1)*clockDensity ε a s)*1 := by
      rw [Measure.volume_eq_prod ℝ Transverse,integral_prod_mul
        (fun s => (defect ε s)^(n+1)*clockDensity ε a s) (fun ξ => ‖unitGaussian h hh ξ‖^2),
        ← KFCausalAveragedEnergyGraph.l2_norm_square,unitGaussian_norm,one_pow]
    _ = _ := by
      rw [mul_one,initialMoment,clockLaw,integral_withDensity_eq_integral_toReal_smul
        (clockDensity_continuous ε a).measurable.ennreal_ofReal
        (Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
      apply integral_congr_ae
      filter_upwards [] with s
      rw [ENNReal.toReal_ofReal (clockDensity_nonnegative ε a hε ha s),smul_eq_mul,mul_comm]

theorem initialMoment_tendsto_zero (ε a : ℝ) (hε : 0 < ε) (ha : 0 < a) :
    Tendsto (initialMoment ε a) atTop (𝓝 0) := by
  letI := clockLaw_probability ε a hε ha
  have he : Tendsto (fun n : ℕ => ∫ s, (defect ε s)^(n+1) ∂clockLaw ε a) atTop
      (𝓝 (∫ _s : ℝ, (0:ℝ) ∂clockLaw ε a)) := by
    apply tendsto_integral_of_dominated_convergence (fun _ : ℝ => (1:ℝ))
    · intro n
      exact ((defect_continuous ε hε).pow (n+1)).aestronglyMeasurable
    · exact integrable_const 1
    · intro n
      filter_upwards [] with s
      rw [Real.norm_eq_abs,abs_of_nonneg (pow_nonneg (defect_strict_bounds ε hε s).1.le _)]
      exact pow_le_one₀ (defect_strict_bounds ε hε s).1.le (defect_strict_bounds ε hε s).2.le
    · filter_upwards [] with s
      have hp := tendsto_pow_atTop_nhds_zero_of_lt_one (defect_strict_bounds ε hε s).1.le (defect_strict_bounds ε hε s).2
      simpa only [pow_succ,zero_mul] using hp.mul_const (defect ε s)
  simpa only [integral_zero] using he

def leftMass (S : ℝ) (f : Hilbert) : ℝ := ∫ x : Configuration in {x | x.1 ≤ S}, ‖f x‖^2

theorem leftMass_moment_bound (ε : ℝ) (hε : 0 < ε) (n : ℕ) (S : ℝ) (f : Hilbert) :
    (defect ε S)^(n+1)*leftMass S f ≤ moment ε hε n f := by
  have hset : MeasurableSet {x : Configuration | x.1 ≤ S} := measurableSet_le measurable_fst measurable_const
  have hi := (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable f)).mp (Lp.memLp f)
  rw [leftMass,← integral_indicator hset,← integral_const_mul,moment_integral]
  apply integral_mono_ae ((hi.indicator hset).const_mul _) (moment_integrable ε hε n f)
  filter_upwards [] with x
  by_cases hx : x.1 ≤ S
  · rw [Set.indicator_of_mem (show x ∈ {x : Configuration | x.1 ≤ S} from hx)]
    have hd : defect ε S ≤ defect ε x.1 := div_le_div_of_nonneg_left hε.le
      (clock_positive ε x.1 hε.le) (add_le_add (Real.exp_le_exp.mpr hx) le_rfl)
    exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (defect_strict_bounds ε hε S).1.le hd (n+1)) (sq_nonneg _)
  · rw [Set.indicator_of_notMem (show x ∉ {x : Configuration | x.1 ≤ S} from hx),mul_zero]
    exact mul_nonneg (pow_nonneg (defect_strict_bounds ε hε x.1).1.le _) (sq_nonneg _)

#print axioms defect_strict_bounds
#print axioms defect_continuous
#print axioms moment_integrable
#print axioms moment_integral
#print axioms boostedState_density
#print axioms boosted_initial_moment
#print axioms initialMoment_tendsto_zero
#print axioms leftMass_moment_bound

end
end UnifiedTheory.Audit.KFCausalClockFloorClockMomentLaw
