/- Identification of the integrated boosted exponential-energy limit with
exp(p_clock/C)/C averaged against the physical clock probability law.
This is an initial unaveraged result, not averaged-symbol identification
or propagation of the law. -/
import UnifiedTheory.Audit.KFCausalClockFloorBoostedEnergyLimit
import UnifiedTheory.Audit.KFCausalClockFloorInitialEnergyIdentification

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1800000

namespace UnifiedTheory.Audit.KFCausalClockFloorBoostedEnergyIdentification
noncomputable section
open MeasureTheory Filter
open scoped Topology
open UnifiedTheory.Audit.KFCausalClockFloorShearBounds
open UnifiedTheory.Audit.KFCausalClockFloorShearIntegrals (majorant_integral)
open UnifiedTheory.Audit.KFCausalClockFloorFullGaussian
open UnifiedTheory.Audit.KFCausalClockFloorBoostedRescaledLimit (limitDensity)
open UnifiedTheory.Audit.KFCausalClockFloorBoostedEnergyLimit (exponentialLimit exponential_energy_tendsto)
open UnifiedTheory.Audit.KFCausalClockFloorBoostedSpectral (boostedExponentialOutput)
open UnifiedTheory.Audit.KFCausalClockFloorInvariantTrial (neutralWidth neutralWidth_positive neutralWidth_bound clockFunction)
open UnifiedTheory.Audit.KFCausalChargeGaussianGeometry (groundWidth groundWidth_positive)
open UnifiedTheory.Audit.KFCausalPhysicalGaussianNormalization
open UnifiedTheory.Audit.KFCausalClockFloorTrialEnergyNorms (clockMass)
open UnifiedTheory.Audit.KFCausalClockFloorTrialClockEnergy (dampedClockFunction)
open UnifiedTheory.Audit.KFCausalClockFloorInitialEnergyIdentification (dampedClock_square)
open UnifiedTheory.Audit.KFCausalClockFloorInitialClassicalLaw
open UnifiedTheory.Audit.KFCausalClockFloorFlow (clock)
open UnifiedTheory.Audit.KFCausalClockFloorCanonicalDefect (clock_positive)
open UnifiedTheory.Audit.KFCausalClockFloorComplexDefect (realClock realClock_positive)
open UnifiedTheory.Audit.KFCausalComplexClockInverse (complexInverse_real)
open UnifiedTheory.Audit.KFCausalRegularizedLongitudinalChart (chart chartIso chartIso_apply)
open UnifiedTheory.Audit.KFCausalClockFloorChargeTrialBridge (amplitude amplitude_square clockFunction_factor)
open UnifiedTheory.Audit.KFCausalCoupledTestPullback (clock_change_integral)
open UnifiedTheory.Audit.KFCausalCoupledLongitudinalFlow (Configuration)

theorem packet_real_square (α β s : ℝ) (x : Grouped) :
    ‖packet α β (s:ℂ) x‖^2 = majorant (2*α*Real.exp s) (2*β) (2*(Real.exp (s/2)-1)) x := by
  rw [packet_norm_square,quadratic_re,majorant,← Real.exp_add]
  congr 1
  simp [shift,complexScale,Complex.exp_re,Complex.exp_im]
  ring

theorem packet_real_mass (α β s : ℝ) (hα : 0 < α) (hβ : 0 < β) :
    (∫ x : Grouped, ‖packet α β (s:ℂ) x‖^2) = gaussianMass α β*Real.exp (-2*s) := by
  simp_rw [packet_real_square]
  rw [majorant_integral _ _ _ (by positivity) (by positivity)]
  have he : (Real.pi/(2*α*Real.exp s))^2 = (Real.pi/(2*α))^2*Real.exp (-2*s) := by
    rw [show -2*s = -(s+s) by ring,Real.exp_neg,Real.exp_add]
    field_simp
  rw [he]
  unfold gaussianMass
  ring

theorem dampedClock_density (ε a s : ℝ) (hε : 0 < ε) :
    ‖dampedClockFunction ε a s‖^2 = clock ε s*Real.exp (-2*s)*Real.exp (-2*a*(chart ε s)^2) := by
  have hn : (Real.sqrt (Real.exp s+ε):ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr (by positivity)).ne'
  have he : dampedClockFunction ε a s = (amplitude ε s:ℂ)*clockFactor a (chart ε s:ℂ) := by
    rw [dampedClockFunction,clockFunction_factor ε a s hε]
    field_simp
  have hf : ‖clockFactor a (chart ε s:ℂ)‖^2 = Real.exp (-2*a*(chart ε s)^2) := by
    have h := congrArg (fun r : ℝ => r^2) (clockFactor_norm a (chart ε s) 0)
    simp only [Complex.ofReal_zero,zero_mul,add_zero,zero_pow (by decide : 2 ≠ 0),sub_zero] at h
    rw [h,← Real.exp_nat_mul]
    congr 1
    norm_num only [Nat.cast_ofNat]
    ring
  rw [he,norm_mul,mul_pow,Complex.norm_real,Real.norm_eq_abs,sq_abs,amplitude_square ε s hε,hf]
  rfl

theorem exponential_clock_bound (ε r q : ℝ) (hε : 0 < ε) :
    Real.exp (r/realClock ε hε q) ≤ Real.exp (|r|/ε) := by
  have hc : ε ≤ realClock ε hε q := by unfold realClock clock; linarith [Real.exp_pos ((chartIso ε hε).symm q)]
  apply Real.exp_le_exp.mpr
  exact (div_le_div_of_nonneg_right (le_abs_self r) (realClock_positive ε hε q).le).trans
    (div_le_div_of_nonneg_left (abs_nonneg r) hε hc)

theorem limitDensity_integrable (ε a : ℝ) (hε : 0 < ε) (ha : 0 < a) (p : Configuration) :
    Integrable (limitDensity ε a hε p) volume := by
  have hm := line_memLp ε a (groundWidth 1) (neutralWidth 1) 0 hε ha
    (groundWidth_positive 1 one_ne_zero) (neutralWidth_positive 1 one_ne_zero) (neutralWidth_bound 1) (by simp; positivity)
  have hc : Continuous (realClock ε hε) :=
    (Real.continuous_exp.comp (chartIso ε hε).symm.toHomeomorph.continuous).add continuous_const
  have hw : Continuous (fun z : ℝ × Grouped => Real.exp (p.1/realClock ε hε z.1)) :=
    Real.continuous_exp.comp (continuous_const.div (hc.comp continuous_fst) (fun z => (realClock_positive ε hε z.1).ne'))
  apply (((memLp_two_iff_integrable_sq_norm hm.1).mp hm).const_mul (Real.exp (|p.1|/ε))).mono'
    (hw.aestronglyMeasurable.mul (hm.1.norm.pow 2))
  filter_upwards [] with z
  change ‖Real.exp (p.1/realClock ε hε z.1)*‖line ε a (groundWidth 1) (neutralWidth 1) 0 z‖^2‖ ≤ _
  rw [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg (Real.exp_pos _).le (sq_nonneg _))]
  exact mul_le_mul_of_nonneg_right (exponential_clock_bound ε p.1 z.1 hε) (sq_nonneg _)

theorem limitDensity_slice (ε a : ℝ) (hε : 0 < ε) (p : Configuration) (q : ℝ) :
    (∫ x : Grouped, limitDensity ε a hε p (q,x)) =
      Real.exp (p.1/realClock ε hε q)*Real.exp (-2*a*q^2)*
        (gaussianMass (groundWidth 1) (neutralWidth 1)*Real.exp (-2*((chartIso ε hε).symm q))) := by
  unfold limitDensity
  dsimp only [Prod.fst]
  rw [integral_const_mul]
  simp_rw [line_square,zero_pow (by decide : 2 ≠ 0),mul_zero,Real.exp_zero,one_mul,
    Complex.ofReal_zero,zero_mul,add_zero,complexInverse_real ε hε]
  rw [integral_const_mul,packet_real_mass _ _ _ (groundWidth_positive 1 one_ne_zero) (neutralWidth_positive 1 one_ne_zero)]
  ring

theorem limitDensity_mass (ε a : ℝ) (hε : 0 < ε) (ha : 0 < a) (p : Configuration) :
    (∫ z : ℝ × Grouped, limitDensity ε a hε p z) =
      (∫ s : ℝ, Real.exp (p.1/clock ε s)*‖dampedClockFunction ε a s‖^2)*
        gaussianMass (groundWidth 1) (neutralWidth 1) := by
  have hi := limitDensity_integrable ε a hε ha p
  rw [Measure.volume_eq_prod ℝ Grouped] at hi ⊢
  rw [integral_prod _ hi,← clock_change_integral ε hε (fun q => ∫ x : Grouped, limitDensity ε a hε p (q,x))]
  simp_rw [limitDensity_slice]
  rw [← integral_mul_const]
  apply integral_congr_ae
  filter_upwards [] with s
  have hc : (chartIso ε hε).symm (chart ε s) = s := (chartIso ε hε).symm_apply_apply s
  rw [realClock,hc,dampedClock_density ε a s hε]
  unfold clock
  ring

theorem exponentialLimit_clockLaw (ε a : ℝ) (hε : 0 < ε) (ha : 0 < a) (p : Configuration) :
    exponentialLimit ε a hε p =
      ∫ s : ℝ, Real.exp (p.1/clock ε s)/clock ε s ∂clockLaw ε a := by
  rw [exponentialLimit,limitDensity_mass ε a hε ha p,
    mul_div_mul_right _ _ (gaussianMass_positive _ _ (groundWidth_positive 1 one_ne_zero)
      (neutralWidth_positive 1 one_ne_zero)).ne']
  rw [clockLaw,integral_withDensity_eq_integral_toReal_smul
    (clockDensity_continuous ε a).measurable.ennreal_ofReal
    (Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top)),← integral_div]
  apply integral_congr_ae
  filter_upwards [] with s
  rw [ENNReal.toReal_ofReal (clockDensity_nonnegative ε a hε ha s),smul_eq_mul,dampedClock_square ε a s hε]
  unfold clockDensity
  ring

theorem exponential_energy_clockLaw (ε a : ℝ) (hε : 0 < ε) (ha : 0 < a) (p : Configuration)
    (h : ℕ → ℝ) (hh : ∀ n, h n ≠ 0) (hb : ∀ n, |h n| ≤ 2*Real.pi*ε/3)
    (h1 : ∀ n, |h n| ≤ 1) (hz : Tendsto h atTop (𝓝 0)) :
    Tendsto (fun n => ‖boostedExponentialOutput ε a (h n) hε ha (hh n) (hb n) p‖^2) atTop
      (𝓝 (∫ s : ℝ, Real.exp (p.1/clock ε s)/clock ε s ∂clockLaw ε a)) := by
  rw [← exponentialLimit_clockLaw ε a hε ha p]
  exact exponential_energy_tendsto ε a hε ha p h hh hb h1 hz

#print axioms packet_real_square
#print axioms packet_real_mass
#print axioms dampedClock_density
#print axioms exponential_clock_bound
#print axioms limitDensity_integrable
#print axioms limitDensity_slice
#print axioms limitDensity_mass
#print axioms exponentialLimit_clockLaw
#print axioms exponential_energy_clockLaw

end
end UnifiedTheory.Audit.KFCausalClockFloorBoostedEnergyIdentification
