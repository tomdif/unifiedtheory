/- The strongly approximating inverse-clock output has an exact classical
clock-density pairing. The actual ordered output inherits this drift limit. -/
import UnifiedTheory.Audit.KFCausalClockFloorStrongInitialOutput
import UnifiedTheory.Audit.KFCausalClockFloorInitialEnergyIdentification
import UnifiedTheory.Audit.KFCausalClockFloorQuantumVelocityOutput

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1200000

namespace UnifiedTheory.Audit.KFCausalClockFloorInitialDriftPairing
noncomputable section
open MeasureTheory Filter
open scoped Topology
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalCoupledLongitudinalFlow (Configuration)
open UnifiedTheory.Audit.KFCausalTransverseDilationFlow (Transverse)
open UnifiedTheory.Audit.KFCausalClockFloorShearBounds (physicalGaussian)
open UnifiedTheory.Audit.KFCausalClockFloorCanonicalDefect
open UnifiedTheory.Audit.KFCausalClockFloorDefectTransportScalar (drift drift_bound)
open UnifiedTheory.Audit.KFCausalClockFloorDefectTransportOperator
open UnifiedTheory.Audit.KFCausalClockFloorInvariantTrial
open UnifiedTheory.Audit.KFCausalClockFloorTrialClockEnergy
open UnifiedTheory.Audit.KFCausalClockFloorTrialUnitary
open UnifiedTheory.Audit.KFCausalClockFloorTrialMomentum (dampedProfile_eq)
open UnifiedTheory.Audit.KFCausalClockFloorTrialEnergyNorms
open UnifiedTheory.Audit.KFCausalPhysicalGaussianNormalization
open UnifiedTheory.Audit.KFCausalChargeGaussianGeometry
open UnifiedTheory.Audit.KFCausalChargeGaussianIdentities (configurationProfile)
open UnifiedTheory.Audit.KFCausalClockFloorStrongInitialOutput

theorem real_multiplier_pairing {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (m : X → ℝ) (f g : Lp ℂ 2 μ) (hg : g =ᵐ[μ] fun x => (m x:ℂ)*f x) :
    (inner ℂ f g).re = ∫ x, m x*‖f x‖^2 ∂μ := by
  have he := integral_re (L2.integrable_inner (𝕜 := ℂ) f g)
  change (∫ x, (inner ℂ (f x) (g x)).re ∂μ) = (∫ x, inner ℂ (f x) (g x) ∂μ).re at he
  rw [L2.inner_def,← he]
  apply integral_congr_ae
  filter_upwards [hg] with x hx
  rw [hx]
  change (inner ℂ (f x) ((m x:ℂ) • f x)).re = _
  rw [inner_smul_right,inner_self_eq_norm_sq_to_K]
  change ((m x:ℂ)*(‖f x‖:ℂ)^2).re = _
  rw [← Complex.ofReal_pow,← Complex.ofReal_mul,Complex.ofReal_re]

theorem pairing_real_smul {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (A : E →L[ℂ] E) (r : ℝ) (f : E) :
    (inner ℂ (r • f) (A (r • f))).re = r^2*(inner ℂ f (A f)).re := by
  rw [A.map_smul_of_tower]
  have he : inner ℂ (r • f) (r • A f) = (r:ℂ)^2*inner ℂ f (A f) := by
    rw [inner_smul_left_eq_smul,inner_smul_right_eq_smul]
    simp only [Complex.real_smul]
    ring
  rw [he,← Complex.ofReal_pow]
  simp only [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]

theorem drift_clock_bound (ε : ℝ) (hε : 0 < ε) (s : ℝ) : |drift ε (defect ε s)| ≤ 1/ε := by
  apply drift_bound ε _ hε
  constructor
  · exact (defect_positive ε s hε).le
  · rw [defect,div_le_one (clock_positive ε s hε.le)]
    unfold KFCausalClockFloorFlow.clock
    linarith [Real.exp_pos s]

theorem drift_clock_continuous (ε : ℝ) (hε : 0 < ε) : Continuous (fun s => drift ε (defect ε s)) := by
  have hd : Continuous (defect ε) := continuous_const.div (Real.continuous_exp.add continuous_const)
    (fun s => (clock_positive ε s hε.le).ne')
  unfold drift
  fun_prop

def driftMass (ε a : ℝ) : ℝ := ∫ s : ℝ, drift ε (defect ε s)*‖dampedClockFunction ε a s‖^2

theorem driftMass_integrable (ε a : ℝ) (hε : 0 < ε) (ha : 0 < a) :
    Integrable (fun s : ℝ => drift ε (defect ε s)*‖dampedClockFunction ε a s‖^2) := by
  have hd := dampedClockFunction_memLp ε a hε ha
  have hi := (memLp_two_iff_integrable_sq_norm hd.1).mp hd
  apply (hi.const_mul (1/ε)).mono'
    ((drift_clock_continuous ε hε).aestronglyMeasurable.mul (hd.1.norm.pow 2))
  filter_upwards [] with s
  dsimp only [Pi.mul_apply,Pi.pow_apply]
  rw [norm_mul,Real.norm_eq_abs,Real.norm_eq_abs,
    abs_of_nonneg (sq_nonneg ‖dampedClockFunction ε a s‖)]
  exact mul_le_mul_of_nonneg_right (drift_clock_bound ε hε s) (sq_nonneg _)

theorem damped_drift_pairing (ε a hbar : ℝ) (hε : 0 < ε) (ha : 0 < a) (hh : hbar ≠ 0) :
    (inner ℂ (dampedState ε a hbar hε ha hh)
      (driftOperator ε hε (dampedState ε a hbar hε ha hh))).re =
        driftMass ε a*gaussianMass (groundWidth hbar) (neutralWidth hbar) := by
  rw [real_multiplier_pairing volume _ _ _ (driftOperator_coe ε hε _)]
  calc
    _ = ∫ x : Configuration, (drift ε (defect ε x.1)*‖dampedClockFunction ε a x.1‖^2)*
        ‖physicalGaussian (groundWidth hbar) (neutralWidth hbar) x.2‖^2 := by
      apply integral_congr_ae
      filter_upwards [dampedState_coe ε a hbar hε ha hh] with x hx
      rw [hx,dampedProfile_eq]
      simp only [configurationProfile,norm_mul,mul_pow]
      ring
    _ = _ := by
      rw [Measure.volume_eq_prod ℝ Transverse,
        integral_prod_mul (fun s : ℝ => drift ε (defect ε s)*‖dampedClockFunction ε a s‖^2)
          (fun x : Transverse => ‖physicalGaussian (groundWidth hbar) (neutralWidth hbar) x‖^2),
        physicalGaussian_mass _ _ (groundWidth_positive hbar hh)]
      rfl

theorem normalizedDamped_drift_pairing (ε a hbar : ℝ) (hε : 0 < ε) (ha : 0 < a) (hh : hbar ≠ 0) :
    (inner ℂ (normalizedDamped ε a hbar hε ha hh)
      (driftOperator ε hε (normalizedDamped ε a hbar hε ha hh))).re = driftMass ε a/clockMass ε a := by
  rw [normalizedDamped,pairing_real_smul,inv_pow,trial_norm_square,damped_drift_pairing,← div_eq_inv_mul]
  exact mul_div_mul_right _ _ (gaussianMass_positive _ _ (groundWidth_positive hbar hh)
    (neutralWidth_positive hbar hh)).ne'

theorem normalizedOutput_drift_limit (ε a : ℝ) (hε : 0 < ε) (ha : 0 < a)
    (h : ℕ → ℝ) (hh : ∀ n, h n ≠ 0) (hb : ∀ n, |h n| ≤ 2*Real.pi*ε/3)
    (hz : Tendsto h atTop (𝓝 0)) :
    Tendsto (fun n => (inner ℂ (normalizedOutput ε a (h n) hε ha (hh n) (hb n))
      (driftOperator ε hε (normalizedOutput ε a (h n) hε ha (hh n) (hb n)))).re)
      atTop (𝓝 (driftMass ε a/clockMass ε a)) := by
  have hc := bounded_output_pairing_limit ε a hε ha h hh hb hz (driftOperator ε hε)
  have hr := (Complex.continuous_re.tendsto (0:ℂ)).comp hc
  simp only [Function.comp_def,Complex.sub_re,Complex.zero_re,normalizedDamped_drift_pairing] at hr
  have ht := hr.add_const (driftMass ε a/clockMass ε a)
  simpa only [sub_add_cancel,zero_add] using ht

#print axioms real_multiplier_pairing
#print axioms pairing_real_smul
#print axioms drift_clock_bound
#print axioms drift_clock_continuous
#print axioms driftMass_integrable
#print axioms damped_drift_pairing
#print axioms normalizedDamped_drift_pairing
#print axioms normalizedOutput_drift_limit

end
end UnifiedTheory.Audit.KFCausalClockFloorInitialDriftPairing
