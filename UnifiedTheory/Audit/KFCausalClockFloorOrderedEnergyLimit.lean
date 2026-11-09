/- The actual ordered exponential energy of the normalized physical trial
converges to its inverse-clock energy as hbar tends to zero. Width rescaling
and two-sided exponential Fourier moments justify this unbounded limit. -/
import UnifiedTheory.Audit.KFCausalExponentialEnergyContinuity
import UnifiedTheory.Audit.KFCausalClockFloorGaussianRescaling

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1200000

namespace UnifiedTheory.Audit.KFCausalClockFloorOrderedEnergyLimit
noncomputable section
open MeasureTheory Filter
open scoped Topology
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalClockFloorShearBounds (Grouped)
open UnifiedTheory.Audit.KFCausalClockFloorFullGaussian
open UnifiedTheory.Audit.KFCausalClockFloorGaussianEnergy
open UnifiedTheory.Audit.KFCausalClockFloorFullFourierEnergy (exponentialFourier_square)
open UnifiedTheory.Audit.KFCausalClockFloorGaussianRescaling
open UnifiedTheory.Audit.KFCausalPhysicalGaussianNormalization
open UnifiedTheory.Audit.KFCausalChargeGaussianGeometry
open UnifiedTheory.Audit.KFCausalClockFloorInvariantTrial
open UnifiedTheory.Audit.KFCausalClockFloorTrialEnergyNorms
open UnifiedTheory.Audit.KFCausalClockFloorTrialClockEnergy
open UnifiedTheory.Audit.KFCausalClockFloorTrialMomentum
open UnifiedTheory.Audit.KFCausalClockFloorTrialUnitary
open UnifiedTheory.Audit.KFCausalClockFloorTrialSpectralDomain
open UnifiedTheory.Audit.KFCausalClockFloorShiftedOutput

def spectralEnergy (ε a α β hbar : ℝ) : ℝ :=
  ∫ w : ℝ × Grouped, Real.exp (2*Real.pi*hbar*w.1)*‖fourierLine ε a α β 0 w‖^2

theorem spectralEnergy_continuousAt_zero (ε a α β : ℝ) (hε : 0 < ε) (ha : 0 < a)
    (hα : 0 < α) (hβ : 0 < β) (hw : 32*β ≤ α) :
    ContinuousAt (spectralEnergy ε a α β) 0 := by
  let r : ℝ := 2*Real.pi*ε/3
  have hr : 0 < r := by dsimp [r]; positivity
  have hp := longitudinal_density_integrable ε a α β r hε ha hα hβ hw
    (by rw [abs_of_pos hr])
  have hm := longitudinal_density_integrable ε a α β (-r) hε ha hα hβ hw
    (by rw [abs_neg,abs_of_pos hr])
  have hmeas := fourierLine_aestronglyMeasurable ε a α β 0 hε (by simp; positivity)
  have hc := KFCausalExponentialEnergyContinuity.integral_continuousAt_zero volume
    (fun w : ℝ × Grouped => 2*Real.pi*w.1) (fun w => ‖fourierLine ε a α β 0 w‖^2)
    (measurable_const.mul measurable_fst) (hmeas.norm.pow 2) (fun _ => sq_nonneg _) r hr
    (by convert hp using 1; funext w; congr 2; ring)
    (by convert hm using 1; funext w; congr 2; ring)
  convert hc using 1
  funext h
  apply integral_congr_ae
  filter_upwards [] with w
  congr 2
  ring

theorem spectralEnergy_eq_line (ε a α β hbar : ℝ) (hε : 0 < ε) (ha : 0 < a)
    (hα : 0 < α) (hβ : 0 < β) (hw : 32*β ≤ α) (hb : |hbar| ≤ 2*Real.pi*ε/3) :
    spectralEnergy ε a α β hbar =
      ∫ z : ℝ × Grouped, ‖line ε a α β (-hbar/2) z‖^2 := by
  unfold spectralEnergy
  simp_rw [← exponentialFourier_square]
  exact exponential_energy_identity ε a α β hbar hε ha hα hβ hw hb

theorem ground_line_mass_ratio (ε a hbar y : ℝ) (hε : 0 < ε) (ha : 0 < a)
    (hh : hbar ≠ 0) (hy : |y| ≤ Real.pi*ε/3) :
    (∫ z : ℝ × Grouped, ‖line ε a (groundWidth hbar) (neutralWidth hbar) y z‖^2)/
        gaussianMass (groundWidth hbar) (neutralWidth hbar) =
      (∫ z : ℝ × Grouped, ‖line ε a (groundWidth 1) (neutralWidth 1) y z‖^2)/
        gaussianMass (groundWidth 1) (neutralWidth 1) := by
  let c := Real.sqrt (2*groundWidth hbar)
  have hc : 0 < c := Real.sqrt_pos.mpr (by positivity [groundWidth_positive hbar hh])
  have hc2 : c^2 = 2*groundWidth hbar := Real.sq_sqrt (by positivity [groundWidth_positive hbar hh])
  have hα : c^2*groundWidth 1 = groundWidth hbar := by
    rw [hc2]
    norm_num [groundWidth]
    ring
  have hβ : c^2*neutralWidth 1 = neutralWidth hbar := by
    rw [neutralWidth,neutralWidth,← mul_div_assoc,hα]
  simpa only [hα,hβ] using line_mass_ratio ε a (groundWidth 1) (neutralWidth 1) y c hε ha
    (groundWidth_positive 1 one_ne_zero) (neutralWidth_positive 1 one_ne_zero)
    (neutralWidth_bound 1) hy hc

theorem dampedState_mass (ε a hbar : ℝ) (hε : 0 < ε) (ha : 0 < a) (hh : hbar ≠ 0) :
    ‖dampedState ε a hbar hε ha hh‖^2 =
      dampedMass ε a*gaussianMass (groundWidth hbar) (neutralWidth hbar) := by
  have he := norm_square_of_representative _ _ (dampedProfile_memLp ε a hbar hε ha hh)
    (dampedState_coe ε a hbar hε ha hh)
  rw [dampedProfile_eq] at he
  exact he.trans (profile_square_integral _ _ (groundWidth_positive hbar hh)
    (neutralWidth_positive hbar hh) _ (dampedClockFunction_memLp ε a hε ha))

theorem ground_line_zero_mass (ε a hbar : ℝ) (hε : 0 < ε) (ha : 0 < a) (hh : hbar ≠ 0) :
    (∫ z : ℝ × Grouped, ‖line ε a (groundWidth hbar) (neutralWidth hbar) 0 z‖^2) =
      dampedMass ε a*gaussianMass (groundWidth hbar) (neutralWidth hbar) := by
  have he := straightenedState_square_integral ε a hbar hε ha hh
  rw [KFCausalClockFloorChargeTrialBridge.dressedTrial_eq] at he
  exact he.symm.trans (dampedState_mass ε a hbar hε ha hh)

def orderedRatio (ε a hbar : ℝ) : ℝ :=
  spectralEnergy ε a (groundWidth 1) (neutralWidth 1) hbar /
    (clockMass ε a*gaussianMass (groundWidth 1) (neutralWidth 1))

theorem orderedRatio_continuousAt_zero (ε a : ℝ) (hε : 0 < ε) (ha : 0 < a) :
    ContinuousAt (orderedRatio ε a) 0 :=
  (spectralEnergy_continuousAt_zero ε a _ _ hε ha (groundWidth_positive 1 one_ne_zero)
    (neutralWidth_positive 1 one_ne_zero) (neutralWidth_bound 1)).div_const _

theorem orderedRatio_zero (ε a : ℝ) (hε : 0 < ε) (ha : 0 < a) :
    orderedRatio ε a 0 = dampedMass ε a/clockMass ε a := by
  rw [orderedRatio,spectralEnergy_eq_line ε a _ _ 0 hε ha (groundWidth_positive 1 one_ne_zero)
    (neutralWidth_positive 1 one_ne_zero) (neutralWidth_bound 1) (by simp; positivity)]
  simp only [neg_zero,zero_div]
  rw [ground_line_zero_mass ε a 1 hε ha one_ne_zero]
  exact mul_div_mul_right _ _ (gaussianMass_positive _ _ (groundWidth_positive 1 one_ne_zero)
    (neutralWidth_positive 1 one_ne_zero)).ne'

theorem ordered_output_ratio (ε a hbar : ℝ) (hε : 0 < ε) (ha : 0 < a)
    (hh : hbar ≠ 0) (hb : |hbar| ≤ 2*Real.pi*ε/3) (g : Hilbert)
    (hg : (trialState ε a hbar hε ha hh,g) ∈ (orderedExponential ε hε hbar).graph) :
    ‖g‖^2/‖trialState ε a hbar hε ha hh‖^2 = orderedRatio ε a hbar := by
  have he := (orderedExponential ε hε hbar).mem_graph_snd_inj' hg
    (trialState_shifted_graph ε a hbar hε ha hh hb) rfl
  dsimp only [Prod.snd] at he
  rw [he,trial_norm_square,shiftedOutput,gaussianState_mass,orderedRatio,
    spectralEnergy_eq_line ε a _ _ hbar hε ha (groundWidth_positive 1 one_ne_zero)
      (neutralWidth_positive 1 one_ne_zero) (neutralWidth_bound 1) hb]
  rw [mul_comm (clockMass ε a),← div_div,mul_comm (clockMass ε a),← div_div,
    ground_line_mass_ratio ε a hbar (-hbar/2) hε ha hh (shift_bound ε hbar hb)]

theorem ordered_output_ratio_tendsto (ε a : ℝ) (hε : 0 < ε) (ha : 0 < a)
    (h : ℕ → ℝ) (hh : ∀ n, h n ≠ 0) (hb : ∀ n, |h n| ≤ 2*Real.pi*ε/3)
    (hz : Tendsto h atTop (𝓝 0)) (g : ℕ → Hilbert)
    (hg : ∀ n, (trialState ε a (h n) hε ha (hh n),g n) ∈ (orderedExponential ε hε (h n)).graph) :
    Tendsto (fun n => ‖g n‖^2/‖trialState ε a (h n) hε ha (hh n)‖^2) atTop
      (𝓝 (dampedMass ε a/clockMass ε a)) := by
  simp_rw [ordered_output_ratio ε a _ hε ha (hh _) (hb _) _ (hg _)]
  rw [← orderedRatio_zero ε a hε ha]
  exact (orderedRatio_continuousAt_zero ε a hε ha).tendsto.comp hz

#print axioms spectralEnergy_continuousAt_zero
#print axioms spectralEnergy_eq_line
#print axioms ground_line_mass_ratio
#print axioms dampedState_mass
#print axioms ground_line_zero_mass
#print axioms orderedRatio_continuousAt_zero
#print axioms orderedRatio_zero
#print axioms ordered_output_ratio
#print axioms ordered_output_ratio_tendsto

end
end UnifiedTheory.Audit.KFCausalClockFloorOrderedEnergyLimit
