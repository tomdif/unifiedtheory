/- Exact rescaling of differences of sheared Gaussian outputs, including
identification of the unshifted output with the true inverse-clock action. -/
import UnifiedTheory.Audit.KFCausalClockFloorGaussianDifferenceEnergy

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1200000

namespace UnifiedTheory.Audit.KFCausalClockFloorGaussianDifferenceRescaling
noncomputable section
open MeasureTheory Filter
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalCoupledLongitudinalFlow (Configuration)
open UnifiedTheory.Audit.KFCausalClockFloorShearBounds (Grouped Charged)
open UnifiedTheory.Audit.KFCausalClockFloorFullGaussian
open UnifiedTheory.Audit.KFCausalClockFloorShiftedOutput
open UnifiedTheory.Audit.KFCausalClockFloorUnitaryCoordinates (coordinates)
open UnifiedTheory.Audit.KFCausalClockFloorGroupedCoordinates
open UnifiedTheory.Audit.KFCausalClockFloorFourierCoordinates (coupledFourier)
open UnifiedTheory.Audit.KFCausalCoupledFunctionEnergy (toLp_square_integral)
open UnifiedTheory.Audit.KFCausalClockFloorGaussianRescaling
open UnifiedTheory.Audit.KFCausalClockFloorGaussianDifferenceEnergy
open UnifiedTheory.Audit.KFCausalPhysicalGaussianNormalization
open UnifiedTheory.Audit.KFCausalChargeGaussianGeometry
open UnifiedTheory.Audit.KFCausalClockFloorInvariantTrial
open UnifiedTheory.Audit.KFCausalClockFloorTrialUnitary
open UnifiedTheory.Audit.KFCausalClockFloorTrialSpectralDomain
open UnifiedTheory.Audit.KFCausalClockFloorTrialEnergyNorms

def differenceMass (ε a α β y z : ℝ) : ℝ :=
  ∫ x : ℝ × Grouped, ‖line ε a α β y x-line ε a α β z x‖^2

theorem gaussianState_difference_mass (ε a α β y z : ℝ) (hε : 0 < ε) (ha : 0 < a)
    (hα : 0 < α) (hβ : 0 < β) (hw : 32*β ≤ α)
    (hy : |y| ≤ Real.pi*ε/3) (hz : |z| ≤ Real.pi*ε/3) :
    ‖gaussianState ε a α β y hε ha hα hβ hw hy-
      gaussianState ε a α β z hε ha hα hβ hw hz‖^2 = differenceMass ε a α β y z := by
  let p := configurationLine ε a α β y
  let q := configurationLine ε a α β z
  have hp : MemLp p 2 := configurationLine_memLp ε a α β y hε ha hα hβ hw hy
  have hq : MemLp q 2 := configurationLine_memLp ε a α β z hε ha hα hβ hw hz
  have he : hp.toLp p-hq.toLp q = (hp.sub hq).toLp (p-q) := by
    apply Lp.ext
    filter_upwards [Lp.coeFn_sub (hp.toLp p) (hq.toLp q),hp.coeFn_toLp,hq.coeFn_toLp,
      (hp.sub hq).coeFn_toLp] with x hs hx hy hz
    rw [hs,Pi.sub_apply,hx,hy,hz]
    rfl
  change ‖coordinates ε hε (hp.toLp p)-coordinates ε hε (hq.toLp q)‖^2 = _
  rw [← map_sub,(coordinates ε hε).norm_map,he,toLp_square_integral]
  exact grouping_preserves_volume.integral_comp grouping.measurableEmbedding
    (fun x : ℝ × Grouped => ‖line ε a α β y x-line ε a α β z x‖^2)

theorem differenceMass_smul (ε a α β y z c : ℝ) (hε : 0 < ε) (ha : 0 < a)
    (hα : 0 < α) (hβ : 0 < β) (hw : 32*β ≤ α)
    (hy : |y| ≤ Real.pi*ε/3) (hz : |z| ≤ Real.pi*ε/3) (hc : 0 < c) :
    differenceMass ε a (c^2*α) (c^2*β) y z = (c^5)⁻¹*differenceMass ε a α β y z := by
  letI : Measure.IsAddHaarMeasure (volume : Measure Grouped) :=
    Measure.prod.instIsAddHaarMeasure _ _
  have hr : Module.finrank ℝ Grouped = 5 := by simp [Grouped,Charged,Module.finrank_prod]
  have hα' : 0 < c^2*α := by positivity
  have hβ' : 0 < c^2*β := by positivity
  have hw' : 32*(c^2*β) ≤ c^2*α := by
    nlinarith only [mul_le_mul_of_nonneg_left hw (sq_nonneg c)]
  have h0 := (line_memLp ε a α β y hε ha hα hβ hw hy).sub
    (line_memLp ε a α β z hε ha hα hβ hw hz)
  have h1 := (line_memLp ε a (c^2*α) (c^2*β) y hε ha hα' hβ' hw' hy).sub
    (line_memLp ε a (c^2*α) (c^2*β) z hε ha hα' hβ' hw' hz)
  have hi0 := (memLp_two_iff_integrable_sq_norm h0.1).mp h0
  have hi1 := (memLp_two_iff_integrable_sq_norm h1.1).mp h1
  dsimp only [Pi.sub_apply] at hi0 hi1
  unfold differenceMass
  rw [Measure.volume_eq_prod ℝ Grouped] at hi0 hi1 ⊢
  rw [integral_prod _ hi1,integral_prod _ hi0,← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with q
  simp_rw [← line_smul]
  simpa only [hr,smul_eq_mul] using
    (Measure.integral_comp_smul_of_nonneg (volume : Measure Grouped)
      (fun x => ‖line ε a α β y (q,x)-line ε a α β z (q,x)‖^2) c (hR := hc.le))

theorem differenceMass_ratio (ε a α β y z c : ℝ) (hε : 0 < ε) (ha : 0 < a)
    (hα : 0 < α) (hβ : 0 < β) (hw : 32*β ≤ α)
    (hy : |y| ≤ Real.pi*ε/3) (hz : |z| ≤ Real.pi*ε/3) (hc : 0 < c) :
    differenceMass ε a (c^2*α) (c^2*β) y z/gaussianMass (c^2*α) (c^2*β) =
      differenceMass ε a α β y z/gaussianMass α β := by
  rw [differenceMass_smul ε a α β y z c hε ha hα hβ hw hy hz hc,gaussianMass_smul α β c hα hβ hc]
  exact mul_div_mul_left _ _ (inv_ne_zero (pow_ne_zero 5 hc.ne'))

theorem ground_differenceMass_ratio (ε a hbar y z : ℝ) (hε : 0 < ε) (ha : 0 < a)
    (hh : hbar ≠ 0) (hy : |y| ≤ Real.pi*ε/3) (hz : |z| ≤ Real.pi*ε/3) :
    differenceMass ε a (groundWidth hbar) (neutralWidth hbar) y z/
      gaussianMass (groundWidth hbar) (neutralWidth hbar) =
    differenceMass ε a (groundWidth 1) (neutralWidth 1) y z/
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
  simpa only [hα,hβ] using differenceMass_ratio ε a (groundWidth 1) (neutralWidth 1) y z c hε ha
    (groundWidth_positive 1 one_ne_zero) (neutralWidth_positive 1 one_ne_zero)
    (neutralWidth_bound 1) hy hz hc

theorem gaussianState_zero_eq_damped (ε a hbar : ℝ) (hε : 0 < ε) (ha : 0 < a) (hh : hbar ≠ 0) :
    gaussianState ε a (groundWidth hbar) (neutralWidth hbar) 0 hε ha
      (groundWidth_positive hbar hh) (neutralWidth_positive hbar hh) (neutralWidth_bound hbar)
      (by simp; positivity) = dampedState ε a hbar hε ha hh := by
  apply (coupledFourier ε hε).injective
  apply Lp.ext
  filter_upwards [gaussianState_fourier ε a (groundWidth hbar) (neutralWidth hbar) 0 hε ha
      (groundWidth_positive hbar hh) (neutralWidth_positive hbar hh) (neutralWidth_bound hbar)
      (by simp; positivity),dampedState_fourier_coe ε a hbar hε ha hh] with k hg hd
  exact hg.trans hd.symm

theorem ordered_difference_ratio (ε a hbar : ℝ) (hε : 0 < ε) (ha : 0 < a)
    (hh : hbar ≠ 0) (hb : |hbar| ≤ 2*Real.pi*ε/3) :
    ‖shiftedOutput ε a hbar hε ha hh hb-dampedState ε a hbar hε ha hh‖^2/
        ‖trialState ε a hbar hε ha hh‖^2 =
      differenceEnergy ε a (groundWidth 1) (neutralWidth 1) hbar/
        (clockMass ε a*gaussianMass (groundWidth 1) (neutralWidth 1)) := by
  rw [← gaussianState_zero_eq_damped ε a hbar hε ha hh,shiftedOutput,
    gaussianState_difference_mass,trial_norm_square]
  rw [mul_comm (clockMass ε a),← div_div,
    ground_differenceMass_ratio ε a hbar (-hbar/2) 0 hε ha hh (shift_bound ε hbar hb) (by simp; positivity)]
  rw [← gaussianState_difference_mass ε a (groundWidth 1) (neutralWidth 1) (-hbar/2) 0 hε ha
    (groundWidth_positive 1 one_ne_zero) (neutralWidth_positive 1 one_ne_zero) (neutralWidth_bound 1)
    (shift_bound ε hbar hb) (by simp; positivity),
    gaussianState_difference_energy ε a (groundWidth 1) (neutralWidth 1) hbar hε ha
      (groundWidth_positive 1 one_ne_zero) (neutralWidth_positive 1 one_ne_zero) (neutralWidth_bound 1) hb]
  ring

#print axioms gaussianState_difference_mass
#print axioms differenceMass_smul
#print axioms differenceMass_ratio
#print axioms ground_differenceMass_ratio
#print axioms gaussianState_zero_eq_damped
#print axioms ordered_difference_ratio

end
end UnifiedTheory.Audit.KFCausalClockFloorGaussianDifferenceRescaling
