/- Exact transverse rescaling of the sheared analytic Gaussian and its
energy integral. This keeps the true longitudinal shear and factor order. -/
import UnifiedTheory.Audit.KFCausalClockFloorTrialEnergyNorms
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

namespace UnifiedTheory.Audit.KFCausalClockFloorGaussianRescaling
noncomputable section
open MeasureTheory
open UnifiedTheory.Audit.KFCausalClockFloorShearBounds
open UnifiedTheory.Audit.KFCausalClockFloorFullGaussian
open UnifiedTheory.Audit.KFCausalPhysicalGaussianNormalization
open UnifiedTheory.Audit.KFCausalTransverseDilationFlow (Transverse)
open UnifiedTheory.Audit.KFCausalChargeGaussianGeometry

theorem quadratic_smul (α β c : ℝ) (z : ℂ) (x : Grouped) :
    quadratic α β z (c • x.1) (c*x.2) = quadratic (c^2*α) (c^2*β) z x.1 x.2 := by
  have hs : squared (c • x.1) = c^2*squared x.1 := by
    simp only [squared,Pi.smul_apply,smul_eq_mul,mul_pow,Finset.mul_sum]
  have hm : mix (c • x.1) = c*mix x.1 := by simp [mix,mul_add]
  simp only [quadratic,hs,hm,Complex.ofReal_mul,Complex.ofReal_pow]
  ring

theorem line_smul (ε a α β y c q : ℝ) (x : Grouped) :
    line ε a α β y (q,c • x) = line ε a (c^2*α) (c^2*β) y (q,x) := by
  simp only [line,trial,packet,Prod.smul_fst,Prod.smul_snd,smul_eq_mul,quadratic_smul]

theorem line_mass_smul (ε a α β y c : ℝ) (hε : 0 < ε) (ha : 0 < a)
    (hα : 0 < α) (hβ : 0 < β) (hw : 32*β ≤ α)
    (hy : |y| ≤ Real.pi*ε/3) (hc : 0 < c) :
    (∫ z : ℝ × Grouped, ‖line ε a (c^2*α) (c^2*β) y z‖^2) =
      (c^5)⁻¹*(∫ z : ℝ × Grouped, ‖line ε a α β y z‖^2) := by
  letI : Measure.IsAddHaarMeasure (volume : Measure Grouped) :=
    Measure.prod.instIsAddHaarMeasure _ _
  have hr : Module.finrank ℝ Grouped = 5 := by
    simp [Grouped,Charged,Module.finrank_prod]
  have h0 := line_memLp ε a α β y hε ha hα hβ hw hy
  have h1 := line_memLp ε a (c^2*α) (c^2*β) y hε ha
    (by positivity) (by positivity)
    (by nlinarith only [mul_le_mul_of_nonneg_left hw (sq_nonneg c)]) hy
  have hi0 := (memLp_two_iff_integrable_sq_norm h0.1).mp h0
  have hi1 := (memLp_two_iff_integrable_sq_norm h1.1).mp h1
  rw [Measure.volume_eq_prod ℝ Grouped] at hi0 hi1 ⊢
  rw [integral_prod _ hi1,integral_prod _ hi0,← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with q
  simp_rw [← line_smul]
  simpa only [hr,smul_eq_mul] using
    (Measure.integral_comp_smul_of_nonneg (volume : Measure Grouped)
      (fun x => ‖line ε a α β y (q,x)‖^2) c (hR := hc.le))

theorem gaussianMass_smul (α β c : ℝ) (hα : 0 < α) (hβ : 0 < β) (hc : 0 < c) :
    gaussianMass (c^2*α) (c^2*β) = (c^5)⁻¹*gaussianMass α β := by
  have hs : Real.sqrt (Real.pi/(2*(c^2*β))) = Real.sqrt (Real.pi/(2*β))/c := by
    rw [show Real.pi/(2*(c^2*β)) = (Real.pi/(2*β))/c^2 by field_simp,
      Real.sqrt_div (by positivity),Real.sqrt_sq hc.le]
  unfold gaussianMass
  rw [hs]
  field_simp

theorem line_mass_ratio (ε a α β y c : ℝ) (hε : 0 < ε) (ha : 0 < a)
    (hα : 0 < α) (hβ : 0 < β) (hw : 32*β ≤ α)
    (hy : |y| ≤ Real.pi*ε/3) (hc : 0 < c) :
    (∫ z : ℝ × Grouped, ‖line ε a (c^2*α) (c^2*β) y z‖^2)/gaussianMass (c^2*α) (c^2*β) =
      (∫ z : ℝ × Grouped, ‖line ε a α β y z‖^2)/gaussianMass α β := by
  rw [line_mass_smul ε a α β y c hε ha hα hβ hw hy hc,gaussianMass_smul α β c hα hβ hc]
  exact mul_div_mul_left _ _ (inv_ne_zero (pow_ne_zero 5 hc.ne'))

#print axioms quadratic_smul
#print axioms line_smul
#print axioms line_mass_smul
#print axioms gaussianMass_smul
#print axioms line_mass_ratio

end
end UnifiedTheory.Audit.KFCausalClockFloorGaussianRescaling
