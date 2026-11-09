/- The clock amplitude of the shifted physical Gaussian is square
integrable by comparison with the previously constructed clock trial.
The estimate keeps the inverse square-root clock factor explicit. -/
import UnifiedTheory.Audit.KFCausalShiftedGaussianPhysicalProfile

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 500000

namespace UnifiedTheory.Audit.KFCausalShiftedClockAmplitude
noncomputable section
open MeasureTheory
open UnifiedTheory.Audit.KFCausalRegularizedLongitudinalChart (chart)
open UnifiedTheory.Audit.KFCausalClockFloorChargeTrialBridge
open UnifiedTheory.Audit.KFCausalClockFloorInvariantTrial (clockFunction clockFunction_memLp)
open UnifiedTheory.Audit.KFCausalClockFloorCoherentStrip (clockPhase clockPhase_bound)
open UnifiedTheory.Audit.KFCausalClockFloorFullGaussian (clockFactor clockFactor_norm)
open UnifiedTheory.Audit.KFCausalClockFloorRelativeShift
open UnifiedTheory.Audit.KFCausalShiftedGaussianPhysicalProfile (clockAmplitude clockAmplitude_smooth)

def bound (ε a p y : ℝ) : ℝ := (Real.sqrt ε)⁻¹*Real.exp (|p| *Real.pi/3+a*y^2)

theorem bound_positive (ε a p y : ℝ) (hε : 0 < ε) : 0 < bound ε a p y := by
  unfold bound
  positivity

theorem clockFunction_norm (ε a s : ℝ) (hε : 0 < ε) :
    ‖clockFunction ε a s‖ = amplitude ε s*Real.sqrt (Real.exp s+ε)*
      Real.exp (-a*(chart ε s)^2) := by
  rw [clockFunction_factor ε a s hε,norm_mul,norm_mul]
  have hg := clockFactor_norm a (chart ε s) 0
  simp only [Complex.ofReal_zero,zero_mul,add_zero,zero_pow (by norm_num : (2:ℕ) ≠ 0),
    sub_zero] at hg
  rw [hg]
  simp only [Complex.norm_real,Real.norm_eq_abs,
    abs_of_pos (amplitude_positive ε s hε),abs_of_nonneg (Real.sqrt_nonneg _)]

theorem amplitude_gaussian_bound (ε a s : ℝ) (hε : 0 < ε) :
    amplitude ε s*Real.exp (-a*(chart ε s)^2) ≤
      (Real.sqrt ε)⁻¹*‖clockFunction ε a s‖ := by
  have hr : Real.sqrt ε ≤ Real.sqrt (Real.exp s+ε) :=
    Real.sqrt_le_sqrt (by linarith [Real.exp_pos s])
  have hm := mul_le_mul_of_nonneg_left hr
    (mul_nonneg (amplitude_positive ε s hε).le (Real.exp_pos (-a*(chart ε s)^2)).le)
  rw [clockFunction_norm ε a s hε]
  rw [inv_mul_eq_div]
  apply (le_div_iff₀ (Real.sqrt_pos.mpr hε)).mpr
  convert hm using 1
  ring

theorem clockAmplitude_bound (ε a p y s : ℝ) (hε : 0 < ε)
    (hy : |y| ≤ Real.pi*ε/3) :
    ‖clockAmplitude ε a p y s‖ ≤ bound ε a p y*‖clockFunction ε a s‖ := by
  have hi := KFCausalClockInverseStripBounds.inverse_im_third_strip ε hε
    (argument ε y s) (by simpa [argument] using hy)
  have hp := clockPhase_bound p (inverse ε y s) hi
  have ha := amplitude_gaussian_bound ε a s hε
  have he : Real.exp (-a*((chart ε s)^2-y^2)) =
      Real.exp (a*y^2)*Real.exp (-a*(chart ε s)^2) := by
    rw [← Real.exp_add]
    congr 1
    ring
  simp only [clockAmplitude,norm_mul,Complex.norm_real,Real.norm_eq_abs,
    abs_of_pos (amplitude_positive ε s hε),argument,clockFactor_norm,he]
  calc
    _ ≤ (Real.exp (|p| *Real.pi/3)*Real.exp (a*y^2))*
        (amplitude ε s*Real.exp (-a*(chart ε s)^2)) := by
      have hm := mul_le_mul_of_nonneg_left hp (amplitude_positive ε s hε).le
      have hn := mul_le_mul_of_nonneg_right hm
        (mul_nonneg (Real.exp_pos (a*y^2)).le (Real.exp_pos (-a*(chart ε s)^2)).le)
      convert hn using 1
      ring
    _ ≤ _ := by
      have hm := mul_le_mul_of_nonneg_left ha
        (mul_nonneg (Real.exp_pos (|p| *Real.pi/3)).le (Real.exp_pos (a*y^2)).le)
      rw [← Real.exp_add] at hm
      rw [← Real.exp_add]
      convert hm using 1
      unfold bound
      ring

theorem clockAmplitude_memLp (ε a p y : ℝ) (hε : 0 < ε) (ha : 0 < a)
    (hy : |y| ≤ Real.pi*ε/3) : MemLp (clockAmplitude ε a p y) 2 volume := by
  apply ((clockFunction_memLp ε a hε ha).const_mul (bound ε a p y:ℂ)).of_le
    (clockAmplitude_smooth ε a p y hε hy).continuous.aestronglyMeasurable
  filter_upwards [] with s
  simpa only [norm_mul,Complex.norm_real,Real.norm_eq_abs,
    abs_of_pos (bound_positive ε a p y hε)] using clockAmplitude_bound ε a p y s hε hy

#print axioms bound_positive
#print axioms clockFunction_norm
#print axioms amplitude_gaussian_bound
#print axioms clockAmplitude_bound
#print axioms clockAmplitude_memLp
end
end UnifiedTheory.Audit.KFCausalShiftedClockAmplitude
