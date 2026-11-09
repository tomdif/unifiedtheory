/- Every physical radial moment, including one clock moment, is L2 on
 the existing closed imaginary strip. No smaller strip is required. -/
import UnifiedTheory.Audit.KFCausalRadialMultipliers
import UnifiedTheory.Audit.KFCausalGaussianClockMoment
import UnifiedTheory.Audit.KFCausalShiftedClockAmplitude

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 800000

namespace UnifiedTheory.Audit.KFCausalShiftedGaussianRadialMoments
noncomputable section
open MeasureTheory
open KFCausalCoupledLongitudinalFlow (Configuration)
open KFCausalClockFloorRelativeShift
open KFCausalRelativeGaussianDifferential (profile profile_smooth)
open KFCausalShiftedGaussianPhysicalProfile (clockAmplitude clockAmplitude_smooth)
open KFCausalImaginaryShearInterpolation (path path_one)
open KFCausalImaginaryShearPathBounds (envelope path_bound)
open KFCausalShearRadius (radius radius_positive)

theorem relative_strip (ε y : ℝ) (hε : 0 < ε) (hy : |y| ≤ Real.pi*ε/3) (s : ℝ) :
    ‖relative ε y s‖ ≤ Real.pi/3 :=
  (relative_bound ε y s hε hy).trans ((div_le_iff₀ hε).mpr (by linarith))

theorem profile_radius_memLp (ε y : ℝ) (A : ℝ → ℂ) (hε : 0 < ε)
    (hy : |y| ≤ Real.pi*ε/3) (hA : ContDiff ℝ 1 A) (hAm : MemLp A 2 volume)
    (α β : ℝ) (hα : 0 < α) (hβ : 0 < β) (hw : 32*β ≤ α) (b : Fin 5 → ℂ) (n : ℕ) :
    MemLp (fun x : Configuration => ((radius x.2^n:ℝ):ℂ)*profile A (scale ε y) α β b x) 2 volume := by
  have hc : Continuous (fun x : Configuration => ((radius x.2^n:ℝ):ℂ)) := by unfold radius; fun_prop
  apply (KFCausalGaussianAllRadiusMoments.radius_envelope_memLp A hAm α β hα hβ b n).of_le
    (hc.mul (profile_smooth A (scale ε y) hA (scale_smooth ε y hε hy) α β b).continuous).aestronglyMeasurable
  filter_upwards [] with x
  have hb := path_bound A (relative ε y) (relative_strip ε y hε hy) α β hα hβ hw b 1
    (by constructor <;> norm_num) x
  simp only [path_one] at hb
  have hb' : ‖profile A (scale ε y) α β b x‖ ≤ ‖envelope A α β b x‖ := hb
  simpa only [Pi.mul_apply,norm_mul] using mul_le_mul_of_nonneg_left hb' (norm_nonneg (((radius x.2^n:ℝ):ℂ)))

theorem amplitude_moment_memLp (ε a p y : ℝ) (hε : 0 < ε) (ha : 0 < a)
    (hy : |y| ≤ Real.pi*ε/3) :
    MemLp (fun s => argument ε y s*clockAmplitude ε a p y s) 2 volume := by
  have hm := KFCausalShiftedClockAmplitude.clockAmplitude_memLp ε (a/2) p y hε (by positivity) hy
  have hc := (argument_smooth ε y).continuous.mul (clockAmplitude_smooth ε a p y hε hy).continuous
  apply (hm.const_mul (KFCausalGaussianClockMoment.bound a y:ℂ)).of_le hc.aestronglyMeasurable
  filter_upwards [] with s
  have he : clockAmplitude ε a p y s =
      KFCausalClockFloorFullGaussian.clockFactor (a/2) (argument ε y s)*clockAmplitude ε (a/2) p y s := by
    unfold clockAmplitude
    rw [KFCausalGaussianClockMoment.factor_split a]
    ring
  simp only [Pi.mul_apply]
  rw [he,← mul_assoc]
  have hb := mul_le_mul_of_nonneg_right
    (KFCausalGaussianClockMoment.moment_bound a (KFCausalRegularizedLongitudinalChart.chart ε s) y ha)
    (norm_nonneg (clockAmplitude ε (a/2) p y s))
  simpa only [norm_mul,Complex.norm_real,Real.norm_eq_abs,
    abs_of_pos (KFCausalGaussianClockMoment.bound_positive a y ha)] using hb

theorem shifted_radius_memLp (ε a α β p y : ℝ) (b : Fin 5 → ℂ)
    (hε : 0 < ε) (ha : 0 < a) (hα : 0 < α) (hβ : 0 < β) (hw : 32*β ≤ α)
    (hy : |y| ≤ Real.pi*ε/3) (n : ℕ) :
    MemLp (fun x : Configuration => ((radius x.2^n:ℝ):ℂ)*
      profile (clockAmplitude ε a p y) (scale ε y) α β b x) 2 volume :=
  profile_radius_memLp ε y _ hε hy (clockAmplitude_smooth ε a p y hε hy)
    (KFCausalShiftedClockAmplitude.clockAmplitude_memLp ε a p y hε ha hy) α β hα hβ hw b n

theorem shifted_moment_radius_memLp (ε a α β p y : ℝ) (b : Fin 5 → ℂ)
    (hε : 0 < ε) (ha : 0 < a) (hα : 0 < α) (hβ : 0 < β) (hw : 32*β ≤ α)
    (hy : |y| ≤ Real.pi*ε/3) (n : ℕ) :
    MemLp (fun x : Configuration => ((radius x.2^n:ℝ):ℂ)*
      (argument ε y x.1*profile (clockAmplitude ε a p y) (scale ε y) α β b x)) 2 volume := by
  have hm := profile_radius_memLp ε y (fun s => argument ε y s*clockAmplitude ε a p y s) hε hy
    ((argument_smooth ε y).mul (clockAmplitude_smooth ε a p y hε hy))
    (amplitude_moment_memLp ε a p y hε ha hy) α β hα hβ hw b n
  convert hm using 1
  funext x
  unfold profile
  ring

#print axioms relative_strip
#print axioms profile_radius_memLp
#print axioms amplitude_moment_memLp
#print axioms shifted_radius_memLp
#print axioms shifted_moment_radius_memLp
end
end UnifiedTheory.Audit.KFCausalShiftedGaussianRadialMoments
