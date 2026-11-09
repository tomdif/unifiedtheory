/- Clock energy and weak-response weights are integrable for every positive
Gaussian clock width and real frequency in the established closed strip. -/
import UnifiedTheory.Audit.KFCausalShiftedClockAmplitude
import UnifiedTheory.Audit.KFCausalGaussianClockMoment
import UnifiedTheory.Audit.KFCausalPositiveKernelClockResponse

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1800000

namespace UnifiedTheory.Audit.KFCausalGaussianClockResponseIntegrability
noncomputable section
open MeasureTheory
open KFCausalShiftedGaussianPhysicalProfile (clockAmplitude clockAmplitude_smooth)
open KFCausalShiftedClockAmplitude (clockAmplitude_memLp)
open KFCausalClockFloorRelativeShift (argument argument_smooth)
open KFCausalClockFloorFullGaussian (clockFactor)
open KFCausalShiftedGaussianLongitudinalDifferential
  (inverseClock inverseClock_continuous inverseClock_bound)
open KFCausalClockResponseTransport (weakSlope)
open KFCausalPositiveKernelClockResponse (clockWeight)

private theorem bounded_mul (c f : ℝ → ℂ) (hc : Continuous c) (hf : MemLp f 2 volume)
    (M : ℝ) (hb : ∀ s, ‖c s‖ ≤ M) : MemLp (fun s => c s*f s) 2 volume := by
  apply hf.of_le_mul (c := M) (hc.aestronglyMeasurable.mul hf.aestronglyMeasurable)
  filter_upwards [] with s
  change ‖c s*f s‖ ≤ M*‖f s‖
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_right (hb s) (norm_nonneg _)

variable (ε a p y : ℝ) (hε : 0 < ε) (ha : 0 < a) (hy : |y| ≤ Real.pi*ε/3)

include hε ha hy

theorem argument_amplitude_memLp :
    MemLp (fun s => argument ε y s*clockAmplitude ε a p y s) 2 volume := by
  have hc : Continuous (fun s => argument ε y s*clockFactor (a/2) (argument ε y s)) := by
    unfold clockFactor
    exact (argument_smooth ε y).continuous.mul
      ((continuous_const.mul ((argument_smooth ε y).continuous.pow 2)).cexp)
  have hm := bounded_mul _ _ hc (clockAmplitude_memLp ε (a/2) p y hε (by positivity) hy)
    (KFCausalGaussianClockMoment.bound a y)
    (fun s => KFCausalGaussianClockMoment.moment_bound a
      (KFCausalRegularizedLongitudinalChart.chart ε s) y ha)
  convert hm using 1
  funext s
  unfold clockAmplitude
  rw [KFCausalGaussianClockMoment.factor_split a]
  ring

theorem weak_amplitude_memLp :
    MemLp (fun s => weakSlope ε a p y s*clockAmplitude ε a p y s) 2 volume := by
  have hA := clockAmplitude_memLp ε a p y hε ha hy
  have hi := bounded_mul (inverseClock ε y) _ (inverseClock_continuous ε y hε hy) hA
    (1/ε) (fun s => inverseClock_bound ε y s hε hy)
  have hii := bounded_mul (inverseClock ε y) _ (inverseClock_continuous ε y hε hy) hi
    (1/ε) (fun s => inverseClock_bound ε y s hε hy)
  convert ((hi.const_mul ((p:ℂ)*Complex.I-1)).sub
    ((argument_amplitude_memLp ε a p y hε ha hy).const_mul (2*(a:ℂ)))).add
    ((hi.sub (hii.const_mul (ε:ℂ))).const_mul (1/2:ℂ)) using 1
  funext s
  simp only [weakSlope,Pi.add_apply,Pi.sub_apply]
  ring

theorem clockWeight_integrable : Integrable (clockWeight ε a p y) volume :=
  (memLp_two_iff_integrable_sq_norm (clockAmplitude_memLp ε a p y hε ha hy).1).mp
    (clockAmplitude_memLp ε a p y hε ha hy)

theorem weakWeight_integrable :
    Integrable (fun s => 2*(weakSlope ε a p y s).re*clockWeight ε a p y s) volume := by
  have hi := ((clockAmplitude_memLp ε a p y hε ha hy).star.integrable_mul
    (weak_amplitude_memLp ε a p y hε ha hy)).re.const_mul 2
  convert hi using 1
  funext s
  change 2*(weakSlope ε a p y s).re*clockWeight ε a p y s =
    2*(star (clockAmplitude ε a p y s)*(weakSlope ε a p y s*clockAmplitude ε a p y s)).re
  simp only [clockWeight,Complex.star_def,Complex.mul_re,Complex.mul_im,
    Complex.conj_re,Complex.conj_im,Complex.sq_norm,Complex.normSq_apply]
  ring

#print axioms argument_amplitude_memLp
#print axioms weak_amplitude_memLp
#print axioms clockWeight_integrable
#print axioms weakWeight_integrable
end
end UnifiedTheory.Audit.KFCausalGaussianClockResponseIntegrability
