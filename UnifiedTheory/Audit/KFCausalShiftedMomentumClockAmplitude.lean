/- The actual shifted pure-momentum clock amplitude is L2. Its
unbounded chart moment is absorbed by a half-width clock Gaussian. -/
import UnifiedTheory.Audit.KFCausalCorrelatedClusteredPureMomentumLimit
import UnifiedTheory.Audit.KFCausalShiftedClockAmplitude

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1800000

namespace UnifiedTheory.Audit.KFCausalShiftedMomentumClockAmplitude
noncomputable section
open MeasureTheory
open KFCausalShiftedGaussianPhysicalProfile (clockAmplitude clockAmplitude_smooth)
open KFCausalShiftedClockAmplitude (clockAmplitude_memLp)
open KFCausalClockFloorFullGaussian (clockFactor)
open KFCausalClockFloorRelativeShift (argument argument_smooth)
open KFCausalRegularizedLongitudinalChart (chart)
open KFCausalGaussianClockMoment (factor_split moment_bound bound bound_positive)
open KFCausalShiftedGaussianLongitudinalDifferential (inverseClock inverseClock_continuous inverseClock_bound)
open KFCausalClockResponseTransport (weakSlope)

theorem clockAmplitude_half (ε a p y s : ℝ) :
    clockAmplitude ε a p y s = clockFactor (a/2) (argument ε y s)*clockAmplitude ε (a/2) p y s := by
  unfold clockAmplitude
  rw [factor_split a]
  ring

theorem moment_continuous (ε a p y : ℝ) (hε : 0 < ε) (hy : |y| ≤ Real.pi*ε/3) :
    Continuous (fun s => argument ε y s*clockAmplitude ε a p y s) :=
  (argument_smooth ε y).continuous.mul (clockAmplitude_smooth ε a p y hε hy).continuous

theorem moment_memLp (ε a p y : ℝ) (hε : 0 < ε) (ha : 0 < a) (hy : |y| ≤ Real.pi*ε/3) :
    MemLp (fun s => argument ε y s*clockAmplitude ε a p y s) 2 volume := by
  apply ((clockAmplitude_memLp ε (a/2) p y hε (by positivity) hy).const_mul (bound a y:ℂ)).of_le
    (moment_continuous ε a p y hε hy).aestronglyMeasurable
  filter_upwards [] with s
  rw [clockAmplitude_half ε a p y s,← mul_assoc]
  have hm := mul_le_mul_of_nonneg_right (moment_bound a (chart ε s) y ha)
    (norm_nonneg (clockAmplitude ε (a/2) p y s))
  simpa only [argument,norm_mul,Complex.norm_real,Real.norm_eq_abs,
    abs_of_pos (bound_positive a y ha)] using hm

theorem inverse_mul_memLp (ε y : ℝ) (hε : 0 < ε) (hy : |y| ≤ Real.pi*ε/3)
    (g : ℝ → ℂ) (hg : MemLp g 2 volume) :
    MemLp (fun s => inverseClock ε y s*g s) 2 volume := by
  have hm := (inverseClock_continuous ε y hε hy).aestronglyMeasurable.mul hg.aestronglyMeasurable
  apply (hg.const_mul ((1/ε:ℝ):ℂ)).of_le hm
  filter_upwards [] with s
  simp only [Pi.mul_apply,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (by positivity : 0 < 1/ε)]
  exact mul_le_mul_of_nonneg_right (inverseClock_bound ε y s hε hy) (norm_nonneg (g s))

def amplitude (ε a p y h s : ℝ) : ℂ :=
  (-Complex.I*(h:ℂ))*weakSlope ε a p y s*clockAmplitude ε a p y s

theorem amplitude_continuous (ε a p y h : ℝ) (hε : 0 < ε) (hy : |y| ≤ Real.pi*ε/3) :
    Continuous (amplitude ε a p y h) := by
  have hi := inverseClock_continuous ε y hε hy
  have ht := (argument_smooth ε y).continuous
  have hc := (clockAmplitude_smooth ε a p y hε hy).continuous
  unfold amplitude weakSlope
  fun_prop

theorem amplitude_memLp (ε a p y h : ℝ) (hε : 0 < ε) (ha : 0 < a) (hy : |y| ≤ Real.pi*ε/3) :
    MemLp (amplitude ε a p y h) 2 volume := by
  have hg := clockAmplitude_memLp ε a p y hε ha hy
  have hi := inverse_mul_memLp ε y hε hy _ hg
  have hi2 := inverse_mul_memLp ε y hε hy _ hi
  have hm := moment_memLp ε a p y hε ha hy
  have hs := (((hi.const_mul ((p:ℂ)*Complex.I-1)).sub (hm.const_mul (2*(a:ℂ)))).add
    ((hi.sub (hi2.const_mul (ε:ℂ))).const_mul (1/2:ℂ))).const_mul (-Complex.I*(h:ℂ))
  convert hs using 1
  funext s
  simp only [amplitude,weakSlope,Pi.add_apply,Pi.sub_apply]
  ring

def amplitudes {m : ℕ} (ε h : ℝ) (a p : Fin m → ℝ) (s : ℝ) (i : Fin m) : ℂ :=
  amplitude ε (a i) (p i) (-h/2) h s

#print axioms clockAmplitude_half
#print axioms moment_continuous
#print axioms moment_memLp
#print axioms inverse_mul_memLp
#print axioms amplitude_continuous
#print axioms amplitude_memLp
end
end UnifiedTheory.Audit.KFCausalShiftedMomentumClockAmplitude
