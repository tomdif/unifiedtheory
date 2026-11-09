/- The clock coefficients needed for mixed field-power domination are
continuous and L2. Their polynomial growth bounds are derived from the
actual shifted Gaussian and shifted pure-clock momentum amplitudes. -/
import UnifiedTheory.Audit.KFCausalMixedFieldClockBounds

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2000000

namespace UnifiedTheory.Audit.KFCausalMixedFieldClockCoefficients
noncomputable section
open MeasureTheory
open KFCausalMixedFieldClockBounds
open KFCausalShiftedPolynomialClockWeights (weight power_amplitude_memLp power_momentum_memLp)
open KFCausalShiftedGaussianPhysicalProfile (clockAmplitude clockAmplitude_smooth)
open KFCausalShiftedMomentumClockAmplitude (amplitude amplitude_continuous amplitude_memLp)

theorem multiply_memLp (ε y z : ℝ) (hε : 0 < ε) (hy : y ≠ 0) (n : ℕ)
    (g : ℝ → ℂ) (hg : AEStronglyMeasurable g volume)
    (hm : MemLp (fun s => (weight ε s:ℂ)^n*g s) 2 volume) :
    MemLp (fun s => (fieldBound ε y z s:ℂ)^n*g s) 2 volume := by
  have hc := (Complex.continuous_ofReal.comp (fieldBound_continuous ε y z)).pow n
  apply (hm.const_mul ((fieldConstant ε y z:ℂ)^n)).of_le (hc.aestronglyMeasurable.mul hg)
  filter_upwards [] with s
  change ‖(fieldBound ε y z s:ℂ)^n*g s‖ ≤
    ‖(fieldConstant ε y z:ℂ)^n*((weight ε s:ℂ)^n*g s)‖
  simp only [norm_mul,norm_pow,Complex.norm_real,Real.norm_eq_abs,
    abs_of_pos (fieldBound_positive ε y z s hε hy),
    abs_of_pos (fieldConstant_positive ε y z hε hy),
    abs_of_pos (KFCausalShiftedPolynomialClockWeights.weight_positive ε s)]
  have hp := pow_le_pow_left₀ (fieldBound_positive ε y z s hε hy).le
    (fieldBound_growth ε y z s hε hy) n
  rw [mul_pow] at hp
  nlinarith only [mul_le_mul_of_nonneg_right hp (norm_nonneg (g s))]

def inputCoefficient (ε a p y z : ℝ) (n : ℕ) (s : ℝ) : ℂ :=
  (fieldBound ε y z s:ℂ)^n*clockAmplitude ε a p y s

def momentumCoefficient (ε a p y z h : ℝ) (n : ℕ) (s : ℝ) : ℂ :=
  (fieldBound ε y z s:ℂ)^n*amplitude ε a p y h s

theorem inputCoefficient_continuous (ε a p y z : ℝ) (n : ℕ) (hε : 0 < ε)
    (hy : |y| ≤ Real.pi*ε/3) : Continuous (inputCoefficient ε a p y z n) :=
  ((Complex.continuous_ofReal.comp (fieldBound_continuous ε y z)).pow n).mul
    (clockAmplitude_smooth ε a p y hε hy).continuous

theorem momentumCoefficient_continuous (ε a p y z h : ℝ) (n : ℕ) (hε : 0 < ε)
    (hy : |y| ≤ Real.pi*ε/3) : Continuous (momentumCoefficient ε a p y z h n) :=
  ((Complex.continuous_ofReal.comp (fieldBound_continuous ε y z)).pow n).mul
    (amplitude_continuous ε a p y h hε hy)

theorem inputCoefficient_memLp (ε a p y z : ℝ) (n : ℕ) (hε : 0 < ε) (ha : 0 < a)
    (hy : |y| ≤ Real.pi*ε/3) (hy0 : y ≠ 0) : MemLp (inputCoefficient ε a p y z n) 2 volume :=
  multiply_memLp ε y z hε hy0 n _
    (clockAmplitude_smooth ε a p y hε hy).continuous.aestronglyMeasurable
    (power_amplitude_memLp n ε a p y hε ha hy)

theorem momentumCoefficient_memLp (ε a p y z h : ℝ) (n : ℕ) (hε : 0 < ε) (ha : 0 < a)
    (hy : |y| ≤ Real.pi*ε/3) (hy0 : y ≠ 0) : MemLp (momentumCoefficient ε a p y z h n) 2 volume :=
  multiply_memLp ε y z hε hy0 n _
    (amplitude_continuous ε a p y h hε hy).aestronglyMeasurable
    (power_momentum_memLp n ε a p y h hε ha hy)

#print axioms multiply_memLp
#print axioms inputCoefficient_continuous
#print axioms momentumCoefficient_continuous
#print axioms inputCoefficient_memLp
#print axioms momentumCoefficient_memLp
end
end UnifiedTheory.Audit.KFCausalMixedFieldClockCoefficients
