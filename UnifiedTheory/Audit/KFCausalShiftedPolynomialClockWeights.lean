/- Every fixed polynomial clock weight is absorbed by the actual
shifted Gaussian and shifted pure-momentum amplitudes. These constants
may depend on the polynomial degree and fixed clock parameters. -/
import UnifiedTheory.Audit.KFCausalShiftedMomentumClockAmplitude

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2000000

namespace UnifiedTheory.Audit.KFCausalShiftedPolynomialClockWeights
noncomputable section
open MeasureTheory
open KFCausalRegularizedLongitudinalChart (chart chart_continuous)
open KFCausalClockFloorRelativeShift (argument argument_smooth)
open KFCausalClockFloorFullGaussian (clockFactor clockFactor_norm)
open KFCausalShiftedGaussianPhysicalProfile (clockAmplitude clockAmplitude_smooth)
open KFCausalShiftedClockAmplitude (clockAmplitude_memLp)
open KFCausalGaussianClockMoment (bound bound_positive moment_bound)
open KFCausalShiftedMomentumClockAmplitude (clockAmplitude_half inverse_mul_memLp amplitude amplitude_continuous)
open KFCausalClockResponseTransport (weakSlope)
open KFCausalShiftedGaussianLongitudinalDifferential (inverseClock)

def weight (ε s : ℝ) : ℝ := 1+|chart ε s|
def halfBound (a y : ℝ) : ℝ := Real.exp ((a/2)*y^2)+bound a y

theorem weight_positive (ε s : ℝ) : 0 < weight ε s := by unfold weight; positivity

theorem weight_continuous (ε : ℝ) : Continuous (weight ε) :=
  continuous_const.add (chart_continuous ε).abs

theorem half_bound (ε a y s : ℝ) (ha : 0 < a) :
    weight ε s*‖clockFactor (a/2) (argument ε y s)‖ ≤ halfBound a y := by
  have hq : |chart ε s| ≤ ‖argument ε y s‖ := by
    simpa only [argument,Complex.add_re,Complex.ofReal_re,Complex.mul_re,Complex.ofReal_im,
      Complex.I_re,Complex.I_im,mul_zero,zero_mul,sub_zero,add_zero] using
      Complex.abs_re_le_norm (argument ε y s)
  have he : ‖clockFactor (a/2) (argument ε y s)‖ ≤ Real.exp ((a/2)*y^2) := by
    rw [argument,clockFactor_norm]
    apply Real.exp_le_exp.mpr
    nlinarith [sq_nonneg (chart ε s)]
  have hm := moment_bound a (chart ε s) y ha
  rw [norm_mul] at hm
  have hx := mul_le_mul_of_nonneg_right hq (norm_nonneg (clockFactor (a/2) (argument ε y s)))
  change ‖argument ε y s‖*‖clockFactor (a/2) (argument ε y s)‖ ≤ bound a y at hm
  unfold weight halfBound
  nlinarith only [he,hm,hx]

theorem power_amplitude_memLp (n : ℕ) (ε a p y : ℝ) (hε : 0 < ε) (ha : 0 < a)
    (hy : |y| ≤ Real.pi*ε/3) :
    MemLp (fun s => ((weight ε s)^n:ℂ)*clockAmplitude ε a p y s) 2 volume := by
  induction n generalizing a with
  | zero => simpa only [pow_zero,Complex.ofReal_one,one_mul] using clockAmplitude_memLp ε a p y hε ha hy
  | succ n ih =>
    have hg := ih (a/2) (by positivity)
    have hC : 0 ≤ halfBound a y := by unfold halfBound; exact add_nonneg (Real.exp_pos _).le (bound_positive a y ha).le
    have hc : Continuous (fun s => ((weight ε s)^(n+1):ℂ)*clockAmplitude ε a p y s) :=
      ((Complex.continuous_ofReal.comp (weight_continuous ε)).pow _).mul
        (clockAmplitude_smooth ε a p y hε hy).continuous
    apply (hg.const_mul (halfBound a y:ℂ)).of_le hc.aestronglyMeasurable
    filter_upwards [] with s
    have he : ((weight ε s)^(n+1):ℂ)*clockAmplitude ε a p y s =
        ((weight ε s:ℝ):ℂ)*clockFactor (a/2) (argument ε y s)*
          (((weight ε s)^n:ℂ)*clockAmplitude ε (a/2) p y s) := by
      rw [clockAmplitude_half,pow_succ]
      ring
    rw [he]
    simp only [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hC,
      abs_of_pos (weight_positive ε s)]
    exact mul_le_mul_of_nonneg_right (half_bound ε a y s ha) (by positivity)

theorem argument_bound (ε y s : ℝ) : ‖argument ε y s‖ ≤ (1+|y|)*weight ε s := by
  have h := norm_add_le (chart ε s:ℂ) ((y:ℂ)*Complex.I)
  simp only [norm_mul,Complex.norm_real,Real.norm_eq_abs,Complex.norm_I,mul_one] at h
  unfold argument weight
  nlinarith [mul_nonneg (abs_nonneg y) (abs_nonneg (chart ε s))]

theorem power_moment_memLp (n : ℕ) (ε a p y : ℝ) (hε : 0 < ε) (ha : 0 < a)
    (hy : |y| ≤ Real.pi*ε/3) :
    MemLp (fun s => argument ε y s*(((weight ε s)^n:ℂ)*clockAmplitude ε a p y s)) 2 volume := by
  have hc : Continuous (fun s => argument ε y s*(((weight ε s)^n:ℂ)*clockAmplitude ε a p y s)) :=
    (argument_smooth ε y).continuous.mul
      (((Complex.continuous_ofReal.comp (weight_continuous ε)).pow _).mul
        (clockAmplitude_smooth ε a p y hε hy).continuous)
  apply ((power_amplitude_memLp (n+1) ε a p y hε ha hy).const_mul ((1+|y|:ℝ):ℂ)).of_le hc.aestronglyMeasurable
  filter_upwards [] with s
  simp only [norm_mul,norm_pow,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (by positivity : 0 < 1+|y|),
    abs_of_pos (weight_positive ε s),pow_succ]
  have hm := mul_le_mul_of_nonneg_right (argument_bound ε y s)
    (mul_nonneg (pow_nonneg (weight_positive ε s).le n) (norm_nonneg (clockAmplitude ε a p y s)))
  nlinarith only [hm]

theorem power_momentum_memLp (n : ℕ) (ε a p y h : ℝ) (hε : 0 < ε) (ha : 0 < a)
    (hy : |y| ≤ Real.pi*ε/3) :
    MemLp (fun s => ((weight ε s)^n:ℂ)*amplitude ε a p y h s) 2 volume := by
  let g := fun s => ((weight ε s)^n:ℂ)*clockAmplitude ε a p y s
  have hg := power_amplitude_memLp n ε a p y hε ha hy
  have hi := inverse_mul_memLp ε y hε hy g hg
  have hi2 := inverse_mul_memLp ε y hε hy _ hi
  have hm := power_moment_memLp n ε a p y hε ha hy
  have hs := (((hi.const_mul ((p:ℂ)*Complex.I-1)).sub (hm.const_mul (2*(a:ℂ)))).add
    ((hi.sub (hi2.const_mul (ε:ℂ))).const_mul (1/2:ℂ))).const_mul (-Complex.I*(h:ℂ))
  convert hs using 1
  funext s
  simp only [amplitude,weakSlope,Pi.add_apply,Pi.sub_apply,g]
  ring

theorem exponential_bound (ε s : ℝ) (hε : 0 ≤ ε) : Real.exp s ≤ weight ε s := by
  by_cases hs : 0 ≤ s
  · have hc : Real.exp s ≤ chart ε s := by unfold chart; nlinarith [mul_nonneg hε hs]
    exact hc.trans ((le_abs_self _).trans (by unfold weight; linarith))
  · have he : Real.exp s ≤ 1 := Real.exp_le_one_iff.mpr (le_of_not_ge hs)
    exact he.trans (by unfold weight; linarith [abs_nonneg (chart ε s)])

#print axioms weight_positive
#print axioms weight_continuous
#print axioms half_bound
#print axioms power_amplitude_memLp
#print axioms argument_bound
#print axioms power_moment_memLp
#print axioms power_momentum_memLp
#print axioms exponential_bound
end
end UnifiedTheory.Audit.KFCausalShiftedPolynomialClockWeights
