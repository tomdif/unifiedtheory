/- Identification of the actual paired Levy exponent with normalized shifted log-cosh ratios. -/
import UnifiedTheory.Audit.KFCausalChargedCoolingLevyLaplace
import UnifiedTheory.Audit.KFCausalOddHyperbolicSeries
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.Pow.Complex

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalChargedCoolingLogCosh
noncomputable section
open MeasureTheory Filter Set
open scoped Topology BigOperators ComplexOrder
open KFCausalPositiveKernelExponential (phase)
open KFCausalChargedCoolingLevyTruncation
open KFCausalChargedCoolingLevyConvergence
open KFCausalChargedCoolingLevyDerivative
open KFCausalChargedCoolingLevyLaplace
open KFCausalOddHyperbolicSeries

def shifted (s z : ℝ) : ℂ := (z:ℂ)+(s:ℂ)*Complex.I/2

theorem shifted_cosh_slitPlane (s z : ℝ) (hs : |s| < Real.pi) :
    Complex.cosh (shifted s z) ∈ Complex.slitPlane := by
  have hc : 0 < Real.cos (s/2) :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [neg_abs_le s],by linarith [le_abs_self s]⟩
  apply Or.inl
  have he : (Complex.cosh (shifted s z)).re = Real.cosh z*Real.cos (s/2) := by
    rw [shifted,show (s:ℂ)*Complex.I/2 = ((s/2:ℝ):ℂ)*Complex.I by push_cast; ring,
      Complex.cosh_add,Complex.cosh_mul_I,Complex.sinh_mul_I]
    rw [← Complex.ofReal_cosh,← Complex.ofReal_sinh,← Complex.ofReal_cos,← Complex.ofReal_sin]
    simp only [Complex.add_re,Complex.mul_re,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,
      Complex.I_re,Complex.I_im,mul_zero,zero_mul,sub_zero,add_zero]
  rw [he]
  exact mul_pos (Real.cosh_pos z) hc

theorem shifted_log_derivative (s z : ℝ) (hs : |s| < Real.pi) :
    HasDerivAt (fun x => Complex.log (Complex.cosh (shifted s x)))
      (Complex.tanh (shifted s z)) z := by
  have hd := (hasDerivAt_id (z:ℂ)).add_const ((s:ℂ)*Complex.I/2)
  have h := (hd.ccosh.clog (shifted_cosh_slitPlane s z hs)).comp_ofReal
  simpa only [shifted,Complex.tanh_eq_sinh_div_cosh,mul_one,Function.comp_apply] using h

theorem mode_strip (kind : Bool) (θ z : ℝ) (hθ : |θ| < Real.pi/2) (j : Fin 3) :
    |(shifted (mode kind j*θ) z).im| < Real.pi/2 := by
  have h := mode_decay kind θ hθ 0 j
  norm_num [oddRate] at h
  norm_num [shifted,Complex.mul_re,Complex.mul_im,Complex.div_re,Complex.div_im,abs_div]
  linarith

theorem rationalPartial_as_odd (kind : Bool) (θ z : ℝ) (hθ : |θ| < Real.pi/2) (N : ℕ) :
    rationalPartial kind θ z N = ∑ j : Fin 3,
      (coefficient kind j:ℂ)*(-oddPartial (shifted (mode kind j*θ) z) N) := by
  unfold rationalPartial
  apply Finset.sum_congr rfl
  intro j _
  congr 1
  rw [oddPartial,← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro n _
  rw [rationalPair_eq _ _ z (mode_decay kind θ hθ n j)]
  unfold shifted oddRate
  push_cast
  ring

def derivativeValue (kind : Bool) (θ z : ℝ) : ℂ :=
  ∑ j : Fin 3, (coefficient kind j:ℂ)*(-Complex.tanh (shifted (mode kind j*θ) z))

theorem derivative_integral_identification (kind : Bool) (θ z : ℝ) (hθ : |θ| < Real.pi/2) :
    (∫ t in Ioi 0, pairedDerivative kind θ z t) = derivativeValue kind θ z := by
  have ht := tendsto_finset_sum Finset.univ (fun j _ =>
    ((oddPartial_tendsto (shifted (mode kind j*θ) z) (mode_strip kind θ z hθ j)).neg).const_mul (coefficient kind j:ℂ))
  have he : Tendsto (rationalPartial kind θ z) atTop (𝓝 (derivativeValue kind θ z)) := by
    change Tendsto (fun N => rationalPartial kind θ z N) atTop _
    simpa only [rationalPartial_as_odd kind θ z hθ,derivativeValue] using ht
  exact tendsto_nhds_unique (rationalPartial_tendsto kind θ z hθ) he

def logRatio (kind : Bool) (θ z : ℝ) : ℂ :=
  ∑ j : Fin 3, (coefficient kind j:ℂ)*
    (-(Complex.log (Complex.cosh (shifted (mode kind j*θ) z))-
      Complex.log (Complex.cosh (shifted (mode kind j*θ) 0))))

theorem logRatio_derivative (kind : Bool) (θ z : ℝ) (hθ : |θ| < Real.pi/2) :
    HasDerivAt (logRatio kind θ) (derivativeValue kind θ z) z := by
  have hd (j : Fin 3) : HasDerivAt (fun x => (coefficient kind j:ℂ)*
      (-(Complex.log (Complex.cosh (shifted (mode kind j*θ) x))-
        Complex.log (Complex.cosh (shifted (mode kind j*θ) 0)))))
      ((coefficient kind j:ℂ)*(-Complex.tanh (shifted (mode kind j*θ) z))) z := by
    have hm : |mode kind j*θ| < Real.pi := by simpa [oddRate] using mode_decay kind θ hθ 0 j
    exact (((shifted_log_derivative (mode kind j*θ) z hm).sub_const
      (Complex.log (Complex.cosh (shifted (mode kind j*θ) 0)))).neg).const_mul _
  simpa only [logRatio,derivativeValue,Finset.sum_apply] using
    HasDerivAt.sum (u := Finset.univ) (fun j _ => hd j)

theorem fullExponent_zero (kind : Bool) (θ : ℝ) : fullExponent kind θ 0 = 0 := by
  simp [fullExponent,paired,phase]

theorem fullExponent_eq_logRatio (kind : Bool) (θ : ℝ) (hθ : |θ| < Real.pi/2) (z : ℝ) :
    fullExponent kind θ z = logRatio kind θ z := by
  have hf (x : ℝ) : HasDerivAt (fullExponent kind θ) (derivativeValue kind θ x) x := by
    rw [← derivative_integral_identification kind θ x hθ]
    exact (fullExponent_differentiation kind θ x hθ).2
  have hg (x : ℝ) := logRatio_derivative kind θ x hθ
  have he := eq_of_fderiv_eq (fun x => (hf x).differentiableAt)
    (fun x => (hg x).differentiableAt)
    (fun x => by rw [(hf x).hasFDerivAt.fderiv,(hg x).hasFDerivAt.fderiv]) (0:ℝ)
    (by rw [fullExponent_zero]; simp [logRatio])
  exact congrFun he z

/-- Positive definiteness now applies to the explicit normalized shifted log-cosh formula,
with the integral representation fully derived. -/
theorem logRatio_kernel_positive {n : Type*} [Fintype n]
    (kind : Bool) (θ : ℝ) (hθ : |θ| < Real.pi/2) (x : n → ℝ) :
    Matrix.PosSemidef (fun i j => Complex.exp (logRatio kind θ (x j-x i))) := by
  simpa only [fullExponent_eq_logRatio kind θ hθ] using full_kernel_positive kind θ hθ x

#print axioms shifted_cosh_slitPlane
#print axioms shifted_log_derivative
#print axioms mode_strip
#print axioms rationalPartial_as_odd
#print axioms derivative_integral_identification
#print axioms logRatio_derivative
#print axioms fullExponent_zero
#print axioms fullExponent_eq_logRatio
#print axioms logRatio_kernel_positive
end
end UnifiedTheory.Audit.KFCausalChargedCoolingLogCosh
