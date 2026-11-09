/- Complex Gaussian moments with an arbitrary linear source. The exact
recurrence includes every degree needed by the quartic Fourier jet and
its charged derivative. No division by the imaginary clock coordinate
is used; the only denominator is a Gaussian width of positive real part. -/
import UnifiedTheory.Audit.KFCausalComplexGaussianMoments
import UnifiedTheory.Audit.KFCausalNeutralLinePackets
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1800000

namespace UnifiedTheory.Audit.KFCausalShiftedComplexGaussianMoments
noncomputable section
open MeasureTheory
open scoped FourierTransform
open KFCausalGaussianQuarticFourier (fourier_const_mul fourier_sub)

def moment (b c : ℂ) (n : ℕ) (x : ℝ) : ℂ :=
  (x:ℂ)^n*Complex.exp (-b*(x:ℂ)^2+c*(x:ℂ))
def value (b c : ℂ) (n : ℕ) : ℂ := ∫ x, moment b c n x
def mass (b c : ℂ) : ℂ :=
  KFCausalComplexGaussianMoments.gaussianValue b*Complex.exp (c^2/(4*b))
def normalized (b c : ℂ) : ℕ → ℂ
  | 0 => 1
  | 1 => c/(2*b)
  | n+2 => ((n+1:ℂ)*normalized b c n+c*normalized b c (n+1))/(2*b)

theorem moment_norm (b c : ℂ) (n : ℕ) (x : ℝ) :
    ‖moment b c n x‖ = |x|^n*Real.exp (-b.re*x^2+c.re*x) := by
  simp [moment,norm_pow,Complex.norm_exp,Complex.mul_re,Complex.mul_im,pow_two]

theorem moment_integrable (b c : ℂ) (hb : 0 < b.re) (n : ℕ) :
    Integrable (moment b c n) := by
  apply (KFCausalNeutralLinePackets.monomial_integrable b.re hb c n).norm.mono'
    (by unfold moment; fun_prop)
  filter_upwards [] with x
  rw [moment_norm,KFCausalNeutralLinePackets.monomial_norm]

theorem gaussian_derivative (b c : ℂ) (x : ℝ) :
    HasDerivAt (moment b c 0) (c*moment b c 0 x-(2*b)*moment b c 1 x) x := by
  have hd := ((((hasDerivAt_id x).ofReal_comp.pow 2).const_mul (-b)).add
    ((hasDerivAt_id x).ofReal_comp.const_mul c)).cexp
  convert hd using 1
  · funext y
    simp [moment]
  · norm_num [moment]
    ring

theorem successor_derivative (b c : ℂ) (x : ℝ) (n : ℕ) :
    HasDerivAt (moment b c (n+1))
      ((n+1:ℂ)*moment b c n x+c*moment b c (n+1) x-(2*b)*moment b c (n+2) x) x := by
  have hd := ((hasDerivAt_id x).ofReal_comp.pow (n+1)).mul (gaussian_derivative b c x)
  convert hd using 1
  · funext u
    simp only [Pi.mul_apply,Pi.pow_apply,id_eq,moment,pow_zero,one_mul]
  · simp only [Pi.pow_apply,id_eq,moment,pow_zero,pow_one,one_mul,Nat.add_sub_cancel,
      Nat.cast_add,Nat.cast_one,Complex.ofReal_one,mul_one]
    rw [show n+2 = (n+1)+1 by omega,pow_succ,pow_succ]
    ring

private theorem fourier_zero (f : ℝ → ℂ) : (𝓕 f) 0 = ∫ x, f x := by
  simp [Real.fourier_eq]

theorem first_recurrence (b c : ℂ) (hb : 0 < b.re) :
    (2*b)*value b c 1 = c*value b c 0 := by
  have hd : deriv (moment b c 0) = fun x => c*moment b c 0 x-(2*b)*moment b c 1 x :=
    funext (fun x => (gaussian_derivative b c x).deriv)
  have hi := ((moment_integrable b c hb 0).const_mul c).sub
    ((moment_integrable b c hb 1).const_mul (2*b))
  have hF := congrFun (Real.fourier_deriv (moment_integrable b c hb 0)
    (fun x => (gaussian_derivative b c x).differentiableAt) (by rwa [hd])) 0
  rw [hd,fourier_sub _ _ ((moment_integrable b c hb 0).const_mul c)
    ((moment_integrable b c hb 1).const_mul (2*b)),fourier_const_mul,fourier_const_mul,
    fourier_zero,fourier_zero] at hF
  change c*value b c 0-(2*b)*value b c 1 = _ at hF
  have hz : c*value b c 0-(2*b)*value b c 1 = 0 := by simpa using hF
  exact (sub_eq_zero.mp hz).symm

theorem recurrence (b c : ℂ) (hb : 0 < b.re) (n : ℕ) :
    (2*b)*value b c (n+2) = (n+1:ℂ)*value b c n+c*value b c (n+1) := by
  have hd : deriv (moment b c (n+1)) = fun x =>
      (n+1:ℂ)*moment b c n x+c*moment b c (n+1) x-(2*b)*moment b c (n+2) x :=
    funext (fun x => (successor_derivative b c x n).deriv)
  have hi0 := ((moment_integrable b c hb n).const_mul (n+1:ℂ)).add
    ((moment_integrable b c hb (n+1)).const_mul c)
  change Integrable (fun x => (n+1:ℂ)*moment b c n x+c*moment b c (n+1) x) at hi0
  have hi1 := (moment_integrable b c hb (n+2)).const_mul (2*b)
  have hF := congrFun (Real.fourier_deriv (moment_integrable b c hb (n+1))
    (fun x => (successor_derivative b c x n).differentiableAt)
    (by rw [hd]; exact hi0.sub hi1)) 0
  rw [hd,fourier_zero,integral_sub hi0 hi1,integral_add,
    integral_const_mul,integral_const_mul,integral_const_mul] at hF
  · change (n+1:ℂ)*value b c n+c*value b c (n+1)-(2*b)*value b c (n+2) = _ at hF
    have hz : (n+1:ℂ)*value b c n+c*value b c (n+1)-(2*b)*value b c (n+2) = 0 := by
      simpa using hF
    exact (sub_eq_zero.mp hz).symm
  · exact (moment_integrable b c hb n).const_mul _
  · exact (moment_integrable b c hb (n+1)).const_mul _

theorem value_zero (b c : ℂ) (hb : 0 < b.re) : value b c 0 = mass b c := by
  have hn : (-b).re < 0 := by simpa using hb
  simpa only [value,moment,pow_zero,one_mul,add_zero,mass,
    KFCausalComplexGaussianMoments.gaussianValue,neg_neg,mul_neg,div_neg,zero_sub]
    using integral_cexp_quadratic hn c 0

theorem value_one (b c : ℂ) (hb : 0 < b.re) :
    value b c 1 = mass b c*(c/(2*b)) := by
  have hn : b ≠ 0 := by intro hz; simp [hz] at hb
  apply mul_left_cancel₀ (show 2*b ≠ 0 from mul_ne_zero (by norm_num) hn)
  rw [first_recurrence b c hb,value_zero b c hb]
  field_simp

theorem value_all (b c : ℂ) (hb : 0 < b.re) (n : ℕ) :
    value b c n = mass b c*normalized b c n := by
  have hn : b ≠ 0 := by intro hz; simp [hz] at hb
  induction n using Nat.twoStepInduction with
  | zero => simpa only [normalized,mul_one] using value_zero b c hb
  | one => exact value_one b c hb
  | more n h0 h1 =>
    apply mul_left_cancel₀ (show 2*b ≠ 0 from mul_ne_zero (by norm_num) hn)
    rw [recurrence b c hb,h0,h1,normalized]
    field_simp

theorem value_two (b c : ℂ) (hb : 0 < b.re) :
    value b c 2 = mass b c*(c^2+2*b)/(4*b^2) := by
  have hn : b ≠ 0 := by intro hz; simp [hz] at hb
  rw [value_all b c hb]
  norm_num [normalized]
  field_simp
  ring

theorem value_three (b c : ℂ) (hb : 0 < b.re) :
    value b c 3 = mass b c*(c^3+6*b*c)/(8*b^3) := by
  have hn : b ≠ 0 := by intro hz; simp [hz] at hb
  rw [value_all b c hb]
  norm_num [normalized]
  field_simp
  ring

theorem value_four (b c : ℂ) (hb : 0 < b.re) :
    value b c 4 = mass b c*(c^4+12*b*c^2+12*b^2)/(16*b^4) := by
  have hn : b ≠ 0 := by intro hz; simp [hz] at hb
  rw [value_all b c hb]
  norm_num [normalized]
  field_simp
  ring

#print axioms moment_norm
#print axioms moment_integrable
#print axioms gaussian_derivative
#print axioms successor_derivative
#print axioms first_recurrence
#print axioms recurrence
#print axioms value_zero
#print axioms value_one
#print axioms value_all
#print axioms value_two
#print axioms value_three
#print axioms value_four
end
end UnifiedTheory.Audit.KFCausalShiftedComplexGaussianMoments
