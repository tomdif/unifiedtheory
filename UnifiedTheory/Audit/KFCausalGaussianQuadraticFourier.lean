/- Exact scalar quadratic Gaussian Fourier moment, retaining the 2*pi
normalization. Integrability and derivative identities are derived. -/
import UnifiedTheory.Audit.KFCausalPolynomialGaussianIntegrals
import UnifiedTheory.Audit.KFCausalGaussianSliceDomain
import Mathlib.Analysis.Fourier.FourierTransformDeriv

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1600000

namespace UnifiedTheory.Audit.KFCausalGaussianQuadraticFourier
noncomputable section
open MeasureTheory
open scoped FourierTransform
open KFCausalGaussianSliceDomain (gaussian)

def moment (α : ℝ) (n : ℕ) (x : ℝ) : ℂ := (x:ℂ)^n*gaussian α x

theorem moment_real (α : ℝ) (n : ℕ) (x : ℝ) :
    moment α n x = ((x^n*Real.exp (-α*x^2):ℝ):ℂ) := by
  simp only [moment,gaussian,Complex.ofReal_mul,Complex.ofReal_pow,Complex.ofReal_exp,
    Complex.ofReal_neg]

theorem moment_integrable (α : ℝ) (hα : 0 < α) (n : ℕ) :
    Integrable (moment α n) volume := by
  change Integrable (fun x => moment α n x) volume
  simp_rw [moment_real]
  exact (KFCausalPolynomialGaussianIntegrals.scalar_moment_integrable α hα n).ofReal

theorem moment_continuous (α : ℝ) (n : ℕ) : Continuous (moment α n) := by
  unfold moment gaussian
  fun_prop

theorem moment_memLp (α : ℝ) (hα : 0 < α) (n : ℕ) :
    MemLp (moment α n) 2 volume := by
  apply (memLp_two_iff_integrable_sq_norm (moment_continuous α n).aestronglyMeasurable).mpr
  have he (x : ℝ) : ‖moment α n x‖^2 = x^(2*n)*Real.exp (-(2*α)*x^2) := by
    rw [moment,norm_mul,mul_pow,KFCausalGaussianSliceDomain.gaussian_norm_square]
    simp only [Complex.ofReal_re,norm_pow,Complex.norm_real,Real.norm_eq_abs]
    rw [← pow_mul, mul_comm n 2, pow_mul, sq_abs, ← pow_mul]
  simp_rw [he]
  exact KFCausalPolynomialGaussianIntegrals.scalar_moment_integrable (2*α) (by positivity) (2*n)

theorem gaussian_derivative (α x : ℝ) :
    HasDerivAt (moment α 0) ((-2*(α:ℂ))*moment α 1 x) x := by
  have hd := (((hasDerivAt_id x).ofReal_comp.pow 2).const_mul (-(α:ℂ))).cexp
  convert hd using 1
  · funext y
    simp [moment,gaussian]
  · norm_num [moment,gaussian]
    ring

theorem first_moment_derivative (α x : ℝ) :
    HasDerivAt (moment α 1) (moment α 0 x-(2*(α:ℂ))*moment α 2 x) x := by
  have hd := (hasDerivAt_id x).ofReal_comp.mul (gaussian_derivative α x)
  convert hd using 1
  · funext y
    simp [moment]
  · norm_num [moment]
    ring

private theorem fourier_const_mul (c : ℂ) (f : ℝ → ℂ) (w : ℝ) :
    (𝓕 (fun x => c*f x)) w = c*(𝓕 f) w :=
  congrFun (VectorFourier.fourierIntegral_const_smul Real.fourierChar volume
    (innerₗ ℝ) f c) w

private theorem fourier_sub (f g : ℝ → ℂ) (hf : Integrable f) (hg : Integrable g) (w : ℝ) :
    (𝓕 (fun x => f x-g x)) w = (𝓕 f) w-(𝓕 g) w := by
  simp only [Real.fourier_eq,smul_sub]
  exact integral_sub ((Real.fourierIntegral_convergent_iff w).mpr hf)
    ((Real.fourierIntegral_convergent_iff w).mpr hg)

theorem first_moment_fourier (α : ℝ) (hα : 0 < α) (w : ℝ) :
    (𝓕 (moment α 1)) w = (-(Real.pi:ℂ)*Complex.I*w/α)*(𝓕 (moment α 0)) w := by
  have hd : deriv (moment α 0) = fun x => (-2*(α:ℂ))*moment α 1 x :=
    funext (fun x => (gaussian_derivative α x).deriv)
  have hF := congrFun (Real.fourier_deriv (moment_integrable α hα 0)
    (fun x => (gaussian_derivative α x).differentiableAt)
    (by rw [hd]; exact (moment_integrable α hα 1).const_mul _)) w
  rw [hd,fourier_const_mul] at hF
  change (-2*(α:ℂ))*(𝓕 (moment α 1)) w =
    (2*Real.pi*Complex.I*w)*(𝓕 (moment α 0)) w at hF
  have ha : (α:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hα.ne'
  apply mul_left_cancel₀ (show (-2*(α:ℂ)) ≠ 0 by exact mul_ne_zero (by norm_num) ha)
  rw [hF]
  field_simp

theorem second_moment_fourier (α : ℝ) (hα : 0 < α) (w : ℝ) :
    (𝓕 (moment α 2)) w =
      (1/(2*(α:ℂ))-(Real.pi:ℂ)^2*(w:ℂ)^2/(α:ℂ)^2)*(𝓕 (moment α 0)) w := by
  have hd : deriv (moment α 1) = fun x => moment α 0 x-(2*(α:ℂ))*moment α 2 x :=
    funext (fun x => (first_moment_derivative α x).deriv)
  have hi : Integrable (fun x => moment α 0 x-(2*(α:ℂ))*moment α 2 x) volume :=
    (moment_integrable α hα 0).sub ((moment_integrable α hα 2).const_mul _)
  have hF := congrFun (Real.fourier_deriv (moment_integrable α hα 1)
    (fun x => (first_moment_derivative α x).differentiableAt) (by rwa [hd])) w
  rw [hd,fourier_sub _ _ (moment_integrable α hα 0)
    ((moment_integrable α hα 2).const_mul _),fourier_const_mul,first_moment_fourier α hα] at hF
  change (𝓕 (moment α 0)) w-(2*(α:ℂ))*(𝓕 (moment α 2)) w =
    (2*Real.pi*Complex.I*w)*((-(Real.pi:ℂ)*Complex.I*w/α)*(𝓕 (moment α 0)) w) at hF
  have ha : (α:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hα.ne'
  apply mul_left_cancel₀ (show (2*(α:ℂ)) ≠ 0 by exact mul_ne_zero (by norm_num) ha)
  have he : (2*(α:ℂ))*(𝓕 (moment α 2)) w =
      (𝓕 (moment α 0)) w-
        (2*Real.pi*Complex.I*w)*((-(Real.pi:ℂ)*Complex.I*w/α)*(𝓕 (moment α 0)) w) := by
    linear_combination -hF
  rw [he]
  field_simp
  ring_nf
  simp [Complex.I_sq,sub_eq_add_neg]

#print axioms moment_real
#print axioms moment_integrable
#print axioms moment_continuous
#print axioms moment_memLp
#print axioms gaussian_derivative
#print axioms first_moment_derivative
#print axioms first_moment_fourier
#print axioms second_moment_fourier
end
end UnifiedTheory.Audit.KFCausalGaussianQuadraticFourier
