/- Exact cubic and quartic Gaussian Fourier moments, with the physical
2*pi convention. The recurrence is derived from actual differentiable
integrable Gaussian moments. -/
import UnifiedTheory.Audit.KFCausalGaussianQuadraticFourier

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2400000

namespace UnifiedTheory.Audit.KFCausalGaussianQuarticFourier
noncomputable section
open MeasureTheory
open scoped FourierTransform
open KFCausalGaussianQuadraticFourier
  (moment moment_integrable gaussian_derivative first_moment_fourier second_moment_fourier)

theorem moment_successor_derivative (α x : ℝ) (n : ℕ) :
    HasDerivAt (moment α (n+1))
      ((n+1:ℂ)*moment α n x-(2*(α:ℂ))*moment α (n+2) x) x := by
  have hd := ((hasDerivAt_id x).ofReal_comp.pow (n+1)).mul (gaussian_derivative α x)
  convert hd using 1
  · funext u
    simp only [Pi.mul_apply,Pi.pow_apply,id_eq,moment,pow_zero,one_mul]
  · simp only [Pi.pow_apply,id_eq,moment,pow_zero,pow_one,one_mul,Nat.add_sub_cancel,
      Nat.cast_add,Nat.cast_one,Complex.ofReal_one,mul_one]
    rw [show n+2 = (n+1)+1 by omega,pow_succ,pow_succ]
    ring

theorem fourier_const_mul (c : ℂ) (f : ℝ → ℂ) (w : ℝ) :
    (𝓕 (fun x => c*f x)) w = c*(𝓕 f) w :=
  congrFun (VectorFourier.fourierIntegral_const_smul Real.fourierChar volume
    (innerₗ ℝ) f c) w

theorem fourier_sub (f g : ℝ → ℂ) (hf : Integrable f) (hg : Integrable g) (w : ℝ) :
    (𝓕 (fun x => f x-g x)) w = (𝓕 f) w-(𝓕 g) w := by
  simp only [Real.fourier_eq,smul_sub]
  exact integral_sub ((Real.fourierIntegral_convergent_iff w).mpr hf)
    ((Real.fourierIntegral_convergent_iff w).mpr hg)

theorem moment_fourier_recurrence (α : ℝ) (hα : 0 < α) (n : ℕ) (w : ℝ) :
    (2*(α:ℂ))*(𝓕 (moment α (n+2))) w =
      (n+1:ℂ)*(𝓕 (moment α n)) w-
        (2*Real.pi*Complex.I*w)*(𝓕 (moment α (n+1))) w := by
  have hd : deriv (moment α (n+1)) =
      fun x => (n+1:ℂ)*moment α n x-(2*(α:ℂ))*moment α (n+2) x :=
    funext (fun x => (moment_successor_derivative α x n).deriv)
  have hi : Integrable (fun x => (n+1:ℂ)*moment α n x-(2*(α:ℂ))*moment α (n+2) x) volume :=
    ((moment_integrable α hα n).const_mul _).sub ((moment_integrable α hα (n+2)).const_mul _)
  have hF := congrFun (Real.fourier_deriv (moment_integrable α hα (n+1))
    (fun x => (moment_successor_derivative α x n).differentiableAt) (by rwa [hd])) w
  rw [hd,fourier_sub _ _ ((moment_integrable α hα n).const_mul _)
    ((moment_integrable α hα (n+2)).const_mul _),fourier_const_mul,fourier_const_mul] at hF
  change (n+1:ℂ)*(𝓕 (moment α n)) w-(2*(α:ℂ))*(𝓕 (moment α (n+2))) w =
    (2*Real.pi*Complex.I*w)*(𝓕 (moment α (n+1))) w at hF
  linear_combination -hF

theorem third_moment_fourier (α : ℝ) (hα : 0 < α) (w : ℝ) :
    (𝓕 (moment α 3)) w =
      (-(3*(Real.pi:ℂ)*Complex.I*(w:ℂ))/(2*(α:ℂ)^2)+
        (Real.pi:ℂ)^3*Complex.I*(w:ℂ)^3/(α:ℂ)^3)*(𝓕 (moment α 0)) w := by
  have he := moment_fourier_recurrence α hα 1 w
  norm_num at he
  rw [first_moment_fourier α hα,second_moment_fourier α hα] at he
  have ha : (α:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hα.ne'
  apply mul_left_cancel₀ (show 2*(α:ℂ) ≠ 0 by exact mul_ne_zero (by norm_num) ha)
  rw [he]
  field_simp
  ring

theorem fourth_moment_fourier (α : ℝ) (hα : 0 < α) (w : ℝ) :
    (𝓕 (moment α 4)) w =
      (3/(4*(α:ℂ)^2)-3*(Real.pi:ℂ)^2*(w:ℂ)^2/(α:ℂ)^3+
        (Real.pi:ℂ)^4*(w:ℂ)^4/(α:ℂ)^4)*(𝓕 (moment α 0)) w := by
  have he := moment_fourier_recurrence α hα 2 w
  norm_num only [Nat.cast_ofNat,show 2+2=4 by rfl,show 2+1=3 by rfl] at he
  rw [second_moment_fourier α hα,third_moment_fourier α hα] at he
  have ha : (α:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hα.ne'
  apply mul_left_cancel₀ (show 2*(α:ℂ) ≠ 0 by exact mul_ne_zero (by norm_num) ha)
  rw [he]
  field_simp
  ring_nf
  simp only [Complex.I_sq,sub_eq_add_neg]
  ring

#print axioms moment_successor_derivative
#print axioms fourier_const_mul
#print axioms fourier_sub
#print axioms moment_fourier_recurrence
#print axioms third_moment_fourier
#print axioms fourth_moment_fourier
end
end UnifiedTheory.Audit.KFCausalGaussianQuarticFourier
