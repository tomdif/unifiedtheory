/- Exact complex Gaussian moments through degree four. Integrability
and the moment recurrence are derived for every positive real part. -/
import UnifiedTheory.Audit.KFCausalGaussianQuarticFourier

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

namespace UnifiedTheory.Audit.KFCausalComplexGaussianMoments
noncomputable section
open MeasureTheory
open scoped FourierTransform
open KFCausalGaussianQuarticFourier (fourier_const_mul fourier_sub)

def moment (b : ℂ) (n : ℕ) (x : ℝ) : ℂ := (x:ℂ)^n*Complex.exp (-b*(x:ℂ)^2)
def value (b : ℂ) (n : ℕ) : ℂ := ∫ x, moment b n x
def gaussianValue (b : ℂ) : ℂ := ((Real.pi:ℂ)/b)^(1/2:ℂ)

theorem moment_integrable (b : ℂ) (hb : 0 < b.re) (n : ℕ) : Integrable (moment b n) := by
  apply (KFCausalPolynomialGaussianIntegrals.scalar_moment_integrable b.re hb n).norm.mono'
    (by unfold moment; fun_prop)
  filter_upwards [] with x
  simp only [moment,norm_mul,norm_pow,norm_cexp_neg_mul_sq,Complex.norm_real,Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos _)]
  exact le_rfl

private theorem fourier_zero (f : ℝ → ℂ) : (𝓕 f) 0 = ∫ x, f x := by
  simp [Real.fourier_eq]

theorem gaussian_derivative (b : ℂ) (x : ℝ) :
    HasDerivAt (moment b 0) ((-2*b)*moment b 1 x) x := by
  have hd := (((hasDerivAt_id x).ofReal_comp.pow 2).const_mul (-b)).cexp
  convert hd using 1
  · funext y
    simp [moment]
  · norm_num [moment]
    ring

theorem successor_derivative (b : ℂ) (x : ℝ) (n : ℕ) :
    HasDerivAt (moment b (n+1)) ((n+1:ℂ)*moment b n x-(2*b)*moment b (n+2) x) x := by
  have hd := ((hasDerivAt_id x).ofReal_comp.pow (n+1)).mul (gaussian_derivative b x)
  convert hd using 1
  · funext u
    simp only [Pi.mul_apply,Pi.pow_apply,id_eq,moment,pow_zero,one_mul]
  · simp only [Pi.pow_apply,id_eq,moment,pow_zero,pow_one,one_mul,Nat.add_sub_cancel,
      Nat.cast_add,Nat.cast_one,Complex.ofReal_one,mul_one]
    rw [show n+2 = (n+1)+1 by omega,pow_succ,pow_succ]
    ring

theorem recurrence (b : ℂ) (hb : 0 < b.re) (n : ℕ) :
    (2*b)*value b (n+2) = (n+1:ℂ)*value b n := by
  have hd : deriv (moment b (n+1)) = fun x => (n+1:ℂ)*moment b n x-(2*b)*moment b (n+2) x :=
    funext (fun x => (successor_derivative b x n).deriv)
  have hi : Integrable (fun x => (n+1:ℂ)*moment b n x-(2*b)*moment b (n+2) x) :=
    ((moment_integrable b hb n).const_mul _).sub ((moment_integrable b hb (n+2)).const_mul _)
  have hF := congrFun (Real.fourier_deriv (moment_integrable b hb (n+1))
    (fun x => (successor_derivative b x n).differentiableAt) (by rwa [hd])) 0
  rw [hd,fourier_sub _ _ ((moment_integrable b hb n).const_mul _)
    ((moment_integrable b hb (n+2)).const_mul _),fourier_const_mul,fourier_const_mul,
    fourier_zero,fourier_zero] at hF
  change (n+1:ℂ)*value b n-(2*b)*value b (n+2) = _ at hF
  have hz : (n+1:ℂ)*value b n-(2*b)*value b (n+2) = 0 := by simpa using hF
  exact (sub_eq_zero.mp hz).symm

theorem value_zero (b : ℂ) (hb : 0 < b.re) : value b 0 = gaussianValue b := by
  simpa only [value,moment,pow_zero,one_mul,gaussianValue] using integral_gaussian_complex hb

theorem value_one (b : ℂ) (hb : 0 < b.re) : value b 1 = 0 := by
  have hd : deriv (moment b 0) = fun x => (-2*b)*moment b 1 x :=
    funext (fun x => (gaussian_derivative b x).deriv)
  have hF := congrFun (Real.fourier_deriv (moment_integrable b hb 0)
    (fun x => (gaussian_derivative b x).differentiableAt)
    (by rw [hd]; exact (moment_integrable b hb 1).const_mul _)) 0
  rw [hd,fourier_const_mul,fourier_zero] at hF
  have hn : b ≠ 0 := by intro hz; simp [hz] at hb
  change (-2*b)*value b 1 = _ at hF
  have hz : (-2*b)*value b 1 = 0 := by simpa using hF
  exact (mul_eq_zero.mp hz).resolve_left (mul_ne_zero (by norm_num) hn)

theorem value_two (b : ℂ) (hb : 0 < b.re) : value b 2 = gaussianValue b/(2*b) := by
  have hn : b ≠ 0 := by intro hz; simp [hz] at hb
  apply (eq_div_iff (mul_ne_zero (by norm_num) hn)).mpr
  have hr := recurrence b hb 0
  simpa only [zero_add,Nat.cast_zero,zero_add,one_mul,value_zero b hb,mul_comm] using hr

theorem value_three (b : ℂ) (hb : 0 < b.re) : value b 3 = 0 := by
  have hn : b ≠ 0 := by intro hz; simp [hz] at hb
  have hr := recurrence b hb 1
  rw [value_one b hb,mul_zero] at hr
  exact (mul_eq_zero.mp hr).resolve_left (mul_ne_zero (by norm_num) hn)

theorem value_four (b : ℂ) (hb : 0 < b.re) : value b 4 = 3*gaussianValue b/(4*b^2) := by
  have hn : b ≠ 0 := by intro hz; simp [hz] at hb
  have hr := recurrence b hb 2
  rw [value_two b hb] at hr
  apply mul_left_cancel₀ (show 2*b ≠ 0 from mul_ne_zero (by norm_num) hn)
  rw [hr]
  norm_num only [Nat.cast_ofNat]
  field_simp
  ring

#print axioms moment_integrable
#print axioms gaussian_derivative
#print axioms successor_derivative
#print axioms recurrence
#print axioms value_zero
#print axioms value_one
#print axioms value_two
#print axioms value_three
#print axioms value_four
end
end UnifiedTheory.Audit.KFCausalComplexGaussianMoments
