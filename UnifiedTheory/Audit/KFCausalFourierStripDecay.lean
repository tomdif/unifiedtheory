/- Fourier decay derived from a Gaussian-bounded holomorphic strip, using
the proved contour shift and vanishing vertical edges. -/
import UnifiedTheory.Audit.KFCausalGaussianContourShift

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 800000

namespace UnifiedTheory.Audit.KFCausalFourierStripDecay
noncomputable section
open MeasureTheory Set Filter Complex
open scoped FourierTransform
open UnifiedTheory.Audit.KFCausalGaussianContourShift

def kernel (k : ℝ) (z : ℂ) : ℂ := Complex.exp (-((2*Real.pi*k:ℝ):ℂ)*I*z)
def twist (f : ℂ → ℂ) (k : ℝ) (z : ℂ) : ℂ := kernel k z*f z

theorem kernel_line (k y x : ℝ) :
    kernel k ((x:ℂ)+(y:ℂ)*I) =
      (Real.exp (2*Real.pi*k*y):ℂ)*Complex.exp ((-2*Real.pi*x*k:ℝ)*I) := by
  unfold kernel
  rw [Complex.ofReal_exp,← Complex.exp_add]
  congr 1
  apply Complex.ext <;> simp [Complex.mul_re,Complex.mul_im]
  ring

theorem kernel_line_norm (k y x : ℝ) :
    ‖kernel k ((x:ℂ)+(y:ℂ)*I)‖ = Real.exp (2*Real.pi*k*y) := by
  rw [kernel,Complex.norm_exp]
  congr 1
  simp [Complex.mul_re,Complex.mul_im]

theorem twist_differentiable (f : ℂ → ℂ) (hf : Differentiable ℂ f) (k : ℝ) :
    Differentiable ℂ (twist f k) := by
  unfold twist kernel
  fun_prop

theorem twist_gaussian_bound (f : ℂ → ℂ) (a B y k : ℝ)
    (hb : ∀ x r, |r| ≤ |y| → ‖horizontal f r x‖ ≤ B*Real.exp (-a*x^2)) :
    ∀ x r, |r| ≤ |y| → ‖horizontal (twist f k) r x‖ ≤
      (Real.exp (2*Real.pi*|k| *|y|)*B)*Real.exp (-a*x^2) := by
  intro x r hr
  have hkr : k*r ≤ |k| *|y| := by
    calc
      _ ≤ |k*r| := le_abs_self _
      _ = |k| *|r| := abs_mul _ _
      _ ≤ _ := mul_le_mul_of_nonneg_left hr (abs_nonneg _)
  have hk : Real.exp (2*Real.pi*k*r) ≤ Real.exp (2*Real.pi*|k| *|y|) := by
    apply Real.exp_le_exp.mpr
    nlinarith [Real.pi_pos]
  change ‖kernel k ((x:ℂ)+(r:ℂ)*I)*horizontal f r x‖ ≤ _
  rw [norm_mul,kernel_line_norm]
  have hh := mul_le_mul hk (hb x r hr) (norm_nonneg _) (Real.exp_pos _).le
  convert hh using 1
  ring

theorem twist_integral (f : ℂ → ℂ) (k y : ℝ) :
    (∫ x, horizontal (twist f k) y x) =
      (Real.exp (2*Real.pi*k*y):ℂ)*(𝓕 (horizontal f y)) k := by
  rw [Real.fourier_real_eq_integral_exp_smul,← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with x
  change kernel k ((x:ℂ)+(y:ℂ)*I)*f ((x:ℂ)+(y:ℂ)*I) = _
  rw [kernel_line]
  simp only [horizontal,smul_eq_mul,mul_assoc]

theorem fourier_shift (f : ℂ → ℂ) (hf : Differentiable ℂ f) (a B y : ℝ)
    (ha : 0 < a)
    (hb : ∀ x r, |r| ≤ |y| → ‖horizontal f r x‖ ≤ B*Real.exp (-a*x^2)) (k : ℝ) :
    (𝓕 (horizontal f 0)) k = (Real.exp (2*Real.pi*k*y):ℂ)*(𝓕 (horizontal f y)) k := by
  have hh := horizontal_integral_eq (twist f k) (twist_differentiable f hf k)
    a (Real.exp (2*Real.pi*|k| *|y|)*B) y ha (twist_gaussian_bound f a B y k hb)
  rw [twist_integral,twist_integral] at hh
  simpa only [mul_zero,Real.exp_zero,ofReal_one,one_mul] using hh

theorem fourier_norm_le_integral_norm (g : ℝ → ℂ) (k : ℝ) :
    ‖(𝓕 g) k‖ ≤ ∫ x, ‖g x‖ := by
  rw [Real.fourier_real_eq]
  apply (norm_integral_le_integral_norm _).trans_eq
  simp only [Circle.norm_smul]

theorem fourier_shift_bound (f : ℂ → ℂ) (hf : Differentiable ℂ f) (a B y : ℝ)
    (ha : 0 < a)
    (hb : ∀ x r, |r| ≤ |y| → ‖horizontal f r x‖ ≤ B*Real.exp (-a*x^2)) (k : ℝ) :
    ‖(𝓕 (horizontal f 0)) k‖ ≤
      Real.exp (2*Real.pi*k*y)*(B*(∫ x : ℝ, Real.exp (-a*x^2))) := by
  rw [fourier_shift f hf a B y ha hb k,norm_mul,Complex.norm_real,Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos _)]
  apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
  apply (fourier_norm_le_integral_norm _ _).trans
  have hi := horizontal_integrable f hf.continuous a B y ha (fun x => hb x y le_rfl)
  have hh := integral_mono hi.norm ((integrable_exp_neg_mul_sq ha).const_mul B)
    (fun x => hb x y le_rfl)
  simpa only [integral_const_mul] using hh

theorem fourier_exponential_decay (f : ℂ → ℂ) (hf : Differentiable ℂ f) (a B d : ℝ)
    (ha : 0 < a) (hd : 0 ≤ d)
    (hb : ∀ x r, |r| ≤ d → ‖horizontal f r x‖ ≤ B*Real.exp (-a*x^2)) (k : ℝ) :
    ‖(𝓕 (horizontal f 0)) k‖ ≤
      Real.exp (-2*Real.pi*d*|k|)*(B*(∫ x : ℝ, Real.exp (-a*x^2))) := by
  by_cases hk : 0 ≤ k
  · have hh := fourier_shift_bound f hf a B (-d) ha
      (fun x r hr => hb x r (by simpa only [abs_neg,abs_of_nonneg hd] using hr)) k
    convert hh using 1
    rw [abs_of_nonneg hk]
    congr 2
    ring
  · have hh := fourier_shift_bound f hf a B d ha
      (fun x r hr => hb x r (by simpa only [abs_of_nonneg hd] using hr)) k
    convert hh using 1
    rw [abs_of_neg (lt_of_not_ge hk)]
    congr 2
    ring

#print axioms kernel_line
#print axioms twist_gaussian_bound
#print axioms fourier_shift
#print axioms fourier_shift_bound
#print axioms fourier_exponential_decay

end
end UnifiedTheory.Audit.KFCausalFourierStripDecay
