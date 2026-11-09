/- A contour-shift lemma with explicit Gaussian bounds on the vertical
edges. No equality of horizontal integrals or Fourier decay is assumed. -/
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 800000

namespace UnifiedTheory.Audit.KFCausalGaussianContourShift
noncomputable section
open MeasureTheory Set Filter Complex
open scoped Topology

def horizontal (f : ℂ → ℂ) (y : ℝ) (x : ℝ) : ℂ := f ((x:ℂ)+(y:ℂ)*I)
def vertical (f : ℂ → ℂ) (y T : ℝ) : ℂ := ∫ r : ℝ in 0..y, f ((T:ℂ)+(r:ℂ)*I)

theorem abs_le_of_mem_uIoc (y r : ℝ) (hr : r ∈ uIoc 0 y) : |r| ≤ |y| := by
  rcases le_or_gt 0 y with h | h
  · rw [uIoc_of_le h] at hr
    rw [abs_of_nonneg h,abs_of_pos hr.1]
    exact hr.2
  · rw [uIoc_of_ge h.le] at hr
    rw [abs_of_neg h,abs_of_nonpos hr.2]
    exact neg_le_neg hr.1.le

theorem horizontal_integrable (f : ℂ → ℂ) (hf : Continuous f) (a B y : ℝ)
    (ha : 0 < a) (hb : ∀ x, ‖horizontal f y x‖ ≤ B*Real.exp (-a*x^2)) :
    Integrable (horizontal f y) := by
  apply ((integrable_exp_neg_mul_sq ha).const_mul B).mono'
    (show Continuous (horizontal f y) by unfold horizontal; fun_prop).aestronglyMeasurable
  exact Eventually.of_forall hb

theorem vertical_norm_bound (f : ℂ → ℂ) (a B y T : ℝ)
    (hb : ∀ x r, |r| ≤ |y| → ‖horizontal f r x‖ ≤ B*Real.exp (-a*x^2)) :
    ‖vertical f y T‖ ≤ |y| *(B*Real.exp (-a*T^2)) := by
  unfold vertical
  have hh : ∀ r ∈ uIoc 0 y, ‖f ((T:ℂ)+(r:ℂ)*I)‖ ≤ B*Real.exp (-a*T^2) := by
    intro r hr
    exact hb T r (abs_le_of_mem_uIoc y r hr)
  have hi := intervalIntegral.norm_integral_le_of_norm_le_const hh
  simpa only [sub_zero,mul_comm] using hi

theorem gaussian_tendsto_zero (a : ℝ) (ha : 0 < a) :
    Tendsto (fun T : ℝ => Real.exp (-a*T^2)) atTop (𝓝 0) :=
  Real.tendsto_exp_atBot.comp ((tendsto_pow_atTop two_ne_zero).const_mul_atTop_of_neg (neg_lt_zero.mpr ha))

theorem vertical_tendsto_zero (f : ℂ → ℂ) (a B y : ℝ) (ha : 0 < a)
    (hb : ∀ x r, |r| ≤ |y| → ‖horizontal f r x‖ ≤ B*Real.exp (-a*x^2)) :
    Tendsto (vertical f y) atTop (𝓝 0) ∧
      Tendsto (fun T => vertical f y (-T)) atTop (𝓝 0) := by
  have hl : Tendsto (fun T : ℝ => |y| *(B*Real.exp (-a*T^2))) atTop (𝓝 0) := by
    simpa using ((gaussian_tendsto_zero a ha).const_mul B).const_mul |y|
  constructor <;> rw [tendsto_zero_iff_norm_tendsto_zero]
  · exact squeeze_zero (fun _ => norm_nonneg _) (fun T => vertical_norm_bound f a B y T hb) hl
  · apply squeeze_zero (fun _ => norm_nonneg _) (fun T => ?_) hl
    simpa only [neg_sq] using vertical_norm_bound f a B y (-T) hb

theorem horizontal_integral_eq (f : ℂ → ℂ) (hf : Differentiable ℂ f)
    (a B y : ℝ) (ha : 0 < a)
    (hb : ∀ x r, |r| ≤ |y| → ‖horizontal f r x‖ ≤ B*Real.exp (-a*x^2)) :
    (∫ x, horizontal f 0 x) = ∫ x, horizontal f y x := by
  have hi0 := horizontal_integrable f hf.continuous a B 0 ha
    (fun x => hb x 0 (by simp))
  have hiy := horizontal_integrable f hf.continuous a B y ha (fun x => hb x y le_rfl)
  have hv := vertical_tendsto_zero f a B y ha hb
  have hr (T : ℝ) :
      (∫ x : ℝ in -T..T, horizontal f 0 x) - (∫ x : ℝ in -T..T, horizontal f y x) +
        I*vertical f y T-I*vertical f y (-T) = 0 := by
    have hh := integral_boundary_rect_eq_zero_of_differentiableOn f (-T) ((T:ℂ)+(y:ℂ)*I)
      hf.differentiableOn
    simpa only [horizontal,vertical,neg_im,ofReal_im,neg_zero,ofReal_zero,zero_mul,add_zero,
      neg_re,ofReal_re,add_re,mul_re,I_re,mul_zero,I_im,sub_zero,add_im,mul_im,mul_one,
      zero_add,smul_eq_mul,ofReal_neg] using hh
  have ht0 : Tendsto (fun T : ℝ => ∫ x : ℝ in -T..T, horizontal f 0 x) atTop
      (𝓝 (∫ x, horizontal f 0 x)) :=
    intervalIntegral_tendsto_integral hi0 tendsto_neg_atTop_atBot tendsto_id
  have hty : Tendsto (fun T : ℝ => ∫ x : ℝ in -T..T, horizontal f y x) atTop
      (𝓝 (∫ x, horizontal f y x)) :=
    intervalIntegral_tendsto_integral hiy tendsto_neg_atTop_atBot tendsto_id
  have ht := ((ht0.sub hty).add (hv.1.const_mul I)).sub (hv.2.const_mul I)
  have hz : Tendsto (fun T : ℝ =>
      (∫ x : ℝ in -T..T, horizontal f 0 x) - (∫ x : ℝ in -T..T, horizontal f y x) +
        I*vertical f y T-I*vertical f y (-T)) atTop (𝓝 0) := by
    simpa only [hr] using (tendsto_const_nhds : Tendsto (fun _ : ℝ => (0:ℂ)) atTop (𝓝 0))
  have he := tendsto_nhds_unique ht hz
  simpa only [mul_zero,add_zero,sub_zero,sub_eq_zero] using he

#print axioms horizontal_integrable
#print axioms vertical_norm_bound
#print axioms vertical_tendsto_zero
#print axioms horizontal_integral_eq

end
end UnifiedTheory.Audit.KFCausalGaussianContourShift
