/- Contour translation needs analyticity only near the closed strip
being traversed. This version permits inverse-clock coefficients, which
have a proved analytic branch there but are not asserted to be entire. -/
import UnifiedTheory.Audit.KFCausalFourierStripDecay

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 800000

namespace UnifiedTheory.Audit.KFCausalLocalStripContour
noncomputable section
open MeasureTheory Set Filter Complex
open scoped Topology FourierTransform
open UnifiedTheory.Audit.KFCausalGaussianContourShift
open UnifiedTheory.Audit.KFCausalFourierStripDecay

theorem horizontal_continuous (f : ℂ → ℂ) (y r : ℝ)
    (hf : ∀ z : ℂ, |z.im| ≤ |y| → DifferentiableAt ℂ f z) (hr : |r| ≤ |y|) :
    Continuous (horizontal f r) := by
  apply continuous_iff_continuousAt.mpr
  intro x
  have hz : |((x:ℂ)+(r:ℂ)*I).im| ≤ |y| := by simpa using hr
  change ContinuousAt (fun x : ℝ => f ((x:ℂ)+(r:ℂ)*I)) x
  exact (hf _ hz).continuousAt.comp (f := fun x : ℝ => (x:ℂ)+(r:ℂ)*I)
    (show ContinuousAt (fun x : ℝ => (x:ℂ)+(r:ℂ)*I) x by fun_prop)

theorem horizontal_integral_eq_strip (f : ℂ → ℂ) (a B y : ℝ)
    (hf : ∀ z : ℂ, |z.im| ≤ |y| → DifferentiableAt ℂ f z) (ha : 0 < a)
    (hb : ∀ x r, |r| ≤ |y| → ‖horizontal f r x‖ ≤ B*Real.exp (-a*x^2)) :
    (∫ x, horizontal f 0 x) = ∫ x, horizontal f y x := by
  have hi (r : ℝ) (hr : |r| ≤ |y|) : Integrable (horizontal f r) := by
    apply ((integrable_exp_neg_mul_sq ha).const_mul B).mono'
      (horizontal_continuous f y r hf hr).aestronglyMeasurable
    exact Eventually.of_forall (fun x => hb x r hr)
  have hi0 := hi 0 (by simp)
  have hiy := hi y le_rfl
  have hv := vertical_tendsto_zero f a B y ha hb
  have hr (T : ℝ) :
      (∫ x : ℝ in -T..T, horizontal f 0 x) - (∫ x : ℝ in -T..T, horizontal f y x) +
        I*vertical f y T-I*vertical f y (-T) = 0 := by
    have hh := integral_boundary_rect_eq_zero_of_differentiableOn f (-T) ((T:ℂ)+(y:ℂ)*I)
      (by
        intro z hz
        have hm : z.im ∈ uIcc 0 y := by simpa using hz.2
        have hm' : |z.im| ≤ |y| := by simpa using abs_sub_left_of_mem_uIcc hm
        exact (hf z hm').differentiableWithinAt)
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

theorem fourier_shift_strip (f : ℂ → ℂ) (a B y : ℝ)
    (hf : ∀ z : ℂ, |z.im| ≤ |y| → DifferentiableAt ℂ f z) (ha : 0 < a)
    (hb : ∀ x r, |r| ≤ |y| → ‖horizontal f r x‖ ≤ B*Real.exp (-a*x^2)) (k : ℝ) :
    (𝓕 (horizontal f 0)) k = (Real.exp (2*Real.pi*k*y):ℂ)*(𝓕 (horizontal f y)) k := by
  have ht : ∀ z : ℂ, |z.im| ≤ |y| → DifferentiableAt ℂ (twist f k) z := by
    intro z hz
    have hk : DifferentiableAt ℂ (kernel k) z := by unfold kernel; fun_prop
    exact hk.mul (hf z hz)
  have hh := horizontal_integral_eq_strip (twist f k)
    a (Real.exp (2*Real.pi*|k| *|y|)*B) y ht ha (twist_gaussian_bound f a B y k hb)
  rw [twist_integral,twist_integral] at hh
  simpa only [mul_zero,Real.exp_zero,ofReal_one,one_mul] using hh

#print axioms horizontal_continuous
#print axioms horizontal_integral_eq_strip
#print axioms fourier_shift_strip

end
end UnifiedTheory.Audit.KFCausalLocalStripContour
