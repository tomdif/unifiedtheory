/- Likelihood response is controlled by actual variance, without an
observable-range factor. All densities and moments remain explicit. -/
import UnifiedTheory.Clay.YangMills.CompactDensityEntropy

set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace UnifiedTheory.Clay.YangMills.CompactLikelihoodVariance
noncomputable section
open MeasureTheory ProbabilityTheory CompactDensityEntropy

theorem ratio_deviation (r L : ℝ) (hL : 1 ≤ L) (hr : r ≤ L) (hl : 1 ≤ L * r) :
    |r-1| ≤ L-1 := by
  rw [abs_le]
  constructor
  · by_cases h : r ≤ 1
    · nlinarith [mul_nonneg (sub_nonneg.mpr hL) (sub_nonneg.mpr h)]
    · linarith
  · linarith

variable {X : Type*} [TopologicalSpace X] [CompactSpace X]
  [MeasurableSpace X] [BorelSpace X] (μ : Measure X) [IsProbabilityMeasure μ]

theorem variance_formula (f : X → ℝ) (hf : Continuous f) :
    variance f μ = (∫ x, (f x)^2 ∂μ) - (∫ x, f x ∂μ)^2 := by
  exact variance_eq_sub (hf.memLp_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))

theorem centered_likelihood (r f : X → ℝ) (hr : Continuous r) (hf : Continuous f)
    (hm : (∫ x, r x ∂μ) = 1) :
    (∫ x, (r x-1)*(f x-∫ y, f y ∂μ) ∂μ) =
      (∫ x, r x*f x ∂μ) - (∫ x, f x ∂μ) := by
  let m := ∫ y, f y ∂μ
  have hiR := continuous_integrable μ _ hr
  have hiF := continuous_integrable μ _ hf
  have hiRF := continuous_integrable μ _ (hr.mul hf)
  have h1 := integral_add ((hiRF.sub hiF).sub (hiR.const_mul m)) (integrable_const m)
  have h2 := integral_sub (hiRF.sub hiF) (hiR.const_mul m)
  have h3 := integral_sub hiRF hiF
  simp only [Pi.sub_apply, Pi.mul_apply] at h1 h2 h3
  calc
    _ = ∫ x, (r x*f x-f x)-m*r x+m ∂μ := by
      apply integral_congr_ae
      filter_upwards with x
      dsimp only [m]
      ring
    _ = _ := by
      rw [h1, h2, h3, integral_const_mul, hm, integral_const, probReal_univ,
        smul_eq_mul, one_mul]
      ring

/-- A normalized likelihood bound pays for response with the actual source variance. -/
theorem response_sq_le_variance (r f : X → ℝ) (hr : Continuous r) (hf : Continuous f)
    (hm : (∫ x, r x ∂μ) = 1) (b : ℝ) (hb : 0 ≤ b)
    (hbound : ∀ x, |r x - 1| ≤ b) :
    ((∫ x, r x*f x ∂μ)-(∫ x, f x ∂μ))^2 ≤ b^2 * variance f μ := by
  have h := integral_product_sq μ (fun x => r x-1) (fun x => f x-∫ y, f y ∂μ)
    (hr.sub continuous_const) (hf.sub continuous_const)
  rw [centered_likelihood μ r f hr hf hm,
    ← variance_eq_integral hf.measurable.aemeasurable] at h
  have hsq (x : X) : (r x-1)^2 ≤ b^2 := by
    simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) hb).mpr (hbound x)
  have hc := integral_mono (continuous_integrable μ _ ((hr.sub continuous_const).pow 2))
    (integrable_const (b^2)) hsq
  rw [integral_const, probReal_univ, smul_eq_mul, one_mul] at hc
  have hv : 0 ≤ variance f μ := by
    rw [variance_eq_integral hf.measurable.aemeasurable]
    exact integral_nonneg (fun x => sq_nonneg _)
  exact h.trans (mul_le_mul_of_nonneg_right hc hv)

end
end UnifiedTheory.Clay.YangMills.CompactLikelihoodVariance
