/- The mean-one constraint improves a likelihood response estimate. The
range ratio is measured before normalization, with one shared normalizer. -/
import UnifiedTheory.Clay.YangMills.CompactLikelihoodVariance

set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace UnifiedTheory.Clay.YangMills.CompactNormalizedLikelihood
noncomputable section
open MeasureTheory ProbabilityTheory CompactDensityEntropy CompactLikelihoodVariance

/-- Scalar optimization of the Bhatia-Davis bound with a fixed range ratio. -/
theorem range_product_le (R m : ℝ) (hR : 0 < R) :
    (R*m-1)*(1-m) ≤ (R-1)^2/(4*R) := by
  apply (le_div_iff₀ (by positivity : 0 < 4*R)).mpr
  nlinarith [sq_nonneg (2*R*m-(R+1))]

variable {X : Type*} [TopologicalSpace X] [CompactSpace X]
  [MeasurableSpace X] [BorelSpace X] (μ : Measure X) [IsProbabilityMeasure μ]

omit [CompactSpace X] in
/-- Unlike a pointwise deviation estimate, this uses exact normalization. -/
theorem variance_le_range_ratio (r : X → ℝ) (hr : Continuous r)
    (hm : (∫ x, r x ∂μ) = 1) (R m : ℝ) (hR : 0 < R)
    (hb : ∀ x, r x ∈ Set.Icc m (R * m)) :
    variance r μ ≤ (R-1)^2/(4*R) := by
  have h := variance_le_sub_mul_sub (μ := μ) (Filter.Eventually.of_forall hb)
    hr.measurable.aemeasurable
  rw [hm] at h
  exact h.trans (range_product_le R m hR)

/-- Cauchy-Schwarz retains the exact variance of the normalized likelihood. -/
theorem response_sq_le_likelihood_variance (r f : X → ℝ)
    (hr : Continuous r) (hf : Continuous f) (hm : (∫ x, r x ∂μ) = 1) :
    ((∫ x, r x*f x ∂μ)-(∫ x, f x ∂μ))^2 ≤ variance r μ * variance f μ := by
  have h := integral_product_sq μ (fun x => r x-1) (fun x => f x-∫ y, f y ∂μ)
    (hr.sub continuous_const) (hf.sub continuous_const)
  rw [centered_likelihood μ r f hr hf hm,
    ← variance_eq_integral hf.measurable.aemeasurable] at h
  have he : (∫ x, (r x-1)^2 ∂μ) = variance r μ := by
    rw [variance_eq_integral hr.measurable.aemeasurable, hm]
  rw [he] at h
  exact h

/-- The improved coefficient depends only on the unnormalized range ratio. -/
theorem response_sq_le_range_ratio (r f : X → ℝ) (hr : Continuous r) (hf : Continuous f)
    (hm : (∫ x, r x ∂μ) = 1) (R m : ℝ) (hR : 0 < R)
    (hb : ∀ x, r x ∈ Set.Icc m (R * m)) :
    ((∫ x, r x*f x ∂μ)-(∫ x, f x ∂μ))^2 ≤
      ((R-1)^2/(4*R)) * variance f μ := by
  have hv : 0 ≤ variance f μ := by
    rw [variance_eq_integral hf.measurable.aemeasurable]
    exact integral_nonneg (fun x => sq_nonneg _)
  exact (response_sq_le_likelihood_variance μ r f hr hf hm).trans
    (mul_le_mul_of_nonneg_right (variance_le_range_ratio μ r hr hm R m hR hb) hv)

end
end UnifiedTheory.Clay.YangMills.CompactNormalizedLikelihood
