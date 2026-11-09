/- Signed Gram bounds retain cancellations. Orthogonal subtraction of a
single nuisance score is constructed even when that score has zero norm. -/
import UnifiedTheory.Clay.YangMills.CompactGramResponse

set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace UnifiedTheory.Clay.YangMills.CompactScoreResidual
noncomputable section
open MeasureTheory CompactDensityEntropy CompactGramResponse

variable {I : Type*} [Fintype I]
variable {X : Type*} [TopologicalSpace X] [CompactSpace X]
  [MeasurableSpace X] [BorelSpace X] (μ : Measure X) [IsProbabilityMeasure μ]

theorem collective_of_quadratic (s : I → X → ℝ) (hs : ∀ i, Continuous (s i))
    (f : X → ℝ) (hf : Continuous f) (κ : ℝ) (hκ : 0 ≤ κ)
    (hquad : ∀ a : I → ℝ, (∑ i, ∑ j, a i*a j*gram μ s i j) ≤ κ*∑ i, (a i)^2) :
    (∑ i, (∫ x, s i x*(f x-∫ y, f y ∂μ) ∂μ)^2) ≤
      κ * ProbabilityTheory.variance f μ := by
  let d : I → ℝ := fun i => ∫ x, s i x*(f x-∫ y, f y ∂μ) ∂μ
  let S := ∑ i, (d i)^2
  let A := fun x => ∑ i, d i*s i x
  have hA : Continuous A := continuous_finset_sum _ (fun i _ => continuous_const.mul (hs i))
  have he : (∫ x, A x*(f x-∫ y, f y ∂μ) ∂μ) = S := by
    simp only [A, Finset.sum_mul]
    have hi (i : I) : Integrable (fun x => d i*s i x*(f x-∫ y, f y ∂μ)) μ :=
      continuous_integrable μ _ ((continuous_const.mul (hs i)).mul (hf.sub continuous_const))
    rw [integral_finset_sum _ (fun i _ => hi i)]
    simp_rw [mul_assoc, integral_const_mul]
    simp only [S, d, pow_two]
  have hq : (∫ x, (A x)^2 ∂μ) ≤ κ*S := by
    rw [gram_quadratic μ s hs d]
    exact hquad d
  have hc := integral_product_sq μ A (fun x => f x-∫ y, f y ∂μ)
    hA (hf.sub continuous_const)
  rw [he, ← ProbabilityTheory.variance_eq_integral hf.measurable.aemeasurable] at hc
  have hv : 0 ≤ ProbabilityTheory.variance f μ := by
    rw [ProbabilityTheory.variance_eq_integral hf.measurable.aemeasurable]
    exact integral_nonneg (fun x => sq_nonneg _)
  have hS : 0 ≤ S := Finset.sum_nonneg (fun i _ => sq_nonneg _)
  have hh := hc.trans (mul_le_mul_of_nonneg_right hq hv)
  change S ≤ κ * ProbabilityTheory.variance f μ
  by_cases hz : S = 0
  · rw [hz]
    exact mul_nonneg hκ hv
  · have hp : 0 < S := lt_of_le_of_ne hS (Ne.symm hz)
    nlinarith


def pair (s t : X → ℝ) : ℝ := ∫ x, s x*t x ∂μ

omit [Fintype I] [TopologicalSpace X] [CompactSpace X] [BorelSpace X]
  [IsProbabilityMeasure μ] in
theorem pair_symm (s t : X → ℝ) : pair μ s t = pair μ t s := by
  simp only [pair, mul_comm]

omit [Fintype I] [TopologicalSpace X] [CompactSpace X] [BorelSpace X]
  [IsProbabilityMeasure μ] in
theorem pair_self_nonneg (t : X → ℝ) : 0 ≤ pair μ t t :=
  integral_nonneg (fun x => mul_self_nonneg (t x))

omit [Fintype I] in
theorem pair_sq_le (s t : X → ℝ) (hs : Continuous s) (ht : Continuous t) :
    (pair μ s t)^2 ≤ pair μ s s * pair μ t t := by
  simpa only [pair, pow_two] using integral_product_sq μ s t hs ht

omit [Fintype I] in
theorem pair_zero_of_self_zero (s t : X → ℝ) (hs : Continuous s) (ht : Continuous t)
    (hz : pair μ t t = 0) : pair μ s t = 0 := by
  have h := pair_sq_le μ s t hs ht
  rw [hz, mul_zero] at h
  nlinarith [sq_nonneg (pair μ s t)]

def coefficient (s t : X → ℝ) : ℝ := pair μ s t / pair μ t t

def residual (s t : X → ℝ) (x : X) : ℝ := s x-coefficient μ s t*t x

omit [Fintype I] [CompactSpace X] [BorelSpace X] [IsProbabilityMeasure μ] in
theorem residual_continuous (s t : X → ℝ) (hs : Continuous s) (ht : Continuous t) :
    Continuous (residual μ s t) := hs.sub (continuous_const.mul ht)

omit [Fintype I] in
theorem coefficient_normal (s t : X → ℝ) (hs : Continuous s) (ht : Continuous t) :
    coefficient μ s t * pair μ t t = pair μ s t := by
  by_cases hz : pair μ t t = 0
  · simp only [coefficient, hz, div_zero, mul_zero, pair_zero_of_self_zero μ s t hs ht hz]
  · exact div_mul_cancel₀ _ hz

omit [Fintype I] in
theorem pair_residual_left (s t r : X → ℝ)
    (hs : Continuous s) (ht : Continuous t) (hr : Continuous r) :
    pair μ (residual μ s t) r = pair μ s r-coefficient μ s t*pair μ t r := by
  unfold pair residual
  simp_rw [sub_mul, mul_assoc]
  have hi := integral_sub (continuous_integrable μ _ (hs.mul hr))
    ((continuous_integrable μ _ (ht.mul hr)).const_mul (coefficient μ s t))
  simp only [Pi.mul_apply] at hi
  rw [hi, integral_const_mul]

omit [Fintype I] in
theorem pair_residual_right (s t r : X → ℝ)
    (hs : Continuous s) (ht : Continuous t) (hr : Continuous r) :
    pair μ r (residual μ s t) = pair μ r s-coefficient μ s t*pair μ r t := by
  rw [pair_symm, pair_residual_left μ s t r hs ht hr,
    pair_symm μ s r, pair_symm μ t r]

omit [Fintype I] in
theorem residual_orthogonal (s t : X → ℝ) (hs : Continuous s) (ht : Continuous t) :
    pair μ (residual μ s t) t = 0 := by
  rw [pair_residual_left μ s t t hs ht ht, coefficient_normal μ s t hs ht, sub_self]

omit [Fintype I] in
/-- Removing a score orthogonal to the tested observable leaves its response unchanged. -/
theorem residual_response (s t f : X → ℝ)
    (hs : Continuous s) (ht : Continuous t) (hf : Continuous f)
    (hzero : (∫ x, t x * (f x - ∫ y, f y ∂μ) ∂μ) = 0) :
    (∫ x, residual μ s t x * (f x - ∫ y, f y ∂μ) ∂μ) =
      ∫ x, s x*(f x-∫ y, f y ∂μ) ∂μ := by
  have h := pair_residual_left μ s t (fun x => f x-∫ y, f y ∂μ)
    hs ht (hf.sub continuous_const)
  unfold pair at h
  rw [hzero, mul_zero, sub_zero] at h
  exact h

omit [Fintype I] in
/-- Exact rank-one subtraction, with the zero-variance case included by real division at zero. -/
theorem residual_pair (s r t : X → ℝ)
    (hs : Continuous s) (hr : Continuous r) (ht : Continuous t) :
    pair μ (residual μ s t) (residual μ r t) =
      pair μ s r - pair μ s t*pair μ r t / pair μ t t := by
  rw [pair_residual_left μ s t _ hs ht (residual_continuous μ r t hr ht),
    pair_residual_right μ r t s hr ht hs, pair_residual_right μ r t t hr ht ht,
    coefficient_normal μ r t hr ht, pair_symm μ t r, sub_self, mul_zero, sub_zero]
  unfold coefficient
  ring

theorem residual_gram_quadratic (s : I → X → ℝ) (t : X → ℝ)
    (hs : ∀ i, Continuous (s i)) (ht : Continuous t) (a : I → ℝ) :
    (∑ i, ∑ j, a i*a j*gram μ (fun k => residual μ (s k) t) i j) =
      (∑ i, ∑ j, a i*a j*gram μ s i j) -
        (∑ i, a i*pair μ (s i) t)^2 / pair μ t t := by
  have he (i j : I) : gram μ (fun k => residual μ (s k) t) i j =
      gram μ s i j - pair μ (s i) t*pair μ (s j) t / pair μ t t :=
    residual_pair μ (s i) (s j) t (hs i) (hs j) ht
  simp_rw [he, mul_sub, Finset.sum_sub_distrib]
  congr 1
  rw [pow_two, Finset.sum_mul]
  simp_rw [Finset.mul_sum, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- The actual quadratic form decreases; no entrywise sign assumption is required. -/
theorem residual_gram_le (s : I → X → ℝ) (t : X → ℝ)
    (hs : ∀ i, Continuous (s i)) (ht : Continuous t) (a : I → ℝ) :
    (∑ i, ∑ j, a i*a j*gram μ (fun k => residual μ (s k) t) i j) ≤
      ∑ i, ∑ j, a i*a j*gram μ s i j := by
  rw [residual_gram_quadratic μ s t hs ht a]
  exact sub_le_self _ (div_nonneg (sq_nonneg _) (pair_self_nonneg μ t))

end
end UnifiedTheory.Clay.YangMills.CompactScoreResidual
