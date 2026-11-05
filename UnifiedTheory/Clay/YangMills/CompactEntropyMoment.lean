/- Relative entropy controls response with the true centered second moment,
provided the compared density has an explicit relative upper bound. -/
import UnifiedTheory.Clay.YangMills.CompactLikelihoodVariance

set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace UnifiedTheory.Clay.YangMills.CompactEntropyMoment
noncomputable section
open MeasureTheory CompactDensityEntropy

variable {X : Type*} [TopologicalSpace X] [CompactSpace X]
  [MeasurableSpace X] [BorelSpace X] (μ : Measure X) [IsProbabilityMeasure μ]

/-- The center is arbitrary; choosing the actual mean gives the actual variance. -/
theorem response_sq_le_entropy_moment (p q f : X → ℝ)
    (hp : Continuous p) (hq : Continuous q) (hf : Continuous f)
    (hp0 : ∀ x, 0 < p x) (hq0 : ∀ x, 0 < q x)
    (hpm : (∫ x, p x ∂μ) = 1) (hqm : (∫ x, q x ∂μ) = 1)
    (R c : ℝ) (hR : 0 ≤ R) (hr : ∀ x, q x ≤ R * p x) :
    ((∫ x, p x*f x ∂μ)-(∫ x, q x*f x ∂μ))^2 ≤
      (2*(1+R))*(∫ x, p x*(f x-c)^2 ∂μ)*entropy μ p q := by
  let a := fun x => Real.sqrt (p x)-Real.sqrt (q x)
  let b := fun x => (f x-c)*(Real.sqrt (p x)+Real.sqrt (q x))
  have ha : Continuous a := hp.sqrt.sub hq.sqrt
  have hb : Continuous b := (hf.sub continuous_const).mul (hp.sqrt.add hq.sqrt)
  have he : (∫ x, a x*b x ∂μ) =
      (∫ x, p x*f x ∂μ)-(∫ x, q x*f x ∂μ) := by
    have hpw := continuous_integrable μ _ hp
    have hqw := continuous_integrable μ _ hq
    calc
      _ = ∫ x, (p x*f x-q x*f x)-c*(p x-q x) ∂μ := by
        apply integral_congr_ae
        filter_upwards with x
        dsimp [a, b]
        calc
          _ = (f x-c)*((Real.sqrt (p x))^2-(Real.sqrt (q x))^2) := by ring
          _ = _ := by rw [Real.sq_sqrt (hp0 x).le, Real.sq_sqrt (hq0 x).le]; ring
      _ = _ := by
        have houter := integral_sub ((continuous_integrable μ _ (hp.mul hf)).sub
          (continuous_integrable μ _ (hq.mul hf))) ((hpw.sub hqw).const_mul c)
        have hinner := integral_sub (continuous_integrable μ _ (hp.mul hf))
          (continuous_integrable μ _ (hq.mul hf))
        have hpq := integral_sub hpw hqw
        simp only [Pi.sub_apply, Pi.mul_apply] at houter hinner hpq
        rw [houter, hinner, integral_const_mul, hpq, hpm, hqm]
        ring
  have hmoment : 0 ≤ ∫ x, p x*(f x-c)^2 ∂μ :=
    integral_nonneg (fun x => mul_nonneg (hp0 x).le (sq_nonneg _))
  have hb2 : (∫ x, (b x)^2 ∂μ) ≤ (2*(1+R))*(∫ x, p x*(f x-c)^2 ∂μ) := by
    have hx (x : X) : (b x)^2 ≤ (2*(1+R))*(p x*(f x-c)^2) := by
      have hs : (Real.sqrt (p x)+Real.sqrt (q x))^2 ≤ (2*(1+R))*p x := by
        nlinarith [sq_nonneg (Real.sqrt (p x)-Real.sqrt (q x)),
          Real.sq_sqrt (hp0 x).le, Real.sq_sqrt (hq0 x).le, hr x]
      have ht := mul_le_mul_of_nonneg_left hs (sq_nonneg (f x-c))
      dsimp [b]
      nlinarith
    have h := integral_mono (continuous_integrable μ _ (hb.pow 2))
      (continuous_integrable μ _ (continuous_const.mul
        (hp.mul ((hf.sub continuous_const).pow 2)))) hx
    simpa only [Pi.mul_apply, integral_const_mul] using h
  have hc := integral_product_sq μ a b ha hb
  rw [he] at hc
  calc
    _ ≤ _ := hc
    _ ≤ (∫ x, (a x)^2 ∂μ)*((2*(1+R))*(∫ x, p x*(f x-c)^2 ∂μ)) :=
      mul_le_mul_of_nonneg_left hb2 (integral_nonneg (fun x => sq_nonneg _))
    _ ≤ entropy μ p q*((2*(1+R))*(∫ x, p x*(f x-c)^2 ∂μ)) :=
      mul_le_mul_of_nonneg_right (hellinger_le_entropy μ p q hp hq hp0 hq0 hpm hqm)
        (mul_nonneg (by positivity) hmoment)
    _ = _ := by ring

omit [CompactSpace X] in
/-- Centering at any constant can only increase the true variance. -/
theorem variance_le_centered_moment (f : X → ℝ) (hf : Continuous f) (c : ℝ) :
    ProbabilityTheory.variance f μ ≤ ∫ x, (f x-c)^2 ∂μ := by
  have h := ProbabilityTheory.variance_le_expectation_sq (μ := μ) (X := fun x => f x-c)
    ((hf.sub continuous_const).measurable.aestronglyMeasurable)
  rw [ProbabilityTheory.variance_sub_const hf.measurable.aestronglyMeasurable c] at h
  exact h

omit μ [IsProbabilityMeasure μ] in
/-- A two-sided variance ratio controls the difference of standard deviations. -/
theorem sqrt_gap (a b r : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hr : 1 ≤ r)
    (hab : a ≤ r ^ 2 * b) (hba : b ≤ r ^ 2 * a) :
    (Real.sqrt b-Real.sqrt a)^2 ≤ (r-1)^2*a := by
  have hx := Real.sqrt_nonneg a
  have hy := Real.sqrt_nonneg b
  have hxa := Real.sq_sqrt ha
  have hyb := Real.sq_sqrt hb
  have hxy : Real.sqrt a ≤ r*Real.sqrt b := by
    nlinarith [mul_nonneg (show 0 ≤ r by linarith) hy]
  have hyx : Real.sqrt b ≤ r*Real.sqrt a := by
    nlinarith [mul_nonneg (show 0 ≤ r by linarith) hx]
  have habs : |Real.sqrt b-Real.sqrt a| ≤ (r-1)*Real.sqrt a := by
    apply abs_le.mpr
    constructor
    · by_cases h : Real.sqrt a ≤ Real.sqrt b
      · nlinarith
      · have hh := mul_le_mul_of_nonneg_left (le_of_not_ge h) (sub_nonneg.mpr hr)
        nlinarith
    · nlinarith
  have h := (sq_le_sq₀ (abs_nonneg _) (mul_nonneg (sub_nonneg.mpr hr) hx)).mpr habs
  simpa only [sq_abs, mul_pow, hxa] using h

end
end UnifiedTheory.Clay.YangMills.CompactEntropyMoment
