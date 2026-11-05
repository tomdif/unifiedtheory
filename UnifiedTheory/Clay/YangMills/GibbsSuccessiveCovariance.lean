/- Successive covariance removal under the actual induced compact Gibbs laws.
The second action is the negative logarithm of the first fiber partition, and
its source is the first normalized response. The two removed forms are
orthogonal under the original law. No repeated-scale smallness is assumed. -/
import UnifiedTheory.Clay.YangMills.GibbsCrossCovariance

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Clay.YangMills.GibbsSuccessiveCovariance
noncomputable section
open MeasureTheory Filter GibbsMarginalTower GibbsCrossCovariance

section OneStep
variable {B X : Type*}
  [TopologicalSpace B] [CompactSpace B] [SecondCountableTopology B]
  [MeasurableSpace B] [BorelSpace B]
  [TopologicalSpace X] [CompactSpace X] [SecondCountableTopology X]
  [MeasurableSpace X] [BorelSpace X]
  (μB : Measure B) (μX : Measure X) [IsProbabilityMeasure μB] [IsProbabilityMeasure μX]

/-- The actual covariance removed by one integration, as a fluctuation Gram form. -/
def gram (A F G : B × X → ℝ) : ℝ :=
  ∫ p, removed μX A F p * removed μX A G p
    ∂CompactGibbsContinuity.law (μB.prod μX) A

omit [TopologicalSpace B] [CompactSpace B] [SecondCountableTopology B] [BorelSpace B]
  [TopologicalSpace X] [CompactSpace X] [SecondCountableTopology X] [BorelSpace X]
  [IsProbabilityMeasure μB] [IsProbabilityMeasure μX] in
theorem gram_self_nonneg (A F : B × X → ℝ) : 0 ≤ gram μB μX A F F :=
  integral_nonneg (fun _ => mul_self_nonneg _)

theorem gram_eq_conditional (A F G : B × X → ℝ) (hA : Continuous A)
    (hF : Continuous F) (hG : Continuous G) :
    gram μB μX A F G =
      ∫ b, conditionalCovariance μX A F G b ∂marginal μB μX A := by
  have h := response_expectation μB μX A
    (fun p => removed μX A F p * removed μX A G p) hA
    ((removed_continuous μX A F hA hF).mul (removed_continuous μX A G hA hG))
  simp_rw [conditional_removed_product μX A F G hA hF hG] at h
  exact h.symm

/-- The full covariance splits into its actual removed Gram form and retained covariance. -/
theorem covariance_decomposition (A F G : B × X → ℝ) (hA : Continuous A)
    (hF : Continuous F) (hG : Continuous G) :
    covariance (CompactGibbsContinuity.law (μB.prod μX) A) F G =
      gram μB μX A F G +
      covariance (marginal μB μX A) (response μX A F) (response μX A G) := by
  rw [gram_eq_conditional μB μX A F G hA hF hG]
  exact total_covariance μB μX A F G hA hF hG

/-- Every continuous retained-coordinate multiplier is orthogonal to the removed fluctuation. -/
theorem removed_boundary_orthogonal (A F : B × X → ℝ) (H : B → ℝ)
    (hA : Continuous A) (hF : Continuous F) (hH : Continuous H) :
    (∫ p, removed μX A F p * H p.1 ∂CompactGibbsContinuity.law (μB.prod μX) A) = 0 := by
  have hr (b : B) : response μX A (fun p => removed μX A F p * H p.1) b = 0 := by
    rw [response_eq_expectation μX A _ hA b]
    change (∫ x, removed μX A F (b, x) * H b
      ∂CompactGibbsContinuity.law μX (fun x => A (b, x))) = 0
    rw [integral_mul_const]
    rw [← response_eq_expectation μX A (removed μX A F) hA b,
      removed_response μX A F hA hF b, zero_mul]
  have h := response_expectation μB μX A (fun p => removed μX A F p * H p.1) hA
    ((removed_continuous μX A F hA hF).mul (hH.comp continuous_fst))
  simp_rw [hr] at h
  simpa only [integral_zero] using h.symm

/-- A retained-coordinate integral is taken under the genuine pushforward law. -/
theorem boundary_integral (A : B × X → ℝ) (H : B → ℝ)
    (hA : Continuous A) (hH : Continuous H) :
    (∫ p, H p.1 ∂CompactGibbsContinuity.law (μB.prod μX) A) =
      ∫ b, H b ∂marginal μB μX A := by
  have h := response_expectation μB μX A (fun p => H p.1) hA (hH.comp continuous_fst)
  simp_rw [response_boundary μX A hA H] at h
  exact h.symm

end OneStep

/-- A continuous real covariance has a nonnegative diagonal under a probability law. -/
theorem covariance_self_nonneg {W : Type*} [TopologicalSpace W] [CompactSpace W]
    [MeasurableSpace W] [BorelSpace W] (ν : Measure W) [IsProbabilityMeasure ν]
    (H : W → ℝ) (hH : Continuous H) : 0 ≤ covariance ν H H := by
  rw [covariance_eq_centered ν H H hH hH]
  exact integral_nonneg (fun _ => mul_self_nonneg _)

section TwoSteps
variable {X Y Z : Type*}
  [TopologicalSpace X] [CompactSpace X] [SecondCountableTopology X]
  [MeasurableSpace X] [BorelSpace X]
  [TopologicalSpace Y] [CompactSpace Y] [SecondCountableTopology Y]
  [MeasurableSpace Y] [BorelSpace Y]
  [TopologicalSpace Z] [CompactSpace Z] [SecondCountableTopology Z]
  [MeasurableSpace Z] [BorelSpace Z]
  (μZ : Measure Z) (μY : Measure Y) (μX : Measure X)
  [IsProbabilityMeasure μZ] [IsProbabilityMeasure μY] [IsProbabilityMeasure μX]

/-- The second removed form uses the actual first effective action and first source response. -/
def secondGram (A F G : (Z × Y) × X → ℝ) : ℝ :=
  gram μZ μY (effectiveAction μX A) (response μX A F) (response μX A G)

/-- The cumulative fluctuation removed by the two genuine successive integrations. -/
def jointNoise (A F : (Z × Y) × X → ℝ) (p : (Z × Y) × X) : ℝ :=
  F p - response μY (effectiveAction μX A) (response μX A F) p.1.1

omit [TopologicalSpace X] [CompactSpace X] [SecondCountableTopology X] [BorelSpace X]
  [TopologicalSpace Y] [CompactSpace Y] [SecondCountableTopology Y] [BorelSpace Y]
  [TopologicalSpace Z] [CompactSpace Z] [SecondCountableTopology Z] [BorelSpace Z]
  [IsProbabilityMeasure μZ] [IsProbabilityMeasure μY] [IsProbabilityMeasure μX] in
theorem secondGram_self_nonneg (A F : (Z × Y) × X → ℝ) :
    0 ≤ secondGram μZ μY μX A F F :=
  gram_self_nonneg μZ μY _ _

/-- Exact telescoping covariance: the intermediate law is induced, not reused original law. -/
theorem successive_covariance (A F G : (Z × Y) × X → ℝ) (hA : Continuous A)
    (hF : Continuous F) (hG : Continuous G) :
    covariance (CompactGibbsContinuity.law ((μZ.prod μY).prod μX) A) F G =
      gram (μZ.prod μY) μX A F G + secondGram μZ μY μX A F G +
      covariance (marginal μZ μY (effectiveAction μX A))
        (response μY (effectiveAction μX A) (response μX A F))
        (response μY (effectiveAction μX A) (response μX A G)) := by
  rw [covariance_decomposition (μZ.prod μY) μX A F G hA hF hG,
    marginal_eq_effectiveLaw (μZ.prod μY) μX A hA,
    covariance_decomposition μZ μY (effectiveAction μX A)
      (response μX A F) (response μX A G) (effectiveAction_continuous μX A hA)
      (response_continuous μX A F hA hF) (response_continuous μX A G hA hG)]
  simp only [secondGram, add_assoc]

/-- Cross-stage noise is exactly orthogonal under the original interacting law. -/
theorem successive_noise_orthogonal (A F G : (Z × Y) × X → ℝ) (hA : Continuous A)
    (hF : Continuous F) (hG : Continuous G) :
    (∫ p, removed μX A F p *
      removed μY (effectiveAction μX A) (response μX A G) p.1
      ∂CompactGibbsContinuity.law ((μZ.prod μY).prod μX) A) = 0 :=
  removed_boundary_orthogonal (μZ.prod μY) μX A F _ hA hF
    (removed_continuous μY _ _ (effectiveAction_continuous μX A hA)
      (response_continuous μX A G hA hG))

omit [TopologicalSpace X] [CompactSpace X] [SecondCountableTopology X] [BorelSpace X]
  [TopologicalSpace Y] [CompactSpace Y] [SecondCountableTopology Y] [BorelSpace Y]
  [TopologicalSpace Z] [CompactSpace Z] [SecondCountableTopology Z] [MeasurableSpace Z]
  [BorelSpace Z] [IsProbabilityMeasure μY] [IsProbabilityMeasure μX] in
theorem jointNoise_decomposition (A F : (Z × Y) × X → ℝ) (p : (Z × Y) × X) :
    jointNoise μY μX A F p = removed μX A F p +
      removed μY (effectiveAction μX A) (response μX A F) p.1 := by
  unfold jointNoise removed
  ring

/-- The later noise has its second moment under the actual first marginal. -/
theorem secondGram_original_integral (A F G : (Z × Y) × X → ℝ) (hA : Continuous A)
    (hF : Continuous F) (hG : Continuous G) :
    secondGram μZ μY μX A F G =
      ∫ p, removed μY (effectiveAction μX A) (response μX A F) p.1 *
        removed μY (effectiveAction μX A) (response μX A G) p.1
        ∂CompactGibbsContinuity.law ((μZ.prod μY).prod μX) A := by
  have hRF := removed_continuous μY _ _ (effectiveAction_continuous μX A hA)
    (response_continuous μX A F hA hF)
  have hRG := removed_continuous μY _ _ (effectiveAction_continuous μX A hA)
    (response_continuous μX A G hA hG)
  have h := boundary_integral (μZ.prod μY) μX A
    (fun p => removed μY (effectiveAction μX A) (response μX A F) p *
      removed μY (effectiveAction μX A) (response μX A G) p) hA (hRF.mul hRG)
  rw [marginal_eq_effectiveLaw (μZ.prod μY) μX A hA] at h
  exact h.symm

/-- The cumulative removed Gram is the sum of the two orthogonal stage Grams. -/
theorem joint_noise_gram (A F G : (Z × Y) × X → ℝ) (hA : Continuous A)
    (hF : Continuous F) (hG : Continuous G) :
    (∫ p, jointNoise μY μX A F p * jointNoise μY μX A G p
      ∂CompactGibbsContinuity.law ((μZ.prod μY).prod μX) A) =
      gram (μZ.prod μY) μX A F G + secondGram μZ μY μX A F G := by
  let ν := CompactGibbsContinuity.law ((μZ.prod μY).prod μX) A
  letI : IsProbabilityMeasure ν := CompactGibbsContinuity.law_probability _ _ hA
  let rF := removed μX A F
  let rG := removed μX A G
  let sF := fun p : (Z × Y) × X =>
    removed μY (effectiveAction μX A) (response μX A F) p.1
  let sG := fun p : (Z × Y) × X =>
    removed μY (effectiveAction μX A) (response μX A G) p.1
  have hrF : Continuous rF := removed_continuous μX A F hA hF
  have hrG : Continuous rG := removed_continuous μX A G hA hG
  have hsF : Continuous sF := (removed_continuous μY _ _
    (effectiveAction_continuous μX A hA) (response_continuous μX A F hA hF)).comp continuous_fst
  have hsG : Continuous sG := (removed_continuous μY _ _
    (effectiveAction_continuous μX A hA) (response_continuous μX A G hA hG)).comp continuous_fst
  have h11 : Integrable (fun p => rF p * rG p) ν :=
    (hrF.mul hrG).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have h12 : Integrable (fun p => rF p * sG p) ν :=
    (hrF.mul hsG).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have h21 : Integrable (fun p => rG p * sF p) ν :=
    (hrG.mul hsF).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have h22 : Integrable (fun p => sF p * sG p) ν :=
    (hsF.mul hsG).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hp (p : (Z × Y) × X) : jointNoise μY μX A F p * jointNoise μY μX A G p =
      (rF p * rG p + rF p * sG p) + (rG p * sF p + sF p * sG p) := by
    rw [jointNoise_decomposition, jointNoise_decomposition]
    change (rF p + sF p) * (rG p + sG p) = _
    ring
  simp_rw [hp]
  change (∫ p, (rF p * rG p + rF p * sG p) + (rG p * sF p + sF p * sG p) ∂ν) = _
  have hl : Integrable (fun p => rF p * rG p + rF p * sG p) ν := h11.add h12
  have hr : Integrable (fun p => rG p * sF p + sF p * sG p) ν := h21.add h22
  rw [integral_add hl hr, integral_add h11 h12, integral_add h21 h22]
  have hx := successive_noise_orthogonal μZ μY μX A F G hA hF hG
  have hy := successive_noise_orthogonal μZ μY μX A G F hA hG hF
  change (∫ p, rF p * sG p ∂ν) = 0 at hx
  change (∫ p, rG p * sF p ∂ν) = 0 at hy
  rw [hx, hy, add_zero, zero_add]
  have hz := secondGram_original_integral μZ μY μX A F G hA hF hG
  change secondGram μZ μY μX A F G = ∫ p, sF p * sG p ∂ν at hz
  rw [← hz]
  rfl

/-- Two successive positive noise budgets never exceed the original variance. -/
theorem cumulative_variance_budget (A F : (Z × Y) × X → ℝ) (hA : Continuous A)
    (hF : Continuous F) :
    0 ≤ gram (μZ.prod μY) μX A F F + secondGram μZ μY μX A F F ∧
      gram (μZ.prod μY) μX A F F + secondGram μZ μY μX A F F ≤
        covariance (CompactGibbsContinuity.law ((μZ.prod μY).prod μX) A) F F := by
  have h1 := gram_self_nonneg (μZ.prod μY) μX A F
  have h2 := secondGram_self_nonneg μZ μY μX A F
  have hA1 := effectiveAction_continuous μX A hA
  have hF1 := response_continuous μX A F hA hF
  letI := marginal_probability μZ μY (effectiveAction μX A) hA1
  have h3 := covariance_self_nonneg (marginal μZ μY (effectiveAction μX A))
    (response μY (effectiveAction μX A) (response μX A F))
    (response_continuous μY _ _ hA1 hF1)
  have ht := successive_covariance μZ μY μX A F F hA hF hF
  constructor <;> linarith

/-- The final covariance is positive and no larger than the original variance.
This supplies nonexpansion, not strict contraction or a cutoff-uniform bound. -/
theorem final_variance_bounds (A F : (Z × Y) × X → ℝ) (hA : Continuous A)
    (hF : Continuous F) :
    0 ≤ covariance (marginal μZ μY (effectiveAction μX A))
      (response μY (effectiveAction μX A) (response μX A F))
      (response μY (effectiveAction μX A) (response μX A F)) ∧
    covariance (marginal μZ μY (effectiveAction μX A))
      (response μY (effectiveAction μX A) (response μX A F))
      (response μY (effectiveAction μX A) (response μX A F)) ≤
      covariance (CompactGibbsContinuity.law ((μZ.prod μY).prod μX) A) F F := by
  have hA1 := effectiveAction_continuous μX A hA
  have hF1 := response_continuous μX A F hA hF
  letI := marginal_probability μZ μY (effectiveAction μX A) hA1
  have h3 := covariance_self_nonneg (marginal μZ μY (effectiveAction μX A))
    (response μY (effectiveAction μX A) (response μX A F))
    (response_continuous μY _ _ hA1 hF1)
  have h1 := (cumulative_variance_budget μZ μY μX A F hA hF).1
  have ht := successive_covariance μZ μY μX A F F hA hF hF
  constructor <;> linarith

/-- Sources depending only on the final coordinates are retained exactly.
Thus the general identities cannot imply blanket strict variance contraction. -/
theorem retained_exact_boundary (A : (Z × Y) × X → ℝ) (hA : Continuous A)
    (H J : Z → ℝ) (hH : Continuous H) (hJ : Continuous J) :
    covariance (CompactGibbsContinuity.law ((μZ.prod μY).prod μX) A)
      (fun p => H p.1.1) (fun p => J p.1.1) =
    covariance (marginal μZ μY (effectiveAction μX A)) H J := by
  have hfirst (L : Z → ℝ) : response μX A (fun p => L p.1.1) = fun q => L q.1 := by
    funext q
    exact response_boundary μX A hA (fun q : Z × Y => L q.1) q
  have hsecond (L : Z → ℝ) :
      response μY (effectiveAction μX A) (fun q => L q.1) = L := by
    funext z
    exact response_boundary μY (effectiveAction μX A) (effectiveAction_continuous μX A hA) L z
  have h := successive_covariance μZ μY μX A (fun p => H p.1.1) (fun p => J p.1.1)
    hA (hH.comp (continuous_fst.comp continuous_fst))
    (hJ.comp (continuous_fst.comp continuous_fst))
  simpa only [gram, secondGram, removed, hfirst, hsecond, sub_self, zero_mul,
    integral_zero, zero_add] using h

end TwoSteps
end
end UnifiedTheory.Clay.YangMills.GibbsSuccessiveCovariance
