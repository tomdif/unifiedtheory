/- Bounds preserved by actual normalized conditional expectations.
The covariance constants follow from the proved bounded-range Gruss inequality,
including after an induced action has replaced the original action. -/
import UnifiedTheory.Clay.YangMills.GibbsSuccessiveCovariance
import UnifiedTheory.Clay.YangMills.CompactGibbsOscillation

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Clay.YangMills.GibbsBoundedResponse
noncomputable section
open MeasureTheory GibbsMarginalTower GibbsCrossCovariance GibbsSuccessiveCovariance

variable {B X : Type*}
  [TopologicalSpace B] [CompactSpace B] [SecondCountableTopology B]
  [MeasurableSpace B] [BorelSpace B]
  [TopologicalSpace X] [CompactSpace X] [SecondCountableTopology X]
  [MeasurableSpace X] [BorelSpace X]
  (μB : Measure B) (μX : Measure X) [IsProbabilityMeasure μB] [IsProbabilityMeasure μX]

omit [CompactSpace B] [SecondCountableTopology B] [MeasurableSpace B] [BorelSpace B]
  [SecondCountableTopology X] in
/-- Exact scalar linearity under the same actual normalized fiber law. -/
theorem response_const_mul (A F : B × X → ℝ) (hA : Continuous A) (c : ℝ) (b : B) :
    response μX A (fun z => c * F z) b = c * response μX A F b := by
  simp only [response_eq_expectation μX A _ hA b, integral_const_mul]

omit [CompactSpace B] [SecondCountableTopology B] [MeasurableSpace B] [BorelSpace B]
  [SecondCountableTopology X] in
/-- Finite source expansions retain all coefficients through conditional averaging. -/
theorem response_sum {J : Type*} (s : Finset J) (A : B × X → ℝ)
    (F : J → B × X → ℝ) (hA : Continuous A) (hF : ∀ j, Continuous (F j)) (b : B) :
    response μX A (fun z => ∑ j ∈ s, F j z) b = ∑ j ∈ s, response μX A (F j) b := by
  simp only [response_eq_expectation μX A _ hA b]
  letI := CompactGibbsContinuity.law_probability μX (fun x => A (b, x))
    (hA.comp (continuous_const.prodMk continuous_id))
  apply integral_finset_sum
  intro j hj
  exact ((hF j).comp (continuous_const.prodMk continuous_id)).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

omit [CompactSpace B] [SecondCountableTopology B] [MeasurableSpace B] [BorelSpace B]
  [SecondCountableTopology X] in
/-- The actual fiber law preserves a continuous observable's original interval. -/
theorem response_bounds (A F : B × X → ℝ) (hA : Continuous A) (hF : Continuous F)
    (lo hi : ℝ) (hFbound : ∀ z, F z ∈ Set.Icc lo hi) (b : B) :
    response μX A F b ∈ Set.Icc lo hi := by
  let ν := CompactGibbsContinuity.law μX (fun x => A (b, x))
  letI : IsProbabilityMeasure ν := CompactGibbsContinuity.law_probability μX _
    (hA.comp (continuous_const.prodMk continuous_id))
  have hI : Integrable (fun x => F (b, x)) ν :=
    (hF.comp (continuous_const.prodMk continuous_id)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  rw [response_eq_expectation μX A F hA b]
  have hL := integral_mono (integrable_const lo) hI (fun x => (hFbound (b, x)).1)
  have hH := integral_mono hI (integrable_const hi) (fun x => (hFbound (b, x)).2)
  simpa only [integral_const, probReal_univ, one_smul] using And.intro hL hH

omit [CompactSpace B] [SecondCountableTopology B] [MeasurableSpace B] [BorelSpace B]
  [SecondCountableTopology X] in
/-- A sharp range-based bound for the literal normalized conditional covariance. -/
theorem conditional_covariance_abs_le (A F G : B × X → ℝ)
    (hA : Continuous A) (hF : Continuous F) (hG : Continuous G)
    (lo hi lo' hi' : ℝ) (hlo : lo ≤ hi) (hhi : lo' ≤ hi')
    (hFb : ∀ z, F z ∈ Set.Icc lo hi) (hGb : ∀ z, G z ∈ Set.Icc lo' hi') (b : B) :
    |conditionalCovariance μX A F G b| ≤ (hi - lo) * (hi' - lo') / 4 := by
  let ν := CompactGibbsContinuity.law μX (fun x => A (b, x))
  letI : IsProbabilityMeasure ν := CompactGibbsContinuity.law_probability μX _
    (hA.comp (continuous_const.prodMk continuous_id))
  unfold conditionalCovariance
  simp_rw [response_eq_expectation μX A _ hA b]
  exact CompactGibbsOscillation.covariance_bound ν (fun x => F (b, x)) (fun x => G (b, x))
    (hF.comp (continuous_const.prodMk continuous_id))
    (hG.comp (continuous_const.prodMk continuous_id)) lo hi lo' hi' hlo hhi
    (fun x => hFb (b, x)) (fun x => hGb (b, x))

/-- Averaging the actual removed covariance preserves the same interval constant. -/
theorem gram_abs_le (A F G : B × X → ℝ)
    (hA : Continuous A) (hF : Continuous F) (hG : Continuous G)
    (lo hi lo' hi' : ℝ) (hlo : lo ≤ hi) (hhi : lo' ≤ hi')
    (hFb : ∀ z, F z ∈ Set.Icc lo hi) (hGb : ∀ z, G z ∈ Set.Icc lo' hi') :
    |gram μB μX A F G| ≤ (hi - lo) * (hi' - lo') / 4 := by
  letI := marginal_probability μB μX A hA
  have hc : Continuous (conditionalCovariance μX A F G) :=
    (response_continuous μX A (fun z => F z * G z) hA (hF.mul hG)).sub
      ((response_continuous μX A F hA hF).mul (response_continuous μX A G hA hG))
  have hI : Integrable (fun b => |conditionalCovariance μX A F G b|)
      (marginal μB μX A) :=
    hc.abs.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  rw [gram_eq_conditional μB μX A F G hA hF hG]
  apply abs_integral_le_integral_abs.trans
  have h := integral_mono hI (integrable_const ((hi - lo) * (hi' - lo') / 4))
    (conditional_covariance_abs_le μX A F G hA hF hG lo hi lo' hi' hlo hhi hFb hGb)
  simpa only [integral_const, probReal_univ, one_smul] using h

end
end UnifiedTheory.Clay.YangMills.GibbsBoundedResponse
