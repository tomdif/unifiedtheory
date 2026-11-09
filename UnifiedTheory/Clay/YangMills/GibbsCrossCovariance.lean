/- Exact mixed-source transport under an actual compact Gibbs marginal.
The removed mixed fluctuation vanishes when the conditional product factors.
This does not bound the retained covariance or identify a continuum limit. -/
import UnifiedTheory.Clay.YangMills.GibbsMarginalTower

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Clay.YangMills.GibbsCrossCovariance
noncomputable section
open MeasureTheory GibbsMarginalTower

def covariance {Y : Type*} [MeasurableSpace Y] (μ : Measure Y) (F G : Y → ℝ) : ℝ :=
  (∫ y, F y * G y ∂μ)-(∫ y, F y ∂μ) * (∫ y, G y ∂μ)

section OneMeasure
variable {Y : Type*} [TopologicalSpace Y] [CompactSpace Y]
  [MeasurableSpace Y] [BorelSpace Y] (μ : Measure Y) [IsProbabilityMeasure μ]

theorem centered_product (F G : Y → ℝ) (hF : Continuous F) (hG : Continuous G)
    (c d : ℝ) :
    (∫ y, (F y-c) * (G y-d) ∂μ) =
      (∫ y, F y * G y ∂μ)-d * (∫ y, F y ∂μ)-c * (∫ y, G y ∂μ)+c * d := by
  have hiF := hF.integrable_of_hasCompactSupport (μ := μ) (HasCompactSupport.of_compactSpace _)
  have hiG := hG.integrable_of_hasCompactSupport (μ := μ) (HasCompactSupport.of_compactSpace _)
  have hiFG : Integrable (fun y => F y * G y) μ := (hF.mul hG).integrable_of_hasCompactSupport
    (μ := μ) (HasCompactSupport.of_compactSpace _)
  calc
    _ = ∫ y, ((F y * G y-d * F y)-c * G y)+c * d ∂μ := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun y => by ring)
    _ = _ := by
      have hsub : Integrable (fun y => F y * G y-d * F y) μ := hiFG.sub (hiF.const_mul d)
      have hsub2 : Integrable (fun y => F y * G y-d * F y-c * G y) μ :=
        hsub.sub (hiG.const_mul c)
      rw [integral_add hsub2 (integrable_const (c * d)),
        integral_sub hsub (hiG.const_mul c),
        integral_sub hiFG (hiF.const_mul d), integral_const_mul, integral_const_mul]
      simp

theorem covariance_eq_centered (F G : Y → ℝ) (hF : Continuous F) (hG : Continuous G) :
    covariance μ F G = ∫ y, (F y-∫ z, F z ∂μ) * (G y-∫ z, G z ∂μ) ∂μ := by
  rw [centered_product μ F G hF hG]
  unfold covariance
  ring

omit [TopologicalSpace Y] [CompactSpace Y] [BorelSpace Y] [IsProbabilityMeasure μ] in
theorem covariance_scale (F G : Y → ℝ) (s t : ℝ) :
    covariance μ (fun y => s * F y) (fun y => t * G y) = s * t * covariance μ F G := by
  unfold covariance
  have he (y : Y) : (s * F y) * (t * G y) = (s * t) * (F y * G y) := by ring
  simp_rw [he, integral_const_mul]
  ring
end OneMeasure

variable {B X : Type*}
  [TopologicalSpace B] [CompactSpace B] [SecondCountableTopology B]
  [MeasurableSpace B] [BorelSpace B]
  [TopologicalSpace X] [CompactSpace X] [SecondCountableTopology X]
  [MeasurableSpace X] [BorelSpace X]
  (μB : Measure B) (μX : Measure X) [IsProbabilityMeasure μB] [IsProbabilityMeasure μX]

def conditionalCovariance (A F G : B × X → ℝ) (b : B) : ℝ :=
  response μX A (fun p => F p * G p) b-response μX A F b * response μX A G b

/-- Total covariance retains both the within-fiber and retained-mean terms. -/
theorem total_covariance (A F G : B × X → ℝ) (hA : Continuous A)
    (hF : Continuous F) (hG : Continuous G) :
    covariance (CompactGibbsContinuity.law (μB.prod μX) A) F G =
      (∫ b, conditionalCovariance μX A F G b ∂marginal μB μX A)+
      covariance (marginal μB μX A) (response μX A F) (response μX A G) := by
  letI := marginal_probability μB μX A hA
  have hR := response_continuous μX A F hA hF
  have hS := response_continuous μX A G hA hG
  have hT := response_continuous μX A (fun p => F p * G p) hA (hF.mul hG)
  have hiRS : Integrable (fun b => response μX A F b * response μX A G b)
      (marginal μB μX A) :=
    (hR.mul hS).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  unfold covariance conditionalCovariance
  rw [integral_sub
    (hT.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
    hiRS,
    response_expectation μB μX A (fun p => F p * G p) hA (hF.mul hG),
    response_expectation μB μX A F hA hF,
    response_expectation μB μX A G hA hG]
  ring

theorem product_preserved (A F G : B × X → ℝ) (hA : Continuous A)
    (hF : Continuous F) (hG : Continuous G)
    (hprod : ∀ b, response μX A (fun p => F p * G p) b =
      response μX A F b * response μX A G b) :
    (∫ p, F p * G p ∂CompactGibbsContinuity.law (μB.prod μX) A) =
      ∫ b, response μX A F b * response μX A G b ∂marginal μB μX A := by
  rw [← response_expectation μB μX A (fun p => F p * G p) hA (hF.mul hG)]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall hprod

theorem covariance_preserved (A F G : B × X → ℝ) (hA : Continuous A)
    (hF : Continuous F) (hG : Continuous G)
    (hprod : ∀ b, response μX A (fun p => F p * G p) b =
      response μX A F b * response μX A G b) :
    covariance (CompactGibbsContinuity.law (μB.prod μX) A) F G =
      covariance (marginal μB μX A) (response μX A F) (response μX A G) := by
  rw [total_covariance μB μX A F G hA hF hG]
  have hz (b : B) : conditionalCovariance μX A F G b = 0 := by
    simp only [conditionalCovariance, hprod b, sub_self]
  simp only [hz, integral_zero, zero_add]

def removed (A F : B × X → ℝ) (p : B × X) : ℝ := F p-response μX A F p.1

omit [MeasurableSpace B] [BorelSpace B] [SecondCountableTopology X] in
theorem removed_continuous (A F : B × X → ℝ) (hA : Continuous A) (hF : Continuous F) :
    Continuous (removed μX A F) :=
  hF.sub ((response_continuous μX A F hA hF).comp continuous_fst)

omit [MeasurableSpace B] [BorelSpace B] [SecondCountableTopology X] in
theorem removed_response (A F : B × X → ℝ) (hA : Continuous A) (hF : Continuous F)
    (b : B) : response μX A (removed μX A F) b = 0 := by
  change response μX A (fun p => F p-response μX A F p.1) b = 0
  rw [response_sub_boundary μX A F hA hF _
    (response_continuous μX A F hA hF)]
  exact sub_self _

omit [CompactSpace B] [SecondCountableTopology B] [MeasurableSpace B]
  [BorelSpace B] [SecondCountableTopology X] in
theorem conditional_removed_product (A F G : B × X → ℝ) (hA : Continuous A)
    (hF : Continuous F) (hG : Continuous G) (b : B) :
    response μX A (fun p => removed μX A F p * removed μX A G p) b =
      conditionalCovariance μX A F G b := by
  let ν := CompactGibbsContinuity.law μX (fun x => A (b,x))
  letI : IsProbabilityMeasure ν := CompactGibbsContinuity.law_probability μX _
    (hA.comp (continuous_const.prodMk continuous_id))
  rw [response_eq_expectation μX A _ hA b]
  change (∫ x, (F (b,x)-response μX A F b) * (G (b,x)-response μX A G b) ∂ν) = _
  rw [centered_product ν (fun x => F (b,x)) (fun x => G (b,x))
    (hF.comp (continuous_const.prodMk continuous_id))
    (hG.comp (continuous_const.prodMk continuous_id))]
  unfold conditionalCovariance
  simp_rw [response_eq_expectation μX A _ hA b]
  change (∫ x, F (b,x) * G (b,x) ∂ν)-
      (∫ x, G (b,x) ∂ν) * (∫ x, F (b,x) ∂ν)-
      (∫ x, F (b,x) ∂ν) * (∫ x, G (b,x) ∂ν)+
      (∫ x, F (b,x) ∂ν) * (∫ x, G (b,x) ∂ν) = _
  ring

/-- Removed fluctuations can have large ordinary norms while their mixed
pairing is exactly zero. A reflected-null interpretation needs reflection
compatibility and support hypotheses separately. -/
theorem removed_product_zero (A F G : B × X → ℝ) (hA : Continuous A)
    (hF : Continuous F) (hG : Continuous G)
    (hprod : ∀ b, response μX A (fun p => F p * G p) b =
      response μX A F b * response μX A G b) :
    (∫ p, removed μX A F p * removed μX A G p
      ∂CompactGibbsContinuity.law (μB.prod μX) A) = 0 := by
  rw [← response_expectation μB μX A
    (fun p => removed μX A F p * removed μX A G p) hA
    ((removed_continuous μX A F hA hF).mul (removed_continuous μX A G hA hG))]
  have hz (b : B) : response μX A (fun p => removed μX A F p * removed μX A G p) b = 0 := by
    rw [conditional_removed_product μX A F G hA hF hG b]
    simp only [conditionalCovariance, hprod b, sub_self]
  simp only [hz, integral_zero]

end
end UnifiedTheory.Clay.YangMills.GibbsCrossCovariance
