/- Variance-weighted conditional noise estimates under actual compact Gibbs fibers,
with a bare SU(2) plaquette binding. These local bounds retain the true variance;
the range and source radius change under physical rescaling. -/
import UnifiedTheory.Clay.YangMills.VarianceWeightedNoise
import UnifiedTheory.Clay.YangMills.GibbsBoundedResponse
import UnifiedTheory.Clay.YangMills.WilsonConditionalCumulants
import UnifiedTheory.Clay.YangMills.WilsonBlockNoiseKernel

set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace UnifiedTheory.Clay.YangMills.WilsonVarianceWeightedNoise
noncomputable section
open MeasureTheory GibbsMarginalTower GibbsCrossCovariance GibbsConditionalCumulants
open RegulatedGauge PeriodicLattice4 WilsonBlockMarginal WilsonSingleLinkStaples

section Conditional
variable {B X : Type*}
  [TopologicalSpace B] [CompactSpace B] [SecondCountableTopology B]
  [MeasurableSpace B] [BorelSpace B]
  [TopologicalSpace X] [CompactSpace X] [SecondCountableTopology X]
  [MeasurableSpace X] [BorelSpace X]
  (μX : Measure X) [IsProbabilityMeasure μX]

omit [CompactSpace B] [SecondCountableTopology B] [MeasurableSpace B]
  [BorelSpace B] [SecondCountableTopology X] in
/-- Centering in the actual fiber does not enlarge the original interval width. -/
theorem removed_abs_le (A F : B × X → ℝ) (hA : Continuous A) (hF : Continuous F)
    (lo hi : ℝ) (hbound : ∀ p, F p ∈ Set.Icc lo hi) (p : B × X) :
    |removed μX A F p| ≤ hi - lo := by
  have hm := GibbsBoundedResponse.response_bounds μX A F hA hF lo hi hbound p.1
  have hf := hbound p
  unfold removed
  rw [abs_le]
  constructor <;> linarith [hm.1, hm.2, hf.1, hf.2]

omit [CompactSpace B] [SecondCountableTopology B] [MeasurableSpace B]
  [BorelSpace B] [SecondCountableTopology X] in
/-- The true variance is bounded by one quarter of the squared original range. -/
theorem variance_bound (A F : B × X → ℝ) (hA : Continuous A) (hF : Continuous F)
    (lo hi : ℝ) (hlohi : lo ≤ hi) (hbound : ∀ p, F p ∈ Set.Icc lo hi) (b : B) :
    noiseMoment μX A F 2 b ≤ (hi - lo) ^ 2 / 4 := by
  rw [noiseMoment_two_eq_covariance μX A F hA hF b]
  have h := GibbsBoundedResponse.conditional_covariance_abs_le μX A F F hA hF hF
    lo hi lo hi hlohi hlohi hbound hbound b
  simpa only [pow_two] using (abs_le.mp h).2

omit [MeasurableSpace B] [BorelSpace B] [SecondCountableTopology X] in
/-- Every fixed higher conditional moment has a range-power times variance bound. -/
theorem conditional_moment_bound (A F : B × X → ℝ) (hA : Continuous A)
    (hF : Continuous F) (lo hi : ℝ) (hbound : ∀ p, F p ∈ Set.Icc lo hi)
    (k : ℕ) (b : B) :
    |noiseMoment μX A F (k + 2) b| ≤ (hi - lo) ^ k * noiseMoment μX A F 2 b := by
  let ν := CompactGibbsContinuity.law μX (fun x => A (b, x))
  letI : IsProbabilityMeasure ν := CompactGibbsContinuity.law_probability μX _
    (hA.comp (continuous_const.prodMk continuous_id))
  have hc : Continuous (fun x => removed μX A F (b, x)) :=
    (removed_continuous μX A F hA hF).comp (continuous_const.prodMk continuous_id)
  have h := VarianceWeightedNoise.moment_bound ν _ hc (hi - lo)
    (fun x => removed_abs_le μX A F hA hF lo hi hbound (b, x)) k
  simpa only [noiseMoment, response_eq_expectation μX _ _ hA b] using h

omit [MeasurableSpace B] [BorelSpace B] [SecondCountableTopology X] in
/-- A genuinely variance-weighted fourth conditional cumulant bound. -/
theorem conditional_fourth_bound (A F : B × X → ℝ) (hA : Continuous A)
    (hF : Continuous F) (lo hi : ℝ) (hlohi : lo ≤ hi)
    (hbound : ∀ p, F p ∈ Set.Icc lo hi) (b : B) :
    |noiseCumulantFour μX A F b| ≤ (hi - lo) ^ 2 * noiseMoment μX A F 2 b := by
  let ν := CompactGibbsContinuity.law μX (fun x => A (b, x))
  letI : IsProbabilityMeasure ν := CompactGibbsContinuity.law_probability μX _
    (hA.comp (continuous_const.prodMk continuous_id))
  have hc : Continuous (fun x => removed μX A F (b, x)) :=
    (removed_continuous μX A F hA hF).comp (continuous_const.prodMk continuous_id)
  have hm : (∫ x, removed μX A F (b, x) ∂ν) = 0 := by
    rw [← response_eq_expectation μX A _ hA b]
    exact removed_response μX A F hA hF b
  have hv := variance_bound μX A F hA hF lo hi hlohi hbound b
  rw [noiseMoment, response_eq_expectation μX _ _ hA b] at hv
  have h := VarianceWeightedNoise.fourth_cumulant_bound ν _ hc (hi - lo)
    (fun x => removed_abs_le μX A F hA hF lo hi hbound (b, x)) hm hv
  simpa only [cumulantFour, centeredMoment, hm, sub_zero, noiseCumulantFour,
    noiseMoment, response_eq_expectation μX _ _ hA b] using h

omit [MeasurableSpace B] [BorelSpace B] [SecondCountableTopology X] in
/-- Exact centered conditional log-MGF control on its stated finite source interval. -/
theorem conditional_log_mgf_bound (A F : B × X → ℝ) (hA : Continuous A)
    (hF : Continuous F) (lo hi : ℝ) (hbound : ∀ p, F p ∈ Set.Icc lo hi)
    (b : B) (t : ℝ) (ht : |t| * (hi - lo) ≤ 1) :
    0 ≤ Real.log (∫ x, Real.exp (t * removed μX A F (b, x))
      ∂CompactGibbsContinuity.law μX (fun x => A (b, x))) ∧
    Real.log (∫ x, Real.exp (t * removed μX A F (b, x))
      ∂CompactGibbsContinuity.law μX (fun x => A (b, x))) ≤
        t ^ 2 * noiseMoment μX A F 2 b := by
  let ν := CompactGibbsContinuity.law μX (fun x => A (b, x))
  letI : IsProbabilityMeasure ν := CompactGibbsContinuity.law_probability μX _
    (hA.comp (continuous_const.prodMk continuous_id))
  have hc : Continuous (fun x => removed μX A F (b, x)) :=
    (removed_continuous μX A F hA hF).comp (continuous_const.prodMk continuous_id)
  have hm : (∫ x, removed μX A F (b, x) ∂ν) = 0 := by
    rw [← response_eq_expectation μX A _ hA b]
    exact removed_response μX A F hA hF b
  have h := VarianceWeightedNoise.log_mgf_bound ν _ hc (hi - lo)
    (fun x => removed_abs_le μX A F hA hF lo hi hbound (b, x)) hm t ht
  simpa only [noiseMoment, response_eq_expectation μX _ _ hA b] using h
end Conditional

section Successive
variable {X Y Z : Type*}
  [TopologicalSpace X] [CompactSpace X] [SecondCountableTopology X]
  [MeasurableSpace X] [BorelSpace X]
  [TopologicalSpace Y] [CompactSpace Y] [SecondCountableTopology Y]
  [MeasurableSpace Y] [BorelSpace Y]
  [TopologicalSpace Z] [CompactSpace Z] [SecondCountableTopology Z]
  [MeasurableSpace Z] [BorelSpace Z]
  (μY : Measure Y) (μX : Measure X) [IsProbabilityMeasure μY] [IsProbabilityMeasure μX]

omit [SecondCountableTopology X] [MeasurableSpace Z] [BorelSpace Z] in
/-- The same all-order estimate survives a genuine prior elimination, with no new range input. -/
theorem second_stage_moment_bound (A F : (Z × Y) × X → ℝ)
    (hA : Continuous A) (hF : Continuous F) (lo hi : ℝ)
    (hbound : ∀ p, F p ∈ Set.Icc lo hi) (k : ℕ) (z : Z) :
    |noiseMoment μY (effectiveAction μX A) (response μX A F) (k + 2) z| ≤
      (hi - lo) ^ k * noiseMoment μY (effectiveAction μX A) (response μX A F) 2 z :=
  conditional_moment_bound μY _ _ (effectiveAction_continuous μX A hA)
    (response_continuous μX A F hA hF) lo hi
    (GibbsBoundedResponse.response_bounds μX A F hA hF lo hi hbound) k z

omit [SecondCountableTopology X] [MeasurableSpace Z] [BorelSpace Z] in
/-- The local log-MGF estimate also uses the actual first induced action and source. -/
theorem second_stage_log_mgf_bound (A F : (Z × Y) × X → ℝ)
    (hA : Continuous A) (hF : Continuous F) (lo hi : ℝ)
    (hbound : ∀ p, F p ∈ Set.Icc lo hi) (z : Z) (t : ℝ)
    (ht : |t| * (hi - lo) ≤ 1) :
    0 ≤ Real.log (∫ y, Real.exp (t * removed μY (effectiveAction μX A)
      (response μX A F) (z, y)) ∂CompactGibbsContinuity.law μY
        (fun y => effectiveAction μX A (z, y))) ∧
    Real.log (∫ y, Real.exp (t * removed μY (effectiveAction μX A)
      (response μX A F) (z, y)) ∂CompactGibbsContinuity.law μY
        (fun y => effectiveAction μX A (z, y))) ≤
      t ^ 2 * noiseMoment μY (effectiveAction μX A) (response μX A F) 2 z :=
  conditional_log_mgf_bound μY _ _ (effectiveAction_continuous μX A hA)
    (response_continuous μX A F hA hF) lo hi
    (GibbsBoundedResponse.response_bounds μX A F hA hF lo hi hbound) z t ht
end Successive

variable (n : ℕ) [NeZero n]
local instance edgeDecidableEq : DecidableEq (Edge (Vertex n)) := Classical.decEq _

/-- Actual bare plaquette conditional moments, uniform in beta, volume and exterior. -/
theorem plaquette_moment_bound (β : ℝ) (S : Finset (Edge (Vertex n)))
    (p : PlaquetteIndex n) (k : ℕ) (r : Outside (G := Q) S) :
    |WilsonConditionalCumulants.conditionalNoiseMoment n Q character β 2 S
      (WilsonBlockNoiseKernel.basis n p) (k + 2) r| ≤
    4 ^ k * WilsonConditionalCumulants.conditionalNoiseMoment n Q character β 2 S
      (WilsonBlockNoiseKernel.basis n p) 2 r := by
  have h := conditional_moment_bound (insideMeasure S (compactHaar Q))
    (splitAction n Q character β 2 S)
    (WilsonSeparatedSources.splitSource n Q character 2 S (WilsonBlockNoiseKernel.basis n p))
    (splitAction_continuous n Q character character_continuous β 2 S)
    (WilsonCrossCovariance.splitSource_continuous n Q character character_continuous 2 S
      (WilsonBlockNoiseKernel.basis n p)) 0 4
    (fun z => WilsonBlockNoiseKernel.source_basis_bounds n p (assemble S z)) k r
  simpa only [sub_zero] using h

/-- The actual conditional fourth cumulant is at most sixteen times its variance. -/
theorem plaquette_fourth_bound (β : ℝ) (S : Finset (Edge (Vertex n)))
    (p : PlaquetteIndex n) (r : Outside (G := Q) S) :
    |WilsonConditionalCumulants.conditionalNoiseFourth n Q character β 2 S
      (WilsonBlockNoiseKernel.basis n p) r| ≤
    16 * WilsonConditionalCumulants.conditionalNoiseMoment n Q character β 2 S
      (WilsonBlockNoiseKernel.basis n p) 2 r := by
  have h := conditional_fourth_bound (insideMeasure S (compactHaar Q))
    (splitAction n Q character β 2 S)
    (WilsonSeparatedSources.splitSource n Q character 2 S (WilsonBlockNoiseKernel.basis n p))
    (splitAction_continuous n Q character character_continuous β 2 S)
    (WilsonCrossCovariance.splitSource_continuous n Q character character_continuous 2 S
      (WilsonBlockNoiseKernel.basis n p)) 0 4 (by norm_num)
    (fun z => WilsonBlockNoiseKernel.source_basis_bounds n p (assemble S z)) r
  norm_num only [sub_zero, show (4 : ℝ) ^ 2 = 16 by norm_num] at h
  exact h

/-- The actual bare plaquette centered fiber logarithm has the uniform source radius one quarter. -/
theorem plaquette_log_mgf_bound (β : ℝ) (S : Finset (Edge (Vertex n)))
    (p : PlaquetteIndex n) (r : Outside (G := Q) S) (t : ℝ) (ht : |t| ≤ 1 / 4) :
    0 ≤ Real.log (∫ v, Real.exp (t * WilsonBlockNoiseKernel.noise n β S
      (WilsonBlockNoiseKernel.basis n p) (assemble S (r, v)))
      ∂CompactGibbsContinuity.law (insideMeasure S (compactHaar Q))
        (fun v => splitAction n Q character β 2 S (r, v))) ∧
    Real.log (∫ v, Real.exp (t * WilsonBlockNoiseKernel.noise n β S
      (WilsonBlockNoiseKernel.basis n p) (assemble S (r, v)))
      ∂CompactGibbsContinuity.law (insideMeasure S (compactHaar Q))
        (fun v => splitAction n Q character β 2 S (r, v))) ≤
    t ^ 2 * WilsonConditionalCumulants.conditionalNoiseMoment n Q character β 2 S
      (WilsonBlockNoiseKernel.basis n p) 2 r := by
  have h := conditional_log_mgf_bound (insideMeasure S (compactHaar Q))
    (splitAction n Q character β 2 S)
    (WilsonSeparatedSources.splitSource n Q character 2 S (WilsonBlockNoiseKernel.basis n p))
    (splitAction_continuous n Q character character_continuous β 2 S)
    (WilsonCrossCovariance.splitSource_continuous n Q character character_continuous 2 S
      (WilsonBlockNoiseKernel.basis n p)) 0 4
    (fun z => WilsonBlockNoiseKernel.source_basis_bounds n p (assemble S z)) r t (by linarith)
  simpa only [WilsonBlockNoiseKernel.noise, WilsonCrossCovariance.removedSource_assemble] using h

end
end UnifiedTheory.Clay.YangMills.WilsonVarianceWeightedNoise
