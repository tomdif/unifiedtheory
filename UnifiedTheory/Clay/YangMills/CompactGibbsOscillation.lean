/-
Sharp bounded-test influence for actual normalized compact Gibbs laws.
The covariance estimate is proved from the L2 Cauchy-Schwarz inequality and
Popoviciu's variance bound; integration of the actual source derivative gives
finite action perturbations with oscillation factor one quarter.
No mixing, gap, or continuum estimate is assumed or concluded.
-/
import UnifiedTheory.Clay.YangMills.CompactGibbsSource
import Mathlib.Probability.Moments.Variance
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Analysis.Calculus.MeanValue

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Clay.YangMills.CompactGibbsOscillation
noncomputable section
open MeasureTheory
open scoped RealInnerProductSpace

variable {X : Type*} [TopologicalSpace X] [CompactSpace X]
  [MeasurableSpace X] [BorelSpace X] (μ : Measure X) [IsProbabilityMeasure μ]

/-- Sharp Grüss bound for a compact probability law, proved through its actual L2 embedding. -/
theorem covariance_bound (F G : X → ℝ) (hF : Continuous F) (hG : Continuous G)
    (a b c d : ℝ) (hab : a ≤ b) (hcd : c ≤ d)
    (hFb : ∀ x, F x ∈ Set.Icc a b) (hGb : ∀ x, G x ∈ Set.Icc c d) :
    |(∫ x, F x * G x ∂μ) - (∫ x, F x ∂μ) * (∫ x, G x ∂μ)| ≤
      (b - a) * (d - c) / 4 := by
  let FC : C(X, ℝ) := ⟨fun x => F x - ∫ y, F y ∂μ, hF.sub continuous_const⟩
  let GC : C(X, ℝ) := ⟨fun x => G x - ∫ y, G y ∂μ, hG.sub continuous_const⟩
  let u := ContinuousMap.toLp 2 μ ℝ FC
  let v := ContinuousMap.toLp 2 μ ℝ GC
  have hinner : ⟪u, v⟫ = ProbabilityTheory.covariance F G μ := by
    rw [ContinuousMap.inner_toLp]
    unfold ProbabilityTheory.covariance
    apply integral_congr_ae
    filter_upwards with x
    simp only [FC, GC, ContinuousMap.coe_mk, starRingEnd_apply, star_trivial]
    ring
  have hFu : ‖u‖ ^ 2 = ProbabilityTheory.variance F μ := by
    rw [← real_inner_self_eq_norm_sq, ContinuousMap.inner_toLp,
      ProbabilityTheory.variance_eq_integral hF.measurable.aemeasurable]
    apply integral_congr_ae
    filter_upwards with x
    simp only [FC, ContinuousMap.coe_mk, starRingEnd_apply, star_trivial]
    ring
  have hGv : ‖v‖ ^ 2 = ProbabilityTheory.variance G μ := by
    rw [← real_inner_self_eq_norm_sq, ContinuousMap.inner_toLp,
      ProbabilityTheory.variance_eq_integral hG.measurable.aemeasurable]
    apply integral_congr_ae
    filter_upwards with x
    simp only [GC, ContinuousMap.coe_mk, starRingEnd_apply, star_trivial]
    ring
  have hu : ‖u‖ ≤ (b - a) / 2 := by
    apply (sq_le_sq₀ (norm_nonneg _) (by linarith)).mp
    rw [hFu]
    exact ProbabilityTheory.variance_le_sq_of_bounded (Filter.Eventually.of_forall hFb)
      hF.measurable.aemeasurable
  have hv : ‖v‖ ≤ (d - c) / 2 := by
    apply (sq_le_sq₀ (norm_nonneg _) (by linarith)).mp
    rw [hGv]
    exact ProbabilityTheory.variance_le_sq_of_bounded (Filter.Eventually.of_forall hGb)
      hG.measurable.aemeasurable
  have hmemF : MemLp F 2 μ := memLp_of_bounded (Filter.Eventually.of_forall hFb)
    hF.aestronglyMeasurable 2
  have hmemG : MemLp G 2 μ := memLp_of_bounded (Filter.Eventually.of_forall hGb)
    hG.aestronglyMeasurable 2
  have hc := ProbabilityTheory.covariance_eq_sub hmemF hmemG
  simp only [Pi.mul_apply] at hc
  rw [← hc, ← hinner]
  calc
    |⟪u, v⟫| ≤ ‖u‖ * ‖v‖ := abs_real_inner_le_norm u v
    _ ≤ ((b - a) / 2) * ((d - c) / 2) :=
      mul_le_mul hu hv (norm_nonneg _) (by linarith)
    _ = _ := by ring

/-- Uniform source-derivative bound with the full oscillation factor one quarter. -/
theorem source_covariance_bound (A F G : X → ℝ)
    (hA : Continuous A) (hF : Continuous F) (hG : Continuous G)
    (a b c d : ℝ) (hab : a ≤ b) (hcd : c ≤ d)
    (hFb : ∀ x, F x ∈ Set.Icc a b) (hGb : ∀ x, G x ∈ Set.Icc c d) (t : ℝ) :
    |CompactGibbsSource.covariance μ A F G F t| ≤ (d - c) * (b - a) / 4 := by
  let ν := CompactGibbsContinuity.law μ (CompactGibbsSource.action A F t)
  letI : IsProbabilityMeasure ν := CompactGibbsContinuity.law_probability μ _
    (CompactGibbsSource.action_continuous A F hA hF t)
  exact covariance_bound ν G F hG hF c d a b hcd hab hGb hFb

/-- Integrating the exact source derivative controls finite changes of normalized expectations. -/
theorem source_expectation_difference (A F G : X → ℝ)
    (hA : Continuous A) (hF : Continuous F) (hG : Continuous G)
    (a b c d : ℝ) (hab : a ≤ b) (hcd : c ≤ d)
    (hFb : ∀ x, F x ∈ Set.Icc a b) (hGb : ∀ x, G x ∈ Set.Icc c d) :
    |CompactGibbsSource.expectation μ A F G 1 -
      CompactGibbsSource.expectation μ A F G 0| ≤ (d - c) * (b - a) / 4 := by
  have h := norm_image_sub_le_of_norm_deriv_le_segment_01'
    (fun t _ => (CompactGibbsSource.expectation_hasDerivAt μ A F G hA hF hG t).hasDerivWithinAt)
    (fun t _ => source_covariance_bound μ A F G hA hF hG a b c d hab hcd hFb hGb t)
  exact h

/-- Direct action-to-action form: only the action difference oscillation is charged. -/
theorem action_expectation_difference (A B G : X → ℝ)
    (hA : Continuous A) (hB : Continuous B) (hG : Continuous G)
    (a b c d : ℝ) (hab : a ≤ b) (hcd : c ≤ d)
    (hAB : ∀ x, A x - B x ∈ Set.Icc a b) (hGb : ∀ x, G x ∈ Set.Icc c d) :
    |(∫ x, G x ∂CompactGibbsContinuity.law μ B) -
      (∫ x, G x ∂CompactGibbsContinuity.law μ A)| ≤ (d - c) * (b - a) / 4 := by
  have h := source_expectation_difference μ A (fun x => A x - B x) G hA (hA.sub hB) hG
    a b c d hab hcd hAB hGb
  have h1 : CompactGibbsSource.action A (fun x => A x - B x) 1 = B := by
    funext x
    simp [CompactGibbsSource.action]
  have h0 : CompactGibbsSource.action A (fun x => A x - B x) 0 = A := by
    funext x
    simp [CompactGibbsSource.action]
  simpa only [CompactGibbsSource.expectation, h1, h0] using h

end
end UnifiedTheory.Clay.YangMills.CompactGibbsOscillation
