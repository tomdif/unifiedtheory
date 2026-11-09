/- Exact finite-cell disintegration of smeared observables.
This identifies the same integral before and after averaging configurations. -/
import UnifiedTheory.Clay.YangMills.WilsonCellHierarchy

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Clay.YangMills.FiniteCellSmearing
noncomputable section
open MeasureTheory
open scoped BigOperators

variable {E I : Type*} [MeasurableSpace E] [Fintype I] [DecidableEq I]
  [MeasurableSpace I] [MeasurableSingletonClass I]
  (μ : Measure E) (s : E → I) (hs : Measurable s)

def cellFunction (q : I) (f : E → ℂ) (x : E) : ℂ := if s x = q then f x else 0

include hs in
theorem cellFunction_integrable (q : I) (f : E → ℂ) (hf : Integrable f μ) :
    Integrable (cellFunction s q f) μ := by
  have he : cellFunction s q f = (s ⁻¹' {q}).indicator f := by
    funext x
    by_cases hx : s x = q
    · simp [cellFunction, hx]
    · simp [cellFunction, hx]
  rw [he]
  exact hf.indicator (hs (measurableSet_singleton q))

def coefficient (q : I) (f : E → ℂ) : ℂ := ∫ x, cellFunction s q f x ∂μ

theorem pointwise_decomposition (K : I → ℂ) (f : E → ℂ) (x : E) :
    K (s x) * f x = ∑ q, K q * cellFunction s q f x := by
  classical
  simp only [cellFunction, mul_ite, mul_zero]
  simp

include hs in
theorem integral_decomposition (K : I → ℂ) (f : E → ℂ) (hf : Integrable f μ) :
    (∫ x, K (s x) * f x ∂μ) = ∑ q, K q * coefficient μ s q f := by
  simp_rw [pointwise_decomposition s K f]
  rw [integral_finset_sum _ (fun q _ => (cellFunction_integrable μ s hs q f hf).const_mul (K q))]
  simp only [integral_const_mul, coefficient]

variable {Z : Type*}

def observable (F : I → Z → ℂ) (f : E → ℂ) (z : Z) : ℂ :=
  ∑ q, coefficient μ s q f * F q z

include hs in
theorem observable_integral (F : I → Z → ℂ) (f : E → ℂ) (hf : Integrable f μ) (z : Z) :
    observable μ s F f z = ∫ x, F (s x) z * f x ∂μ := by
  rw [integral_decomposition μ s hs (fun q => F q z) f hf]
  apply Finset.sum_congr rfl
  intro q _
  exact mul_comm _ _

include hs in
theorem observable_bound (F : I → Z → ℂ) (B : ℝ) (hF : ∀ q z, ‖F q z‖ ≤ B)
    (f : E → ℂ) (hf : Integrable f μ) (z : Z) :
    ‖observable μ s F f z‖ ≤ B * ∫ x, ‖f x‖ ∂μ := by
  rw [observable_integral μ s hs F f hf z]
  have he (x : E) : ‖F (s x) z * f x‖ ≤ B * ‖f x‖ := by
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right (hF (s x) z) (norm_nonneg _)
  simpa only [integral_const_mul] using
    norm_integral_le_of_norm_le (hf.norm.const_mul B) (Filter.Eventually.of_forall he)

variable [TopologicalSpace Z]

theorem observable_continuous (F : I → Z → ℂ) (hF : ∀ q, Continuous (F q))
    (f : E → ℂ) : Continuous (observable μ s F f) :=
  continuous_finset_sum _ (fun q _ => continuous_const.mul (hF q))

variable [CompactSpace Z] [MeasurableSpace Z] [BorelSpace Z]
  (ν : Measure Z) [IsProbabilityMeasure ν]

include hs in
theorem expectation_identity (F : I → Z → ℂ) (hF : ∀ q, Continuous (F q))
    (f : E → ℂ) (hf : Integrable f μ) :
    (∫ z, observable μ s F f z ∂ν) = ∫ x, (∫ z, F (s x) z ∂ν) * f x ∂μ := by
  rw [integral_decomposition μ s hs (fun q => ∫ z, F q z ∂ν) f hf]
  unfold observable
  rw [integral_finset_sum _ (fun q _ =>
    ((hF q).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)).const_mul _)]
  simp only [integral_const_mul]
  apply Finset.sum_congr rfl
  intro q _
  exact mul_comm _ _

end
end UnifiedTheory.Clay.YangMills.FiniteCellSmearing
