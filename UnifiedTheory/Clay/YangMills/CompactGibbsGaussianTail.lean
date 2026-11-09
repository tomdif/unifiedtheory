/- A reference Gaussian supplies an actual Gibbs partition lower bound.
The fixed exterior constant cancels from the normalized event estimate. -/
import UnifiedTheory.Clay.YangMills.WilsonJointBadStarTail

set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace UnifiedTheory.Clay.YangMills.CompactGibbsGaussianTail
noncomputable section
open MeasureTheory

variable {X : Type*} [TopologicalSpace X] [CompactSpace X]
  [MeasurableSpace X] [BorelSpace X] (μ : Measure X) [IsProbabilityMeasure μ]

theorem partition_lower (A D : X → ℝ) (hA : Continuous A) (hD : Continuous D)
    (c U γ : ℝ) (hupper : ∀ x, A x ≤ c + U + γ * D x) :
    Real.exp (-c - U) * (∫ x, Real.exp (-γ * D x) ∂μ) ≤
      ∫ x, Real.exp (-A x) ∂μ := by
  rw [← integral_const_mul]
  apply integral_mono
    ((continuous_const.mul (continuous_const.mul hD).rexp).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _))
    (hA.neg.rexp.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
  intro x
  simp only [Pi.mul_apply] at *
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  linarith only [hupper x]

/-- No measurability assumption on the exceptional event is needed for
this outer-measure upper bound. The Gaussian normalization is proved separately. -/
theorem event_bound (A D : X → ℝ) (hA : Continuous A) (hD : Continuous D)
    (c U γ K T : ℝ) (E : Set X)
    (hupper : ∀ x, A x ≤ c + U + γ * D x)
    (hgaussian : Real.exp (-K) ≤ ∫ x, Real.exp (-γ * D x) ∂μ)
    (hbad : ∀ x ∈ E, c + T ≤ A x) :
    (CompactGibbsContinuity.law μ A).real E ≤ Real.exp (U + K - T) := by
  have hZ : Real.exp (-(c + U + K)) ≤ ∫ x, Real.exp (-A x) ∂μ := by
    calc
      _ = Real.exp (-c - U) * Real.exp (-K) := by rw [← Real.exp_add]; congr 1; ring
      _ ≤ Real.exp (-c - U) * ∫ x, Real.exp (-γ * D x) ∂μ :=
        mul_le_mul_of_nonneg_left hgaussian (Real.exp_pos _).le
      _ ≤ _ := partition_lower μ A D hA hD c U γ hupper
  have hh := WilsonJointBadStarTail.gibbs_event_bound μ A hA E (c + T) (c + U + K) hbad hZ
  convert hh using 1; congr 1; ring

end
end UnifiedTheory.Clay.YangMills.CompactGibbsGaussianTail
