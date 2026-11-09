/- A bounded within-fiber weight ratio pays once, not twice, when changing
from the reference center to an arbitrary weighted center. -/
import UnifiedTheory.Clay.YangMills.CompactCrossVariance

set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace UnifiedTheory.Clay.YangMills.CompactWeightedCenter
noncomputable section
open MeasureTheory ProbabilityTheory CompactDensityEntropy

variable {X : Type*} [TopologicalSpace X] [CompactSpace X]
  [MeasurableSpace X] [BorelSpace X] (μ : Measure X) [IsProbabilityMeasure μ]

/-- No normalization of the weight is required. The constant is its
oscillation ratio, rather than the square of that ratio. -/
theorem center_comparison (w f : X → ℝ) (hw : Continuous w) (hf : Continuous f)
    (hw0 : ∀ x, 0 ≤ w x) (C : ℝ) (hC : 0 ≤ C)
    (hcontrast : ∀ x y, w x ≤ C * w y) (d : ℝ) :
    (∫ x, w x*(f x-∫ y, f y ∂μ)^2 ∂μ) ≤ C*∫ x, w x*(f x-d)^2 ∂μ := by
  haveI : Nonempty X := MeasureTheory.nonempty_of_isProbabilityMeasure μ
  obtain ⟨a,_,ha⟩ := isCompact_univ.exists_isMinOn Set.univ_nonempty hw.continuousOn
  have hi (c : ℝ) : Integrable (fun x => (f x-c)^2) μ :=
    continuous_integrable μ _ ((hf.sub continuous_const).pow 2)
  have hwi (c : ℝ) : Integrable (fun x => w x*(f x-c)^2) μ :=
    continuous_integrable μ _ (hw.mul ((hf.sub continuous_const).pow 2))
  have hu := integral_mono (hwi (∫ y, f y ∂μ))
    ((hi (∫ y, f y ∂μ)).const_mul (C*w a))
    (fun x => mul_le_mul_of_nonneg_right (hcontrast x a) (sq_nonneg _))
  rw [integral_const_mul, ← variance_eq_integral hf.measurable.aemeasurable] at hu
  have hl := integral_mono ((hi d).const_mul (w a)) (hwi d)
    (fun x => mul_le_mul_of_nonneg_right (ha (Set.mem_univ x)) (sq_nonneg _))
  rw [integral_const_mul] at hl
  have hv := CompactCrossVariance.variance_le_square μ f hf d
  calc
    _ ≤ C*w a*variance f μ := hu
    _ ≤ C*(w a*∫ x, (f x-d)^2 ∂μ) := by
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hv (mul_nonneg hC (hw0 a))
    _ ≤ _ := mul_le_mul_of_nonneg_left hl hC

end
end UnifiedTheory.Clay.YangMills.CompactWeightedCenter
