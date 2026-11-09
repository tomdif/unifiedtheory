/- An independent comparison draw pays for the variance of the original
law with coefficient one. The comparison law need not be stationary. -/
import UnifiedTheory.Clay.YangMills.CompactLikelihoodVariance
import Mathlib.MeasureTheory.Integral.Prod

set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace UnifiedTheory.Clay.YangMills.CompactCrossVariance
noncomputable section
open MeasureTheory ProbabilityTheory CompactDensityEntropy

variable {X : Type*} [TopologicalSpace X] [CompactSpace X]
  [MeasurableSpace X] [BorelSpace X] (μ : Measure X) [IsProbabilityMeasure μ]

theorem square_about_center (f : X → ℝ) (hf : Continuous f) (c : ℝ) :
    (∫ x, (f x-c)^2 ∂μ) = variance f μ + ((∫ x, f x ∂μ)-c)^2 := by
  have hi := continuous_integrable μ f hf
  have hi2 := continuous_integrable μ _ (hf.pow 2)
  have h1 := integral_add (hi2.sub (hi.const_mul (2*c))) (integrable_const (c^2))
  have h2 := integral_sub hi2 (hi.const_mul (2*c))
  simp only [Pi.sub_apply] at h1
  calc
    _ = ∫ x, (f x)^2 - (2*c)*f x + c^2 ∂μ := by
      apply integral_congr_ae
      filter_upwards with x
      ring
    _ = _ := by
      rw [h1, h2, integral_const_mul]
      simp only [integral_const, probReal_univ, smul_eq_mul, one_mul]
      rw [CompactLikelihoodVariance.variance_formula μ f hf]
      ring

theorem variance_le_square (f : X → ℝ) (hf : Continuous f) (c : ℝ) :
    variance f μ ≤ ∫ x, (f x-c)^2 ∂μ := by
  rw [square_about_center μ f hf c]
  exact le_add_of_nonneg_right (sq_nonneg _)

variable {Y : Type*} [TopologicalSpace Y] [CompactSpace Y]
  [MeasurableSpace Y] [BorelSpace Y] (ν : Measure Y) [IsProbabilityMeasure ν]

theorem cross_square (f : X → ℝ) (hf : Continuous f) (g : Y → ℝ) (hg : Continuous g) :
    (∫ y, ∫ x, (f x-g y)^2 ∂μ ∂ν) =
      variance f μ + ∫ y, ((∫ x, f x ∂μ)-g y)^2 ∂ν := by
  simp_rw [square_about_center μ f hf]
  rw [integral_add (integrable_const _)
    (continuous_integrable ν _ ((continuous_const.sub hg).pow 2))]
  simp

theorem cross_square_decomposition (f : X → ℝ) (hf : Continuous f)
    (g : Y → ℝ) (hg : Continuous g) :
    (∫ y, ∫ x, (f x-g y)^2 ∂μ ∂ν) = variance f μ + variance g ν +
      ((∫ x, f x ∂μ)-(∫ y, g y ∂ν))^2 := by
  rw [cross_square μ ν f hf g hg]
  simp_rw [sub_sq_comm (∫ x, f x ∂μ)]
  rw [square_about_center ν g hg]
  ring

theorem variance_le_cross_square (f : X → ℝ) (hf : Continuous f)
    (g : Y → ℝ) (hg : Continuous g) :
    variance f μ ≤ ∫ y, ∫ x, (f x-g y)^2 ∂μ ∂ν := by
  rw [cross_square μ ν f hf g hg]
  exact le_add_of_nonneg_right (integral_nonneg (fun y => sq_nonneg _))

end
end UnifiedTheory.Clay.YangMills.CompactCrossVariance
