/- Exact cancellation of a positive constant in a normalized Gibbs law.
This is an equality of the constructed measures, not a replacement of the
interacting exterior measure by a product distribution. -/
import UnifiedTheory.Clay.YangMills.CompactGibbsContinuity

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Clay.YangMills.GibbsConstantShift
noncomputable section
open MeasureTheory LocalGibbsComparison
open scoped ENNReal

variable {X : Type*} [MeasurableSpace X] (μ : Measure X)

theorem weightedLaw_const_mul (w : X → ℝ) (hw : Measurable w)
    (c : ℝ) (hc : 0 < c) :
    weightedLaw μ (fun x => c * w x) = weightedLaw μ w := by
  unfold weightedLaw
  rw [integral_const_mul, ENNReal.ofReal_mul hc.le]
  simp_rw [ENNReal.ofReal_mul hc.le]
  have hd : μ.withDensity (fun x => ENNReal.ofReal c * ENNReal.ofReal (w x)) =
      ENNReal.ofReal c • μ.withDensity (fun x => ENNReal.ofReal (w x)) :=
    withDensity_smul _ hw.ennreal_ofReal
  rw [hd, smul_smul, ENNReal.mul_inv (by simp) (by simp)]
  congr 1
  rw [mul_assoc, mul_comm (ENNReal.ofReal (∫ x, w x ∂μ))⁻¹ (ENNReal.ofReal c),
    ← mul_assoc, ENNReal.inv_mul_cancel (ENNReal.ofReal_pos.mpr hc).ne'
      ENNReal.ofReal_ne_top, one_mul]

variable [TopologicalSpace X] [BorelSpace X]

/-- An additive action constant cancels from the actual normalized law. -/
theorem law_const_add (S : X → ℝ) (hS : Continuous S) (c : ℝ) :
    CompactGibbsContinuity.law μ (fun x => c + S x) =
      CompactGibbsContinuity.law μ S := by
  unfold CompactGibbsContinuity.law
  have he : (fun x => Real.exp (-(c + S x))) =
      (fun x => Real.exp (-c) * Real.exp (-S x)) := by
    funext x
    rw [← Real.exp_add]
    congr 1
    ring
  rw [he]
  exact weightedLaw_const_mul μ _ (Real.continuous_exp.comp hS.neg).measurable
    _ (Real.exp_pos _)

end
end UnifiedTheory.Clay.YangMills.GibbsConstantShift
