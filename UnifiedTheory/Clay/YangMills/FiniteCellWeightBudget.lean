/- Integrating a test function over a measurable finite partition has an
L1 coefficient budget independent of the number or shape of the cells. -/
import UnifiedTheory.Clay.YangMills.FiniteCellSmearing

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Clay.YangMills.FiniteCellWeightBudget
noncomputable section
open MeasureTheory FiniteCellSmearing

variable {E I : Type*} [MeasurableSpace E] [Fintype I] [DecidableEq I]
  [MeasurableSpace I] [MeasurableSingletonClass I]
  (μ : Measure E) (s : E → I) (hs : Measurable s)

omit [MeasurableSpace E] [MeasurableSpace I] [MeasurableSingletonClass I] in
theorem sum_cell_norm (f : E → ℂ) (x : E) :
    (∑ q, ‖cellFunction s q f x‖) = ‖f x‖ := by
  simp only [cellFunction, apply_ite norm, norm_zero]
  simp

include hs in
theorem coefficient_norm_budget (f : E → ℂ) (hf : Integrable f μ) :
    (∑ q, ‖coefficient μ s q f‖) ≤ ∫ x, ‖f x‖ ∂μ := by
  calc
    (∑ q, ‖coefficient μ s q f‖) ≤
        ∑ q, ∫ x, ‖cellFunction s q f x‖ ∂μ :=
      Finset.sum_le_sum (fun q _ => norm_integral_le_integral_norm _)
    _ = ∫ x, ∑ q, ‖cellFunction s q f x‖ ∂μ :=
      (integral_finset_sum _ (fun q _ =>
        (cellFunction_integrable μ s hs q f hf).norm)).symm
    _ = ∫ x, ‖f x‖ ∂μ := by simp_rw [sum_cell_norm]

include hs in
theorem coefficient_re_budget (f : E → ℂ) (hf : Integrable f μ) :
    (∑ q, |(coefficient μ s q f).re|) ≤ ∫ x, ‖f x‖ ∂μ :=
  (Finset.sum_le_sum (fun q _ => Complex.abs_re_le_norm (coefficient μ s q f))).trans
    (coefficient_norm_budget μ s hs f hf)

include hs in
/-- Real coefficients give precisely the real part of the original complex
smeared observable when the regulated observable is real. -/
theorem real_observable_integral (K : I → ℝ) (f : E → ℂ) (hf : Integrable f μ) :
    (∑ q, (coefficient μ s q f).re * K q) =
      (∫ x, (K (s x) : ℂ) * f x ∂μ).re := by
  rw [integral_decomposition μ s hs (fun q => (K q : ℂ)) f hf]
  simp only [Complex.re_sum, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero]
  apply Finset.sum_congr rfl
  intro q _
  exact mul_comm _ _

end
end UnifiedTheory.Clay.YangMills.FiniteCellWeightBudget
