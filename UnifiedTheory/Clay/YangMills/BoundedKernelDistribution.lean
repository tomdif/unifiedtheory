/- Bounded measurable kernels define actual tempered functionals with an
explicit continuous L1 seminorm bound. No renormalization assertion is made. -/
import UnifiedTheory.Clay.YangMills.SeminormWeakCompactness

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Clay.YangMills.BoundedKernelDistribution
noncomputable section
open MeasureTheory
open scoped NNReal ENNReal

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  (μ : Measure E) [μ.HasTemperateGrowth]

def l1Seminorm : Seminorm ℂ (SchwartzMap E ℂ) :=
  (normSeminorm ℂ (Lp ℂ 1 μ)).comp (SchwartzMap.toLpCLM ℂ ℂ 1 μ).toLinearMap

theorem l1Seminorm_continuous : Continuous (l1Seminorm μ) :=
  continuous_norm.comp (SchwartzMap.toLpCLM ℂ ℂ 1 μ).continuous

theorem l1Seminorm_apply (f : SchwartzMap E ℂ) :
    l1Seminorm μ f = ∫ x, ‖f x‖ ∂μ := by
  change ‖f.toLp 1 μ‖ = _
  rw [L1.norm_eq_integral_norm]
  exact integral_congr_ae ((f.coeFn_toLp 1 μ).fun_comp norm)

def boundSeminorm (B : ℝ≥0) : Seminorm ℂ (SchwartzMap E ℂ) := B • l1Seminorm μ

theorem boundSeminorm_continuous (B : ℝ≥0) : Continuous (boundSeminorm μ B) :=
  continuous_const.mul (l1Seminorm_continuous μ)

theorem kernel_integrable (K : E → ℂ) (hK : Measurable K) (B : ℝ≥0)
    (hb : ∀ x, ‖K x‖ ≤ B) (f : SchwartzMap E ℂ) :
    Integrable (fun x => K x * f x) μ :=
  f.integrable.bdd_mul hK.aestronglyMeasurable (Filter.Eventually.of_forall hb)

def kernelLinear (K : E → ℂ) (hK : Measurable K) (B : ℝ≥0)
    (hb : ∀ x, ‖K x‖ ≤ B) : SchwartzMap E ℂ →ₗ[ℂ] ℂ where
  toFun f := ∫ x, K x * f x ∂μ
  map_add' f g := by
    change (∫ x, K x * (f x + g x) ∂μ) = _
    simp_rw [mul_add]
    exact integral_add (kernel_integrable μ K hK B hb f) (kernel_integrable μ K hK B hb g)
  map_smul' c f := by
    change (∫ x, K x * (c * f x) ∂μ) = c * ∫ x, K x * f x ∂μ
    simp_rw [mul_left_comm (K _) c]
    exact integral_const_mul c _

theorem kernel_bound (K : E → ℂ) (hK : Measurable K) (B : ℝ≥0)
    (hb : ∀ x, ‖K x‖ ≤ B) (f : SchwartzMap E ℂ) :
    ‖kernelLinear μ K hK B hb f‖ ≤ boundSeminorm μ B f := by
  have he : ∀ x, ‖K x * f x‖ ≤ (B : ℝ) * ‖f x‖ :=
    fun x => by rw [norm_mul]; exact mul_le_mul_of_nonneg_right (hb x) (norm_nonneg _)
  have ht := norm_integral_le_of_norm_le (μ := μ) ((f.integrable (μ := μ)).norm.const_mul (B : ℝ))
    (Filter.Eventually.of_forall he)
  change ‖∫ x, K x * f x ∂μ‖ ≤ (B : ℝ) * l1Seminorm μ f
  rw [l1Seminorm_apply]
  simpa only [integral_const_mul] using ht

def functional (K : E → ℂ) (hK : Measurable K) (B : ℝ≥0)
    (hb : ∀ x, ‖K x‖ ≤ B) : SchwartzMap E ℂ →L[ℂ] ℂ :=
  ⟨kernelLinear μ K hK B hb,
    SeminormWeakCompactness.continuous_of_seminorm_bound _ (boundSeminorm μ B)
      (boundSeminorm_continuous μ B) (kernel_bound μ K hK B hb)⟩

theorem functional_apply (K : E → ℂ) (hK : Measurable K) (B : ℝ≥0)
    (hb : ∀ x, ‖K x‖ ≤ B) (f : SchwartzMap E ℂ) :
    functional μ K hK B hb f = ∫ x, K x * f x ∂μ := rfl

theorem functional_bound (K : E → ℂ) (hK : Measurable K) (B : ℝ≥0)
    (hb : ∀ x, ‖K x‖ ≤ B) (f : SchwartzMap E ℂ) :
    ‖functional μ K hK B hb f‖ ≤ boundSeminorm μ B f := kernel_bound μ K hK B hb f

end
end UnifiedTheory.Clay.YangMills.BoundedKernelDistribution
