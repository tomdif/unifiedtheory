/- Bounded measurable kernels act on L1 itself. Their Schwartz functionals
are the restrictions along the canonical Schwartz-to-L1 map. -/
import UnifiedTheory.Clay.YangMills.BoundedKernelDistribution

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Clay.YangMills.BoundedKernelL1
noncomputable section
open MeasureTheory
open scoped NNReal ENNReal

variable {X : Type*} [MeasurableSpace X] (μ : Measure X)

theorem kernel_integrable (K : X → ℂ) (hK : Measurable K) (B : ℝ≥0)
    (hb : ∀ x, ‖K x‖ ≤ B) (f : Lp ℂ 1 μ) :
    Integrable (fun x => K x * f x) μ :=
  (memLp_one_iff_integrable.mp (Lp.memLp f)).bdd_mul hK.aestronglyMeasurable
    (Filter.Eventually.of_forall hb)

def kernelLinear (K : X → ℂ) (hK : Measurable K) (B : ℝ≥0)
    (hb : ∀ x, ‖K x‖ ≤ B) : Lp ℂ 1 μ →ₗ[ℂ] ℂ where
  toFun f := ∫ x, K x * f x ∂μ
  map_add' f g := by
    calc
      (∫ x, K x * (f + g) x ∂μ) = ∫ x, K x * (f x + g x) ∂μ :=
        integral_congr_ae ((Lp.coeFn_add f g).mono (fun x hx => congrArg (K x * ·) hx))
      _ = (∫ x, K x * f x ∂μ) + ∫ x, K x * g x ∂μ := by
        simp_rw [mul_add]
        exact integral_add (kernel_integrable μ K hK B hb f)
          (kernel_integrable μ K hK B hb g)
  map_smul' c f := by
    change (∫ x, K x * (c • f) x ∂μ) = c * ∫ x, K x * f x ∂μ
    calc
      _ = ∫ x, K x * (c * f x) ∂μ :=
        integral_congr_ae ((Lp.coeFn_smul c f).mono
          (fun x hx => congrArg (K x * ·) hx))
      _ = _ := by
        simp_rw [mul_left_comm (K _) c]
        exact integral_const_mul c _

theorem kernel_bound (K : X → ℂ) (hK : Measurable K) (B : ℝ≥0)
    (hb : ∀ x, ‖K x‖ ≤ B) (f : Lp ℂ 1 μ) :
    ‖kernelLinear μ K hK B hb f‖ ≤ (B : ℝ) * ‖f‖ := by
  have he : ∀ x, ‖K x * f x‖ ≤ (B : ℝ) * ‖f x‖ := fun x => by
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right (hb x) (norm_nonneg _)
  have hi := (memLp_one_iff_integrable.mp (Lp.memLp f)).norm.const_mul (B : ℝ)
  have ht := norm_integral_le_of_norm_le (μ := μ) hi (Filter.Eventually.of_forall he)
  change ‖∫ x, K x * f x ∂μ‖ ≤ (B : ℝ) * ‖f‖
  rw [L1.norm_eq_integral_norm]
  simpa only [integral_const_mul] using ht

def functional (K : X → ℂ) (hK : Measurable K) (B : ℝ≥0)
    (hb : ∀ x, ‖K x‖ ≤ B) : Lp ℂ 1 μ →L[ℂ] ℂ :=
  (kernelLinear μ K hK B hb).mkContinuous B (kernel_bound μ K hK B hb)

theorem functional_apply (K : X → ℂ) (hK : Measurable K) (B : ℝ≥0)
    (hb : ∀ x, ‖K x‖ ≤ B) (f : Lp ℂ 1 μ) :
    functional μ K hK B hb f = ∫ x, K x * f x ∂μ := rfl

theorem functional_norm_le (K : X → ℂ) (hK : Measurable K) (B : ℝ≥0)
    (hb : ∀ x, ‖K x‖ ≤ B) : ‖functional μ K hK B hb‖ ≤ B :=
  (functional μ K hK B hb).opNorm_le_bound B.coe_nonneg (kernel_bound μ K hK B hb)

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  (ν : Measure E) [ν.HasTemperateGrowth]

theorem functional_comp_toLp (K : E → ℂ) (hK : Measurable K) (B : ℝ≥0)
    (hb : ∀ x, ‖K x‖ ≤ B) :
    (functional ν K hK B hb).comp (SchwartzMap.toLpCLM ℂ ℂ 1 ν) =
      BoundedKernelDistribution.functional ν K hK B hb := by
  ext f
  change (∫ x, K x * (f.toLp 1 ν) x ∂ν) = ∫ x, K x * f x ∂ν
  exact integral_congr_ae ((f.coeFn_toLp 1 ν).mono
    (fun x hx => congrArg (K x * ·) hx))

end
end UnifiedTheory.Clay.YangMills.BoundedKernelL1
