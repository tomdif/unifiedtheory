/- Uniform test limits control force integrals, endpoint expectations and
time-integrated expectations. Time measurability of a limit is derived. -/
import UnifiedTheory.Audit.KFCausalNeutralTensorTestEquation
import Mathlib.MeasureTheory.Integral.DominatedConvergence

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 350000

namespace UnifiedTheory.Audit.KFCausalSpacetimeUniformTests
noncomputable section
open MeasureTheory Set Filter BoundedContinuousFunction
open scoped Topology
open UnifiedTheory.Audit.KFCausalSpacetimeForcePair (Pair)

variable {X : Type*} [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]

def integralCLM (μ : Measure X) [IsFiniteMeasure μ] : (X →ᵇ ℂ) →L[ℂ] ℂ :=
  LinearMap.mkContinuous
    { toFun := fun q => ∫ x, q x ∂μ
      map_add' := fun q r => integral_add (q.integrable μ) (r.integrable μ)
      map_smul' := fun c q => integral_smul c q }
    (μ.real univ) (fun q => q.norm_integral_le_mul_norm μ)

theorem integralCLM_apply (μ : Measure X) [IsFiniteMeasure μ] (q : X →ᵇ ℂ) :
    integralCLM μ q = ∫ x, q x ∂μ := rfl

def slice (t : ℝ) (q : (ℝ × ℝ) →ᵇ ℂ) : ℝ →ᵇ ℂ :=
  q.compContinuous ⟨fun p => (t,p),continuous_const.prodMk continuous_id⟩

theorem slice_norm_le (t : ℝ) (q : (ℝ × ℝ) →ᵇ ℂ) : ‖slice t q‖ ≤ ‖q‖ := by
  apply (BoundedContinuousFunction.norm_le (norm_nonneg q)).mpr
  exact fun p => q.norm_coe_le_norm (t,p)

def sliceCLM (t : ℝ) : ((ℝ × ℝ) →ᵇ ℂ) →L[ℂ] (ℝ →ᵇ ℂ) :=
  LinearMap.mkContinuous
    { toFun := slice t
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
    1 (fun q => by simpa only [one_mul] using slice_norm_le t q)

def expectation (ν : ℝ → ProbabilityMeasure ℝ) (q : (ℝ × ℝ) →ᵇ ℂ) (t : ℝ) : ℂ :=
  ∫ p, q (t,p) ∂(ν t : Measure ℝ)

theorem expectation_norm (ν : ℝ → ProbabilityMeasure ℝ) (q : (ℝ × ℝ) →ᵇ ℂ) (t : ℝ) :
    ‖expectation ν q t‖ ≤ ‖q‖ :=
  ((slice t q).norm_integral_le_norm (ν t : Measure ℝ)).trans (slice_norm_le t q)

theorem expectation_tendsto (ν : ℝ → ProbabilityMeasure ℝ) (q : ℕ → (ℝ × ℝ) →ᵇ ℂ)
    (q₀ : (ℝ × ℝ) →ᵇ ℂ) (hq : Tendsto q atTop (𝓝 q₀)) (t : ℝ) :
    Tendsto (fun n => expectation ν (q n) t) atTop (𝓝 (expectation ν q₀ t)) :=
  ((integralCLM (ν t : Measure ℝ)).continuous.comp (sliceCLM t).continuous).tendsto q₀ |>.comp hq

theorem force_tendsto (F : Pair) (q : ℕ → (ℝ × ℝ) →ᵇ ℂ)
    (q₀ : (ℝ × ℝ) →ᵇ ℂ) (hq : Tendsto q atTop (𝓝 q₀)) :
    Tendsto (fun n => F.evaluate (q n)) atTop (𝓝 (F.evaluate q₀)) := by
  exact (((integralCLM F.positive).continuous.tendsto q₀ |>.comp hq).sub
    ((integralCLM F.negative).continuous.tendsto q₀ |>.comp hq)).div_const 2

theorem expectation_limit_integrable (ν : ℝ → ProbabilityMeasure ℝ) (a b : ℝ)
    (q : ℕ → (ℝ × ℝ) →ᵇ ℂ) (q₀ : (ℝ × ℝ) →ᵇ ℂ)
    (hq : Tendsto q atTop (𝓝 q₀))
    (hi : ∀ n, Integrable (expectation ν (q n)) (volume.restrict (Icc a b))) :
    Integrable (expectation ν q₀) (volume.restrict (Icc a b)) := by
  have hm : AEStronglyMeasurable (expectation ν q₀) (volume.restrict (Icc a b)) :=
    aestronglyMeasurable_of_tendsto_ae atTop (fun n => (hi n).aestronglyMeasurable)
      (ae_of_all _ (expectation_tendsto ν q q₀ hq))
  exact (integrable_const ‖q₀‖).mono' hm (ae_of_all _ (expectation_norm ν q₀))

theorem expectation_integral_tendsto (ν : ℝ → ProbabilityMeasure ℝ) (a b : ℝ)
    (q : ℕ → (ℝ × ℝ) →ᵇ ℂ) (q₀ : (ℝ × ℝ) →ᵇ ℂ)
    (hq : Tendsto q atTop (𝓝 q₀))
    (hi : ∀ n, Integrable (expectation ν (q n)) (volume.restrict (Icc a b))) :
    Tendsto (fun n => ∫ t in Icc a b, expectation ν (q n) t) atTop
      (𝓝 (∫ t in Icc a b, expectation ν q₀ t)) := by
  obtain ⟨C,hC⟩ := hq.cauchySeq.isBounded_range.exists_norm_le
  exact tendsto_integral_of_dominated_convergence (fun _ => C)
    (fun n => (hi n).aestronglyMeasurable) (integrable_const C)
    (fun n => ae_of_all _ (fun t => (expectation_norm ν (q n) t).trans (hC (q n) ⟨n,rfl⟩)))
    (ae_of_all _ (expectation_tendsto ν q q₀ hq))

#print axioms integralCLM_apply
#print axioms slice_norm_le
#print axioms expectation_norm
#print axioms expectation_tendsto
#print axioms force_tendsto
#print axioms expectation_limit_integrable
#print axioms expectation_integral_tendsto
end
end UnifiedTheory.Audit.KFCausalSpacetimeUniformTests
