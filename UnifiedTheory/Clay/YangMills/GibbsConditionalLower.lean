/- Exact averaging of uniform fiber Gibbs bounds. The full action and its
fiber partition factors are retained; there is no global density-ratio loss. -/
import UnifiedTheory.Clay.YangMills.CompactGibbsContinuity

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Clay.YangMills.GibbsConditionalLower
noncomputable section
open MeasureTheory CompactGibbsContinuity LocalGibbsComparison

variable {X Y : Type*} [TopologicalSpace X] [CompactSpace X] [SecondCountableTopology X]
  [MeasurableSpace X] [BorelSpace X]
  [TopologicalSpace Y] [CompactSpace Y] [SecondCountableTopology Y]
  [MeasurableSpace Y] [BorelSpace Y]
  (μ : Measure X) (ν : Measure Y) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]

theorem expectation_lower (S : Y × X → ℝ) (hS : Continuous S)
    (Q : Y × X → ℝ) (hQ : Continuous Q) (v : ℝ)
    (hv : ∀ y, v ≤ ∫ x, Q (y,x) ∂law μ (fun x => S (y,x))) :
    v ≤ ∫ z, Q z ∂law (ν.prod μ) S := by
  let w := fun z => Real.exp (-S z)
  have hw : Continuous w := Real.continuous_exp.comp hS.neg
  have hiw : Integrable w (ν.prod μ) :=
    hw.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hiq : Integrable (fun z => w z*Q z) (ν.prod μ) :=
    (hw.mul hQ).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hz : 0 < ∫ z, w z ∂ν.prod μ := partition_positive _ S hS
  have hpoint (y : Y) : v*(∫ x, w (y,x) ∂μ) ≤ ∫ x, w (y,x)*Q (y,x) ∂μ := by
    have hs : Continuous (fun x => S (y,x)) := hS.comp (continuous_const.prodMk continuous_id)
    have hp := partition_positive μ (fun x => S (y,x)) hs
    have hh := hv y
    rw [law, weighted_integral μ (fun x => Real.exp (-S (y,x))) (Real.continuous_exp.comp hs.neg).measurable
      (fun x => (Real.exp_pos _).le) hp] at hh
    exact (le_div_iff₀ hp).mp hh
  rw [law, weighted_integral (ν.prod μ) w hw.measurable (fun z => (Real.exp_pos _).le) hz]
  apply (le_div_iff₀ hz).mpr
  change v*(∫ z, w z ∂ν.prod μ) ≤ ∫ z, w z*Q z ∂ν.prod μ
  rw [integral_prod _ hiw, integral_prod _ hiq, ← integral_const_mul]
  exact integral_mono (hiw.integral_prod_left.const_mul v) hiq.integral_prod_left hpoint

end
end UnifiedTheory.Clay.YangMills.GibbsConditionalLower
