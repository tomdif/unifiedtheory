/- Exact transport of normalized Gibbs laws through a measure-preserving
coordinate decomposition, followed by boundary-gluing reflection positivity. -/
import UnifiedTheory.Clay.YangMills.BoundaryReflectionGluing
import UnifiedTheory.Clay.YangMills.RegulatedGaugeOrientation

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Clay.YangMills.GibbsReflectionTransport
noncomputable section
open MeasureTheory RegulatedGauge BoundaryReflectionGluing
open scoped ENNReal

theorem withDensity_transport {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    {μ : Measure X} {ν : Measure Y} {T : X → Y} (hT : MeasurePreserving T μ ν)
    (f : Y → ℝ≥0∞) (hf : Measurable f) :
    MeasurePreserving T (μ.withDensity (f ∘ T)) (ν.withDensity f) := by
  refine ⟨hT.measurable, ?_⟩
  apply Measure.ext
  intro s hs
  rw [Measure.map_apply hT.measurable hs, withDensity_apply _ (hT.measurable hs),
    withDensity_apply _ hs]
  exact hT.setLIntegral_comp_preimage hs hf

theorem normalized_transport {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    {μ : Measure X} {ν : Measure Y} {T : X → Y} (hT : MeasurePreserving T μ ν)
    (f : Y → ℝ≥0∞) (hf : Measurable f) :
    MeasurePreserving T ((∫⁻ x, f (T x) ∂μ)⁻¹ • μ.withDensity (f ∘ T))
      ((∫⁻ y, f y ∂ν)⁻¹ • ν.withDensity f) := by
  rw [hT.lintegral_comp hf]
  exact (withDensity_transport hT f hf).smul_measure _

variable {B X : Type*} [TopologicalSpace B] [CompactSpace B] [SecondCountableTopology B]
  [MeasurableSpace B] [BorelSpace B]
  [TopologicalSpace X] [CompactSpace X] [SecondCountableTopology X]
  [MeasurableSpace X] [BorelSpace X]
  (μB : Measure B) (μX : Measure X) [IsProbabilityMeasure μB] [IsProbabilityMeasure μX]
  (V : Type*) [Quiver V] (G : Type*) [Group G]
  [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] [Fintype (Edge V)]

theorem gibbs_to_boundary (S : Configuration V G → ℝ)
    (T : Configuration V G → B × (X × X))
    (hT : MeasurePreserving T (referenceMeasure G V) (μB.prod (μX.prod μX)))
    (w : B → ℝ) (hcw : Continuous w) (A : B × X → ℝ) (hA : Continuous A)
    (hd : ∀ U, Real.exp (-S U) = weight w A (T U)) :
    MeasurePreserving T (gibbsMeasure V G S) (law μB μX w A) := by
  have he : gibbsDensity V G S = (fun z => ENNReal.ofReal (weight w A z)) ∘ T := by
    funext U
    exact congrArg ENNReal.ofReal (hd U)
  unfold gibbsMeasure gibbsPartition
  rw [he]
  exact normalized_transport hT _ (weight_continuous w hcw A hA).measurable.ennreal_ofReal

/-- Once the actual coordinate/action identification is proved, the reflected
integral is exactly the already constructed positive boundary-gluing form. -/
theorem reflection_positive_transport (S : Configuration V G → ℝ)
    (T : Configuration V G ≃ᵐ B × (X × X))
    (hT : MeasurePreserving T (referenceMeasure G V) (μB.prod (μX.prod μX)))
    (R : Configuration V G → Configuration V G)
    (hR : ∀ U, T (R U) = reflection (T U))
    (w : B → ℝ) (hcw : Continuous w) (hw : ∀ b, 0 < w b)
    (A : B × X → ℝ) (hA : Continuous A)
    (hd : ∀ U, Real.exp (-S U) = weight w A (T U))
    (f : B × X → ℂ) (hf : Continuous f) :
    0 ≤ (∫ U, star (halfObservable f (T (R U))) * halfObservable f (T U)
      ∂gibbsMeasure V G S).re ∧
    (∫ U, star (halfObservable f (T (R U))) * halfObservable f (T U)
      ∂gibbsMeasure V G S).im = 0 := by
  simp_rw [hR]
  have hp := gibbs_to_boundary μB μX V G S T hT w hcw A hA hd
  rw [hp.integral_comp T.measurableEmbedding
    (fun z => star (halfObservable f (reflection z)) * halfObservable f z)]
  exact BoundaryReflectionGluing.reflection_positive μB μX w hcw hw A hA f hf

end
end UnifiedTheory.Clay.YangMills.GibbsReflectionTransport
