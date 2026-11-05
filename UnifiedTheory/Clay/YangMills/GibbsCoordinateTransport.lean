/- Exact transport of normalized Gibbs integrals across the finite-product
single-coordinate split. No conditional probability law is assumed. -/
import UnifiedTheory.Clay.YangMills.SingleCoordinateProduct

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Clay.YangMills.GibbsCoordinateTransport
noncomputable section
open MeasureTheory LocalGibbsComparison RegulatedGauge SingleCoordinateProduct
open scoped ENNReal

theorem weighted_integral_transport {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (μ : Measure X) (ν : Measure Y) (e : X ≃ᵐ Y) (he : MeasurePreserving e μ ν)
    (w : Y → ℝ) (hw : Measurable w) (hn : ∀ y, 0 ≤ w y) (hz : 0 < ∫ y, w y ∂ν)
    (f : Y → ℝ) :
    ∫ x, f (e x) ∂weightedLaw μ (w ∘ e) = ∫ y, f y ∂weightedLaw ν w := by
  have hpart : (∫ x, w (e x) ∂μ) = ∫ y, w y ∂ν := he.integral_comp e.measurableEmbedding w
  rw [weighted_integral μ (w ∘ e) (hw.comp e.measurable) (fun x => hn (e x))
    (by simpa only [Function.comp_apply, hpart] using hz) (fun x => f (e x))]
  rw [weighted_integral ν w hw hn hz f]
  change (∫ x, w (e x) * f (e x) ∂μ) / (∫ x, w (e x) ∂μ) = _
  rw [he.integral_comp e.measurableEmbedding (fun y => w y * f y), hpart]

variable (V : Type*) [Quiver V] (G : Type*) [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G] [CompactSpace G] [SecondCountableTopology G]
  [MeasurableSpace G] [BorelSpace G] [Fintype (Edge V)]

theorem gibbs_eq_weightedLaw (S : Configuration V G → ℝ) (hS : Continuous S) :
    gibbsMeasure V G S = weightedLaw (referenceMeasure G V) (fun U => Real.exp (-S U)) := by
  have hi := (Real.continuous_exp.comp hS.neg).integrable_of_hasCompactSupport
    (μ := referenceMeasure G V) (HasCompactSupport.of_compactSpace _)
  have hp : gibbsPartition V G S = ENNReal.ofReal (∫ U, Real.exp (-S U) ∂referenceMeasure G V) := by
    exact (ofReal_integral_eq_lintegral_ofReal hi
      (Filter.Eventually.of_forall (fun U => (Real.exp_pos (-S U)).le))).symm
  simp only [gibbsMeasure, weightedLaw, hp]
  rfl

local instance : DecidableEq (Edge V) := Classical.decEq _

theorem gibbs_integral_split (S : Configuration V G → ℝ) (hS : Continuous S)
    (e : Edge V) (f : Configuration V G → ℝ) :
    ∫ U, f U ∂gibbsMeasure V G S =
      ∫ z, f (assemble e z) ∂weightedLaw
        ((Measure.pi (fun _ : {i : Edge V // i ≠ e} => compactHaar G)).prod (compactHaar G))
        (fun z => Real.exp (-S (assemble e z))) := by
  classical
  rw [gibbs_eq_weightedLaw V G S hS]
  symm
  apply weighted_integral_transport _ _ (assemble e) (assemble_preserving e (compactHaar G))
    (fun U => Real.exp (-S U)) (Real.continuous_exp.comp hS.neg).measurable
    (fun U => (Real.exp_pos _).le)
  exact integral_exp_pos ((Real.continuous_exp.comp hS.neg).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _))

end
end UnifiedTheory.Clay.YangMills.GibbsCoordinateTransport
