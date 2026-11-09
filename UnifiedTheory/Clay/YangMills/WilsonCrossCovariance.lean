/- Exact separated-source covariance under the original interacting Wilson
law. The hypothesis is checked on affected plaquettes, not on a comparison
product measure. No continuum covariance lower bound is asserted. -/
import UnifiedTheory.Clay.YangMills.GibbsCrossCovariance
import UnifiedTheory.Clay.YangMills.WilsonSeparatedSources

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Clay.YangMills.WilsonCrossCovariance
noncomputable section
open MeasureTheory RegulatedGauge PeriodicLattice4 WilsonBlockMarginal
open WilsonSeparatedSources GibbsMarginalTower GibbsCrossCovariance

variable (n : ℕ) [NeZero n] (G : Type*) [Group G]
  [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]

local instance : DecidableEq (Edge (Vertex n)) := Classical.decEq _
local instance : DecidableEq (WilsonIndependentBlocks.Link n) := Classical.decEq _

def retainedLaw (χ : G → ℂ) (β c : ℝ) (S : Finset (Edge (Vertex n))) :
    Measure (Outside (G := G) S) :=
  marginal (outsideMeasure S (compactHaar G)) (insideMeasure S (compactHaar G))
    (splitAction n G χ β c S)

def retainedSource (χ : G → ℂ) (β c : ℝ) (S : Finset (Edge (Vertex n)))
    (f : PlaquetteIndex n → ℝ) : Outside (G := G) S → ℝ :=
  response (insideMeasure S (compactHaar G)) (splitAction n G χ β c S)
    (splitSource n G χ c S f)

omit [CompactSpace G] [SecondCountableTopology G] [BorelSpace G] in
theorem splitSource_continuous (χ : G → ℂ) (hχ : Continuous χ) (c : ℝ)
    (S : Finset (Edge (Vertex n))) (f : PlaquetteIndex n → ℝ) :
    Continuous (splitSource n G χ c S f) :=
  (WilsonBlockIntegration.source_continuous n G χ hχ c f).comp (assemble_continuous S)

theorem retainedSource_continuous (χ : G → ℂ) (hχ : Continuous χ) (β c : ℝ)
    (S : Finset (Edge (Vertex n))) (f : PlaquetteIndex n → ℝ) :
    Continuous (retainedSource n G χ β c S f) :=
  response_continuous _ _ _ (splitAction_continuous n G χ hχ β c S)
    (splitSource_continuous n G χ hχ c S f)

theorem source_mean_preserved (χ : G → ℂ) (hχ : Continuous χ) (β c : ℝ)
    (S : Finset (Edge (Vertex n))) (f : PlaquetteIndex n → ℝ) :
    (∫ U, WilsonBlockIntegration.source n G χ c f U ∂wilsonLaw n G χ β c) =
      ∫ b, retainedSource n G χ β c S f b ∂retainedLaw n G χ β c S := by
  rw [wilson_integral_split n G χ hχ β c S]
  exact (response_expectation _ _ _ _ (splitAction_continuous n G χ hχ β c S)
    (splitSource_continuous n G χ hχ c S f)).symm

/-- Separated mixed moments survive integration exactly, even though the
retained probability need not factor and its action need not be Wilson. -/
theorem source_product_preserved (χ : G → ℂ) (hχ : Continuous χ) (β c : ℝ)
    (S : Finset (Edge (Vertex n)))
    (hS : WilsonIndependentBlocks.Independent n (S.image (WilsonIndependentBlocks.edgeCoord n)))
    (f g : PlaquetteIndex n → ℝ) (hsep : SeparatedOnBlock n S f g) :
    (∫ U, WilsonBlockIntegration.source n G χ c f U *
      WilsonBlockIntegration.source n G χ c g U ∂wilsonLaw n G χ β c) =
      ∫ b, retainedSource n G χ β c S f b * retainedSource n G χ β c S g b
        ∂retainedLaw n G χ β c S := by
  rw [wilson_integral_split n G χ hχ β c S]
  exact product_preserved _ _ _ _ _ (splitAction_continuous n G χ hχ β c S)
    (splitSource_continuous n G χ hχ c S f) (splitSource_continuous n G χ hχ c S g)
    (actual_response_product n G χ hχ β c S hS f g hsep)

theorem source_covariance_preserved (χ : G → ℂ) (hχ : Continuous χ) (β c : ℝ)
    (S : Finset (Edge (Vertex n)))
    (hS : WilsonIndependentBlocks.Independent n (S.image (WilsonIndependentBlocks.edgeCoord n)))
    (f g : PlaquetteIndex n → ℝ) (hsep : SeparatedOnBlock n S f g) :
    covariance (wilsonLaw n G χ β c)
      (WilsonBlockIntegration.source n G χ c f) (WilsonBlockIntegration.source n G χ c g) =
      covariance (retainedLaw n G χ β c S)
        (retainedSource n G χ β c S f) (retainedSource n G χ β c S g) := by
  unfold covariance
  rw [source_product_preserved n G χ hχ β c S hS f g hsep,
    source_mean_preserved n G χ hχ β c S f, source_mean_preserved n G χ hχ β c S g]

/-- Arbitrary scalar rescaling preserves the exact equality; this does not
give any uniform upper or positive lower bound on either side. -/
theorem rescaled_covariance_preserved (χ : G → ℂ) (hχ : Continuous χ) (β c : ℝ)
    (S : Finset (Edge (Vertex n)))
    (hS : WilsonIndependentBlocks.Independent n (S.image (WilsonIndependentBlocks.edgeCoord n)))
    (f g : PlaquetteIndex n → ℝ) (hsep : SeparatedOnBlock n S f g) (s t : ℝ) :
    covariance (wilsonLaw n G χ β c)
      (fun U => s * WilsonBlockIntegration.source n G χ c f U)
      (fun U => t * WilsonBlockIntegration.source n G χ c g U) =
      covariance (retainedLaw n G χ β c S)
        (fun b => s * retainedSource n G χ β c S f b)
        (fun b => t * retainedSource n G χ β c S g b) := by
  rw [covariance_scale, covariance_scale, source_covariance_preserved n G χ hχ β c S hS f g
    hsep]

def removedSource (χ : G → ℂ) (β c : ℝ) (S : Finset (Edge (Vertex n)))
    (f : PlaquetteIndex n → ℝ) (U : Configuration (Vertex n) G) : ℝ :=
  WilsonBlockIntegration.source n G χ c f U -
    retainedSource n G χ β c S f ((assemble S).symm U).1

omit [SecondCountableTopology G] in
theorem removedSource_assemble (χ : G → ℂ) (β c : ℝ) (S : Finset (Edge (Vertex n)))
    (f : PlaquetteIndex n → ℝ) (z : Outside (G := G) S × Inside (G := G) S) :
    removedSource n G χ β c S f (assemble S z) =
      removed (insideMeasure S (compactHaar G)) (splitAction n G χ β c S)
        (splitSource n G χ c S f) z := by
  simp only [removedSource, MeasurableEquiv.symm_apply_apply]
  rfl

/-- The eliminated mixed fluctuation is zero under the original Wilson
probability. An OS-null interpretation additionally needs reflection and
positive-half support compatibility; those are not premises proved here. -/
theorem removed_product_zero (χ : G → ℂ) (hχ : Continuous χ) (β c : ℝ)
    (S : Finset (Edge (Vertex n)))
    (hS : WilsonIndependentBlocks.Independent n (S.image (WilsonIndependentBlocks.edgeCoord n)))
    (f g : PlaquetteIndex n → ℝ) (hsep : SeparatedOnBlock n S f g) :
    (∫ U, removedSource n G χ β c S f U * removedSource n G χ β c S g U
      ∂wilsonLaw n G χ β c) = 0 := by
  rw [wilson_integral_split n G χ hχ β c S]
  simp only [removedSource_assemble]
  exact GibbsCrossCovariance.removed_product_zero _ _ _ _ _
    (splitAction_continuous n G χ hχ β c S)
    (splitSource_continuous n G χ hχ c S f) (splitSource_continuous n G χ hχ c S g)
    (actual_response_product n G χ hχ β c S hS f g hsep)

end
end UnifiedTheory.Clay.YangMills.WilsonCrossCovariance
