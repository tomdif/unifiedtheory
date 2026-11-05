/- The actual retained one-link law is the exterior projection of the full
interacting Wilson probability. The transport is unconditional: it uses the
proved finite-product Haar split and the original Wilson density. Only the
approximation-error corollary needs the separate first-coordinate formula. -/
import UnifiedTheory.Clay.YangMills.SU2WilsonSourceApproximation
import UnifiedTheory.Clay.YangMills.WilsonBlockMarginal

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Clay.YangMills.SU2WilsonMarginalTransport
noncomputable section
open MeasureTheory RegulatedGauge PeriodicLattice4 WilsonUniformVariance
open WilsonSingleLinkStaples SU2WilsonConditionalSource SU2WilsonSourceApproximation

variable (n : ℕ) [NeZero n]

local instance : DecidableEq (Edge (Vertex n)) := Classical.decEq _

/-- The actual exterior coordinates of the original lattice configuration. -/
def exteriorProjection (x : Vertex n) (μ : Fin 4)
    (U : Configuration (Vertex n) Q) : Exterior n Q x μ :=
  fun e => U e.val

omit [NeZero n] in
theorem exteriorProjection_continuous (x : Vertex n) (μ : Fin 4) :
    Continuous (exteriorProjection n x μ) := by
  exact continuous_pi (fun e => continuous_apply e.val)

@[simp] theorem exteriorProjection_assemble (x : Vertex n) (μ : Fin 4)
    (z : Exterior n Q x μ × Q) :
    exteriorProjection n x μ (SingleCoordinateProduct.assemble (selectedLink n x μ) z) = z.1 := by
  funext e
  exact SingleCoordinateProduct.assemble_other _ _ e.property z

theorem exteriorProjection_eq_fst_symm (x : Vertex n) (μ : Fin 4)
    (U : Configuration (Vertex n) Q) :
    exteriorProjection n x μ U =
      ((SingleCoordinateProduct.assemble (G := Q) (selectedLink n x μ)).symm U).1 := by
  have h := exteriorProjection_assemble n x μ
    ((SingleCoordinateProduct.assemble (G := Q) (selectedLink n x μ)).symm U)
  simpa only [MeasurableEquiv.apply_symm_apply] using h

/-- Exact transport of the full Wilson probability to exterior/link coordinates. -/
theorem wilson_coordinates_preserving (x : Vertex n) (μ : Fin 4) (β : ℝ) :
    MeasurePreserving (SingleCoordinateProduct.assemble (G := Q) (selectedLink n x μ)).symm
      (wilsonLaw n Q character β 2)
      (CompactGibbsContinuity.law ((exteriorMeasure n Q x μ).prod SU2HaarTilt.haar)
        (splitAction n x μ β)) := by
  have h := WilsonBlockMarginal.weightedLaw_preserving _ _
    (SingleCoordinateProduct.assemble (G := Q) (selectedLink n x μ))
    (SingleCoordinateProduct.assemble_preserving (selectedLink n x μ) (compactHaar Q))
    (fun U => Real.exp (-orientedWilsonAction (Vertex n) Q character
      (base n) (loops n) β 2 U))
    (Real.continuous_exp.comp
      (continuous_orientedWilsonAction _ Q character character_continuous
        (base n) (loops n) β 2).neg).measurable
  have hg := GibbsCoordinateTransport.gibbs_eq_weightedLaw (Vertex n) Q
    (orientedWilsonAction (Vertex n) Q character (base n) (loops n) β 2)
    (continuous_orientedWilsonAction _ Q character character_continuous
      (base n) (loops n) β 2)
  change wilsonLaw n Q character β 2 = LocalGibbsComparison.weightedLaw
    (Measure.pi (fun _ : Edge (Vertex n) => compactHaar Q))
    (fun U => Real.exp (-orientedWilsonAction (Vertex n) Q character
      (base n) (loops n) β 2 U)) at hg
  rw [← hg] at h
  exact h.symm (SingleCoordinateProduct.assemble (selectedLink n x μ))

/-- Equality of measures, so the identification also holds for retained events. -/
theorem retainedLaw_eq_map (x : Vertex n) (μ : Fin 4) (β : ℝ) :
    retainedLaw n x μ β =
      (wilsonLaw n Q character β 2).map (exteriorProjection n x μ) := by
  unfold retainedLaw GibbsMarginalTower.marginal
  rw [← (wilson_coordinates_preserving n x μ β).map_eq,
    Measure.map_map measurable_fst (SingleCoordinateProduct.assemble _).symm.measurable]
  congr 1

/-- Every continuous retained test is integrated against the original Wilson law. -/
theorem retained_integral_eq_wilson (x : Vertex n) (μ : Fin 4) (β : ℝ)
    (F : Exterior n Q x μ → ℝ) (hF : Continuous F) :
    (∫ r, F r ∂retainedLaw n x μ β) =
      ∫ U, F (exteriorProjection n x μ U) ∂wilsonLaw n Q character β 2 := by
  rw [retainedLaw_eq_map,
    integral_map (exteriorProjection_continuous n x μ).measurable.aemeasurable
      hF.aestronglyMeasurable]

variable [Fact (1 < n)]

/-- The actual source approximation error under the original interacting law.
This is a marginal approximation estimate, not a bound on the removed fluctuation. -/
theorem wilson_error_l2_bound (hcoord : SU2HaarScalarBridge.FirstCoordinateFormula)
    (x : Vertex n) (μ : Fin 4) (β r₀ r₁ : ℝ) (hβ : 0 < β)
    (hr₀ : 0 < r₀) (hcut : r₀ < r₁) (hβr : 3 / 4 ≤ β * r₀)
    (f : PlaquetteIndex n → ℝ) :
    (∫ U, (conditionalSource n x μ β f (exteriorProjection n x μ U) -
      hybridSource n x μ β r₀ r₁ f (exteriorProjection n x μ U))^2
        ∂wilsonLaw n Q character β 2) ≤ (errorEnvelope n x μ β r₀ f)^2 := by
  rw [← retained_integral_eq_wilson n x μ β
    (fun r => (conditionalSource n x μ β f r - hybridSource n x μ β r₀ r₁ f r)^2)
    (((conditionalSource_continuous n x μ β f).sub
      (hybridSource_continuous n x μ β r₀ r₁ hβ hr₀ f)).pow 2)]
  exact retained_error_l2_bound n hcoord x μ β r₀ r₁ hβ hr₀ hcut hβr f

end
end UnifiedTheory.Clay.YangMills.SU2WilsonMarginalTransport
