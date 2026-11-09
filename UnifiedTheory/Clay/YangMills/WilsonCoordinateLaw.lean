/- The positive-link coordinate Gibbs law is exactly the original Wilson law.
This is a measurable equivalence preserving the actual product Haar reference
and normalized interacting density, not a replacement auxiliary model. -/
import UnifiedTheory.Clay.YangMills.WilsonParallelKernel
import UnifiedTheory.Clay.YangMills.WilsonBlockMarginal

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Clay.YangMills.WilsonCoordinateLaw
noncomputable section
open MeasureTheory RegulatedGauge PeriodicLattice4 WilsonUniformVariance
open WilsonIndependentBlocks WilsonSingleLinkStaples WilsonCoordinateInfluence

variable (n : ℕ)

/-- The actual positive edge and its base/direction coordinate are inverse descriptions. -/
def linkEquiv : Link n ≃ Edge (Vertex n) where
  toFun a := selectedLink n a.1 a.2
  invFun := edgeCoord n
  left_inv := edgeCoord_selected n
  right_inv := selected_edgeCoord n

/-- Measurable coordinate reindexing of the entire original configuration. -/
def configEquiv : (Link n → Q) ≃ᵐ Configuration (Vertex n) Q :=
  MeasurableEquiv.piCongrLeft (fun _ : Edge (Vertex n) => Q) (linkEquiv n)

@[simp] theorem configEquiv_selected (U : Link n → Q) (a : Link n) :
    configEquiv n U (selectedLink n a.1 a.2) = U a :=
  MeasurableEquiv.piCongrLeft_apply_apply (β := fun _ : Edge (Vertex n) => Q) (linkEquiv n) U a

/-- The equivalence is literally the coordinate map used in the conditional kernels. -/
theorem configEquiv_apply (U : Link n → Q) (e : Edge (Vertex n)) :
    configEquiv n U e = U (edgeCoord n e) := by
  have h := configEquiv_selected n U (edgeCoord n e)
  simpa only [selected_edgeCoord] using h

theorem configEquiv_eq_toConfiguration : (configEquiv n : (Link n → Q) →
    Configuration (Vertex n) Q) = toConfiguration n := by
  funext U e
  exact configEquiv_apply n U e

@[simp] theorem configEquiv_symm_apply (U : Configuration (Vertex n) Q) (a : Link n) :
    (configEquiv n).symm U a = U (selectedLink n a.1 a.2) := by
  have h := configEquiv_selected n ((configEquiv n).symm U) a
  simpa only [MeasurableEquiv.apply_symm_apply] using h.symm

theorem configEquiv_continuous : Continuous (configEquiv n) := by
  rw [configEquiv_eq_toConfiguration]
  exact continuous_pi (fun e => continuous_apply (edgeCoord n e))

theorem configEquiv_symm_continuous : Continuous (configEquiv n).symm := by
  apply continuous_pi
  intro a
  simpa only [configEquiv_symm_apply] using
    (continuous_apply (selectedLink n a.1 a.2) :
      Continuous (fun U : Configuration (Vertex n) Q => U (selectedLink n a.1 a.2)))

variable [NeZero n]

/-- The coordinate reference law is transported to the original positive-edge product Haar. -/
theorem reference_preserving :
    MeasurePreserving (configEquiv n) (Measure.pi (fun _ : Link n => compactHaar Q))
      (referenceMeasure Q (Vertex n)) :=
  measurePreserving_piCongrLeft (fun _ : Edge (Vertex n) => compactHaar Q) (linkEquiv n)

/-- Exact normalized Gibbs transport, including the partition normalization. -/
theorem gibbs_preserving (S : Configuration (Vertex n) Q → ℝ) (hS : Continuous S) :
    MeasurePreserving (configEquiv n)
      (CompactGibbsContinuity.law (Measure.pi (fun _ : Link n => compactHaar Q))
        (fun U => S (toConfiguration n U)))
      (gibbsMeasure (Vertex n) Q S) := by
  rw [GibbsCoordinateTransport.gibbs_eq_weightedLaw (Vertex n) Q S hS]
  have h := WilsonBlockMarginal.weightedLaw_preserving _ _ (configEquiv n)
    (reference_preserving n) (fun U => Real.exp (-S U))
    (Real.continuous_exp.comp hS.neg).measurable
  simpa only [configEquiv_eq_toConfiguration, CompactGibbsContinuity.law,
    Function.comp_apply] using h

/-- The literal full Wilson action gives the original interacting Wilson probability. -/
theorem wilson_preserving (β : ℝ) :
    MeasurePreserving (configEquiv n)
      (CompactGibbsContinuity.law (Measure.pi (fun _ : Link n => compactHaar Q))
        (WilsonParallelKernel.stateAction n β))
      (wilsonLaw n Q character β 2) :=
  gibbs_preserving n (WilsonBlockIntegration.action n Q character β 2)
    (continuous_orientedWilsonAction (Vertex n) Q character character_continuous
      (base n) (loops n) β 2)

/-- Equality of measures, valid for every event as well as continuous observables. -/
theorem map_coordinate_wilson (β : ℝ) :
    (CompactGibbsContinuity.law (Measure.pi (fun _ : Link n => compactHaar Q))
      (WilsonParallelKernel.stateAction n β)).map
      (toConfiguration n) = wilsonLaw n Q character β 2 := by
  simpa only [configEquiv_eq_toConfiguration] using (wilson_preserving n β).map_eq

/-- The inverse coordinate projection also transports the full original probability exactly. -/
theorem map_wilson_coordinates (β : ℝ) :
    (wilsonLaw n Q character β 2).map (configEquiv n).symm =
      CompactGibbsContinuity.law (Measure.pi (fun _ : Link n => compactHaar Q))
        (WilsonParallelKernel.stateAction n β) :=
  ((wilson_preserving n β).symm (configEquiv n)).map_eq

/-- Every real test integral agrees with the integral under the original Wilson law. -/
theorem coordinate_integral (β : ℝ) (F : Configuration (Vertex n) Q → ℝ) :
    (∫ U, F (toConfiguration n U)
      ∂CompactGibbsContinuity.law (Measure.pi (fun _ : Link n => compactHaar Q))
        (WilsonParallelKernel.stateAction n β)) =
      ∫ U, F U ∂wilsonLaw n Q character β 2 := by
  have h := (wilson_preserving n β).integral_comp (configEquiv n).measurableEmbedding F
  simpa only [configEquiv_eq_toConfiguration] using h

end
end UnifiedTheory.Clay.YangMills.WilsonCoordinateLaw
