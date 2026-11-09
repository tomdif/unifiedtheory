/- Third and fourth source cumulants under the original Wilson measure.
The exact actual block marginal appears on the right, together with every
conditional-noise cross term. No induced law is replaced by a Wilson ansatz. -/
import UnifiedTheory.Clay.YangMills.GibbsConditionalCumulants
import UnifiedTheory.Clay.YangMills.WilsonCrossCovariance

set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace UnifiedTheory.Clay.YangMills.WilsonConditionalCumulants
noncomputable section
open MeasureTheory RegulatedGauge PeriodicLattice4 WilsonBlockMarginal
open WilsonCrossCovariance GibbsMarginalTower GibbsCrossCovariance GibbsConditionalCumulants

variable (n : ℕ) [NeZero n] (G : Type*) [Group G]
  [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
local instance edgeDecidableEq : DecidableEq (Edge (Vertex n)) := Classical.decEq _

/-- Actual conditional moments of the centered source removed by a chosen Wilson block. -/
def conditionalNoiseMoment (χ : G → ℂ) (β c : ℝ) (S : Finset (Edge (Vertex n)))
    (f : PlaquetteIndex n → ℝ) (k : ℕ) : Outside (G := G) S → ℝ :=
  noiseMoment (insideMeasure S (compactHaar G)) (splitAction n G χ β c S)
    (WilsonSeparatedSources.splitSource n G χ c S f) k

/-- Actual fiber fourth cumulant; its sign is not assumed. -/
def conditionalNoiseFourth (χ : G → ℂ) (β c : ℝ) (S : Finset (Edge (Vertex n)))
    (f : PlaquetteIndex n → ℝ) (r : Outside (G := G) S) : ℝ :=
  conditionalNoiseMoment n G χ β c S f 4 r -
    3 * (conditionalNoiseMoment n G χ β c S f 2 r) ^ 2

theorem conditionalNoiseMoment_continuous (χ : G → ℂ) (hχ : Continuous χ) (β c : ℝ)
    (S : Finset (Edge (Vertex n))) (f : PlaquetteIndex n → ℝ) (k : ℕ) :
    Continuous (conditionalNoiseMoment n G χ β c S f k) :=
  noiseMoment_continuous _ _ _ (splitAction_continuous n G χ hχ β c S)
    (splitSource_continuous n G χ hχ c S f) k

/-- The conditional moment is the power of the literal original-law removed source. -/
theorem conditionalNoiseMoment_eq_response (χ : G → ℂ) (hχ : Continuous χ) (β c : ℝ)
    (S : Finset (Edge (Vertex n))) (f : PlaquetteIndex n → ℝ) (k : ℕ)
    (r : Outside (G := G) S) :
    conditionalNoiseMoment n G χ β c S f k r =
      ∫ v, (removedSource n G χ β c S f (assemble S (r, v))) ^ k
        ∂CompactGibbsContinuity.law (insideMeasure S (compactHaar G))
          (fun v => splitAction n G χ β c S (r, v)) := by
  simp_rw [removedSource_assemble]
  exact response_eq_expectation (insideMeasure S (compactHaar G))
    (splitAction n G χ β c S)
    (fun z => (removed (insideMeasure S (compactHaar G)) (splitAction n G χ β c S)
      (WilsonSeparatedSources.splitSource n G χ c S f) z) ^ k)
    (splitAction_continuous n G χ hχ β c S) r

/-- Exact centered moments transport from the original Wilson coordinates. -/
theorem centeredMoment_split (χ : G → ℂ) (hχ : Continuous χ) (β c : ℝ)
    (S : Finset (Edge (Vertex n))) (f : PlaquetteIndex n → ℝ) (k : ℕ) :
    centeredMoment (wilsonLaw n G χ β c) (WilsonBlockIntegration.source n G χ c f) k =
      centeredMoment (CompactGibbsContinuity.law
        ((outsideMeasure S (compactHaar G)).prod (insideMeasure S (compactHaar G)))
        (splitAction n G χ β c S)) (WilsonSeparatedSources.splitSource n G χ c S f) k := by
  unfold centeredMoment
  rw [wilson_integral_split n G χ hχ β c S,
    wilson_integral_split n G χ hχ β c S]
  rfl

/-- The actual third cumulant contains a retained-mean/conditional-variance correlation. -/
theorem source_cumulant_three (χ : G → ℂ) (hχ : Continuous χ) (β c : ℝ)
    (S : Finset (Edge (Vertex n))) (f : PlaquetteIndex n → ℝ) :
    cumulantThree (wilsonLaw n G χ β c) (WilsonBlockIntegration.source n G χ c f) =
      cumulantThree (retainedLaw n G χ β c S) (retainedSource n G χ β c S f) +
      (∫ r, conditionalNoiseMoment n G χ β c S f 3 r ∂retainedLaw n G χ β c S) +
      3 * covariance (retainedLaw n G χ β c S) (retainedSource n G χ β c S f)
        (conditionalNoiseMoment n G χ β c S f 2) := by
  unfold cumulantThree
  rw [centeredMoment_split n G χ hχ β c S f 3]
  exact cumulant_three_decomposition _ _ _ _
    (splitAction_continuous n G χ hχ β c S) (splitSource_continuous n G χ hχ c S f)

/-- The actual fourth cumulant keeps conditional skewness, variance fluctuations,
and centered retained-square/conditional-variance correlations. -/
theorem source_cumulant_four (χ : G → ℂ) (hχ : Continuous χ) (β c : ℝ)
    (S : Finset (Edge (Vertex n))) (f : PlaquetteIndex n → ℝ) :
    cumulantFour (wilsonLaw n G χ β c) (WilsonBlockIntegration.source n G χ c f) =
      cumulantFour (retainedLaw n G χ β c S) (retainedSource n G χ β c S f) +
      (∫ r, conditionalNoiseFourth n G χ β c S f r ∂retainedLaw n G χ β c S) +
      4 * covariance (retainedLaw n G χ β c S) (retainedSource n G χ β c S f)
        (conditionalNoiseMoment n G χ β c S f 3) +
      3 * covariance (retainedLaw n G χ β c S) (conditionalNoiseMoment n G χ β c S f 2)
        (conditionalNoiseMoment n G χ β c S f 2) +
      6 * covariance (retainedLaw n G χ β c S)
        (fun r => (retainedSource n G χ β c S f r -
          ∫ b, retainedSource n G χ β c S f b ∂retainedLaw n G χ β c S) ^ 2)
        (conditionalNoiseMoment n G χ β c S f 2) := by
  unfold cumulantFour
  rw [centeredMoment_split n G χ hχ β c S f 4,
    centeredMoment_split n G χ hχ β c S f 2]
  exact cumulant_four_decomposition _ _ _ _
    (splitAction_continuous n G χ hχ β c S) (splitSource_continuous n G χ hχ c S f)

end
end UnifiedTheory.Clay.YangMills.WilsonConditionalCumulants
