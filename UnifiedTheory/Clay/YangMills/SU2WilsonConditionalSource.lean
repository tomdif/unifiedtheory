/- Exact integration of one link in the actual interacting SU(2) Wilson law.
The six-staple action is derived from the lattice, its exterior constant
cancels from the constructed measure, and the full source expectation is
expressed in the actual one-axis Haar response. No coordinate density or
asymptotic identification is assumed here. -/
import UnifiedTheory.Clay.YangMills.WilsonSingleLinkStaples
import UnifiedTheory.Clay.YangMills.SU2HaarTilt
import UnifiedTheory.Clay.YangMills.GibbsConstantShift
import UnifiedTheory.Clay.YangMills.GibbsMarginalTower

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Clay.YangMills.SU2WilsonConditionalSource
noncomputable section
open MeasureTheory RegulatedGauge PeriodicLattice4 WilsonUniformVariance
open WilsonSingleLinkStaples SU2HaarTilt
open scoped Quaternion RealInnerProductSpace

variable (n : ℕ) [NeZero n] [Fact (1 < n)]

local instance edgeDecidableEq : DecidableEq (Edge (Vertex n)) := Classical.decEq _

/-- The original full action in the actual exterior/link coordinates. -/
def splitAction (x : Vertex n) (μ : Fin 4) (β : ℝ)
    (z : Exterior n Q x μ × Q) : ℝ :=
  orientedWilsonAction (Vertex n) Q character (base n) (loops n) β 2
    (SingleCoordinateProduct.assemble (selectedLink n x μ) z)

def splitSource (x : Vertex n) (μ : Fin 4) (f : PlaquetteIndex n → ℝ)
    (z : Exterior n Q x μ × Q) : ℝ :=
  WilsonBlockIntegration.source n Q character 2 f
    (SingleCoordinateProduct.assemble (selectedLink n x μ) z)

omit [Fact (1 < n)] in
theorem splitAction_continuous (x : Vertex n) (μ : Fin 4) (β : ℝ) :
    Continuous (splitAction n x μ β) :=
  (continuous_orientedWilsonAction (Vertex n) Q character character_continuous
    (base n) (loops n) β 2).comp (SingleCoordinateProduct.assemble_continuous _)

omit [Fact (1 < n)] in
theorem splitSource_continuous (x : Vertex n) (μ : Fin 4) (f : PlaquetteIndex n → ℝ) :
    Continuous (splitSource n x μ f) :=
  (WilsonBlockIntegration.source_continuous n Q character character_continuous 2 f).comp
    (SingleCoordinateProduct.assemble_continuous _)

/-- Normalized conditional law obtained by integrating the original action. -/
def conditionalLaw (x : Vertex n) (μ : Fin 4) (β : ℝ) (r : Exterior n Q x μ) : Measure Q :=
  CompactGibbsContinuity.law haar (fun q => splitAction n x μ β (r, q))

/-- The previous exact Gibbs response operator, applied to the original source. -/
def conditionalSource (x : Vertex n) (μ : Fin 4) (β : ℝ)
    (f : PlaquetteIndex n → ℝ) (r : Exterior n Q x μ) : ℝ :=
  GibbsMarginalTower.response haar (splitAction n x μ β) (splitSource n x μ f) r

omit [Fact (1 < n)] in
theorem conditionalLaw_probability (x : Vertex n) (μ : Fin 4) (β : ℝ)
    (r : Exterior n Q x μ) : IsProbabilityMeasure (conditionalLaw n x μ β r) :=
  CompactGibbsContinuity.law_probability haar _
    ((splitAction_continuous n x μ β).comp (continuous_const.prodMk continuous_id))

/-- An equality of actual measures: the exterior action cancels exactly. -/
theorem conditionalLaw_eq_tiltLaw (x : Vertex n) (μ : Fin 4) (β : ℝ)
    (r : Exterior n Q x μ) :
    conditionalLaw n x μ β r = tiltLaw β (exteriorStaple n x μ r) := by
  have he : (fun q => splitAction n x μ β (r, q)) =
      (fun q : Q => β * exteriorSourceConstant n x μ r (fun _ => 1) +
        (-(2 * β * ⟪(q : ℍ), exteriorStaple n x μ r⟫))) := by
    funext q
    rw [splitAction, action_assemble]
    ring
  unfold conditionalLaw
  rw [he]
  let S : Q → ℝ := fun q => -(2 * β * ⟪(q : ℍ), exteriorStaple n x μ r⟫)
  have hS : Continuous S :=
    (continuous_const.mul (continuous_subtype_val.inner continuous_const)).neg
  rw [GibbsConstantShift.law_const_add haar S hS]
  unfold CompactGibbsContinuity.law tiltLaw tiltWeight
  simp only [S, neg_neg]

omit [Fact (1 < n)] in
theorem conditionalSource_eq_integral (x : Vertex n) (μ : Fin 4) (β : ℝ)
    (f : PlaquetteIndex n → ℝ) (r : Exterior n Q x μ) :
    conditionalSource n x μ β f r =
      ∫ q, splitSource n x μ f (r, q) ∂conditionalLaw n x μ β r :=
  GibbsMarginalTower.response_eq_expectation haar _ _ (splitAction_continuous n x μ β) r

omit [Fact (1 < n)] in
theorem conditionalSource_continuous (x : Vertex n) (μ : Fin 4) (β : ℝ)
    (f : PlaquetteIndex n → ℝ) : Continuous (conditionalSource n x μ β f) :=
  GibbsMarginalTower.response_continuous haar _ _ (splitAction_continuous n x μ β)
    (splitSource_continuous n x μ f)

/-- Exact full weighted source after one conditional integration. -/
theorem conditionalSource_eq_tiltMean (x : Vertex n) (μ : Fin 4) (β : ℝ)
    (f : PlaquetteIndex n → ℝ) (r : Exterior n Q x μ) :
    conditionalSource n x μ β f r = exteriorSourceConstant n x μ r f -
      2 * tiltMean β (exteriorStaple n x μ r) (exteriorWeightedStaple n x μ r f) := by
  rw [conditionalSource_eq_integral, conditionalLaw_eq_tiltLaw]
  have he : (fun q => splitSource n x μ f (r, q)) =
      (fun q : Q => exteriorSourceConstant n x μ r f -
        2 * ⟪(q : ℍ), exteriorWeightedStaple n x μ r f⟫) := by
    funext q
    simpa only [splitSource] using source_assemble n x μ r f q
  rw [he]
  letI := tiltLaw_probability β (exteriorStaple n x μ r)
  have hi : Integrable (fun q : Q => 2 * ⟪(q : ℍ), exteriorWeightedStaple n x μ r f⟫)
      (tiltLaw β (exteriorStaple n x μ r)) :=
    (continuous_const.mul
      (continuous_subtype_val.inner continuous_const)).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)
  rw [integral_sub (integrable_const _) hi, integral_const_mul, tiltLaw_inner_mean]
  simp

/-- The coefficient is the actual one-axis Haar mean, with all lattice
geometry and normalization already identified. -/
theorem conditionalSource_radial (x : Vertex n) (μ : Fin 4) (β : ℝ)
    (f : PlaquetteIndex n → ℝ) (r : Exterior n Q x μ) :
    conditionalSource n x μ β f r = exteriorSourceConstant n x μ r f -
      2 * (axisMean (2 * β * ‖exteriorStaple n x μ r‖) *
        ⟪exteriorStaple n x μ r, exteriorWeightedStaple n x μ r f⟫ /
          ‖exteriorStaple n x μ r‖) := by
  rw [conditionalSource_eq_tiltMean, tiltMean_rotational]

/-- The zero-staple endpoint is exact and uses no division by a vanishing radius. -/
theorem conditionalSource_zero_staple (x : Vertex n) (μ : Fin 4) (β : ℝ)
    (f : PlaquetteIndex n → ℝ) (r : Exterior n Q x μ)
    (hA : exteriorStaple n x μ r = 0) :
    conditionalSource n x μ β f r = exteriorSourceConstant n x μ r f := by
  rw [conditionalSource_eq_tiltMean, hA, tiltMean_zero, mul_zero, sub_zero]

end
end UnifiedTheory.Clay.YangMills.SU2WilsonConditionalSource
