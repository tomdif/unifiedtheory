/- A continuous polynomial approximation of the actual one-link Wilson
response. Every analytic error theorem in this module explicitly requires
the first-coordinate Haar integration formula. The low-staple sector is
retained exactly, and denominators are clipped below the cutoff so the
approximation is continuous on the full exterior configuration space. -/
import UnifiedTheory.Clay.YangMills.SU2WilsonConditionalSource
import UnifiedTheory.Clay.YangMills.SU2HaarScalarBridge
import UnifiedTheory.Clay.YangMills.CouplingTrajectoryRobustness

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Clay.YangMills.SU2WilsonSourceApproximation
noncomputable section
open MeasureTheory RegulatedGauge PeriodicLattice4 WilsonUniformVariance
open WilsonSingleLinkStaples SU2WilsonConditionalSource SU2HaarScalarBridge
open scoped Quaternion RealInnerProductSpace

variable (n : ℕ) [NeZero n] [Fact (1 < n)]

def radius (x : Vertex n) (μ : Fin 4) (r : Exterior n Q x μ) : ℝ :=
  ‖exteriorStaple n x μ r‖

def safeRadius (x : Vertex n) (μ : Fin 4) (r₀ : ℝ) (r : Exterior n Q x μ) : ℝ :=
  max r₀ (radius n x μ r)

/-- A globally defined continuous extension of the good-region polynomial. -/
def approximation (x : Vertex n) (μ : Fin 4) (β r₀ : ℝ)
    (f : PlaquetteIndex n → ℝ) (r : Exterior n Q x μ) : ℝ :=
  let ρ := safeRadius n x μ r₀ r
  let pair := ⟪exteriorStaple n x μ r, exteriorWeightedStaple n x μ r f⟫
  exteriorSourceConstant n x μ r f - 2 * pair / ρ + pair / (β * ρ^2) *
    SU2QuotientRemainder.sourceTruncation ⌊4 * β * r₀⌋₊ (2 * β * ρ)

def hybridSource (x : Vertex n) (μ : Fin 4) (β r₀ r₁ : ℝ)
    (f : PlaquetteIndex n → ℝ) (r : Exterior n Q x μ) : ℝ :=
  HybridSourceApproximation.hybrid r₀ r₁ (radius n x μ r)
    (conditionalSource n x μ β f r) (approximation n x μ β r₀ f r)

def errorEnvelope (x : Vertex n) (μ : Fin 4) (β r₀ : ℝ)
    (f : PlaquetteIndex n → ℝ) : ℝ :=
  1280 * Real.exp 2 * r₀^2 * β^2 * Real.exp (-4 * β * r₀) *
    ∑ p ∈ SingleLinkWilsonOscillation.affected n x μ, |f p|

omit [NeZero n] [Fact (1 < n)] in
theorem errorEnvelope_nonneg (x : Vertex n) (μ : Fin 4) (β r₀ : ℝ)
    (f : PlaquetteIndex n → ℝ) : 0 ≤ errorEnvelope n x μ β r₀ f := by
  unfold errorEnvelope
  positivity

omit [Fact (1 < n)] in
theorem radius_continuous (x : Vertex n) (μ : Fin 4) : Continuous (radius n x μ) :=
  (exteriorStaple_continuous n x μ).norm

omit [Fact (1 < n)] in
theorem safeRadius_continuous (x : Vertex n) (μ : Fin 4) (r₀ : ℝ) :
    Continuous (safeRadius n x μ r₀) :=
  continuous_const.max (radius_continuous n x μ)

omit [NeZero n] [Fact (1 < n)] in
theorem safeRadius_pos (x : Vertex n) (μ : Fin 4) (r₀ : ℝ) (hr₀ : 0 < r₀)
    (r : Exterior n Q x μ) : 0 < safeRadius n x μ r₀ r :=
  hr₀.trans_le (le_max_left _ _)

theorem sourceConstant_continuous (x : Vertex n) (μ : Fin 4) (f : PlaquetteIndex n → ℝ) :
    Continuous (fun r => exteriorSourceConstant n x μ r f) := by
  have he : (fun r => exteriorSourceConstant n x μ r f) =
      (fun r => splitSource n x μ f (r, 1) +
        2 * ⟪(1 : ℍ), exteriorWeightedStaple n x μ r f⟫) := by
    funext r
    have h := source_assemble n x μ r f 1
    change splitSource n x μ f (r, 1) = exteriorSourceConstant n x μ r f -
      2 * ⟪(1 : ℍ), exteriorWeightedStaple n x μ r f⟫ at h
    linarith
  rw [he]
  exact ((splitSource_continuous n x μ f).comp
    (continuous_id.prodMk continuous_const)).add
      (continuous_const.mul (continuous_const.inner (exteriorWeightedStaple_continuous n x μ f)))

theorem approximation_continuous (x : Vertex n) (μ : Fin 4) (β r₀ : ℝ)
    (hβ : 0 < β) (hr₀ : 0 < r₀) (f : PlaquetteIndex n → ℝ) :
    Continuous (approximation n x μ β r₀ f) := by
  have hρ := safeRadius_continuous n x μ r₀
  have hρp := safeRadius_pos n x μ r₀ hr₀
  have hp : Continuous (fun r =>
      ⟪exteriorStaple n x μ r, exteriorWeightedStaple n x μ r f⟫) :=
    (exteriorStaple_continuous n x μ).inner (exteriorWeightedStaple_continuous n x μ f)
  have hκ : Continuous (fun r => 2 * β * safeRadius n x μ r₀ r) := continuous_const.mul hρ
  have hκp (r : Exterior n Q x μ) : 0 < 2 * β * safeRadius n x μ r₀ r := by
    exact mul_pos (mul_pos (by norm_num) hβ) (hρp r)
  have hs : Continuous (fun r => SU2QuotientRemainder.sourceTruncation
      ⌊4 * β * r₀⌋₊ (2 * β * safeRadius n x μ r₀ r)) := by
    unfold SU2QuotientRemainder.sourceTruncation
    apply continuous_finset_sum
    intro i _
    exact continuous_const.div (hκ.pow i) (fun r => (pow_pos (hκp r) i).ne')
  exact ((sourceConstant_continuous n x μ f).sub
    ((continuous_const.mul hp).div hρ (fun r => (hρp r).ne'))).add
      ((hp.div (continuous_const.mul (hρ.pow 2))
        (fun r => (mul_pos hβ (pow_pos (hρp r) 2)).ne')).mul hs)

theorem hybridSource_continuous (x : Vertex n) (μ : Fin 4) (β r₀ r₁ : ℝ)
    (hβ : 0 < β) (hr₀ : 0 < r₀) (f : PlaquetteIndex n → ℝ) :
    Continuous (hybridSource n x μ β r₀ r₁ f) :=
  HybridSourceApproximation.hybrid_continuous r₀ r₁ _ _ _
    (radius_continuous n x μ) (conditionalSource_continuous n x μ β f)
    (approximation_continuous n x μ β r₀ hβ hr₀ f)

omit [Fact (1 < n)] in
theorem approximation_eq_good (x : Vertex n) (μ : Fin 4) (β r₀ : ℝ)
    (f : PlaquetteIndex n → ℝ) (r : Exterior n Q x μ) (hr : r₀ ≤ radius n x μ r) :
    approximation n x μ β r₀ f r =
      affineApproximation β (exteriorSourceConstant n x μ r f)
        (exteriorStaple n x μ r) (exteriorWeightedStaple n x μ r f) ⌊4 * β * r₀⌋₊ := by
  have hr' : r₀ ≤ ‖exteriorStaple n x μ r‖ := hr
  simp only [approximation, safeRadius, radius, affineApproximation, max_eq_right hr']

/-- The only extra analytic input is the explicit first-coordinate Haar formula. -/
theorem good_region_error (hcoord : FirstCoordinateFormula)
    (x : Vertex n) (μ : Fin 4) (β r₀ : ℝ) (hr₀ : 0 < r₀) (hβr : 3 / 4 ≤ β * r₀)
    (f : PlaquetteIndex n → ℝ) (r : Exterior n Q x μ) (hr : r₀ ≤ radius n x μ r) :
    |conditionalSource n x μ β f r - approximation n x μ β r₀ f r| ≤
      errorEnvelope n x μ β r₀ f := by
  rw [approximation_eq_good n x μ β r₀ f r hr, conditionalSource_eq_tiltMean]
  apply (affine_error_bound_quadratic hcoord β (exteriorSourceConstant n x μ r f)
    r₀ hr₀ hβr (exteriorStaple n x μ r) (exteriorWeightedStaple n x μ r f) hr).trans
  exact mul_le_mul_of_nonneg_left (exteriorWeightedStaple_norm_le n x μ r f) (by positivity)

omit [Fact (1 < n)] in
/-- Below the cutoff the entire actual conditional response is retained. -/
theorem hybridSource_exact (x : Vertex n) (μ : Fin 4) (β r₀ r₁ : ℝ)
    (hcut : r₀ < r₁) (f : PlaquetteIndex n → ℝ) (r : Exterior n Q x μ)
    (hr : radius n x μ r ≤ r₀) :
    hybridSource n x μ β r₀ r₁ f r = conditionalSource n x μ β f r :=
  HybridSourceApproximation.hybrid_eq_exact r₀ r₁ _ hcut hr _ _

/-- The geometric density input supplies the former good-region hypothesis
for this actual single-link Wilson response, uniformly over the exterior. -/
theorem hybrid_error_bound (hcoord : FirstCoordinateFormula)
    (x : Vertex n) (μ : Fin 4) (β r₀ r₁ : ℝ) (hr₀ : 0 < r₀) (hcut : r₀ < r₁)
    (hβr : 3 / 4 ≤ β * r₀) (f : PlaquetteIndex n → ℝ) (r : Exterior n Q x μ) :
    |conditionalSource n x μ β f r - hybridSource n x μ β r₀ r₁ f r| ≤
      errorEnvelope n x μ β r₀ f := by
  simpa only [Real.norm_eq_abs] using HybridSourceApproximation.hybrid_error_le
    r₀ r₁ (radius n x μ r) (errorEnvelope n x μ β r₀ f) hcut
    (errorEnvelope_nonneg n x μ β r₀ f) (conditionalSource n x μ β f r)
    (approximation n x μ β r₀ f r) (good_region_error n hcoord x μ β r₀ hr₀ hβr f r)

/-- The retained law is the actual pushforward of the full interacting Gibbs measure. -/
def retainedLaw (x : Vertex n) (μ : Fin 4) (β : ℝ) : Measure (Exterior n Q x μ) :=
  GibbsMarginalTower.marginal (exteriorMeasure n Q x μ) SU2HaarTilt.haar (splitAction n x μ β)

omit [Fact (1 < n)] in
theorem retainedLaw_probability (x : Vertex n) (μ : Fin 4) (β : ℝ) :
    IsProbabilityMeasure (retainedLaw n x μ β) :=
  GibbsMarginalTower.marginal_probability _ _ _ (splitAction_continuous n x μ β)

/-- Mean-square control under the actual correlated exterior law. -/
theorem retained_error_l2_bound (hcoord : FirstCoordinateFormula)
    (x : Vertex n) (μ : Fin 4) (β r₀ r₁ : ℝ) (hβ : 0 < β)
    (hr₀ : 0 < r₀) (hcut : r₀ < r₁) (hβr : 3 / 4 ≤ β * r₀)
    (f : PlaquetteIndex n → ℝ) :
    (∫ r, (conditionalSource n x μ β f r - hybridSource n x μ β r₀ r₁ f r)^2
      ∂retainedLaw n x μ β) ≤ (errorEnvelope n x μ β r₀ f)^2 := by
  letI := retainedLaw_probability n x μ β
  have hi := (((conditionalSource_continuous n x μ β f).sub
    (hybridSource_continuous n x μ β r₀ r₁ hβ hr₀ f)).pow 2).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _) (μ := retainedLaw n x μ β)
  calc
    _ ≤ ∫ _r, (errorEnvelope n x μ β r₀ f)^2 ∂retainedLaw n x μ β := by
      apply integral_mono hi (integrable_const _)
      intro r
      have h := hybrid_error_bound n hcoord x μ β r₀ r₁ hr₀ hcut hβr f r
      simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _)
        (errorEnvelope_nonneg n x μ β r₀ f)).2 h
    _ = _ := by simp

end
end UnifiedTheory.Clay.YangMills.SU2WilsonSourceApproximation
