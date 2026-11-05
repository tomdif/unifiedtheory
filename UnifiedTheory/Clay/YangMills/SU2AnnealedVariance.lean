/-
Annealed variance of the actual weighted one-link Wilson source.
The radial contribution is controlled on all exteriors. Only the coefficient
variation is charged to the actual small-staple event. Its probability is
bounded by the proved Wilson free-energy estimate, without an assumed
marginal concentration bound or replacement probability law.

These are unscaled finite-cutoff estimates. They do not assert control of a
renormalized continuum source or contraction after further interacting steps.
-/
import UnifiedTheory.Clay.YangMills.SU2StarEnergy
import UnifiedTheory.Clay.YangMills.SU2WeightedRadial
import UnifiedTheory.Clay.YangMills.WilsonBadStapleProbability

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Clay.YangMills.SU2AnnealedVariance
noncomputable section
open MeasureTheory RegulatedGauge PeriodicLattice4 WilsonUniformVariance
open WilsonSingleLinkStaples SingleLinkWilsonOscillation SU2HaarTilt
open SU2InducedAction SU2HaarCovariance SU2WeightedRadial
open scoped Quaternion RealInnerProductSpace

/-- The radial bound persists without a good-staple restriction. -/
theorem radial_remainder_all_covariance (β c : ℝ) (A D : ℍ) (hβ : 0 < β) :
    covariance β A (c • A + D) (c • A + D) ≤
      15 * c ^ 2 / (8 * β ^ 2) + 2 * ‖D‖ ^ 2 := by
  have h := covariance_add_le β A (c • A) D
  rw [covariance_smul] at h
  have hr := mul_le_mul_of_nonneg_left (covariance_radial_le_all β A hβ)
    (show 0 ≤ 2 * c ^ 2 by positivity)
  have hd := covariance_self_le β A D
  calc
    _ ≤ 2 * (c ^ 2 * covariance β A A A) + 2 * covariance β A D D := h
    _ ≤ 2 * c ^ 2 * (15 / (16 * β ^ 2)) + 2 * ‖D‖ ^ 2 := by nlinarith
    _ = _ := by ring

variable (n : ℕ) [NeZero n] [Fact (1 < n)]

local instance edgeDecidableEq : DecidableEq (Edge (Vertex n)) := Classical.decEq _

/-- Variation of the six actual plaquette source coefficients around c. -/
def weightVariation (x : Vertex n) (μ : Fin 4) (f : PlaquetteIndex n → ℝ) (c : ℝ) : ℝ :=
  ∑ p ∈ affected n x μ, |f p - c|

/-- The actual normalized full-source conditional variance. -/
def fiberVariance (x : Vertex n) (μ : Fin 4) (β : ℝ) (f : PlaquetteIndex n → ℝ)
    (r : Exterior n Q x μ) : ℝ :=
  ∫ q : Q, (SU2WilsonConditionalSource.splitSource n x μ f (r, q) -
    SU2WilsonConditionalSource.conditionalSource n x μ β f r) ^ 2
    ∂SU2WilsonConditionalSource.conditionalLaw n x μ β r

/-- This observable is evaluated on the original full Wilson configuration. -/
def originalVariance (x : Vertex n) (μ : Fin 4) (β : ℝ) (f : PlaquetteIndex n → ℝ)
    (U : Configuration (Vertex n) Q) : ℝ :=
  fiberVariance n x μ β f (SU2StarEnergy.exterior n x μ U)

omit [NeZero n] [Fact (1 < n)] in
theorem weightVariation_nonneg (x : Vertex n) (μ : Fin 4)
    (f : PlaquetteIndex n → ℝ) (c : ℝ) : 0 ≤ weightVariation n x μ f c :=
  Finset.sum_nonneg (fun _ _ => abs_nonneg _)

omit [Fact (1 < n)] in
theorem fiberVariance_eq_moments (x : Vertex n) (μ : Fin 4) (β : ℝ)
    (f : PlaquetteIndex n → ℝ) (r : Exterior n Q x μ) :
    fiberVariance n x μ β f r =
      GibbsMarginalTower.response haar (SU2WilsonConditionalSource.splitAction n x μ β)
        (fun z => (SU2WilsonConditionalSource.splitSource n x μ f z) ^ 2) r -
          (SU2WilsonConditionalSource.conditionalSource n x μ β f r) ^ 2 := by
  have h := GibbsMarginalTower.response_variance_identity haar
    (SU2WilsonConditionalSource.splitAction n x μ β)
    (SU2WilsonConditionalSource.splitSource n x μ f)
    (SU2WilsonConditionalSource.splitAction_continuous n x μ β)
    (SU2WilsonConditionalSource.splitSource_continuous n x μ f) r
  rw [GibbsMarginalTower.response_eq_expectation haar _ _
    (SU2WilsonConditionalSource.splitAction_continuous n x μ β) r] at h
  exact h

omit [Fact (1 < n)] in
theorem fiberVariance_continuous (x : Vertex n) (μ : Fin 4) (β : ℝ)
    (f : PlaquetteIndex n → ℝ) : Continuous (fiberVariance n x μ β f) := by
  have he := funext (fiberVariance_eq_moments n x μ β f)
  rw [he]
  exact (GibbsMarginalTower.response_continuous haar _ _
    (SU2WilsonConditionalSource.splitAction_continuous n x μ β)
    ((SU2WilsonConditionalSource.splitSource_continuous n x μ f).pow 2)).sub
      ((SU2WilsonConditionalSource.conditionalSource_continuous n x μ β f).pow 2)

omit [Fact (1 < n)] in
theorem originalVariance_continuous (x : Vertex n) (μ : Fin 4) (β : ℝ)
    (f : PlaquetteIndex n → ℝ) : Continuous (originalVariance n x μ β f) :=
  (fiberVariance_continuous n x μ β f).comp (SU2StarEnergy.exterior_continuous n x μ)

omit [Fact (1 < n)] in
theorem originalVariance_nonneg (x : Vertex n) (μ : Fin 4) (β : ℝ)
    (f : PlaquetteIndex n → ℝ) (U : Configuration (Vertex n) Q) :
    0 ≤ originalVariance n x μ β f U := integral_nonneg (fun _ => sq_nonneg _)

/-- No small-staple probability is charged to the radial term. -/
theorem fiberVariance_all_bound (x : Vertex n) (μ : Fin 4) (β c : ℝ)
    (f : PlaquetteIndex n → ℝ) (r : Exterior n Q x μ) (hβ : 0 < β) :
    fiberVariance n x μ β f r ≤
      15 * c ^ 2 / (2 * β ^ 2) + 8 * (weightVariation n x μ f c) ^ 2 := by
  unfold fiberVariance
  rw [conditional_source_variance, exteriorWeightedStaple_decomposition n x μ r f c]
  let A := exteriorStaple n x μ r
  let D := exteriorWeightedStaple n x μ r (fun p => f p - c)
  have hsq : ‖D‖ ^ 2 ≤ (weightVariation n x μ f c) ^ 2 :=
    (sq_le_sq₀ (norm_nonneg D) (weightVariation_nonneg n x μ f c)).mpr
      (exterior_remainder_norm n x μ r f c)
  have h := mul_le_mul_of_nonneg_left (radial_remainder_all_covariance β c A D hβ)
    (show (0 : ℝ) ≤ 4 by norm_num)
  calc
    _ ≤ 4 * (15 * c ^ 2 / (8 * β ^ 2) + 2 * ‖D‖ ^ 2) := h
    _ = 15 * c ^ 2 / (2 * β ^ 2) + 8 * ‖D‖ ^ 2 := by ring
    _ ≤ 15 * c ^ 2 / (2 * β ^ 2) + 8 * (weightVariation n x μ f c) ^ 2 := by
      linarith

/-- Only the coefficient-variation remainder carries the bad-event indicator. -/
theorem originalVariance_indicator_bound (x : Vertex n) (μ : Fin 4) (β c r₀ : ℝ)
    (f : PlaquetteIndex n → ℝ) (hβ : 0 < β) (hr₀ : 0 < r₀)
    (U : Configuration (Vertex n) Q) :
    originalVariance n x μ β f U ≤
      15 * c ^ 2 / (2 * β ^ 2) +
        12 / (β * r₀) * (weightVariation n x μ f c) ^ 2 +
          (SU2StarEnergy.badEvent n x μ r₀).indicator
            (fun _ => 8 * (weightVariation n x μ f c) ^ 2) U := by
  classical
  by_cases hU : U ∈ SU2StarEnergy.badEvent n x μ r₀
  · rw [Set.indicator_of_mem hU]
    have h := fiberVariance_all_bound n x μ β c f (SU2StarEnergy.exterior n x μ U) hβ
    change originalVariance n x μ β f U ≤ _ at h
    have hp : 0 ≤ 12 / (β * r₀) * (weightVariation n x μ f c) ^ 2 := by positivity
    linarith
  · rw [Set.indicator_of_notMem hU, add_zero]
    have hgood : r₀ ≤ ‖exteriorStaple n x μ (SU2StarEnergy.exterior n x μ U)‖ := by
      change ¬ ‖exteriorStaple n x μ (SU2StarEnergy.exterior n x μ U)‖ ≤ r₀ at hU
      exact (lt_of_not_ge hU).le
    have h := conditional_source_variance_bound n x μ (SU2StarEnergy.exterior n x μ U)
      f β c r₀ hβ hr₀ hgood
    change originalVariance n x μ β f U ≤ _ at h
    change originalVariance n x μ β f U ≤
      15 * c ^ 2 / (2 * β ^ 2) + 12 / (β * r₀) * (weightVariation n x μ f c) ^ 2
    convert h using 1
    unfold weightVariation
    ring

/-- Annealed under the original interacting Wilson law, with its actual bad-event probability. -/
theorem annealed_variance_bound (x : Vertex n) (μ : Fin 4) (β c r₀ : ℝ)
    (f : PlaquetteIndex n → ℝ) (hβ : 0 < β) (hr₀ : 0 < r₀) :
    (∫ U, originalVariance n x μ β f U ∂wilsonLaw n Q character β 2) ≤
      15 * c ^ 2 / (2 * β ^ 2) +
        (12 / (β * r₀) + 8 * (wilsonLaw n Q character β 2).real
          (SU2StarEnergy.badEvent n x μ r₀)) * (weightVariation n x μ f c) ^ 2 := by
  let ν := wilsonLaw n Q character β 2
  letI : IsProbabilityMeasure ν := wilsonLaw_probability n Q character character_continuous β 2
  have hv : Integrable (originalVariance n x μ β f) ν :=
    (originalVariance_continuous n x μ β f).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hs := SU2StarEnergy.badEvent_measurable n x μ r₀
  let C := 15 * c ^ 2 / (2 * β ^ 2) +
    12 / (β * r₀) * (weightVariation n x μ f c) ^ 2
  have hind : Integrable ((SU2StarEnergy.badEvent n x μ r₀).indicator
      (fun _ => 8 * (weightVariation n x μ f c) ^ 2)) ν := (integrable_const _).indicator hs
  have h := integral_mono hv ((integrable_const C).add hind)
    (originalVariance_indicator_bound n x μ β c r₀ f hβ hr₀)
  have he : (∫ U, C + (SU2StarEnergy.badEvent n x μ r₀).indicator
      (fun _ => 8 * (weightVariation n x μ f c) ^ 2) U ∂ν) =
      C + ν.real (SU2StarEnergy.badEvent n x μ r₀) *
        (8 * (weightVariation n x μ f c) ^ 2) := by
    rw [integral_add (integrable_const C) hind, integral_indicator_const _ hs]
    simp
  simp only [Pi.add_apply] at h
  rw [he] at h
  change (∫ U, originalVariance n x μ β f U ∂ν) ≤ _
  dsimp only [C] at h
  convert h using 1
  dsimp only [ν]
  ring


/-- Fully explicit original-law estimate, using the proved bad-staple probability bound. -/
theorem annealed_variance_explicit (x : Vertex n) (μ : Fin 4) (β c r₀ : ℝ)
    (f : PlaquetteIndex n → ℝ) (hβ : 0 < β) (hr₀ : 0 < r₀) (hr₆ : r₀ < 6) :
    (∫ U, originalVariance n x μ β f U ∂wilsonLaw n Q character β 2) ≤
      15 * c ^ 2 / (2 * β ^ 2) +
        (12 / (β * r₀) + 144 * WilsonEnergyDensity.energyEnvelope β / (6 - r₀)) *
          (weightVariation n x μ f c) ^ 2 := by
  apply (annealed_variance_bound n x μ β c r₀ f hβ hr₀).trans
  apply add_le_add le_rfl
  apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
  apply add_le_add le_rfl
  have hp := WilsonBadStapleProbability.bad_probability_bound n β hβ x μ r₀ hr₆
  calc
    _ ≤ 8 * (18 * WilsonEnergyDensity.energyEnvelope β / (6 - r₀)) :=
      mul_le_mul_of_nonneg_left hp (by norm_num)
    _ = _ := by ring

end
end UnifiedTheory.Clay.YangMills.SU2AnnealedVariance
