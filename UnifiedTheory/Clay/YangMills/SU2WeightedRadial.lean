/-
Radial/remainder decomposition of the actual weighted Wilson source.
The six individual source coefficients are split around an arbitrary scalar c.
The radial fluctuation uses the proved inverse-square Haar bound, while the
coefficient variation uses the inverse-tilt bound. No independence of probes
or replacement of the actual conditional Wilson law is assumed.
-/
import UnifiedTheory.Clay.YangMills.SU2HaarCovariance

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Clay.YangMills.SU2WeightedRadial
noncomputable section
open MeasureTheory RegulatedGauge PeriodicLattice4 WilsonUniformVariance
open WilsonSingleLinkStaples WilsonIndependentBlocks SingleLinkWilsonOscillation
open SU2HaarTilt SU2HaarCovariance SU2InducedAction
open scoped Quaternion RealInnerProductSpace

theorem covariance_centered (β : ℝ) (A B : ℍ) :
    covariance β A B B =
      ∫ q : Q, (⟪(q : ℍ), B⟫ - tiltMean β A B) ^ 2 ∂tiltLaw β A := by
  have h := CompactGibbsSource.covariance_self_eq haar (baseAction β A) (insertion β B)
    (fun q : Q => ⟪(q : ℍ), B⟫) (baseAction_continuous β A) (insertion_continuous β B)
    (continuous_subtype_val.inner continuous_const) 0
  simpa only [source_covariance, source_expectation, source_law, zero_smul, add_zero] using h

theorem mean_smul (β : ℝ) (A B : ℍ) (c : ℝ) :
    tiltMean β A (c • B) = c * tiltMean β A B := by
  simp only [tiltMean_rotational, real_inner_smul_right]
  ring

theorem covariance_smul (β : ℝ) (A B : ℍ) (c : ℝ) :
    covariance β A (c • B) (c • B) = c ^ 2 * covariance β A B B := by
  rw [covariance_centered, covariance_centered]
  simp only [real_inner_smul_right, mean_smul]
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards with q
  ring

/-- An exact-law variance split; no independence of the two probes is assumed. -/
theorem covariance_add_le (β : ℝ) (A B C : ℍ) :
    covariance β A (B + C) (B + C) ≤ 2 * covariance β A B B + 2 * covariance β A C C := by
  letI := tiltLaw_probability β A
  have hiB : Integrable (fun q : Q => (⟪(q : ℍ), B⟫ - tiltMean β A B) ^ 2)
      (tiltLaw β A) :=
    Continuous.integrable_of_hasCompactSupport (by fun_prop) (HasCompactSupport.of_compactSpace _)
  have hiC : Integrable (fun q : Q => (⟪(q : ℍ), C⟫ - tiltMean β A C) ^ 2)
      (tiltLaw β A) :=
    Continuous.integrable_of_hasCompactSupport (by fun_prop) (HasCompactSupport.of_compactSpace _)
  apply (covariance_le_square_deviation β A (B + C)
    (tiltMean β A B + tiltMean β A C)).trans
  calc
    _ ≤ ∫ q : Q, 2 * (⟪(q : ℍ), B⟫ - tiltMean β A B) ^ 2 +
        2 * (⟪(q : ℍ), C⟫ - tiltMean β A C) ^ 2 ∂tiltLaw β A := by
      apply integral_mono
      · exact Continuous.integrable_of_hasCompactSupport (by fun_prop)
          (HasCompactSupport.of_compactSpace _)
      · exact (hiB.const_mul 2).add (hiC.const_mul 2)
      · intro q
        dsimp only
        rw [inner_add_right]
        nlinarith [sq_nonneg ((⟪(q : ℍ), B⟫ - tiltMean β A B) -
          (⟪(q : ℍ), C⟫ - tiltMean β A C))]
    _ = _ := by
      rw [integral_add (hiB.const_mul 2) (hiC.const_mul 2), integral_const_mul,
        integral_const_mul, ← covariance_centered, ← covariance_centered]

/-- Radial fluctuations retain the stronger inverse-square rate. -/
theorem radial_remainder_covariance (β c : ℝ) (A D : ℍ) (hβ : 0 < β) (hA : A ≠ 0) :
    covariance β A (c • A + D) (c • A + D) ≤
      15 * c ^ 2 / (8 * β ^ 2) + 3 * ‖D‖ ^ 2 / (β * ‖A‖) := by
  have h := covariance_add_le β A (c • A) D
  rw [covariance_smul] at h
  have hr := mul_le_mul_of_nonneg_left (covariance_radial_le_all β A hβ)
    (show 0 ≤ 2 * c ^ 2 by positivity)
  have hd := mul_le_mul_of_nonneg_left (covariance_le_inverse_tilt β A D hβ hA)
    (show (0 : ℝ) ≤ 2 by norm_num)
  calc
    _ ≤ 2 * (c ^ 2 * covariance β A A A) + 2 * covariance β A D D := h
    _ ≤ 2 * c ^ 2 * (15 / (16 * β ^ 2)) +
        2 * (3 * ‖D‖ ^ 2 / (2 * β * ‖A‖)) := by nlinarith
    _ = _ := by ring

variable (n : ℕ) [NeZero n] [Fact (1 < n)]

local instance edgeDecidableEq : DecidableEq (Edge (Vertex n)) := Classical.decEq _

omit [NeZero n] [Fact (1 < n)] in
/-- Exact decomposition of the actual six individually weighted staple triples. -/
theorem weightedStaple_decomposition (U : Configuration (Vertex n) Q)
    (x : Vertex n) (μ : Fin 4) (f : PlaquetteIndex n → ℝ) (c : ℝ) :
    weightedStaple n U x μ f =
      c • stapleSum n U x μ + weightedStaple n U x μ (fun p => f p - c) := by
  unfold stapleSum weightedStaple
  rw [Finset.smul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro p _
  simp only [one_smul]
  module

omit [NeZero n] [Fact (1 < n)] in
theorem exteriorWeightedStaple_decomposition (x : Vertex n) (μ : Fin 4)
    (r : Exterior n Q x μ) (f : PlaquetteIndex n → ℝ) (c : ℝ) :
    exteriorWeightedStaple n x μ r f = c • exteriorStaple n x μ r +
      exteriorWeightedStaple n x μ r (fun p => f p - c) :=
  weightedStaple_decomposition n (exteriorConfig n x μ r) x μ f c

omit [NeZero n] [Fact (1 < n)] in
/-- The remainder is bounded by variation of the actual six source coefficients. -/
theorem exterior_remainder_norm (x : Vertex n) (μ : Fin 4)
    (r : Exterior n Q x μ) (f : PlaquetteIndex n → ℝ) (c : ℝ) :
    ‖exteriorWeightedStaple n x μ r (fun p => f p - c)‖ ≤
      ∑ p ∈ affected n x μ, |f p - c| :=
  exteriorWeightedStaple_norm_le n x μ r (fun p => f p - c)

omit [NeZero n] [Fact (1 < n)] in
/-- A source-sensitive covariance estimate for the actual Wilson exterior vectors. -/
theorem weighted_covariance_bound (x : Vertex n) (μ : Fin 4)
    (r : Exterior n Q x μ) (f : PlaquetteIndex n → ℝ) (β c r₀ : ℝ)
    (hβ : 0 < β) (hr₀ : 0 < r₀) (hgood : r₀ ≤ ‖exteriorStaple n x μ r‖) :
    covariance β (exteriorStaple n x μ r)
      (exteriorWeightedStaple n x μ r f) (exteriorWeightedStaple n x μ r f) ≤
      15 * c ^ 2 / (8 * β ^ 2) +
        3 * (∑ p ∈ affected n x μ, |f p - c|) ^ 2 / (β * r₀) := by
  let A := exteriorStaple n x μ r
  let D := exteriorWeightedStaple n x μ r (fun p => f p - c)
  have hA : A ≠ 0 := norm_ne_zero_iff.mp (ne_of_gt (hr₀.trans_le hgood))
  have hnorm := exterior_remainder_norm n x μ r f c
  have hs : 0 ≤ ∑ p ∈ affected n x μ, |f p - c| := Finset.sum_nonneg (fun _ _ => abs_nonneg _)
  have hsq := (sq_le_sq₀ (norm_nonneg D) hs).mpr hnorm
  rw [exteriorWeightedStaple_decomposition n x μ r f c]
  apply (radial_remainder_covariance β c A D hβ hA).trans
  apply add_le_add le_rfl
  calc
    _ ≤ 3 * (∑ p ∈ affected n x μ, |f p - c|) ^ 2 / (β * ‖A‖) :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hsq (by norm_num)) (by positivity)
    _ ≤ _ := div_le_div_of_nonneg_left (by positivity) (by positivity)
      (mul_le_mul_of_nonneg_left hgood hβ.le)

/-- Exact full-source conditional variance in the original Wilson one-link law. -/
theorem conditional_source_variance (x : Vertex n) (μ : Fin 4) (β : ℝ)
    (f : PlaquetteIndex n → ℝ) (r : Exterior n Q x μ) :
    (∫ q : Q, (SU2WilsonConditionalSource.splitSource n x μ f (r, q) -
      SU2WilsonConditionalSource.conditionalSource n x μ β f r) ^ 2
      ∂SU2WilsonConditionalSource.conditionalLaw n x μ β r) =
      4 * covariance β (exteriorStaple n x μ r)
        (exteriorWeightedStaple n x μ r f) (exteriorWeightedStaple n x μ r f) := by
  rw [SU2WilsonConditionalSource.conditionalLaw_eq_tiltLaw,
    SU2WilsonConditionalSource.conditionalSource_eq_tiltMean, covariance_centered,
    ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards with q
  rw [SU2WilsonConditionalSource.splitSource, source_assemble]
  ring

/-- Slowly varying coefficients enter only through their six-plaquette variation. -/
theorem conditional_source_variance_bound (x : Vertex n) (μ : Fin 4)
    (r : Exterior n Q x μ) (f : PlaquetteIndex n → ℝ) (β c r₀ : ℝ)
    (hβ : 0 < β) (hr₀ : 0 < r₀) (hgood : r₀ ≤ ‖exteriorStaple n x μ r‖) :
    (∫ q : Q, (SU2WilsonConditionalSource.splitSource n x μ f (r, q) -
      SU2WilsonConditionalSource.conditionalSource n x μ β f r) ^ 2
      ∂SU2WilsonConditionalSource.conditionalLaw n x μ β r) ≤
      15 * c ^ 2 / (2 * β ^ 2) +
        12 * (∑ p ∈ affected n x μ, |f p - c|) ^ 2 / (β * r₀) := by
  rw [conditional_source_variance]
  have h := mul_le_mul_of_nonneg_left
    (weighted_covariance_bound n x μ r f β c r₀ hβ hr₀ hgood) (show (0 : ℝ) ≤ 4 by norm_num)
  convert h using 1
  ring

end
end UnifiedTheory.Clay.YangMills.SU2WeightedRadial
