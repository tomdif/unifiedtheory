/- A continuous hybrid retaining an exact low-radius response.
The good-region approximation estimate is an explicit input. This module does
not prove the SU(2) Haar remainder, identify a physical coupling trajectory,
or control the retained source's continuum correlations. -/
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Clay.YangMills.HybridSourceApproximation
noncomputable section
open Filter
open scoped Topology BigOperators

/-- Linear interpolation clipped to the interval `[0,1]`. -/
def cutoff (r₀ r₁ r : ℝ) : ℝ :=
  min 1 (max 0 ((r - r₀) / (r₁ - r₀)))

theorem cutoff_nonneg (r₀ r₁ r : ℝ) : 0 ≤ cutoff r₀ r₁ r :=
  le_min (by norm_num) (le_max_left _ _)

theorem cutoff_le_one (r₀ r₁ r : ℝ) : cutoff r₀ r₁ r ≤ 1 :=
  min_le_left _ _

theorem cutoff_eq_zero (r₀ r₁ r : ℝ) (h : r₀ < r₁) (hr : r ≤ r₀) :
    cutoff r₀ r₁ r = 0 := by
  have hd : (r - r₀) / (r₁ - r₀) ≤ 0 :=
    div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hr) (sub_pos.mpr h).le
  simp [cutoff, max_eq_left hd]

theorem cutoff_eq_one (r₀ r₁ r : ℝ) (h : r₀ < r₁) (hr : r₁ ≤ r) :
    cutoff r₀ r₁ r = 1 := by
  have hd : 1 ≤ (r - r₀) / (r₁ - r₀) := by
    apply (le_div_iff₀ (sub_pos.mpr h)).2
    linarith
  exact min_eq_left (hd.trans (le_max_right _ _))

theorem cutoff_continuous (r₀ r₁ : ℝ) : Continuous (cutoff r₀ r₁) :=
  continuous_const.min
    (continuous_const.max ((continuous_id.sub continuous_const).div_const _))

section Hybrid
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def hybrid (r₀ r₁ r : ℝ) (Y P : E) : E :=
  (1 - cutoff r₀ r₁ r) • Y + cutoff r₀ r₁ r • P

theorem hybrid_eq_exact (r₀ r₁ r : ℝ) (h : r₀ < r₁) (hr : r ≤ r₀)
    (Y P : E) : hybrid r₀ r₁ r Y P = Y := by
  simp [hybrid, cutoff_eq_zero r₀ r₁ r h hr]

theorem hybrid_eq_approximation (r₀ r₁ r : ℝ) (h : r₀ < r₁) (hr : r₁ ≤ r)
    (Y P : E) : hybrid r₀ r₁ r Y P = P := by
  simp [hybrid, cutoff_eq_one r₀ r₁ r h hr]

theorem hybrid_error_identity (r₀ r₁ r : ℝ) (Y P : E) :
    Y - hybrid r₀ r₁ r Y P = cutoff r₀ r₁ r • (Y - P) := by
  simp only [hybrid, sub_smul, one_smul, smul_sub]
  abel

theorem hybrid_error_norm (r₀ r₁ r : ℝ) (Y P : E) :
    ‖Y - hybrid r₀ r₁ r Y P‖ = cutoff r₀ r₁ r * ‖Y - P‖ := by
  rw [hybrid_error_identity, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (cutoff_nonneg r₀ r₁ r)]

/-- No estimate on the exact sector `r ≤ r₀` is needed. -/
theorem hybrid_error_le (r₀ r₁ r ε : ℝ) (h : r₀ < r₁) (hε : 0 ≤ ε)
    (Y P : E) (hgood : r₀ ≤ r → ‖Y - P‖ ≤ ε) :
    ‖Y - hybrid r₀ r₁ r Y P‖ ≤ ε := by
  by_cases hr : r ≤ r₀
  · simpa [hybrid_eq_exact r₀ r₁ r h hr Y P] using hε
  · rw [hybrid_error_norm]
    calc
      cutoff r₀ r₁ r * ‖Y - P‖ ≤ 1 * ‖Y - P‖ :=
        mul_le_mul_of_nonneg_right (cutoff_le_one r₀ r₁ r) (norm_nonneg _)
      _ ≤ ε := by simpa using hgood (le_of_lt (lt_of_not_ge hr))

theorem hybrid_continuous {X : Type*} [TopologicalSpace X]
    (r₀ r₁ : ℝ) (r : X → ℝ) (Y P : X → E)
    (hr : Continuous r) (hY : Continuous Y) (hP : Continuous P) :
    Continuous (fun x => hybrid r₀ r₁ (r x) (Y x) (P x)) := by
  exact ((continuous_const.sub ((cutoff_continuous r₀ r₁).comp hr)).smul hY).add
    (((cutoff_continuous r₀ r₁).comp hr).smul hP)

/-- The error after a finite weighted sum, using individual good-region bounds. -/
theorem weighted_error_le {ι : Type*} (s : Finset ι)
    (r₀ r₁ : ℝ) (h : r₀ < r₁) (r w ε : ι → ℝ) (Y P : ι → E)
    (hε : ∀ i ∈ s, 0 ≤ ε i)
    (hgood : ∀ i ∈ s, r₀ ≤ r i → ‖Y i - P i‖ ≤ ε i) :
    ‖(∑ i ∈ s, w i • Y i) -
      ∑ i ∈ s, w i • hybrid r₀ r₁ (r i) (Y i) (P i)‖ ≤
      ∑ i ∈ s, |w i| * ε i := by
  rw [← Finset.sum_sub_distrib]
  simp_rw [← smul_sub]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum ?_)
  intro i hi
  rw [norm_smul, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_left
    (hybrid_error_le r₀ r₁ (r i) (ε i) h (hε i hi) (Y i) (P i) (hgood i hi))
    (abs_nonneg _)

theorem weighted_error_le_uniform {ι : Type*} (s : Finset ι)
    (r₀ r₁ ε : ℝ) (h : r₀ < r₁) (hε : 0 ≤ ε)
    (r w : ι → ℝ) (Y P : ι → E)
    (hgood : ∀ i ∈ s, r₀ ≤ r i → ‖Y i - P i‖ ≤ ε) :
    ‖(∑ i ∈ s, w i • Y i) -
      ∑ i ∈ s, w i • hybrid r₀ r₁ (r i) (Y i) (P i)‖ ≤
      ε * ∑ i ∈ s, |w i| := by
  have hb := weighted_error_le s r₀ r₁ h r w (fun _ => ε) Y P
    (fun _ _ => hε) hgood
  calc
    _ ≤ ∑ i ∈ s, |w i| * ε := hb
    _ = ε * ∑ i ∈ s, |w i| := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      ring
end Hybrid

/-- The physical rescaling factor for `a = exp(-t)` and `β = b*t`. -/
def trajectoryError (b r₀ t : ℝ) : ℝ :=
  (Real.exp (-t) ^ 4)⁻¹ * (b * t) ^ 2 * Real.exp (-4 * (b * t) * r₀)

theorem trajectoryError_nonneg (b r₀ t : ℝ) : 0 ≤ trajectoryError b r₀ t := by
  unfold trajectoryError
  positivity

theorem trajectoryError_eq (b r₀ t : ℝ) :
    trajectoryError b r₀ t =
      b ^ 2 * (t ^ 2 * Real.exp (-(4 * b * r₀ - 4) * t)) := by
  have he : (Real.exp (-t) ^ 4)⁻¹ = Real.exp (4 * t) := by
    rw [← Real.exp_nat_mul, ← Real.exp_neg]
    congr 1
    norm_num
  unfold trajectoryError
  rw [he]
  calc
    _ = b ^ 2 * t ^ 2 *
        (Real.exp (4 * t) * Real.exp (-4 * (b * t) * r₀)) := by ring
    _ = b ^ 2 * (t ^ 2 * Real.exp (-(4 * b * r₀ - 4) * t)) := by
      rw [← Real.exp_add]
      have hx : 4 * t + -4 * (b * t) * r₀ = -(4 * b * r₀ - 4) * t := by ring
      rw [hx]
      ring

/-- This is an exact logarithmic trajectory, not an identified physical one. -/
theorem trajectoryError_tendsto (b r₀ : ℝ) (h : 1 < b * r₀) :
    Tendsto (trajectoryError b r₀) atTop (𝓝 0) := by
  have hd : 0 < 4 * b * r₀ - 4 := by nlinarith
  have ht : Tendsto (fun t : ℝ => t ^ 2 * Real.exp (-(4 * b * r₀ - 4) * t))
      atTop (𝓝 0) := by
    simpa only [Real.rpow_two] using
      tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 2 (4 * b * r₀ - 4) hd
  change Tendsto (fun t => trajectoryError b r₀ t) atTop (𝓝 0)
  simp_rw [trajectoryError_eq]
  simpa only [mul_zero] using ht.const_mul (b ^ 2)

/-- A norm bound with this physical rescaling is sufficient for convergence. -/
theorem error_tendsto_zero {E : Type*} [NormedAddCommGroup E]
    (b r₀ C : ℝ) (h : 1 < b * r₀) (F : ℝ → E)
    (hF : ∀ᶠ t in atTop, ‖F t‖ ≤ C * trajectoryError b r₀ t) :
    Tendsto F atTop (𝓝 0) := by
  apply squeeze_zero_norm' hF
  simpa only [mul_zero] using (trajectoryError_tendsto b r₀ h).const_mul C

/-- The analytic good-region estimate is supplied explicitly. Its exact-sector
replacement gives a vanishing rescaled error without any bad-event estimate. -/
theorem rescaled_hybrid_error_tendsto {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (b r₀ r₁ C : ℝ) (hcut : r₀ < r₁) (hC : 0 ≤ C) (hb : 1 < b * r₀)
    (r : ℝ → ℝ) (Y P : ℝ → E)
    (hgood : ∀ᶠ t in atTop, r₀ ≤ r t →
      ‖Y t - P t‖ ≤ C * (b * t) ^ 2 * Real.exp (-4 * (b * t) * r₀)) :
    Tendsto (fun t => (Real.exp (-t) ^ 4)⁻¹ •
      (Y t - hybrid r₀ r₁ (r t) (Y t) (P t))) atTop (𝓝 0) := by
  apply error_tendsto_zero b r₀ C hb
  filter_upwards [hgood] with t ht
  have hε : 0 ≤ C * (b * t) ^ 2 * Real.exp (-4 * (b * t) * r₀) := by
    positivity
  have hs : 0 ≤ (Real.exp (-t) ^ 4)⁻¹ := by positivity
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hs]
  calc
    _ ≤ (Real.exp (-t) ^ 4)⁻¹ *
        (C * (b * t) ^ 2 * Real.exp (-4 * (b * t) * r₀)) :=
      mul_le_mul_of_nonneg_left
        (hybrid_error_le r₀ r₁ (r t) _ hcut hε (Y t) (P t) ht) hs
    _ = C * trajectoryError b r₀ t := by unfold trajectoryError; ring

/-- Every slope strictly above `1/6` admits fixed radii below the maximal
six-staple radius. This is algebra, not a physical trajectory theorem. -/
theorem cutoffs_exist (b : ℝ) (hb : 1 / 6 < b) :
    ∃ r₀ r₁ : ℝ, 0 < r₀ ∧ r₀ < r₁ ∧ r₁ < 6 ∧ 1 < b * r₀ := by
  have hb0 : 0 < b := by linarith
  have hi0 : 0 < 1 / b := div_pos zero_lt_one hb0
  have hi6 : 1 / b < 6 := (div_lt_iff₀ hb0).2 (by linarith)
  have hbi : b * (1 / b) = 1 := by field_simp
  refine ⟨(1 / b + 6) / 2, ((1 / b + 6) / 2 + 6) / 2, ?_, ?_, ?_, ?_⟩
  · linarith
  · linarith
  · linarith
  · nlinarith

/-- Numerical parameters suggested by perturbation theory; their physical
identification is not a hypothesis or conclusion of this module. -/
def exampleSlope : ℝ := 11 / (6 * Real.pi ^ 2)
def exampleLower : ℝ := 11 / 2
def exampleUpper : ℝ := 23 / 4

theorem example_cutoffs : 0 < exampleLower ∧ exampleLower < exampleUpper ∧
    exampleUpper < 6 := by
  norm_num [exampleLower, exampleUpper]

theorem example_slope_positive : 0 < exampleSlope := by
  unfold exampleSlope
  positivity

theorem example_margin : 1 < exampleSlope * exampleLower := by
  have hp : 0 < ((3.15 : ℝ) - Real.pi) * (3.15 + Real.pi) :=
    mul_pos (sub_pos.mpr Real.pi_lt_d2) (by linarith [Real.pi_pos])
  unfold exampleSlope exampleLower
  rw [div_mul_eq_mul_div, lt_div_iff₀ (by positivity : 0 < 6 * Real.pi ^ 2)]
  nlinarith

theorem example_trajectory_tendsto :
    Tendsto (trajectoryError exampleSlope exampleLower) atTop (𝓝 0) :=
  trajectoryError_tendsto exampleSlope exampleLower example_margin

end
end UnifiedTheory.Clay.YangMills.HybridSourceApproximation
