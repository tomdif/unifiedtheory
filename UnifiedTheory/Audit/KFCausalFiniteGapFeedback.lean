/-
  Scalar algebra and error support for FINITE_GAP_GEOMETRY_FEEDBACK.md.
  The Schur-complement, response, and continuum arguments are analytic
  suppliers in the note, not a formalization of the full quantum theory.
-/
import UnifiedTheory.Audit.KFCausalCollectiveWave

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Audit.KFCausalFiniteGapFeedback
noncomputable section

theorem strain_factorization (a b c d k : ℝ) :
    k / 2 * ((a - c) ^ 2 + (b - d) ^ 2 - (a - b) ^ 2 - (c - d) ^ 2) =
      k * (a - d) * (b - c) := by ring

theorem strain_gradient_norm (a b c d k : ℝ) :
    (k * (b - c)) ^ 2 + (k * (a - d)) ^ 2 + (-k * (a - d)) ^ 2 +
      (-k * (b - c)) ^ 2 = 2 * k ^ 2 * ((a - d) ^ 2 + (b - c) ^ 2) := by ring

theorem switch_variance (p d b omega : ℝ) (hw : omega ≠ 0)
    (hs : omega ^ 2 = d ^ 2 + 4 * b ^ 2) (hp : p = (1 - d / omega) / 2) :
    p * (1 - p) = b ^ 2 / omega ^ 2 := by
  rw [hp]
  field_simp
  nlinarith [hs]

/-- A real static strain cannot remove the nonzero transverse mixing gap. -/
theorem strained_gap_lower_bound (L b d f R : ℝ)
    (hL : 0 < L) (hb : 0 < b) (hR : 0 ≤ R)
    (hR2 : R ^ 2 = (L * d + f) ^ 2 + 4 * L ^ 2 * b ^ 2) :
    2 * L * b ≤ R := by
  have ht : 0 < 2 * L * b := by positivity
  have hid : (2 * L * b) ^ 2 = 4 * L ^ 2 * b ^ 2 := by ring
  nlinarith [sq_nonneg (L * d + f)]

theorem switch_characteristic_equation (L omega d f R : ℝ)
    (hR : R ^ 2 = L ^ 2 * omega ^ 2 + 2 * L * d * f + f ^ 2) :
    ((L * omega + f - R) / 2) ^ 2 -
      (L * omega + f) * ((L * omega + f - R) / 2) +
      L * (omega - d) * f / 2 = 0 := by
  nlinarith [hR]

theorem feedback_sign (variance gap force : ℝ)
    (hv : 0 ≤ variance) (hg : 0 < gap) :
    -(variance * force ^ 2 / gap) ≤ 0 := by
  have hn : 0 ≤ variance * force ^ 2 / gap := by positivity
  linarith

theorem quartic_strain_scaling (t a b c d k : ℝ) :
    (k * (t * a - t * d) * (t * b - t * c)) ^ 2 =
      t ^ 4 * (k * (a - d) * (b - c)) ^ 2 := by ring

theorem affine_strain (spacing slope k origin : ℝ) :
    k * (spacing * origin - spacing * (origin + 3 * spacing * slope)) *
      (spacing * (origin + spacing * slope) - spacing * (origin + 2 * spacing * slope)) =
      3 * k * spacing ^ 4 * slope ^ 2 := by ring

theorem resolvent_remainder_ratio (beta w gap : ℝ) :
    beta ^ 2 * w ^ 2 / (gap ^ 2 * (gap - w)) =
      (w / gap) * (beta ^ 2 * w / (gap * (gap - w))) := by
  by_cases hg : gap = 0
  · simp [hg]
  by_cases hd : gap - w = 0
  · simp [hd]
  field_simp

theorem residual_after_positive_normalization (error u y residual : ℝ)
    (he : 0 ≤ error) (hu : u ≤ y) (hr : residual ≤ error * u) :
    residual ≤ error * y := by
  exact hr.trans (mul_le_mul_of_nonneg_left hu he)

theorem static_response_from_pole (variance gap : ℝ) (hg : gap ≠ 0) :
    -(2 * gap * variance / (gap ^ 2 - (0 : ℝ) ^ 2)) = -(2 * variance / gap) := by
  field_simp
  ring

/-- The classical quartic coefficient vanishes in any macroscopically fast scaling. -/
theorem macroscopic_feedback_scaling (a L : ℝ) (ha : a ≠ 0) :
    a ^ 4 / L = a ^ 3 / (L / a) := by
  by_cases hL : L = 0
  · simp [hL]
  field_simp

#print axioms strain_factorization
#print axioms strain_gradient_norm
#print axioms switch_variance
#print axioms strained_gap_lower_bound
#print axioms switch_characteristic_equation
#print axioms feedback_sign
#print axioms quartic_strain_scaling
#print axioms affine_strain
#print axioms resolvent_remainder_ratio
#print axioms residual_after_positive_normalization
#print axioms static_response_from_pole
#print axioms macroscopic_feedback_scaling

end
end UnifiedTheory.Audit.KFCausalFiniteGapFeedback
