/- Conditional geometric bridge from actual Haar response to the proved
scalar asymptotic expansion. `FirstCoordinateFormula` is an explicit remaining
Haar marginal-density obligation; this module does not prove or postulate it.
Under that explicit hypothesis, all normalization, response algebra, and
uniform error estimates below are derived. No desired approximation error or
continuum conclusion is supplied as a premise. -/
import UnifiedTheory.Clay.YangMills.SU2HaarTilt
import UnifiedTheory.Clay.YangMills.SU2ScalarTilt
set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace UnifiedTheory.Clay.YangMills.SU2HaarScalarBridge
noncomputable section
open MeasureTheory SU2QuaternionEquivalence SU2HaarTilt
open scoped Quaternion RealInnerProductSpace

/-- The precise normalized semicircle marginal identity, required as an
explicit hypothesis of the bridge theorems. -/
def FirstCoordinateFormula : Prop :=
  ∀ F : ℝ → ℝ, Continuous F →
    (∫ q : UnitQuaternion, F (q : ℍ).re ∂haar) =
      SU2ScalarTilt.semicircleIntegral 0 F / SU2ScalarTilt.partition 0

theorem scalar_weight_shift (κ : ℝ) (F : ℝ → ℝ) :
    SU2ScalarTilt.semicircleIntegral 0 (fun t => Real.exp (κ * t) * F t) =
      SU2ScalarTilt.semicircleIntegral κ F := by
  unfold SU2ScalarTilt.semicircleIntegral SU2ScalarTilt.weight
  apply intervalIntegral.integral_congr
  intro t ht
  simp only [zero_mul, Real.exp_zero, one_mul]
  ring

theorem weighted_coordinate_formula (hcoord : FirstCoordinateFormula) (κ : ℝ)
    (F : ℝ → ℝ) (hF : Continuous F) :
    (∫ q : UnitQuaternion, axisWeight κ q * F (q : ℍ).re ∂haar) =
      SU2ScalarTilt.semicircleIntegral κ F / SU2ScalarTilt.partition 0 := by
  have h := hcoord (fun t => Real.exp (κ * t) * F t)
    ((Real.continuous_exp.comp (continuous_const.mul continuous_id)).mul hF)
  rw [scalar_weight_shift] at h
  exact h

theorem axisPartition_eq_scalar (hcoord : FirstCoordinateFormula) (κ : ℝ) :
    axisPartition κ = SU2ScalarTilt.partition κ / SU2ScalarTilt.partition 0 := by
  simpa only [mul_one, SU2ScalarTilt.partition] using
    weighted_coordinate_formula hcoord κ (fun _ => 1) continuous_const

/-- Common first-coordinate normalization cancels for every real tilt,
including the zero endpoint. -/
theorem axisExcess_eq_scalar (hcoord : FirstCoordinateFormula) (κ : ℝ) :
    axisExcess κ = SU2ScalarTilt.excessMean κ := by
  unfold axisExcess
  rw [weighted_coordinate_formula hcoord κ (fun t => κ * (1-t)) (by fun_prop),
    axisPartition_eq_scalar hcoord κ,
    div_div_div_cancel_right₀ (SU2ScalarTilt.partition_pos 0).ne']
  rfl

/-- The actual affine response with an arbitrary exterior constant. -/
def affineResponse (β D : ℝ) (A B : ℍ) : ℝ := D-2 * tiltMean β A B

/-- Finite source expansion with `κ=2β‖A‖`; no averaged density replaces Haar. -/
def affineApproximation (β D : ℝ) (A B : ℍ) (N : ℕ) : ℝ :=
  D-2 * ⟪A, B⟫ / ‖A‖ + ⟪A, B⟫ / (β * ‖A‖^2) *
    SU2QuotientRemainder.sourceTruncation N (2 * β * ‖A‖)

/-- The exterior constant cancels before any estimate is applied. -/
theorem affine_error_identity (β D : ℝ) (hβ : β ≠ 0) (A B : ℍ)
    (hA : A ≠ 0) (N : ℕ) :
    affineResponse β D A B-affineApproximation β D A B N =
      (⟪A, B⟫ / (β * ‖A‖^2)) * (axisExcess (2 * β * ‖A‖)-
        SU2QuotientRemainder.sourceTruncation N (2 * β * ‖A‖)) := by
  unfold affineResponse affineApproximation
  rw [tiltMean_excess β hβ A B hA]
  field_simp
  ring

theorem affine_coefficient_bound (β : ℝ) (hβ : 0 < β) (A B : ℍ)
    (hA : 0 < ‖A‖) : |⟪A, B⟫ / (β * ‖A‖^2)| ≤ ‖B‖ / (β * ‖A‖) := by
  rw [abs_div, abs_of_pos (by positivity : 0 < β * ‖A‖^2)]
  calc
    _ ≤ (‖A‖ * ‖B‖) / (β * ‖A‖^2) :=
      div_le_div_of_nonneg_right (abs_real_inner_le_norm A B) (by positivity)
    _ = _ := by field_simp

/-- Uniform error over `‖A‖≥r₀`, conditional only on the stated marginal
density identity and explicit scalar parameter inequalities. -/
theorem affine_error_bound (hcoord : FirstCoordinateFormula)
    (β D r₀ : ℝ) (hr₀ : 0 < r₀) (hβr : 3 / 4 ≤ β * r₀)
    (A B : ℍ) (hA : r₀ ≤ ‖A‖) :
    |affineResponse β D A B-affineApproximation β D A B ⌊4 * β * r₀⌋₊| ≤
      24 * Real.exp 2 * (4 * β * r₀ + 1) * (4 * β * r₀ + 9 / 2) * Real.exp (-4 * β * r₀) * ‖B‖ := by
  have hβ : 0 < β := by
    by_contra hn
    have h := mul_nonpos_of_nonpos_of_nonneg (le_of_not_gt hn) hr₀.le
    linarith
  have hAn : 0 < ‖A‖ := hr₀.trans_le hA
  have hA0 : A ≠ 0 := norm_ne_zero_iff.mp hAn.ne'
  have hc : |⟪A, B⟫ / (β * ‖A‖^2)| ≤ ‖B‖ / (β * r₀) := by
    apply (affine_coefficient_bound β hβ A B hAn).trans
    apply div_le_div_of_nonneg_left (norm_nonneg B) (mul_pos hβ hr₀)
    exact mul_le_mul_of_nonneg_left hA hβ.le
  have hκ₀ : 3 / 2 ≤ 2 * β * r₀ := by linarith
  have hκ : 2 * β * r₀ ≤ 2 * β * ‖A‖ :=
    mul_le_mul_of_nonneg_left hA (by positivity)
  have hs := SU2ScalarTilt.excessMean_optimal_remainder (2 * β * r₀) (2 * β * ‖A‖) hκ₀ hκ
  have he : 2 * (2 * β * r₀) = 4 * β * r₀ := by ring
  have hen : -2 * (2 * β * r₀) = -4 * β * r₀ := by ring
  rw [he, hen] at hs
  rw [affine_error_identity β D hβ.ne' A B hA0, abs_mul, axisExcess_eq_scalar hcoord]
  calc
    _ ≤ (‖B‖ / (β * r₀)) *
        (6 * Real.exp 2 * (4 * β * r₀) * (4 * β * r₀ + 1) *
          (4 * β * r₀ + 9 / 2) * Real.exp (-4 * β * r₀)) :=
      mul_le_mul hc hs (abs_nonneg _) (by positivity)
    _ = _ := by field_simp; ring

/-- The optimal remainder has the quadratic coupling prefactor required
by the earlier hybrid-source convergence theorem. -/
theorem affine_error_bound_quadratic (hcoord : FirstCoordinateFormula)
    (β D r₀ : ℝ) (hr₀ : 0 < r₀) (hβr : 3 / 4 ≤ β * r₀)
    (A B : ℍ) (hA : r₀ ≤ ‖A‖) :
    |affineResponse β D A B-affineApproximation β D A B ⌊4 * β * r₀⌋₊| ≤
      1280 * Real.exp 2 * r₀^2 * β^2 * Real.exp (-4 * β * r₀) * ‖B‖ := by
  have hp : 24 * (4 * β * r₀ + 1) * (4 * β * r₀ + 9 / 2) ≤ 1280 * (β * r₀)^2 := by
    have h := mul_nonneg (show 0 ≤ β * r₀-3 / 4 by linarith)
      (show 0 ≤ 896 * (β * r₀) + 144 by linarith)
    nlinarith
  calc
    _ ≤ 24 * Real.exp 2 * (4 * β * r₀ + 1) * (4 * β * r₀ + 9 / 2) * Real.exp (-4 * β * r₀) * ‖B‖ :=
      affine_error_bound hcoord β D r₀ hr₀ hβr A B hA
    _ = (24 * (4 * β * r₀ + 1) * (4 * β * r₀ + 9 / 2)) *
        (Real.exp 2 * Real.exp (-4 * β * r₀) * ‖B‖) := by ring
    _ ≤ (1280 * (β * r₀)^2) * (Real.exp 2 * Real.exp (-4 * β * r₀) * ‖B‖) :=
      mul_le_mul_of_nonneg_right hp (by positivity)
    _ = _ := by ring

/-- Zero source has an exact affine response, with no density hypothesis. -/
theorem affine_zero_exact (β D : ℝ) (B : ℍ) (N : ℕ) :
    affineResponse β D 0 B = affineApproximation β D 0 B N := by
  simp [affineResponse, affineApproximation, tiltMean_zero]

end
end UnifiedTheory.Clay.YangMills.SU2HaarScalarBridge
