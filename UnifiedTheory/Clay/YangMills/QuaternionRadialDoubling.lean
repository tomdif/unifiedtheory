/- A homogeneous extension of quaternion squaring controls Haar distortion
through four-dimensional cone volume. Its global Lipschitz constant is three. -/
import UnifiedTheory.Clay.YangMills.QuaternionChordMidpoint
import Mathlib.MeasureTheory.Measure.Hausdorff

set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace UnifiedTheory.Clay.YangMills.QuaternionRadialDoubling
noncomputable section
open MeasureTheory WilsonSlabOperator QuaternionSymmetricChange
open scoped Quaternion ENNReal

def direction (x : ℍ) : ℍ := ‖x‖⁻¹ • x

theorem direction_norm (x : ℍ) (hx : x ≠ 0) : ‖direction x‖ = 1 := by
  simp only [direction, norm_smul, Real.norm_eq_abs, abs_inv, abs_norm]
  exact inv_mul_cancel₀ (norm_ne_zero_iff.mpr hx)

theorem direction_restore (x : ℍ) : ‖x‖ • direction x = x := by
  by_cases hx : x = 0
  · simp [hx, direction]
  · simp only [direction, smul_smul, mul_inv_cancel₀ (norm_ne_zero_iff.mpr hx), one_smul]

theorem direction_difference (x y : ℍ) (hy : y ≠ 0) :
    ‖x‖ * ‖direction x - direction y‖ ≤ 2 * ‖x - y‖ := by
  have he : ‖x‖ • (direction x - direction y) =
      (x - y) + (‖y‖ - ‖x‖) • direction y := by
    rw [smul_sub, sub_smul, direction_restore, direction_restore]
    abel
  have hh := norm_add_le (x - y) ((‖y‖ - ‖x‖) • direction y)
  rw [← he, norm_smul, Real.norm_eq_abs, abs_norm, norm_smul, Real.norm_eq_abs,
    direction_norm y hy, mul_one] at hh
  have hn := abs_norm_sub_norm_le y x
  rw [norm_sub_rev y x] at hn
  linarith

def radialDouble (x : ℍ) : ℍ := direction x * x

theorem radialDouble_zero : radialDouble 0 = 0 := by simp [radialDouble]

theorem radialDouble_norm (x : ℍ) : ‖radialDouble x‖ = ‖x‖ := by
  by_cases hx : x = 0
  · simp [hx, radialDouble_zero]
  · rw [radialDouble, norm_mul, direction_norm x hx, one_mul]

theorem radialDouble_lipschitz : LipschitzWith 3 radialDouble := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simp only [dist_eq_norm, NNReal.coe_ofNat]
  by_cases hy : y = 0
  · simp only [hy, radialDouble_zero, sub_zero, radialDouble_norm]
    linarith [norm_nonneg x]
  · have he : radialDouble x - radialDouble y =
        (direction x - direction y) * x + direction y * (x - y) := by
      unfold radialDouble
      noncomm_ring
    rw [he]
    have hh := norm_add_le ((direction x - direction y) * x) (direction y * (x - y))
    simp only [norm_mul, direction_norm y hy, one_mul] at hh
    nlinarith only [hh, direction_difference x y hy]

theorem radialDouble_smul (r : ℝ) (hr : 0 ≤ r) (x : ℍ) :
    radialDouble (r • x) = r • radialDouble x := by
  by_cases hr0 : r = 0
  · simp [hr0, radialDouble_zero]
  · unfold radialDouble direction
    simp only [norm_smul, Real.norm_eq_abs, abs_of_nonneg hr, mul_inv_rev,
      smul_smul, smul_mul_assoc, mul_smul_comm]
    congr 1
    field_simp

theorem radialDouble_unit (q : Q) : radialDouble (q : ℍ) = ((q * q : Q) : ℍ) := by
  simp only [radialDouble, direction, unit_norm, inv_one, one_smul]
  rfl

/-- Haar uniqueness transfers the metric Hausdorff image estimate to the
actual Euclidean volume; the unknown proportionality cancels from the bound. -/
theorem volume_image_bound (f : ℍ → ℍ) (hf : LipschitzWith 3 f) (s : Set ℍ) :
    volume (f '' s) ≤ 81 * volume s := by
  let H : Measure ℍ := Measure.hausdorffMeasure (Module.finrank ℝ ℍ)
  have hv := Measure.isAddLeftInvariant_eq_smul (volume : Measure ℍ) H
  have hh := hf.hausdorffMeasure_image_le
    (d := (Module.finrank ℝ ℍ : ℝ)) (by positivity) s
  rw [Quaternion.finrank_eq_four, ENNReal.rpow_natCast] at hh
  have hh' : H (f '' s) ≤ 81 * H s := by
    norm_num only [ENNReal.coe_ofNat, show (3 : ℝ≥0∞) ^ 4 = 81 by norm_num] at hh
    simpa only [H, Quaternion.finrank_eq_four] using hh
  rw [hv, Measure.smul_apply, Measure.smul_apply]
  simp only [ENNReal.smul_def, smul_eq_mul]
  calc
    _ ≤ _ := mul_le_mul_right hh' _
    _ = _ := by ac_rfl

theorem radialDouble_volume (s : Set ℍ) :
    volume (radialDouble '' s) ≤ 81 * volume s :=
  volume_image_bound radialDouble radialDouble_lipschitz s

end
end UnifiedTheory.Clay.YangMills.QuaternionRadialDoubling
