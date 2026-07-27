/-
  Audit/KFCausalMinkowski4DKernelBounds.lean — explicit kernel bounds for the
  quadrant passage

  The rectangle → quadrant limits need no dominated convergence: every boundary
  object vanishes (or converges) at an explicit LINEAR rate, driven by these
  bounds (all for `z ≥ 0`, all from `e^z ≥ 1 + z + z²/2 + z³/6`):

    |J4(z)| ≤ z,     |G4(z)| ≤ 2z,     |H4(z)| ≤ 2z,
    |K4d(z)| ≤ 3,    |K4(z) − K4(0)| ≤ 3z.

  Consequences (next file): |D1(ε,v)| ≤ a(2v² + 2ε² + 3εv)·ε — the u-axis line
  dies linearly in ε uniformly on v ≤ B; |𝒦(u,δ) + 1/6| ≤ a(uδ² + u³ + 3u²δ/2)·δ
  — the v-axis line converges to the −1/6 counterterm linearly in δ uniformly
  on u ≤ A.
-/
import Mathlib
import UnifiedTheory.Audit.KFCausalMinkowski4DKernel

open Real
open UnifiedTheory.Audit.KFCausalMinkowski4DKernel

namespace UnifiedTheory.Audit.KFCausalMinkowski4DKernelBounds

/-- The cubic exponential lower bound, `z ≥ 0`: `1 + z + z²/2 + z³/6 ≤ e^z`. -/
theorem exp_cubic_lower (z : ℝ) (hz : 0 ≤ z) :
    1 + z + z^2/2 + z^3/6 ≤ Real.exp z := by
  have h := Real.sum_le_exp_of_nonneg hz 4
  simp [Finset.sum_range_succ] at h
  nlinarith [h]

theorem J4_abs_le (z : ℝ) (hz : 0 ≤ z) : |J4 z| ≤ z := by
  unfold UnifiedTheory.Audit.KFCausalMinkowski4DKernel.J4
  have he : 1 + z ≤ Real.exp z := by linarith [Real.add_one_le_exp z]
  have hep : 0 < Real.exp z := Real.exp_pos z
  rw [Real.exp_neg, abs_mul, abs_mul]
  rw [abs_of_nonneg (by norm_num : (0:ℝ) ≤ 1/3), abs_of_pos (inv_pos.mpr hep)]
  have habs : |z - z^2| ≤ z * (1 + z) := by
    rw [abs_le]
    constructor <;> nlinarith [sq_nonneg z]
  calc 1/3 * (Real.exp z)⁻¹ * |z - z^2|
      ≤ 1/3 * (Real.exp z)⁻¹ * (z * (1 + z)) := by
        apply mul_le_mul_of_nonneg_left habs
        positivity
    _ ≤ z := by
        have hkey : z * (1 + z) ≤ z * Real.exp z :=
          mul_le_mul_of_nonneg_left he hz
        have h1 : 1/3 * (Real.exp z)⁻¹ * (z * (1 + z))
            ≤ 1/3 * (Real.exp z)⁻¹ * (z * Real.exp z) := by
          apply mul_le_mul_of_nonneg_left hkey
          positivity
        calc 1/3 * (Real.exp z)⁻¹ * (z * (1 + z))
            ≤ 1/3 * (Real.exp z)⁻¹ * (z * Real.exp z) := h1
          _ = z/3 := by
              field_simp
          _ ≤ z := by linarith

theorem G4_abs_le (z : ℝ) (hz : 0 ≤ z) : |G4 z| ≤ 2*z := by
  have hexpand : G4 z = (1/3) * Real.exp (-z) * (3*z - 7*z^2 + 2*z^3) := by
    unfold UnifiedTheory.Audit.KFCausalMinkowski4DKernel.G4
      UnifiedTheory.Audit.KFCausalMinkowski4DKernel.J4
      UnifiedTheory.Audit.KFCausalMinkowski4DKernel.J4d
    ring
  have he := exp_cubic_lower z hz
  have hep : 0 < Real.exp z := Real.exp_pos z
  rw [hexpand, Real.exp_neg, abs_mul, abs_mul]
  rw [abs_of_nonneg (by norm_num : (0:ℝ) ≤ 1/3), abs_of_pos (inv_pos.mpr hep)]
  have habs : |3*z - 7*z^2 + 2*z^3| ≤ z * (3 + 7*z + 2*z^2) := by
    rw [abs_le]
    constructor <;> nlinarith [sq_nonneg z, mul_nonneg hz hz,
      mul_nonneg (mul_nonneg hz hz) hz]
  calc 1/3 * (Real.exp z)⁻¹ * |3*z - 7*z^2 + 2*z^3|
      ≤ 1/3 * (Real.exp z)⁻¹ * (z * (3 + 7*z + 2*z^2)) := by
        apply mul_le_mul_of_nonneg_left habs
        positivity
    _ ≤ 2*z := by
        have hkey : z * (3 + 7*z + 2*z^2) ≤ z * (6 * Real.exp z) := by
          apply mul_le_mul_of_nonneg_left ?_ hz
          nlinarith [he]
        have h1 : 1/3 * (Real.exp z)⁻¹ * (z * (3 + 7*z + 2*z^2))
            ≤ 1/3 * (Real.exp z)⁻¹ * (z * (6 * Real.exp z)) := by
          apply mul_le_mul_of_nonneg_left hkey
          positivity
        calc 1/3 * (Real.exp z)⁻¹ * (z * (3 + 7*z + 2*z^2))
            ≤ 1/3 * (Real.exp z)⁻¹ * (z * (6 * Real.exp z)) := h1
          _ = 2*z := by
              field_simp
              ring

theorem H4_abs_le (z : ℝ) (hz : 0 ≤ z) : |H4 z| ≤ 2*z := by
  have hexpand : H4 z = (1/3) * Real.exp (-z) * (z - 5*z^2 + 2*z^3) := by
    unfold UnifiedTheory.Audit.KFCausalMinkowski4DKernel.H4
      UnifiedTheory.Audit.KFCausalMinkowski4DKernel.J4
      UnifiedTheory.Audit.KFCausalMinkowski4DKernel.J4d
    ring
  have he := exp_cubic_lower z hz
  have hep : 0 < Real.exp z := Real.exp_pos z
  rw [hexpand, Real.exp_neg, abs_mul, abs_mul]
  rw [abs_of_nonneg (by norm_num : (0:ℝ) ≤ 1/3), abs_of_pos (inv_pos.mpr hep)]
  have habs : |z - 5*z^2 + 2*z^3| ≤ z * (1 + 5*z + 2*z^2) := by
    rw [abs_le]
    constructor <;> nlinarith [sq_nonneg z, mul_nonneg hz hz,
      mul_nonneg (mul_nonneg hz hz) hz]
  calc 1/3 * (Real.exp z)⁻¹ * |z - 5*z^2 + 2*z^3|
      ≤ 1/3 * (Real.exp z)⁻¹ * (z * (1 + 5*z + 2*z^2)) := by
        apply mul_le_mul_of_nonneg_left habs
        positivity
    _ ≤ 2*z := by
        have hkey : z * (1 + 5*z + 2*z^2) ≤ z * (6 * Real.exp z) := by
          apply mul_le_mul_of_nonneg_left ?_ hz
          nlinarith [he]
        have h1 : 1/3 * (Real.exp z)⁻¹ * (z * (1 + 5*z + 2*z^2))
            ≤ 1/3 * (Real.exp z)⁻¹ * (z * (6 * Real.exp z)) := by
          apply mul_le_mul_of_nonneg_left hkey
          positivity
        calc 1/3 * (Real.exp z)⁻¹ * (z * (1 + 5*z + 2*z^2))
            ≤ 1/3 * (Real.exp z)⁻¹ * (z * (6 * Real.exp z)) := h1
          _ = 2*z := by
              field_simp
              ring

theorem K4d_abs_le (z : ℝ) (hz : 0 ≤ z) : |K4d z| ≤ 3 := by
  unfold UnifiedTheory.Audit.KFCausalMinkowski4DKernel.K4d
  have he := exp_cubic_lower z hz
  have hep : 0 < Real.exp z := Real.exp_pos z
  rw [Real.exp_neg, abs_mul, abs_mul]
  rw [abs_of_nonneg (by norm_num : (0:ℝ) ≤ 1/3), abs_of_pos (inv_pos.mpr hep)]
  have habs : |3 - 12*z + 4*z^2| ≤ 3 + 12*z + 4*z^2 := by
    rw [abs_le]
    constructor <;> nlinarith [sq_nonneg z]
  calc 1/3 * (Real.exp z)⁻¹ * |3 - 12*z + 4*z^2|
      ≤ 1/3 * (Real.exp z)⁻¹ * (3 + 12*z + 4*z^2) := by
        apply mul_le_mul_of_nonneg_left habs
        positivity
    _ ≤ 3 := by
        have hkey : 3 + 12*z + 4*z^2 ≤ 9 * Real.exp z := by
          nlinarith [he, mul_nonneg (mul_nonneg hz hz) hz]
        have h1 : 1/3 * (Real.exp z)⁻¹ * (3 + 12*z + 4*z^2)
            ≤ 1/3 * (Real.exp z)⁻¹ * (9 * Real.exp z) := by
          apply mul_le_mul_of_nonneg_left hkey
          positivity
        calc 1/3 * (Real.exp z)⁻¹ * (3 + 12*z + 4*z^2)
            ≤ 1/3 * (Real.exp z)⁻¹ * (9 * Real.exp z) := h1
          _ = 3 := by
              field_simp
              ring

theorem K4_sub_K40_abs_le (z : ℝ) (hz : 0 ≤ z) : |K4 z - K4 0| ≤ 3*z := by
  have hmvt := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (f := K4) (f' := K4d) (C := 3) (s := Set.Ici (0:ℝ))
    (fun x hx => (K4_hasDerivAt x).hasDerivWithinAt)
    (fun x hx => by simpa [Real.norm_eq_abs] using K4d_abs_le x hx)
    (convex_Ici 0) (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr hz)
  rw [Real.norm_eq_abs, Real.norm_eq_abs, sub_zero, abs_of_nonneg hz] at hmvt
  exact hmvt

#print axioms J4_abs_le
#print axioms G4_abs_le
#print axioms H4_abs_le
#print axioms K4d_abs_le
#print axioms K4_sub_K40_abs_le

end UnifiedTheory.Audit.KFCausalMinkowski4DKernelBounds
