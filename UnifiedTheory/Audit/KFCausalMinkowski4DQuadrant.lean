/-
  Audit/KFCausalMinkowski4DQuadrant.lean — the quadrant passage (step 1):
  uniform linear bounds on the two boundary lines

  From the kernel bounds:
  * `D1_bound_uniform`: |D1(ε,v)| ≤ a·(2v² + 2ε² + 3εv)·ε — the u-axis line of
    the rectangle identity dies linearly in ε, uniformly on 0 < v ≤ B;
  * `K_bound_uniform`: |𝒦(u,δ) + 1/6| ≤ a·(uδ² + u³ + (3/2)u²δ)·δ — the v-axis
    line converges to the −1/6 axis constant linearly in δ, uniformly on
    0 < u ≤ A.

  These are the rates that carry `corner4_rectangle_chain` to `(0,∞)²` by plain
  norm × strip-measure estimates — no dominated convergence.
-/
import Mathlib
import UnifiedTheory.Audit.KFCausalMinkowski4DKernelBounds

open Real
open UnifiedTheory.Audit.KFCausalMinkowski4DKernel
open UnifiedTheory.Audit.KFCausalMinkowski4DKernelBounds

namespace UnifiedTheory.Audit.KFCausalMinkowski4DQuadrant

/-- The `u`-axis line dies linearly: for `a ≥ 0`, `ε > 0`, `v ≠ 0`,
`|D1(ε,v)| ≤ a(2v² + 2ε² + 3ε|v|)·ε`. -/
theorem D1_bound_uniform (a ε v : ℝ) (ha : 0 ≤ a) (hε : 0 < ε) (hv : v ≠ 0) :
    |ε⁻¹ * G4 (a*ε^2*v^2) + ε * (v^2)⁻¹ * H4 (a*ε^2*v^2)
      - a*ε^2*v * K4d (a*ε^2*v^2)|
    ≤ a * (2*v^2 + 2*ε^2 + 3*ε*|v|) * ε := by
  have hz : 0 ≤ a*ε^2*v^2 := by positivity
  have h1 : |ε⁻¹ * G4 (a*ε^2*v^2)| ≤ 2*a*ε*v^2 := by
    rw [abs_mul, abs_of_pos (inv_pos.mpr hε)]
    calc ε⁻¹ * |G4 (a*ε^2*v^2)| ≤ ε⁻¹ * (2*(a*ε^2*v^2)) := by
          apply mul_le_mul_of_nonneg_left (G4_abs_le _ hz)
            (le_of_lt (inv_pos.mpr hε))
      _ = 2*a*ε*v^2 := by field_simp
  have h2 : |ε * (v^2)⁻¹ * H4 (a*ε^2*v^2)| ≤ 2*a*ε^3 := by
    have hv2 : (0:ℝ) < v^2 := by positivity
    rw [abs_mul, abs_mul, abs_of_pos hε, abs_of_pos (inv_pos.mpr hv2)]
    calc ε * (v^2)⁻¹ * |H4 (a*ε^2*v^2)| ≤ ε * (v^2)⁻¹ * (2*(a*ε^2*v^2)) := by
          apply mul_le_mul_of_nonneg_left (H4_abs_le _ hz) (by positivity)
      _ = 2*a*ε^3 := by field_simp
  have h3 : |a*ε^2*v * K4d (a*ε^2*v^2)| ≤ 3*a*ε^2*|v| := by
    rw [abs_mul]
    calc |a*ε^2*v| * |K4d (a*ε^2*v^2)| ≤ |a*ε^2*v| * 3 :=
          mul_le_mul_of_nonneg_left (K4d_abs_le _ hz) (abs_nonneg _)
      _ = 3*a*ε^2*|v| := by
          rw [abs_mul, abs_mul, abs_of_nonneg ha, abs_of_nonneg (sq_nonneg ε)]
          ring
  have hsum : a * (2*v^2 + 2*ε^2 + 3*ε*|v|) * ε
      = 2*a*ε*v^2 + 2*a*ε^3 + 3*a*ε^2*|v| := by ring
  rw [abs_le]
  constructor
  · linarith [h1, h2, h3, neg_abs_le (ε⁻¹ * G4 (a*ε^2*v^2)),
      neg_abs_le (ε * (v^2)⁻¹ * H4 (a*ε^2*v^2)),
      le_abs_self (a*ε^2*v * K4d (a*ε^2*v^2))]
  · linarith [h1, h2, h3, le_abs_self (ε⁻¹ * G4 (a*ε^2*v^2)),
      le_abs_self (ε * (v^2)⁻¹ * H4 (a*ε^2*v^2)),
      neg_abs_le (a*ε^2*v * K4d (a*ε^2*v^2))]

/-- The `v`-axis line converges linearly to the axis constant: for `a ≥ 0`,
`δ > 0`, `u ≠ 0`, `|𝒦(u,δ) + 1/6| ≤ a(|u|δ² + |u|³ + (3/2)u²δ)·δ`. -/
theorem K_bound_uniform (a u δ : ℝ) (ha : 0 ≤ a) (hδ : 0 < δ) (hu : u ≠ 0) :
    |(δ/u) * J4 (a*u^2*δ^2) + u * δ⁻¹ * J4 (a*u^2*δ^2)
      - (1/2) * K4 (a*u^2*δ^2) + 1/6|
    ≤ a * (|u| * δ^2 + |u|^3 + (3/2)*u^2*δ) * δ := by
  have hz : 0 ≤ a*u^2*δ^2 := by positivity
  have hK40 : K4 0 = 1/3 := by
    unfold UnifiedTheory.Audit.KFCausalMinkowski4DKernel.K4
    norm_num
  have h1 : |(δ/u) * J4 (a*u^2*δ^2)| ≤ a * |u| * δ^3 := by
    rw [abs_mul, abs_div, abs_of_pos hδ]
    calc δ/|u| * |J4 (a*u^2*δ^2)| ≤ δ/|u| * (a*u^2*δ^2) := by
          apply mul_le_mul_of_nonneg_left (J4_abs_le _ hz) (by positivity)
      _ = a * |u| * δ^3 := by
          rw [div_mul_eq_mul_div, div_eq_iff (abs_ne_zero.mpr hu),
            show u^2 = |u|^2 from (sq_abs u).symm]
          ring
  have h2 : |u * δ⁻¹ * J4 (a*u^2*δ^2)| ≤ a * |u|^3 * δ := by
    rw [abs_mul, abs_mul, abs_of_pos (inv_pos.mpr hδ)]
    calc |u| * δ⁻¹ * |J4 (a*u^2*δ^2)| ≤ |u| * δ⁻¹ * (a*u^2*δ^2) := by
          apply mul_le_mul_of_nonneg_left (J4_abs_le _ hz) (by positivity)
      _ = a * |u|^3 * δ := by
          rw [show u^2 = |u|^2 from (sq_abs u).symm]
          field_simp
  have h3 : |(1/2) * K4 (a*u^2*δ^2) - 1/6| ≤ (3/2)*a*u^2*δ^2 := by
    have := K4_sub_K40_abs_le (a*u^2*δ^2) hz
    rw [hK40] at this
    calc |(1/2) * K4 (a*u^2*δ^2) - 1/6|
        = (1/2) * |K4 (a*u^2*δ^2) - 1/3| := by
          rw [← abs_of_nonneg (by norm_num : (0:ℝ) ≤ 1/2), ← abs_mul]
          congr 1
          ring
      _ ≤ (1/2) * (3*(a*u^2*δ^2)) := by
          apply mul_le_mul_of_nonneg_left this (by norm_num)
      _ = (3/2)*a*u^2*δ^2 := by ring
  have hsum : a * (|u| * δ^2 + |u|^3 + (3/2)*u^2*δ) * δ
      = a * |u| * δ^3 + a * |u|^3 * δ + (3/2)*a*u^2*δ^2 := by ring
  rw [abs_le]
  constructor
  · linarith [h1, h2, h3, neg_abs_le ((δ/u) * J4 (a*u^2*δ^2)),
      neg_abs_le (u * δ⁻¹ * J4 (a*u^2*δ^2)),
      le_abs_self ((1/2) * K4 (a*u^2*δ^2) - 1/6)]
  · linarith [h1, h2, h3, le_abs_self ((δ/u) * J4 (a*u^2*δ^2)),
      le_abs_self (u * δ⁻¹ * J4 (a*u^2*δ^2)),
      neg_abs_le ((1/2) * K4 (a*u^2*δ^2) - 1/6)]

#print axioms D1_bound_uniform
#print axioms K_bound_uniform

end UnifiedTheory.Audit.KFCausalMinkowski4DQuadrant
