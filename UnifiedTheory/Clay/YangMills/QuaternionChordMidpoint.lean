/- Normalized quaternion midpoints stay in a small chord cap and are
exact symmetric group rotations. No coordinate or measure change is used. -/
import UnifiedTheory.Clay.YangMills.QuaternionDefectCurvature

set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace UnifiedTheory.Clay.YangMills.QuaternionChordMidpoint
noncomputable section
open WilsonSlabOperator QuaternionSymmetricChange
open scoped Quaternion RealInnerProductSpace

theorem sum_ne_zero (b c z : Q) (ε : ℝ) (hε : ε ^ 2 < 2)
    (hb : ‖(b : ℍ) - (z : ℍ)‖ ≤ ε) (hc : ‖(c : ℍ) - (z : ℍ)‖ ≤ ε) :
    (b : ℍ) + (c : ℍ) ≠ 0 := by
  have hb2 := sq_le_sq₀ (norm_nonneg _) ((norm_nonneg _).trans hb) |>.mpr hb
  have hc2 := sq_le_sq₀ (norm_nonneg _) ((norm_nonneg _).trans hc) |>.mpr hc
  simp only [norm_sub_sq_real, unit_norm] at hb2 hc2
  intro hz
  have hi := congrArg (fun x : ℍ => ⟪x, (z : ℍ)⟫) hz
  simp only [inner_add_left, inner_zero_left] at hi
  nlinarith

def midpoint (b c : Q) (h : (b : ℍ) + (c : ℍ) ≠ 0) : Q :=
  SU2HaarTilt.orientation ((b : ℍ) + (c : ℍ)) h

theorem midpoint_sum (b c : Q) (h : (b : ℍ) + (c : ℍ) ≠ 0) :
    (b : ℍ) + (c : ℍ) = ‖(b : ℍ) + (c : ℍ)‖ • (midpoint b c h : ℍ) :=
  SU2HaarTilt.orientation_decomposition _ h

theorem midpoint_inner (b c : Q) (h : (b : ℍ) + (c : ℍ) ≠ 0) :
    2 * ⟪(b : ℍ), (midpoint b c h : ℍ)⟫ = ‖(b : ℍ) + (c : ℍ)‖ := by
  have hp : 0 < ‖(b : ℍ) + (c : ℍ)‖ := norm_pos_iff.mpr h
  have hi := congrArg (fun x : ℍ => ⟪(b : ℍ), x⟫) (midpoint_sum b c h)
  simp only [inner_add_right, real_inner_self_eq_norm_sq, real_inner_smul_right,
    unit_norm] at hi
  have hn := norm_add_sq_real (b : ℍ) (c : ℍ)
  simp only [unit_norm] at hn
  nlinarith

/-- The two endpoints are literal opposite left rotations of their midpoint. -/
theorem midpoint_symmetric (b c : Q) (h : (b : ℍ) + (c : ℍ) ≠ 0) :
    (b * (midpoint b c h)⁻¹)⁻¹ * midpoint b c h = c := by
  let m := midpoint b c h
  let a := b * m⁻¹
  have hap : a * m = b := by dsimp [a]; group
  have hre : 2 * (a : ℍ).re = ‖(b : ℍ) + (c : ℍ)‖ := by
    simpa only [a, Quaternion.inner_def] using midpoint_inner b c h
  have hs : ((a * m : Q) : ℍ) + ((a⁻¹ * m : Q) : ℍ) =
      (2 * (a : ℍ).re) • (m : ℍ) := by
    change (a : ℍ) * (m : ℍ) + star (a : ℍ) * (m : ℍ) = _
    rw [← add_mul, Quaternion.self_add_star']
    exact (Algebra.smul_def (2 * (a : ℍ).re) (m : ℍ)).symm
  rw [hap, hre, ← midpoint_sum b c h] at hs
  exact Subtype.ext (add_left_cancel hs)

theorem midpoint_cap (b c z : Q) (ε : ℝ) (hε : ε ^ 2 < 2)
    (hb : ‖(b : ℍ) - (z : ℍ)‖ ≤ ε) (hc : ‖(c : ℍ) - (z : ℍ)‖ ≤ ε)
    (h : (b : ℍ) + (c : ℍ) ≠ 0) :
    ‖(midpoint b c h : ℍ) - (z : ℍ)‖ ≤ ε := by
  have he : 0 ≤ ε := (norm_nonneg _).trans hb
  have hb2 := (sq_le_sq₀ (norm_nonneg _) he).mpr hb
  have hc2 := (sq_le_sq₀ (norm_nonneg _) he).mpr hc
  simp only [norm_sub_sq_real, unit_norm] at hb2 hc2
  have hi := congrArg (fun x : ℍ => ⟪x, (z : ℍ)⟫) (midpoint_sum b c h)
  simp only [inner_add_left, real_inner_smul_left] at hi
  have hn : ‖(b : ℍ) + (c : ℍ)‖ ≤ 2 := by
    simpa only [unit_norm, one_add_one_eq_two] using norm_add_le (b : ℍ) (c : ℍ)
  have hp : 0 < ‖(b : ℍ) + (c : ℍ)‖ := norm_pos_iff.mpr h
  have him : 0 ≤ ⟪(midpoint b c h : ℍ), (z : ℍ)⟫ := by
    nlinarith
  apply (sq_le_sq₀ (norm_nonneg _) he).mp
  rw [norm_sub_sq_real, unit_norm, unit_norm]
  nlinarith

theorem midpoint_self (b : Q) (h : (b : ℍ) + (b : ℍ) ≠ 0) : midpoint b b h = b := by
  have hh := midpoint_cap b b b 0 (by norm_num) (by simp) (by simp) h
  exact Subtype.ext (sub_eq_zero.mp (norm_eq_zero.mp (le_antisymm hh (norm_nonneg _))))

theorem midpoint_chord (b c : Q) (h : (b : ℍ) + (c : ℍ) ≠ 0) :
    ‖(b : ℍ) - (c : ℍ)‖ ^ 2 ≤ 4 * ‖(b : ℍ) - (midpoint b c h : ℍ)‖ ^ 2 := by
  have hi := midpoint_inner b c h
  have hn := norm_add_sq_real (b : ℍ) (c : ℍ)
  simp only [unit_norm] at hn
  simp only [norm_sub_sq_real, unit_norm]
  nlinarith [sq_nonneg (‖(b : ℍ) + (c : ℍ)‖ - 2)]

/-- Rotation cost is the actual squared chord distance to the midpoint. -/
theorem rotation_chord (b m : Q) :
    ‖((b * m⁻¹ : Q) : ℍ) - 1‖ = ‖(b : ℍ) - (m : ℍ)‖ := by
  have hm : (m : ℍ) * ((m⁻¹ : Q) : ℍ) = 1 := by
    change ((m * m⁻¹ : Q) : ℍ) = 1
    rw [mul_inv_cancel]
    rfl
  change ‖(b : ℍ) * ((m⁻¹ : Q) : ℍ) - 1‖ = _
  rw [← hm, ← sub_mul, norm_mul, unit_norm, mul_one]

end
end UnifiedTheory.Clay.YangMills.QuaternionChordMidpoint
