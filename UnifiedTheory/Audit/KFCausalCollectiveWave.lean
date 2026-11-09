/-
  Algebra and error support for COLLECTIVE_WAVE_SPACETIME.md.
  The large-spin, monotone-form, cell-band, and continuum constructions
  are analytic suppliers in the note, not fully formalized field theory.
-/
import UnifiedTheory.Audit.KFCausalLocalClock
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Audit.KFCausalCollectiveWave
noncomputable section

theorem spin_half_normalization (kappa : ℝ) : kappa / (1 / 2) = 2 * kappa := by ring

/-- The scalar bound used on the two Holstein-Primakoff shift coefficients. -/
theorem hp_square_root_error (x : ℝ) (h0 : 0 ≤ x) (h1 : x ≤ 1) :
    0 ≤ 1 - Real.sqrt (1 - x) ∧ 1 - Real.sqrt (1 - x) ≤ x := by
  have hs := Real.sqrt_nonneg (1 - x)
  have hsquare := Real.sq_sqrt (by linarith : 0 ≤ 1 - x)
  have hupper : Real.sqrt (1 - x) ≤ 1 := by nlinarith
  have hproduct := mul_nonneg hs (by linarith : 0 ≤ 1 - Real.sqrt (1 - x))
  constructor <;> nlinarith

theorem hp_bond_coefficient_bound (m : ℝ) (hm : 0 ≤ m) :
    3 * m ^ 2 + 2 * m ≤ 3 * (m + 1) ^ 2 := by nlinarith

/-- Degree six fixes the kinetic coefficient and the geometry-independent shift. -/
theorem degree_six_fluctuation_identity (kappa q2 pi2 cross vertices : ℝ) :
    kappa * (6 * ((q2 + pi2 - vertices) / 2) - cross) =
      3 * kappa * pi2 + (kappa / 2) * (6 * q2 - 2 * cross) - 3 * kappa * vertices := by ring

/-- Conserved energy controls fast-geometry leakage at every time. -/
theorem fast_geometry_leakage (Lambda gap leakage energy : ℝ)
    (hL : 0 < Lambda) (hg : 0 < gap) (he : Lambda * gap * leakage ≤ energy) :
    leakage ≤ energy / (Lambda * gap) := by
  apply (le_div_iff₀ (mul_pos hL hg)).mpr
  nlinarith [he]

/-- Elimination of canonical momentum gives the positive temporal susceptibility. -/
theorem temporal_action_coefficient (kappa pi velocity : ℝ)
    (hk : kappa ≠ 0) (hv : velocity = 6 * kappa * pi) :
    pi * velocity - 3 * kappa * pi ^ 2 = velocity ^ 2 / (12 * kappa) := by
  rw [hv]
  field_simp
  ring

theorem collective_frequency_squared (kappa energy : ℝ)
    (hk : 0 ≤ kappa) (he : 0 ≤ energy) :
    (Real.sqrt (6 * kappa * energy)) ^ 2 = 6 * kappa * energy := by
  apply Real.sq_sqrt
  positivity

/-- Divide the squared-frequency error only where the frequency sum is positive. -/
theorem frequency_difference_bound (x y d error : ℝ)
    (hd : 0 < d) (hden : d ≤ x + y) (herr : |x ^ 2 - y ^ 2| ≤ error) :
    |x - y| ≤ error / d := by
  apply (le_div_iff₀ hd).mpr
  calc
    |x - y| * d ≤ |x - y| * (x + y) := mul_le_mul_of_nonneg_left hden (abs_nonneg _)
    _ = |x ^ 2 - y ^ 2| := by
      rw [← abs_of_nonneg (by linarith : 0 ≤ x + y), ← abs_mul]
      congr 1
      ring
    _ ≤ error := herr

theorem wave_cosine_error (t x y : ℝ) :
    |Real.cos (t * x) - Real.cos (t * y)| ≤ |t| * |x - y| := by
  calc
    _ ≤ |t * x - t * y| := Real.abs_cos_sub_cos_le _ _
    _ = |t| * |x - y| := by rw [← mul_sub, abs_mul]

theorem sound_speed_squared_bounds (kappa D : ℝ)
    (hk : 0 ≤ kappa) (hD : kappa / 4 ≤ D ∧ D ≤ 4 * kappa) :
    (3 / 2) * kappa ^ 2 ≤ 6 * kappa * D ∧ 6 * kappa * D ≤ 24 * kappa ^ 2 := by
  have hlow := mul_le_mul_of_nonneg_left hD.1 hk
  have hhigh := mul_le_mul_of_nonneg_left hD.2 hk
  constructor <;> nlinarith

theorem acoustic_characteristic_null (omega kx ky kz kappa Dx Dy Dz : ℝ)
    (hw : omega ^ 2 = 6 * kappa * (Dx * kx ^ 2 + Dy * ky ^ 2 + Dz * kz ^ 2)) :
    -omega ^ 2 + (6 * kappa * Dx) * kx ^ 2 + (6 * kappa * Dy) * ky ^ 2 +
      (6 * kappa * Dz) * kz ^ 2 = 0 := by
  rw [hw]
  ring

#print axioms spin_half_normalization
#print axioms hp_square_root_error
#print axioms hp_bond_coefficient_bound
#print axioms degree_six_fluctuation_identity
#print axioms fast_geometry_leakage
#print axioms temporal_action_coefficient
#print axioms collective_frequency_squared
#print axioms frequency_difference_bound
#print axioms wave_cosine_error
#print axioms sound_speed_squared_bounds
#print axioms acoustic_characteristic_null

end
end UnifiedTheory.Audit.KFCausalCollectiveWave
