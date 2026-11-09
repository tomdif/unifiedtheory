/-
  Scalar support for COLLECTIVE_GEOMETRY_STABILITY.md.
  The rational network audit, Gaussian operator estimates, and variational
  arguments are separate suppliers; no full quantum phase is formalized.
-/
import UnifiedTheory.Audit.KFCausalInducedGeometry

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Audit.KFCausalGeometryStability
noncomputable section

theorem old_resistance_certificate (x y : ℝ) :
    713 * (x ^ 2 + y ^ 2) - (495 * x ^ 2 + 234 * x * y + 261 * y ^ 2) =
      117 * (x - y) ^ 2 + 101 * x ^ 2 + 335 * y ^ 2 := by ring

theorem new_resistance_certificate (x y : ℝ) :
    785 * (x ^ 2 + y ^ 2) - (495 * x ^ 2 - 90 * x * y + 261 * y ^ 2) =
      45 * (x + y) ^ 2 + 245 * x ^ 2 + 479 * y ^ 2 := by ring

theorem old_resistance_bound (x y : ℝ) :
    495 * x ^ 2 + 234 * x * y + 261 * y ^ 2 ≤ 713 * (x ^ 2 + y ^ 2) := by
  nlinarith [old_resistance_certificate x y, sq_nonneg (x - y), sq_nonneg x, sq_nonneg y]

theorem new_resistance_bound (x y : ℝ) :
    495 * x ^ 2 - 90 * x * y + 261 * y ^ 2 ≤ 785 * (x ^ 2 + y ^ 2) := by
  nlinarith [new_resistance_certificate x y, sq_nonneg (x + y), sq_nonneg x, sq_nonneg y]

theorem spin_variance_upper (m : ℝ) : m * (1 - m) ≤ 1 / 4 := by
  nlinarith [sq_nonneg (m - 1 / 2)]

theorem transverse_spin_curvature (L b t : ℝ)
    (hL : 0 ≤ L) (hb : 0 ≤ b) (ht : 0 < t) (hhalf : t ≤ 1 / 2) :
    4 * L * b ≤ L * b / (2 * t ^ 3) := by
  have hpow := pow_le_pow_left₀ ht.le hhalf 3
  have hcube : 8 * t ^ 3 ≤ 1 := by norm_num at hpow; linarith
  apply (le_div_iff₀ (by positivity : 0 < 2 * t ^ 3)).mpr
  calc
    4 * L * b * (2 * t ^ 3) = (L * b) * (8 * t ^ 3) := by ring
    _ ≤ (L * b) * 1 := mul_le_mul_of_nonneg_left hcube (mul_nonneg hL hb)
    _ = L * b := by ring

theorem total_curvature_margin (spin field L b C : ℝ)
    (hs : 4 * L * b ≤ spin) (hf : -C ≤ field) :
    4 * L * b - C ≤ spin + field := by linarith

theorem default_margin_positive : (27 : ℝ) / 20 < 8 / 5 - Real.sqrt 3 / 8 := by
  have hs := Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)
  have hp := Real.sqrt_nonneg (3 : ℝ)
  have hupper : Real.sqrt (3 : ℝ) < 2 := by nlinarith
  linarith

theorem fixed_point_residual_bound (distance residual q : ℝ)
    (hq : q < 1) (h : distance ≤ residual + q * distance) :
    distance ≤ residual / (1 - q) := by
  apply (le_div_iff₀ (by linarith : 0 < 1 - q)).mpr
  nlinarith

theorem euclidean_spectral_factor (energy frequency : ℝ) (he : 0 < energy) :
    2 * energy / (energy ^ 2 + frequency ^ 2) ≤ 2 / energy := by
  have hd : 0 < energy ^ 2 + frequency ^ 2 := by positivity
  apply (div_le_div_iff₀ hd he).mpr
  nlinarith [sq_nonneg frequency]

theorem intensive_trace_error (error coefficient trace C beta sites : ℝ)
    (ha : 0 ≤ coefficient) (hb : 0 < beta) (hN : 0 < sites)
    (he : |error| ≤ coefficient * trace) (ht : trace ≤ C * beta * sites / 2) :
    |error| / (beta * sites) ≤ coefficient * C / 2 := by
  apply (div_le_iff₀ (mul_pos hb hN)).mpr
  have hbound := mul_le_mul_of_nonneg_left ht ha
  nlinarith

theorem free_energy_from_log_partition_bound (logZ logZK scale epsilon : ℝ)
    (hs : 0 < scale) (he : |logZ - logZK| ≤ scale * epsilon) :
    |(-logZ) / scale - (-logZK / scale)| ≤ epsilon := by
  have hid : -logZ / scale - (-logZK / scale) = -(logZ - logZK) / scale := by ring
  rw [hid, abs_div, abs_neg, abs_of_pos hs]
  apply (div_le_iff₀ hs).mpr
  nlinarith

#print axioms old_resistance_certificate
#print axioms new_resistance_certificate
#print axioms old_resistance_bound
#print axioms new_resistance_bound
#print axioms spin_variance_upper
#print axioms transverse_spin_curvature
#print axioms total_curvature_margin
#print axioms default_margin_positive
#print axioms fixed_point_residual_bound
#print axioms euclidean_spectral_factor
#print axioms intensive_trace_error
#print axioms free_energy_from_log_partition_bound

end
end UnifiedTheory.Audit.KFCausalGeometryStability
