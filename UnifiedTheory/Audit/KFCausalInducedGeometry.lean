/-
  Algebra and inequality support for INDUCED_GEOMETRY_INTERACTION.md.
  The Gaussian determinant and spectral arguments are analytic suppliers,
  not a formalization of the interacting quantum field theory.
-/
import UnifiedTheory.Audit.KFCausalFiniteGapFeedback

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Audit.KFCausalInducedGeometry
noncomputable section

theorem reference_reorganization (base change theta occupied : ℝ) :
    base + theta * change + (occupied - theta) * change = base + occupied * change := by ring

theorem midpoint_path_coordinates (x y z : ℝ) :
    ((x ^ 2 + y ^ 2 + z ^ 2) + ((x + y) ^ 2 + y ^ 2 + (y + z) ^ 2)) / 2 =
      ((x + z) ^ 2 + (x - z) ^ 2) / 2 + 2 * y ^ 2 + (x + z) * y := by ring

theorem midpoint_sum_of_squares (u v y : ℝ) :
    4 * ((((u ^ 2 + v ^ 2) / 2 + 2 * y ^ 2 + u * y) ^ 2) -
      3 * (y ^ 2 + u * y) ^ 2) =
      (u ^ 2 + 2 * u * y - 2 * y ^ 2) ^ 2 + 2 * v ^ 2 * (u + y) ^ 2 +
        6 * v ^ 2 * y ^ 2 + v ^ 4 := by ring

theorem midpoint_squared_bound (u v y : ℝ) :
    3 * (y ^ 2 + u * y) ^ 2 ≤
      ((u ^ 2 + v ^ 2) / 2 + 2 * y ^ 2 + u * y) ^ 2 := by
  have hid := midpoint_sum_of_squares u v y
  have h1 : 0 ≤ 2 * v ^ 2 * (u + y) ^ 2 := by positivity
  have h2 : 0 ≤ 6 * v ^ 2 * y ^ 2 := by positivity
  nlinarith [sq_nonneg (u ^ 2 + 2 * u * y - 2 * y ^ 2), pow_nonneg (sq_nonneg v) 2]

theorem bounded_switch_deviation (z : ℝ) (hz : 0 ≤ z ∧ z ≤ 1) :
    |2 * z - 1| ≤ 1 := by
  apply abs_le.mpr
  constructor <;> linarith [hz.1, hz.2]

theorem midpoint_relative_bound (m h : ℝ) (hm : 0 ≤ m) (hs : 3 * h ^ 2 ≤ m ^ 2) :
    Real.sqrt 3 * |h| ≤ m := by
  have hroot : (Real.sqrt 3) ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have ha : |h| ^ 2 = h ^ 2 := sq_abs h
  have hp : 0 ≤ Real.sqrt 3 * |h| := by positivity
  have hid : (Real.sqrt 3 * |h|) ^ 2 = 3 * h ^ 2 := by
    rw [mul_pow, hroot, ha]
  nlinarith

theorem midpoint_radius_less_than_one : 1 / Real.sqrt 3 < 1 := by
  have hs := Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)
  have hp := Real.sqrt_nonneg (3 : ℝ)
  have hgt : (1 : ℝ) < Real.sqrt 3 := by nlinarith
  apply (div_lt_iff₀ (by linarith : 0 < Real.sqrt 3)).mpr
  linarith

theorem angular_kernel_identity (t : ℝ) :
    5 - 35 * t + 63 * t ^ 2 = 63 * (t - 5 / 18) ^ 2 + 5 / 36 := by ring

theorem angular_kernel_positive (t : ℝ) : 0 < 5 - 35 * t + 63 * t ^ 2 := by
  rw [angular_kernel_identity]
  positivity

theorem two_particle_threshold {E : Type*} [NormedAddCommGroup E] (p q : E) :
    ‖p + q‖ ≤ ‖p‖ + ‖q‖ := norm_add_le p q

/-- The scalar matrix-element consequence of commuting with a parity symmetry. -/
theorem parity_selection_rule (s t matrixElement : ℂ) (hst : s ≠ t)
    (hcomm : s * matrixElement = t * matrixElement) : matrixElement = 0 := by
  have hzero : (s - t) * matrixElement = 0 := by rw [sub_mul, hcomm, sub_self]
  exact (mul_eq_zero.mp hzero).resolve_left (sub_ne_zero.mpr hst)

theorem spectral_fourth_power_scaling (coefficient frequency scale : ℝ) :
    coefficient * (scale * frequency) ^ 4 = scale ^ 4 * (coefficient * frequency ^ 4) := by ring

#print axioms reference_reorganization
#print axioms midpoint_path_coordinates
#print axioms midpoint_sum_of_squares
#print axioms midpoint_squared_bound
#print axioms bounded_switch_deviation
#print axioms midpoint_relative_bound
#print axioms midpoint_radius_less_than_one
#print axioms angular_kernel_identity
#print axioms angular_kernel_positive
#print axioms two_particle_threshold
#print axioms parity_selection_rule
#print axioms spectral_fourth_power_scaling

end
end UnifiedTheory.Audit.KFCausalInducedGeometry
