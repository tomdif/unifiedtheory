/-
  Scalar support for BOND_TENSOR_CONSTRAINTS.md. The tensor field, canonical
  brackets, and four constraints are explicit suppliers. No microscopic
  derivation of a tensor phase or nonlinear gravity is asserted here.
-/
import UnifiedTheory.Audit.KFCausalEntangledAcoustic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Audit.KFCausalBondTensor
noncomputable section

theorem six_bond_tensor_encoding (x y z xx yy zz xy yz zx : ℝ) :
    (xx - xy - zx) * x ^ 2 + (yy - xy - yz) * y ^ 2 +
      (zz - yz - zx) * z ^ 2 + xy * (x + y) ^ 2 +
      yz * (y + z) ^ 2 + zx * (z + x) ^ 2 =
    xx * x ^ 2 + yy * y ^ 2 + zz * z ^ 2 +
      2 * xy * x * y + 2 * yz * y * z + 2 * zx * z * x := by ring

theorem positive_isotropic_bond_reference (a d x y z : ℝ) :
    a * (x ^ 2 + y ^ 2 + z ^ 2) +
      d * ((x + y) ^ 2 + (x - y) ^ 2 + (y + z) ^ 2 +
        (y - z) ^ 2 + (z + x) ^ 2 + (z - x) ^ 2) =
      (a + 4 * d) * (x ^ 2 + y ^ 2 + z ^ 2) := by ring

theorem shear_bond_difference (s x y : ℝ) :
    (s / 2) * (x + y) ^ 2 - (s / 2) * (x - y) ^ 2 = 2 * s * x * y := by ring

theorem shear_weights_stay_positive (d s : ℝ) (hs : |s| < 2 * d) :
    0 < d + s / 2 ∧ 0 < d - s / 2 := by
  have h := abs_lt.mp hs
  constructor <;> linarith [h.1, h.2]

theorem scalar_constraint_annihilates_wavevector (x y z : ℝ) :
    (x ^ 2 - (x ^ 2 + y ^ 2 + z ^ 2)) * x + x * y * y + x * z * z = 0 := by ring

theorem spatial_gauge_coefficients (a b d : ℝ)
    (h1 : b + 2 = 0) (h2 : b + d = 0) (h3 : 2 * a + d = 0) :
    a = -1 ∧ b = -2 ∧ d = 2 := by
  constructor
  · linarith
  constructor <;> linarith

theorem scalar_constraint_fixes_kinetic_trace (alpha q : ℝ)
    (hq : q ≠ 0) (h : -2 * q ^ 2 * (1 + 2 * alpha) = 0) : alpha = -1 / 2 := by
  have hp := sq_pos_of_ne_zero hq
  nlinarith

def diagonalK (x y z : ℝ) : ℝ := x ^ 2 + y ^ 2 + z ^ 2 - (x + y + z) ^ 2 / 2

theorem scalar_gauge_kinetic_variation (x y z a q : ℝ) :
    diagonalK (x - a * q ^ 2) (y - a * q ^ 2) z - diagonalK x y z =
      2 * a * q ^ 2 * z := by unfold diagonalK; ring

theorem transverse_traceless_energy (a b : ℝ) :
    diagonalK a (-a) 0 + 2 * b ^ 2 = 2 * (a ^ 2 + b ^ 2) := by
  unfold diagonalK
  ring

theorem trace_momentum_penalty_identity (J U q t : ℝ) :
    J / 2 * diagonalK t t t + U / 2 * (q * t) ^ 2 =
      t ^ 2 / 2 * (-3 * J / 2 + U * q ^ 2) := by unfold diagonalK; ring

theorem finite_penalty_negative_direction (J U q : ℝ)
    (h : U * q ^ 2 < 3 * J / 2) : -3 * J / 2 + U * q ^ 2 < 0 := by linarith

theorem trace_coordinate_penalty_identity (g W q t : ℝ) :
    g / 2 * (-2 * q ^ 2 * t ^ 2) + W / 2 * (-2 * q ^ 2 * t) ^ 2 =
      t ^ 2 * (-g * q ^ 2 + 2 * W * q ^ 4) := by ring

theorem softened_mode_relative_correction (c a q : ℝ) (hq : q ≠ 0) :
    (c ^ 2 * q ^ 2 + a * q ^ 4) / q ^ 2 - c ^ 2 = a * q ^ 2 := by
  field_simp
  ring

theorem curvature_square_cubic_frequency (J g q : ℝ) :
    (J * q ^ 2) * (g * q ^ 4) = J * g * (q ^ 3) ^ 2 := by ring

theorem conserved_free_sources_allow_unequal_couplings (a b source1 source2 : ℝ)
    (h1 : source1 = 0) (h2 : source2 = 0) : a * source1 + b * source2 = 0 := by
  rw [h1, h2]
  ring

#print axioms six_bond_tensor_encoding
#print axioms positive_isotropic_bond_reference
#print axioms shear_bond_difference
#print axioms shear_weights_stay_positive
#print axioms scalar_constraint_annihilates_wavevector
#print axioms spatial_gauge_coefficients
#print axioms scalar_constraint_fixes_kinetic_trace
#print axioms scalar_gauge_kinetic_variation
#print axioms transverse_traceless_energy
#print axioms trace_momentum_penalty_identity
#print axioms finite_penalty_negative_direction
#print axioms trace_coordinate_penalty_identity
#print axioms softened_mode_relative_correction
#print axioms curvature_square_cubic_frequency
#print axioms conserved_free_sources_allow_unequal_couplings

end
end UnifiedTheory.Audit.KFCausalBondTensor
