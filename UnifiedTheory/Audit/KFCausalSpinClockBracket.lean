/-
  Support for SPIN_CLOCK_BRACKET.md. The spin-field operator-domain argument,
  exponential-tail estimate, and physical continuum are separate suppliers.
  No complete gravitational constraint algebra is asserted here.
-/
import UnifiedTheory.Audit.KFCausalGravityConstraint
import Mathlib.LinearAlgebra.Matrix.Trace

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Audit.KFCausalSpinClockBracket
noncomputable section

theorem symmetric_dyad_norm (x y z u v w : ℝ) :
    (x * u) ^ 2 + (y * v) ^ 2 + (z * w) ^ 2 +
      ((x * v + y * u) ^ 2 + (y * w + z * v) ^ 2 + (z * u + x * w) ^ 2) / 2 =
      ((x ^ 2 + y ^ 2 + z ^ 2) * (u ^ 2 + v ^ 2 + w ^ 2) +
        (x * u + y * v + z * w) ^ 2) / 2 := by ring

theorem spin_stiffness_margin (kappa gamma : ℝ) (h : |gamma| < kappa) :
    0 < kappa - |gamma| := by linarith

theorem onsite_lapse_cancellation {n : Type*} [Fintype n]
    (A B : Matrix n n ℂ) (s t : ℂ) :
    (s * t) • (A * B - B * A) + (t * s) • (B * A - A * B) = 0 := by
  rw [mul_comm t s, ← smul_add]
  simp

theorem local_mass_cancels (n m mass : ℝ) :
    m * (mass ^ 2 * n) - n * (mass ^ 2 * m) = 0 := by ring

theorem commutator_trace_zero {n : Type*} [Fintype n]
    (A B : Matrix n n ℂ) : Matrix.trace (A * B - B * A) = 0 := by
  rw [Matrix.trace_sub, Matrix.trace_mul_comm]
  simp

theorem diagonal_commutator_zero {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℂ) (c : n → ℂ) (i : n) :
    (A * Matrix.diagonal c - Matrix.diagonal c * A) i i = 0 := by
  simp [Matrix.mul_diagonal, Matrix.diagonal_mul, mul_comm]

theorem finite_metric_dilation_trace_obstruction {n : Type*} [Fintype n]
    (G C : Matrix n n ℂ) (s : ℂ)
    (hs : s ≠ 0) (hC : Matrix.trace C ≠ 0) :
    Complex.I • (G * C - C * G) ≠ s • C := by
  intro h
  have ht := congrArg Matrix.trace h
  simp only [Matrix.trace_smul, commutator_trace_zero, smul_eq_mul, mul_zero] at ht
  exact (mul_ne_zero hs hC) ht.symm

theorem compression_leakage_identity {A : Type*} [Ring A] (P X Y : A) :
    P * (X * Y - Y * X) * P - (P * X * P * Y * P - P * Y * P * X * P) =
      P * X * (1 - P) * Y * P - P * Y * (1 - P) * X * P := by
  noncomm_ring

theorem isometry_scaling_obstruction {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (T : E →ₗᵢ[ℝ] E) (x : E) (s : ℝ) :
    abs (1 - abs s) * ‖x‖ ≤ ‖T x - s • x‖ := by
  have h := abs_norm_sub_norm_le (T x) (s • x)
  rw [T.norm_map, norm_smul, Real.norm_eq_abs] at h
  have he : ‖x‖ - |s| * ‖x‖ = (1 - |s|) * ‖x‖ := by ring
  rw [he, abs_mul, abs_of_nonneg (norm_nonneg x)] at h
  exact h

theorem stencil_error_factorization (c a e g d f : ℝ) :
    c * ((a ^ 2 * e) * (g + a ^ 2 * d) + f * (a ^ 2 * d)) =
      c * a ^ 2 * (e * (g + a ^ 2 * d) + f * d) := by ring

theorem logarithmic_dilation_defect (sigma ell c d tail : ℝ) (he : ell ≠ 0) :
    (2 * sigma / ell) * (-ell * c + ell * d * tail) + 2 * sigma * c =
      2 * sigma * d * tail := by
  field_simp
  ring

theorem symmetric_block_dressing (b w : ℝ) (hw : w ≠ 0) :
    (b * w) * (1 / w) = b := by field_simp

#print axioms symmetric_dyad_norm
#print axioms spin_stiffness_margin
#print axioms onsite_lapse_cancellation
#print axioms local_mass_cancels
#print axioms commutator_trace_zero
#print axioms diagonal_commutator_zero
#print axioms finite_metric_dilation_trace_obstruction
#print axioms compression_leakage_identity
#print axioms isometry_scaling_obstruction
#print axioms stencil_error_factorization
#print axioms logarithmic_dilation_defect
#print axioms symmetric_block_dressing

end
end UnifiedTheory.Audit.KFCausalSpinClockBracket
