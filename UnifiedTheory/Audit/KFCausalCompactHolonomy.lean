/-
  Compact gauge-loop algebra and the flat determinant orientation.
  The full momentum decomposition, antiunitary spin matrices, and Kato ODE
  are proved analytically / audited separately in COMPACT_MEASURE_HOLONOMY.md.
  These results do not extend the interacting current to all compact fields.
-/
import UnifiedTheory.Audit.KFCausalSecondCohomology
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Audit.KFCausalCompactHolonomy
noncomputable section
open Matrix
open scoped BigOperators

section GaugeLoop
variable {R : Type*} [Ring R]

/-- The Kato generator in the rotating gauge frame is minus the diagonal
part of X. This is the algebra behind Q(t)=G(t) exp(-t X_diag). -/
theorem gauge_rotating_generator (P X : R) (hP : P * P = P) :
    ((X * P - P * X) * P - P * (X * P - P * X)) - X =
      -(P * X * P + (1 - P) * X * (1 - P)) := by
  have hp (Y : R) : P * (P * Y) = P * Y := by rw [← mul_assoc, hP]
  noncomm_ring [hP, hp]

end GaugeLoop

/-- Integer reference occupancy drops out of a compact-loop phase. -/
theorem integer_reference_phase (a : ℂ) (k : ℤ) :
    Complex.exp (-2 * Real.pi * Complex.I * (a + k)) =
      Complex.exp (-2 * Real.pi * Complex.I * a) := by
  have h : -2 * (Real.pi : ℂ) * Complex.I * (a + k) =
      -2 * Real.pi * Complex.I * a + (-k : ℤ) * (2 * Real.pi * Complex.I) := by
    push_cast
    ring
  rw [h, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]

section FlatGap

/-- Put u_mu=1-cos(k_mu); the identity is independent of the toron angles. -/
theorem flat_gap_squared (u₀ u₁ u₂ u₃ : ℝ) :
    (u₀ + u₁ + u₂ + u₃ - 1)^2 +
      (2*u₀-u₀^2) + (2*u₁-u₁^2) + (2*u₂-u₂^2) + (2*u₃-u₃^2) =
      1 + 2*(u₀*u₁+u₀*u₂+u₀*u₃+u₁*u₂+u₁*u₃+u₂*u₃) := by ring

theorem flat_gap_lower_bound (u₀ u₁ u₂ u₃ : ℝ)
    (h₀ : 0 ≤ u₀) (h₁ : 0 ≤ u₁) (h₂ : 0 ≤ u₂) (h₃ : 0 ≤ u₃) :
    1 ≤ (u₀ + u₁ + u₂ + u₃ - 1)^2 +
      (2*u₀-u₀^2) + (2*u₁-u₁^2) + (2*u₂-u₂^2) + (2*u₃-u₃^2) := by
  rw [flat_gap_squared]
  have hn : 0 ≤ 2*(u₀*u₁+u₀*u₂+u₀*u₃+u₁*u₂+u₁*u₃+u₂*u₃) := by positivity
  linarith

end FlatGap

section PairedOrientation

def pairTransition (a b : ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![a, -star b; b, star a]

/-- Changes between normalized frames (v,Jv), with J²=-1, have this form. -/
theorem pair_transition_det (a b : ℂ) :
    (pairTransition a b).det = a * star a + b * star b := by
  rw [pairTransition, Matrix.det_fin_two_of]
  ring

theorem normalized_pair_det (a b : ℂ) (h : a * star a + b * star b = 1) :
    (pairTransition a b).det = 1 := by rw [pair_transition_det, h]

variable {M : Type*} [Fintype M] [DecidableEq M]

/-- A permutation of momentum blocks acts twice, once on each paired column. -/
theorem paired_permutation_sign (σ : Equiv.Perm M) :
    Equiv.Perm.sign (Equiv.prodCongrRight (fun _ : Fin 2 => σ)) = 1 := by
  rw [Equiv.Perm.sign_prodCongrRight, Fin.prod_univ_two]
  exact Int.units_mul_self _

/-- Even block permutation and normalized quaternionic transitions fix the
determinant exactly, without requiring identity transport of the full frame. -/
theorem paired_block_holonomy (σ : Equiv.Perm M) (a b : M → ℂ)
    (h : ∀ m, a m * star (a m) + b m * star (b m) = 1) :
    ((Matrix.blockDiagonal (fun m => pairTransition (a m) (b m))).submatrix
      (Equiv.prodCongrRight (fun _ : Fin 2 => σ)) id).det = 1 := by
  rw [Matrix.det_permute, paired_permutation_sign, Matrix.det_blockDiagonal]
  have hp : (∏ k, (pairTransition (a k) (b k)).det) = 1 :=
    Finset.prod_eq_one (fun k _ => normalized_pair_det (a k) (b k) (h k))
  rw [hp]
  norm_num

end PairedOrientation

section Curvature
variable {N : Type*} [Fintype N] [DecidableEq N]

/-- Antiunitary similarity forces the trace to be real. The square of the
antiunitary is needed for paired orientation, but not for this trace fact. -/
theorem antiunitary_trace_real (J T : Matrix N N ℂ)
    (hJ : Jᴴ * J = 1)
    (hT : J * (T.map (starRingEnd ℂ)) * Jᴴ = T) :
    star (Matrix.trace T) = Matrix.trace T := by
  calc
    star (Matrix.trace T) = Matrix.trace (T.map (starRingEnd ℂ)) :=
      AddMonoidHom.map_trace (starRingEnd ℂ) T
    _ = Matrix.trace (J * (T.map (starRingEnd ℂ)) * Jᴴ) := by
      rw [Matrix.trace_mul_cycle, hJ, Matrix.one_mul]
    _ = Matrix.trace T := by rw [hT]

omit [DecidableEq N] in
theorem hermitian_commutator_trace (P A B : Matrix N N ℂ)
    (hP : Pᴴ = P) (hA : Aᴴ = A) (hB : Bᴴ = B) :
    star (Matrix.trace (P * (A * B - B * A))) =
      -Matrix.trace (P * (A * B - B * A)) := by
  rw [← Matrix.trace_conjTranspose]
  simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_sub, hP, hA, hB]
  rw [Matrix.trace_mul_comm, ← neg_sub (A * B) (B * A), Matrix.mul_neg, Matrix.trace_neg]

/-- The determinant curvature vanishes when the projector and tangents
make P[A,B] invariant under the same antiunitary. -/
theorem antiunitary_curvature_zero (J P A B : Matrix N N ℂ)
    (hJ : Jᴴ * J = 1) (hP : Pᴴ = P) (hA : Aᴴ = A) (hB : Bᴴ = B)
    (hT : J * ((P * (A * B - B * A)).map (starRingEnd ℂ)) * Jᴴ =
      P * (A * B - B * A)) :
    Complex.I * Matrix.trace (P * (A * B - B * A)) = 0 := by
  have hr := antiunitary_trace_real J (P * (A * B - B * A)) hJ hT
  have hi := hermitian_commutator_trace P A B hP hA hB
  have hz : Matrix.trace (P * (A * B - B * A)) = 0 :=
    CharZero.eq_neg_self_iff.mp (hr.symm.trans hi)
  rw [hz, mul_zero]

end Curvature

#print axioms gauge_rotating_generator
#print axioms integer_reference_phase
#print axioms flat_gap_squared
#print axioms flat_gap_lower_bound
#print axioms pair_transition_det
#print axioms normalized_pair_det
#print axioms paired_permutation_sign
#print axioms paired_block_holonomy
#print axioms antiunitary_trace_real
#print axioms hermitian_commutator_trace
#print axioms antiunitary_curvature_zero

end
end UnifiedTheory.Audit.KFCausalCompactHolonomy
