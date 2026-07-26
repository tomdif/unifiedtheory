/-
  LayerA/AdjointMasslessMeasure.lean — The adjoint massless mode is a zero of the
  fermion MEASURE operator, for every connection (unconditional in the holonomy).

  ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
  WHAT THIS PINS DOWN.

  `ConnectionDefectMassless.lean` shows the adjoint mode is zero-cost at the
  QUADRATIC level (a parallel section / protected zero mode) and flags the honest
  residual: turning it into a fermion that runs in the RGEs needs the matter
  MEASURE — the adjoint kinetic/hopping operator whose determinant is the fermion
  partition function.  The one-loop adjoint measure operator built from a holonomy
  `W` is `Ad_W − 1 : X ↦ W X W⁻¹ − X` on the adjoint space `sl(n)`; its
  determinant `det(Ad_W − 1)` is the (log of the) adjoint fermion measure, and its
  kernel is the massless spectrum.

  UNCONDITIONAL FACT (this file, axiom-clean): for EVERY holonomy `W`, the adjoint
  measure operator annihilates `W`'s own generator — any `H` commuting with `W`
  satisfies `W H W⁻¹ = H`, i.e. `(Ad_W − 1) H = 0`.  Since a connection in a
  connected group is `exp` of a nonzero traceless generator (its Cartan
  direction), that generator is a nonzero traceless — genuinely adjoint — element
  of `ker(Ad_W − 1)`.  So the massless adjoint mode is a zero of the fermion
  MEASURE for every connection, not just a zero of a bosonic quadratic form.  The
  `n=2` witness below makes the kernel element concrete and nonvacuous.

  SCOPE (honest — the residual to unconditional UNIFICATION).  This is the
  massless HALF of the matter measure: it locates the exact zero of `det(Ad_W−1)`.
  The RUNNING half — the `W`-dependence of the nonzero eigenvalues that sets the
  β-function coefficient, hence the magnitude of the coupling shift — is the full
  `D_adj` determinant computation, and the continuum limit that makes it a
  literal SM RGE contribution is the refinement wall (R3).  Those are a program,
  not relabelled here.  What is now unconditional: adjoint transformation, adjoint
  dimensions (8,3,1), anomaly-freedom, and masslessness-as-measure-kernel.
-/
import Mathlib

set_option autoImplicit false

namespace UnifiedTheory.LayerA.AdjointMasslessMeasure

open Matrix

/-- **The adjoint action fixes any commuting generator.**  For an invertible `W`
and any `H` with `W H = H W`, `W H W⁻¹ = H`.  In particular `Ad_W` fixes the
Cartan direction of its own holonomy. -/
theorem adjoint_fixes_commuting {n : ℕ} (W H : Matrix (Fin n) (Fin n) ℝ)
    (hW : IsUnit W.det) (hcomm : W * H = H * W) :
    W * H * W⁻¹ = H := by
  rw [hcomm, mul_assoc, mul_nonsing_inv W hW, mul_one]

/-- **The adjoint fermion measure operator annihilates the connection's own
generator.**  The one-loop adjoint measure operator `Ad_W − 1 : X ↦ W X W⁻¹ − X`
kills any `H` commuting with `W`.  So `H ∈ ker(Ad_W − 1)`: a massless mode of the
fermion measure, present for every holonomy `W`. -/
theorem adjoint_measure_annihilates_generator {n : ℕ} (W H : Matrix (Fin n) (Fin n) ℝ)
    (hW : IsUnit W.det) (hcomm : W * H = H * W) :
    W * H * W⁻¹ - H = 0 := by
  rw [adjoint_fixes_commuting W H hW hcomm, sub_self]

/-- **Nonvacuity witness (`n = 2`).**  A nontrivial holonomy `W = diag(2,1)` with a
NONZERO TRACELESS generator `H = diag(1,−1)` in the kernel of its adjoint measure
operator: a genuine adjoint (traceless) massless mode of a genuine (`W ≠ 1`)
connection. -/
theorem adjoint_massless_mode_witness :
    ∃ W H : Matrix (Fin 2) (Fin 2) ℝ,
      IsUnit W.det ∧ W ≠ 1 ∧ H ≠ 0 ∧ trace H = 0 ∧ W * H * W⁻¹ = H := by
  refine ⟨!![2, 0; 0, 1], !![1, 0; 0, -1], ?_, ?_, ?_, ?_, ?_⟩
  · rw [Matrix.det_fin_two_of]; norm_num
  · intro h
    have := congrFun (congrFun h 0) 0
    simp [Matrix.one_apply] at this
  · intro h
    have := congrFun (congrFun h 0) 0
    simp at this
  · rw [Matrix.trace_fin_two]; norm_num
  · apply adjoint_fixes_commuting
    · rw [Matrix.det_fin_two_of]; norm_num
    · rw [← Matrix.ext_iff]; intro i j; fin_cases i <;> fin_cases j <;>
        simp [Matrix.mul_fin_two]

#print axioms adjoint_fixes_commuting
#print axioms adjoint_measure_annihilates_generator
#print axioms adjoint_massless_mode_witness

end UnifiedTheory.LayerA.AdjointMasslessMeasure
