/-
  LayerA/GaugeFromTraceless.lean — Traceless matrices carry gauge structure

  THE GAP CLOSED:
    The codebase establishes that the kernel of trace (= traceless matrices)
    is the dressing sector, but never formally proves that traceless matrices
    form a Lie algebra closed under the adjoint action. This file bridges
    "traceless matrices" to "gauge bosons" by proving:

  THREE THEOREMS (zero sorry, zero axioms):

  1. commutator_traceless: The commutator [A,B] = AB - BA is always traceless.
     This means traceless matrices are closed under the Lie bracket, so
     they form a Lie subalgebra sl(n) ⊂ gl(n).

  2. adjoint_preserves_traceless: Conjugation g X g⁻¹ preserves trace.
     This is the adjoint representation Ad(g)(X) = gXg⁻¹, which is how
     gauge transformations act on gauge bosons (= Lie algebra elements).

  3. bracket_nontrivial: For n ≥ 2, the Lie bracket on traceless matrices
     is nontrivial: ∃ A B with tr(A) = tr(B) = 0 but [A,B] ≠ 0.
     This means sl(n) is a nonabelian Lie algebra — essential for
     nonabelian gauge theory (Yang-Mills).

  Together: traceless matrices form a nontrivial Lie algebra, closed under
  the adjoint action of invertible matrices. This IS the gauge boson structure.
-/
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Data.Real.Basic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.LayerA.GaugeFromTraceless

open Matrix Finset

/-! ## Helper: elementary matrix eij -/

/-- A matrix with 1 at position (i,j) and 0 elsewhere. -/
def eij (n : ℕ) (i j : Fin n) : Matrix (Fin n) (Fin n) ℝ :=
  fun r c => if r = i ∧ c = j then 1 else 0

/-! ## Theorem 1: The commutator is always traceless

  For ANY square matrices A, B over a commutative ring:
    tr(AB - BA) = tr(AB) - tr(BA) = 0

  This uses `Matrix.trace_mul_comm`: tr(AB) = tr(BA).
  In particular, if tr(A) = tr(B) = 0, then tr([A,B]) = 0,
  so traceless matrices are closed under [·,·] and form a Lie subalgebra. -/

theorem commutator_traceless {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℝ) :
    trace (A * B - B * A) = 0 := by
  rw [trace_sub, trace_mul_comm A B, sub_self]

/-! ## Theorem 2: The adjoint action preserves trace

  For g a unit in the matrix ring and X any matrix:
    tr(g X g⁻¹) = tr(X)

  This is the adjoint representation Ad(g)(X) = gXg⁻¹.
  In particular, if tr(X) = 0 then tr(gXg⁻¹) = 0,
  so the adjoint action preserves the traceless condition.
  This is exactly how gauge transformations act on gauge bosons. -/

theorem adjoint_preserves_trace {n : ℕ} (g : (Matrix (Fin n) (Fin n) ℝ)ˣ)
    (X : Matrix (Fin n) (Fin n) ℝ) :
    trace ((g : Matrix (Fin n) (Fin n) ℝ) * X *
      (↑g⁻¹ : Matrix (Fin n) (Fin n) ℝ)) = trace X :=
  trace_units_conj g X

/-- Corollary: the adjoint action preserves the traceless condition. -/
theorem adjoint_preserves_traceless {n : ℕ} (g : (Matrix (Fin n) (Fin n) ℝ)ˣ)
    (X : Matrix (Fin n) (Fin n) ℝ) (hX : trace X = 0) :
    trace ((g : Matrix (Fin n) (Fin n) ℝ) * X *
      (↑g⁻¹ : Matrix (Fin n) (Fin n) ℝ)) = 0 := by
  rw [adjoint_preserves_trace, hX]

/-! ## Theorem 3: The Lie bracket on traceless matrices is nontrivial

  For n ≥ 2, there exist traceless matrices A, B with [A,B] ≠ 0.
  Witness: A = e₀₁ (1 at position (0,1)), B = e₁₀ (1 at position (1,0)).
  Both are traceless (all diagonal entries are 0).
  [A,B] = AB - BA = e₀₀ - e₁₁ ≠ 0 (the (0,0) entry is 1). -/

/-- The trace of an off-diagonal elementary matrix eij (i ≠ j) is 0. -/
theorem trace_eij_off_diag {n : ℕ} (i j : Fin n) (hij : i ≠ j) :
    trace (eij n i j) = 0 := by
  simp only [Matrix.trace, Matrix.diag, eij]
  apply Finset.sum_eq_zero
  intro k _
  split
  · next h => exact absurd (h.1 ▸ h.2 : (i : Fin n) = j) hij
  · rfl

/-- For n ≥ 2, the Lie bracket on traceless matrices is nontrivial.
    Witness: e₀₁ and e₁₀ are both traceless, but [e₀₁, e₁₀] ≠ 0. -/
theorem bracket_nontrivial {n : ℕ} (hn : 2 ≤ n) :
    ∃ A B : Matrix (Fin n) (Fin n) ℝ,
      trace A = 0 ∧ trace B = 0 ∧ A * B - B * A ≠ 0 := by
  set i₀ : Fin n := ⟨0, by omega⟩
  set i₁ : Fin n := ⟨1, by omega⟩
  have h01 : i₀ ≠ i₁ := by
    intro h; have := congr_arg Fin.val h; simp [i₀, i₁] at this
  have h10 : i₁ ≠ i₀ := Ne.symm h01
  refine ⟨eij n i₀ i₁, eij n i₁ i₀,
    trace_eij_off_diag i₀ i₁ h01,
    trace_eij_off_diag i₁ i₀ h10, ?_⟩
  intro heq
  -- Evaluate the commutator at position (i₀, i₀): should be 1 - 0 = 1 ≠ 0
  have h1 : (eij n i₀ i₁ * eij n i₁ i₀ - eij n i₁ i₀ * eij n i₀ i₁) i₀ i₀ = 0 := by
    rw [heq]; simp
  -- Compute each matrix product entry directly
  have prod1 : (eij n i₀ i₁ * eij n i₁ i₀) i₀ i₀ = 1 := by
    simp only [Matrix.mul_apply, eij]
    rw [Finset.sum_eq_single i₁]
    · simp
    · intro b _ hb; simp [hb]
    · intro h; exact absurd (Finset.mem_univ i₁) h
  have prod2 : (eij n i₁ i₀ * eij n i₀ i₁) i₀ i₀ = 0 := by
    simp only [Matrix.mul_apply, eij]
    apply Finset.sum_eq_zero
    intro x _
    by_cases hx : x = i₀
    · subst hx; simp [h01]
    · simp [hx]
  rw [Matrix.sub_apply, prod1, prod2] at h1
  norm_num at h1

/-! ## Summary -/

/-- **GAUGE FROM TRACELESS: the complete connection.**

  (1) Traceless matrices are closed under the Lie bracket [A,B] = AB-BA
  (2) The adjoint action Ad(g)(X) = gXg⁻¹ preserves the traceless condition
  (3) For n ≥ 2, the bracket is nontrivial (sl(n) is nonabelian)

  This establishes: the kernel of trace (= dressing sector from PhysicsFromOrder)
  carries the structure of a nontrivial Lie algebra acted on by the adjoint
  representation. This IS the gauge boson algebra sl(n). -/
theorem gauge_from_traceless :
    -- (1) Commutator is always traceless
    (∀ (m : ℕ) (A B : Matrix (Fin m) (Fin m) ℝ), trace (A * B - B * A) = 0)
    -- (2) Adjoint preserves traceless condition
    ∧ (∀ (m : ℕ) (g : (Matrix (Fin m) (Fin m) ℝ)ˣ)
        (X : Matrix (Fin m) (Fin m) ℝ),
        trace X = 0 →
        trace ((g : Matrix (Fin m) (Fin m) ℝ) * X *
          (↑g⁻¹ : Matrix (Fin m) (Fin m) ℝ)) = 0)
    -- (3) Nontrivial for n ≥ 2
    ∧ (∀ (m : ℕ), 2 ≤ m →
        ∃ A B : Matrix (Fin m) (Fin m) ℝ,
          trace A = 0 ∧ trace B = 0 ∧ A * B - B * A ≠ 0) :=
  ⟨fun _ => commutator_traceless,
   fun _ g X hX => adjoint_preserves_traceless g X hX,
   fun _ hm => bracket_nontrivial hm⟩

end UnifiedTheory.LayerA.GaugeFromTraceless
