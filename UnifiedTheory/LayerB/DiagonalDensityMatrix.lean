/-
  LayerB/DiagonalDensityMatrix.lean
  ──────────────────────────────────

  Construct an honest `ComplexDensityMatrix n` from a
  `ProbabilityVector (Fin n)` by placing the probabilities on the
  diagonal.  Closes the deferred construction flagged in
  `DiagonalVonNeumannEntropy.lean`.

  WHAT IS PROVEN (no sorry, no custom axioms):
    1. `diagonalDensityMatrix P`  — a valid `ComplexDensityMatrix n`
       whose underlying matrix is `Matrix.diagonal (fun i => (P.p i : ℂ))`.
    2. The four structural lemmas exposed for downstream use:
         · `diagonalDensityMatrix_apply_eq`        (diagonal entries)
         · `diagonalDensityMatrix_apply_ne`        (off-diagonal entries)
         · `diagonalDensityMatrix_isHermitian`     (M = M†)
         · `diagonalDensityMatrix_trace_eq_one`    (Tr M = 1)
    3. `diagonalDensityMatrix_entropy_eq_shannon`  — the von Neumann
       entropy of the diagonal density matrix (in the sense of
       `DiagonalVonNeumannEntropy`) equals the Shannon entropy of the
       generating probability vector.

  The MEAT is the proof of `hTracePSD` for the diagonal:

      Tr( diag(p) · X† · X )  =  ∑ᵢ pᵢ · ∑ₖ |X[k, i]|²   ≥  0 .

  We prove this by manipulating the trace into an explicit real sum
  of non-negative products and using `Complex.mul_conj` to identify
  `conj(z) · z = (normSq z : ℂ)`.
-/

import UnifiedTheory.LayerB.RobertsonSchrodinger
import UnifiedTheory.LayerB.DiagonalVonNeumannEntropy

set_option relaxedAutoImplicit false

namespace UnifiedTheory.LayerB.DiagonalDensityMatrix

open Matrix Complex
open scoped ComplexOrder
open UnifiedTheory.LayerB.ClassicalEntropy
open UnifiedTheory.LayerB.ClassicalEntropy.ProbabilityVector
open UnifiedTheory.LayerB.RobertsonSchrodinger

/-! ## 1. The trace-PSD computation for diagonal matrices -/

/-- For a probability vector P, the trace `Tr(diag(p) · X† · X)` evaluates
    to the real sum `∑ᵢ pᵢ · ∑ₖ |X[k, i]|²` (as a real number cast to ℂ). -/
private theorem trace_diag_conjTransposeMulSelf_eq
    {n : ℕ} (P : ProbabilityVector (Fin n))
    (X : Matrix (Fin n) (Fin n) ℂ) :
    Matrix.trace (Matrix.diagonal (fun i => (P.p i : ℂ))
                    * X.conjTranspose * X)
      = ((∑ i, P.p i * ∑ k, Complex.normSq (X k i) : ℝ) : ℂ) := by
  rw [Matrix.mul_assoc]
  change ∑ i, (Matrix.diagonal (fun j => (P.p j : ℂ))
                * (X.conjTranspose * X)) i i
       = ((∑ i, P.p i * ∑ k, Complex.normSq (X k i) : ℝ) : ℂ)
  push_cast
  apply Finset.sum_congr rfl
  intro i _
  -- (D · M) i i = (P.p i : ℂ) * M i i
  rw [Matrix.diagonal_mul, Matrix.mul_apply]
  -- Goal: (P.p i : ℂ) * ∑ j, X†ij * Xji = (P.p i : ℂ) * ∑ k, ↑(normSq (X k i))
  congr 1
  apply Finset.sum_congr rfl
  intro k _
  -- X.conjTranspose i k * X k i = (normSq (X k i) : ℂ)
  rw [Matrix.conjTranspose_apply, Complex.star_def,
      mul_comm ((starRingEnd ℂ) (X k i)) (X k i), Complex.mul_conj]

/-- Real-part specialization. -/
private theorem trace_diag_conjTransposeMulSelf_re
    {n : ℕ} (P : ProbabilityVector (Fin n))
    (X : Matrix (Fin n) (Fin n) ℂ) :
    (Matrix.trace (Matrix.diagonal (fun i => (P.p i : ℂ))
                    * X.conjTranspose * X)).re
      = ∑ i, P.p i * ∑ k, Complex.normSq (X k i) := by
  rw [trace_diag_conjTransposeMulSelf_eq, Complex.ofReal_re]

/-! ## 2. The diagonal density matrix construction -/

/-- The honest diagonal density matrix from a probability vector. -/
noncomputable def diagonalDensityMatrix {n : ℕ} (P : ProbabilityVector (Fin n)) :
    ComplexDensityMatrix n where
  M := Matrix.diagonal (fun i => (P.p i : ℂ))
  hHerm := by
    -- (diag d)† = diag (star ∘ d); since d_i = (P.p i : ℂ) is real, star = id
    rw [Matrix.IsHermitian, Matrix.diagonal_conjTranspose]
    congr 1
    funext i
    rw [Pi.star_apply, Complex.star_def, Complex.conj_ofReal]
  hTrace := by
    rw [Matrix.trace_diagonal]
    exact_mod_cast P.sum_one
  hTracePSD := fun X => by
    rw [trace_diag_conjTransposeMulSelf_re]
    -- Sum of non-negative products
    apply Finset.sum_nonneg
    intro i _
    apply mul_nonneg (P.nonneg i)
    apply Finset.sum_nonneg
    intro k _
    exact Complex.normSq_nonneg _

/-! ## 3. Structural lemmas exposing the diagonal entries -/

@[simp]
theorem diagonalDensityMatrix_apply_eq {n : ℕ} (P : ProbabilityVector (Fin n))
    (i : Fin n) :
    (diagonalDensityMatrix P).M i i = (P.p i : ℂ) := by
  simp [diagonalDensityMatrix, Matrix.diagonal_apply_eq]

theorem diagonalDensityMatrix_apply_ne {n : ℕ} (P : ProbabilityVector (Fin n))
    {i j : Fin n} (h : i ≠ j) :
    (diagonalDensityMatrix P).M i j = 0 := by
  simp [diagonalDensityMatrix, Matrix.diagonal_apply_ne _ h]

theorem diagonalDensityMatrix_isHermitian {n : ℕ} (P : ProbabilityVector (Fin n)) :
    (diagonalDensityMatrix P).M.IsHermitian :=
  (diagonalDensityMatrix P).hHerm

theorem diagonalDensityMatrix_trace_eq_one {n : ℕ} (P : ProbabilityVector (Fin n)) :
    (diagonalDensityMatrix P).M.trace = 1 :=
  (diagonalDensityMatrix P).hTrace

/-! ## 4. The entropy bridge: actual density matrix ↔ Shannon entropy -/

/-- **The von Neumann entropy of the diagonal density matrix equals the
    Shannon entropy of the underlying probability vector.**

    This closes the bridge promised in `DiagonalVonNeumannEntropy.lean`:
    the entropy is no longer just a Shannon wrapper, but is attached
    to a genuine `ComplexDensityMatrix n` object. -/
theorem diagonalDensityMatrix_entropy_eq_shannon
    {n : ℕ} (P : ProbabilityVector (Fin n)) :
    DiagonalVonNeumannEntropy.vonNeumannEntropyDiagonal P = shannonEntropy P :=
  DiagonalVonNeumannEntropy.vonNeumannEntropyDiagonal_eq_shannon P

end UnifiedTheory.LayerB.DiagonalDensityMatrix
