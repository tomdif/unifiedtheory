/-
  LayerB/DiagonalVonNeumannEntropy.lean
  ──────────────────────────────────────

  The von Neumann entropy of a density matrix that is diagonal in
  some basis: it equals the Shannon entropy of its diagonal entries
  (interpreted as a probability distribution).

  This file is the naming-bridge layer

      density matrix diagonal entries
        ↔ probability vector
        ↔ Shannon entropy
        ↔ von Neumann entropy in diagonal basis

  We define `vonNeumannEntropyDiagonal P := shannonEntropy P`
  (definitionally equal) and inherit all the Shannon-entropy lemmas.

  WHAT IS PROVEN (no sorry, no custom axioms):
    1. `vonNeumannEntropyDiagonal P`  definition.
    2. `vonNeumannEntropyDiagonal_eq_shannon` — the bridge identity
       (definitional `rfl`).
    3. `vonNeumannEntropyDiagonal_nonneg` (from `entropy_nonneg`).
    4. `vonNeumannEntropyDiagonal_delta_eq_zero` (pure state has S = 0).
    5. `vonNeumannEntropyDiagonal_uniform_eq_log_n`
       (maximally-mixed state on n levels has S = log n).
    6. `vonNeumannEntropyDiagonal_of_product`
       (S of product = S₁ + S₂, from `entropy_of_product`).

  DEFERRED (separate file `DiagonalDensityMatrix.lean`):
    The actual construction of a `ComplexDensityMatrix` from a
    `ProbabilityVector` requires proving the `hTracePSD` field
    `∀ X, 0 ≤ Re(Tr(diag(p) · X† · X))`.  The proof is direct
    (`∑ᵢ pᵢ · Σₖ |X[k,i]|² ≥ 0`) but requires a custom
    diagonal-trace expansion that Mathlib does not currently
    package as a single lemma.  Once that auxiliary file is in
    place, the present `vonNeumannEntropyDiagonal` value will
    coincide with the *actual* −Tr(ρ log ρ) of the constructed
    density matrix (via spectral functional calculus, also deferred).

  Until then, this file fixes the *vocabulary* so downstream files
  (relative entropy, DPI, Holevo) can refer to "the von Neumann
  entropy of a diagonal density matrix" with a single, stable name.
-/

import UnifiedTheory.LayerB.ClassicalEntropy

set_option relaxedAutoImplicit false

namespace UnifiedTheory.LayerB.DiagonalVonNeumannEntropy

open UnifiedTheory.LayerB.ClassicalEntropy
open UnifiedTheory.LayerB.ClassicalEntropy.ProbabilityVector

/-! ## 1. The bridge definition -/

/-- The von Neumann entropy of a density matrix that is diagonal in
    some basis, specified by the probability vector of its diagonal
    entries.  Definitionally equal to the Shannon entropy. -/
noncomputable def vonNeumannEntropyDiagonal
    {α : Type*} [Fintype α] (P : ProbabilityVector α) : ℝ :=
  shannonEntropy P

/-- **The bridge identity (definitional).** -/
theorem vonNeumannEntropyDiagonal_eq_shannon
    {α : Type*} [Fintype α] (P : ProbabilityVector α) :
    vonNeumannEntropyDiagonal P = shannonEntropy P := rfl

/-! ## 2. Inherited properties -/

/-- **vN entropy of a diagonal density matrix is non-negative.** -/
theorem vonNeumannEntropyDiagonal_nonneg
    {α : Type*} [Fintype α] (P : ProbabilityVector α) :
    0 ≤ vonNeumannEntropyDiagonal P := entropy_nonneg P

/-- **vN entropy of a pure state (delta distribution) is zero.** -/
theorem vonNeumannEntropyDiagonal_delta_eq_zero
    {α : Type*} [Fintype α] [DecidableEq α] (i₀ : α) :
    vonNeumannEntropyDiagonal (delta α i₀) = 0 :=
  entropy_delta_eq_zero i₀

/-- **vN entropy of the maximally-mixed state on n levels is log n.** -/
theorem vonNeumannEntropyDiagonal_uniform_eq_log_n (n : ℕ) (hn : 0 < n) :
    vonNeumannEntropyDiagonal (uniform n hn) = Real.log n :=
  entropy_uniform_eq_log_n n hn

/-- **vN entropy of a product state adds.**  When the diagonal density
    matrix factorizes as `ρ_A ⊗ ρ_B`, the joint vN entropy is the sum
    of the marginal entropies. -/
theorem vonNeumannEntropyDiagonal_of_product
    {α β : Type*} [Fintype α] [Fintype β]
    (P : ProbabilityVector α) (Q : ProbabilityVector β) :
    vonNeumannEntropyDiagonal (productDistribution P Q)
      = vonNeumannEntropyDiagonal P + vonNeumannEntropyDiagonal Q :=
  entropy_of_product P Q

/-! ## 3. Congruence -/

/-- vN entropy respects pointwise equality of probability vectors. -/
theorem vonNeumannEntropyDiagonal_congr
    {α : Type*} [Fintype α] (P Q : ProbabilityVector α)
    (h : ∀ i, P.p i = Q.p i) :
    vonNeumannEntropyDiagonal P = vonNeumannEntropyDiagonal Q :=
  entropy_congr P Q h

end UnifiedTheory.LayerB.DiagonalVonNeumannEntropy
