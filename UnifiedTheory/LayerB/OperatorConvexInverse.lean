/-
  LayerB/OperatorConvexInverse.lean
  ──────────────────────────────────

  **Operator convexity of `x ↦ x⁻¹` on positive-definite Hermitian
  complex matrices**, via the block-matrix / Schur-complement strategy.

  ## Mathematical statement

  For `A, B : Matrix (Fin n) (Fin n) ℂ` both positive definite and
  `α ∈ [0, 1]`,

      (α • A + (1 - α) • B)⁻¹  ≤  α • A⁻¹ + (1 - α) • B⁻¹,

  where the matrix order is `MatrixOrder`'s
  `A ≤ B := (B - A).PosSemidef`.

  ## Strategy

  The proof goes through the block matrix

      M = ⎡  α A + (1-α) B          I              ⎤
          ⎣  I                  α A⁻¹ + (1-α) B⁻¹  ⎦

  and uses Mathlib's Schur characterisation
  (`Matrix.PosDef.fromBlocks₁₁`):

      `(fromBlocks A B Bᴴ D).PosSemidef ↔ (D - Bᴴ * A⁻¹ * B).PosSemidef`
      when `A` is positive definite (hence invertible).

  Applied with `A = α A + (1-α) B` (top-left), `B = 1` (off-diagonal),
  `D = α A⁻¹ + (1-α) B⁻¹` (bottom-right), this gives:
  `M` is PSD iff
  `(α A⁻¹ + (1-α) B⁻¹) - 1ᴴ * (α A + (1-α) B)⁻¹ * 1` is PSD,
  i.e. exactly our target inequality.

  To show `M` is PSD, we exhibit it as a convex combination of two
  PSD block matrices:

      M_A := ⎡ A     I  ⎤    M_B := ⎡ B     I  ⎤
             ⎣ I     A⁻¹⎦           ⎣ I     B⁻¹⎦

  Each `M_A`, `M_B` is PSD by `fromBlocks₂₂` applied with the
  bottom-right block invertible (`(A⁻¹)⁻¹ = A`):
  `(A - 1 * A * 1).PosSemidef` reduces to `(A - A).PosSemidef`,
  which is trivial.

  The convex combination `α • M_A + (1-α) • M_B = M` is then PSD
  as a positive combination of PSD matrices.

  ## What is proved (zero `sorry`, zero custom `axiom`)

  • `block_psd_pair` — the elementary block matrix
    `⎡ A  I; I  A⁻¹ ⎤` is PSD when `A.PosDef`.
  • `inv_operator_convex_block_lemma` — the block matrix
    `⎡ αA + (1-α)B   I; I   αA⁻¹ + (1-α)B⁻¹ ⎤` is PSD.
  • `inv_operator_convex` — the main theorem:
    `(αA + (1-α)B)⁻¹ ≤ α • A⁻¹ + (1-α) • B⁻¹` in `MatrixOrder`.

  ## Key Mathlib lemmas (load-bearing)

  • `Matrix.PosDef.fromBlocks₁₁` and `Matrix.PosDef.fromBlocks₂₂`
    — the Schur characterisation as `PosSemidef ↔ Schur PosSemidef`.
  • `Matrix.PosDef.inv` — inverse of a PosDef matrix is PosDef.
  • `Matrix.PosDef.add`, `Matrix.PosDef.smul` — closure of PosDef.
  • `Matrix.PosSemidef.add`, `Matrix.PosSemidef.smul`
    — closure of PSD under nonneg-scalar convex combinations.
  • `Matrix.fromBlocks_smul`, `Matrix.fromBlocks_add`
    — linearity of the block-matrix constructor.
-/

import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.LinearAlgebra.Matrix.PosDef

set_option relaxedAutoImplicit false

namespace UnifiedTheory.LayerB.OperatorConvexInverse

open Matrix Complex
open scoped MatrixOrder ComplexOrder

variable {n : ℕ}

/-! ## 1. Building block: the elementary block matrix

    `M_X := ⎡ X    I  ⎤
            ⎣ I    X⁻¹⎦`

    is positive semidefinite whenever `X.PosDef`. -/

/-- The Hermitian-adjoint of `1 : Matrix (Fin n) (Fin n) ℂ` is `1`. -/
private lemma one_conjTranspose :
    (1 : Matrix (Fin n) (Fin n) ℂ)ᴴ = 1 := by
  ext i j
  simp [Matrix.one_apply, Matrix.conjTranspose_apply]
  by_cases h : j = i
  · subst h; simp
  · have h' : i ≠ j := fun e => h e.symm
    simp [h, h']

/-- **Block-matrix building block.**

    If `A` is positive definite, then the block matrix
    `⎡ A    I  ⎤
     ⎣ I    A⁻¹⎦`
    is positive semidefinite.

    Proof: `fromBlocks₂₂` with bottom-right `A⁻¹` (PosDef, hence
    invertible) reduces PSD-ness to:
    `(A - 1 * (A⁻¹)⁻¹ * 1).PosSemidef`.
    Since `(A⁻¹)⁻¹ = A`, this is `(A - A).PosSemidef = 0.PosSemidef`,
    which is trivial. -/
theorem block_psd_pair
    (A : Matrix (Fin n) (Fin n) ℂ) (hA : A.PosDef) :
    (Matrix.fromBlocks A (1 : Matrix (Fin n) (Fin n) ℂ)
        (1 : Matrix (Fin n) (Fin n) ℂ) A⁻¹).PosSemidef := by
  have hAinv : A⁻¹.PosDef := hA.inv
  -- `A⁻¹` and `A` are invertible.
  haveI : Invertible A⁻¹ := hAinv.isUnit.invertible
  haveI : Invertible A := hA.isUnit.invertible
  -- The Hermitian adjoint of `1` is `1`.
  have hConj : (1 : Matrix (Fin n) (Fin n) ℂ)ᴴ = 1 := one_conjTranspose
  -- Rewrite the off-diagonal `1` (column position) as `1ᴴ` so the
  -- block matrix has the `⎡ A  Q; Qᴴ  D ⎤` form expected by
  -- `fromBlocks₂₂`.
  have h_eq :
      Matrix.fromBlocks A (1 : Matrix (Fin n) (Fin n) ℂ)
          (1 : Matrix (Fin n) (Fin n) ℂ) A⁻¹
        = Matrix.fromBlocks A (1 : Matrix (Fin n) (Fin n) ℂ)
          ((1 : Matrix (Fin n) (Fin n) ℂ)ᴴ) A⁻¹ := by
    rw [hConj]
  rw [h_eq, Matrix.PosDef.fromBlocks₂₂ A (1 : Matrix (Fin n) (Fin n) ℂ) hAinv]
  -- Goal: `(A - 1 * (A⁻¹)⁻¹ * 1ᴴ).PosSemidef`.
  -- Use targeted `simp only` to normalise `1 * _`, `_ * 1`, `A⁻¹⁻¹ = A`,
  -- and `A - A = 0`; then `PosSemidef.zero` closes.
  simp only [Matrix.inv_inv_of_invertible, one_mul, Matrix.conjTranspose_one,
    mul_one, sub_self]
  exact Matrix.PosSemidef.zero

/-! ## 2. Convex combination of building blocks. -/

/-- Auxiliary: for `a : ℝ` with `0 ≤ a`, the coerced complex scalar
    `(a : ℂ)` satisfies `(0 : ℂ) ≤ (a : ℂ)`. -/
private lemma complex_nonneg_of_real_nonneg {a : ℝ} (ha : 0 ≤ a) :
    (0 : ℂ) ≤ (a : ℂ) := by
  rw [Complex.le_def]
  refine ⟨by simpa using ha, ?_⟩
  simp

/-- Auxiliary: for `a : ℝ` with `0 < a`, the coerced complex scalar
    `(a : ℂ)` satisfies `(0 : ℂ) < (a : ℂ)`. -/
private lemma complex_pos_of_real_pos {a : ℝ} (ha : 0 < a) :
    (0 : ℂ) < (a : ℂ) := by
  rw [Complex.lt_def]
  refine ⟨by simpa using ha, ?_⟩
  simp

/-- The Schur block matrix used to prove operator-convexity of inverse.

    `M := ⎡ αA + (1-α)B           I              ⎤
           ⎣ I                  αA⁻¹ + (1-α)B⁻¹  ⎦`

    is positive semidefinite, because it equals
    `α • M_A + (1 - α) • M_B`, each PSD by `block_psd_pair`. -/
theorem inv_operator_convex_block_lemma
    (A B : Matrix (Fin n) (Fin n) ℂ)
    (hA : A.PosDef) (hB : B.PosDef)
    (α : ℝ) (hα₀ : 0 ≤ α) (hα₁ : α ≤ 1) :
    (Matrix.fromBlocks
        ((α : ℂ) • A + ((1 - α : ℝ) : ℂ) • B)
        (1 : Matrix (Fin n) (Fin n) ℂ)
        (1 : Matrix (Fin n) (Fin n) ℂ)
        ((α : ℂ) • A⁻¹ + ((1 - α : ℝ) : ℂ) • B⁻¹)).PosSemidef := by
  -- The two building blocks.
  have hMA : (Matrix.fromBlocks A (1 : Matrix (Fin n) (Fin n) ℂ)
                (1 : Matrix (Fin n) (Fin n) ℂ) A⁻¹).PosSemidef :=
    block_psd_pair A hA
  have hMB : (Matrix.fromBlocks B (1 : Matrix (Fin n) (Fin n) ℂ)
                (1 : Matrix (Fin n) (Fin n) ℂ) B⁻¹).PosSemidef :=
    block_psd_pair B hB
  -- Nonnegativity of the scalar weights (as complex numbers).
  have hα₀C : (0 : ℂ) ≤ (α : ℂ) := complex_nonneg_of_real_nonneg hα₀
  have h1mα_R : (0 : ℝ) ≤ 1 - α := by linarith
  have h1mα_C : (0 : ℂ) ≤ ((1 - α : ℝ) : ℂ) :=
    complex_nonneg_of_real_nonneg h1mα_R
  -- Their nonneg-scaled versions.
  have hα_scaled : ((α : ℂ) •
      Matrix.fromBlocks A (1 : Matrix (Fin n) (Fin n) ℂ)
        (1 : Matrix (Fin n) (Fin n) ℂ) A⁻¹).PosSemidef :=
    hMA.smul hα₀C
  have h1mα_scaled : (((1 - α : ℝ) : ℂ) •
      Matrix.fromBlocks B (1 : Matrix (Fin n) (Fin n) ℂ)
        (1 : Matrix (Fin n) (Fin n) ℂ) B⁻¹).PosSemidef :=
    hMB.smul h1mα_C
  -- Their sum is PSD.
  have hSum := hα_scaled.add h1mα_scaled
  -- Rewrite the sum as a single `fromBlocks` (linearity of `fromBlocks`).
  have h_lin :
      (α : ℂ) • Matrix.fromBlocks A (1 : Matrix (Fin n) (Fin n) ℂ)
          (1 : Matrix (Fin n) (Fin n) ℂ) A⁻¹
        + ((1 - α : ℝ) : ℂ) • Matrix.fromBlocks B
          (1 : Matrix (Fin n) (Fin n) ℂ)
          (1 : Matrix (Fin n) (Fin n) ℂ) B⁻¹
      = Matrix.fromBlocks
          ((α : ℂ) • A + ((1 - α : ℝ) : ℂ) • B)
          ((α : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ)
              + ((1 - α : ℝ) : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ))
          ((α : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ)
              + ((1 - α : ℝ) : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ))
          ((α : ℂ) • A⁻¹ + ((1 - α : ℝ) : ℂ) • B⁻¹) := by
    rw [Matrix.fromBlocks_smul, Matrix.fromBlocks_smul, Matrix.fromBlocks_add]
  -- The off-diagonal blocks simplify to `1` since α + (1-α) = 1.
  have h_offdiag :
      (α : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ)
        + ((1 - α : ℝ) : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ)
      = (1 : Matrix (Fin n) (Fin n) ℂ) := by
    rw [← add_smul]
    have : (α : ℂ) + ((1 - α : ℝ) : ℂ) = 1 := by
      push_cast; ring
    rw [this, one_smul]
  rw [h_lin, h_offdiag] at hSum
  exact hSum

/-! ## 3. Operator convexity of the inverse. -/

set_option maxHeartbeats 800000 in
-- Raised maxHeartbeats: the proof juggles three layers of typeclass
-- resolution (`MatrixOrder`, `PosDef`, `Invertible`) against the
-- block-matrix Schur lemma `fromBlocks₁₁`, plus the case-split on
-- `α > 0` vs `α = 0` for positive definiteness of the convex
-- combination.  Default 200000 is insufficient.
/-- **Operator convexity of `x ↦ x⁻¹` on positive-definite matrices.**

    For `A, B : Matrix (Fin n) (Fin n) ℂ` both positive definite and
    `α ∈ [0, 1]`,
    `(α • A + (1 - α) • B)⁻¹  ≤  α • A⁻¹ + (1 - α) • B⁻¹`.

    Proof: the block matrix
    `M = ⎡ α A + (1-α) B            I              ⎤
         ⎣ I                  α A⁻¹ + (1-α) B⁻¹  ⎦`
    is PSD by `inv_operator_convex_block_lemma`.  Since the top-left
    block `α A + (1-α) B` is itself positive definite (convex
    combination of PosDef matrices), the Schur characterisation
    `Matrix.PosDef.fromBlocks₁₁` gives:
    `M.PosSemidef ↔ ((α A⁻¹ + (1-α) B⁻¹) - 1ᴴ * (αA+(1-α)B)⁻¹ * 1).PosSemidef`,
    which is exactly the desired inequality. -/
theorem inv_operator_convex
    (A B : Matrix (Fin n) (Fin n) ℂ)
    (hA : A.PosDef) (hB : B.PosDef)
    (α : ℝ) (hα₀ : 0 ≤ α) (hα₁ : α ≤ 1) :
    ((α : ℂ) • A + ((1 - α : ℝ) : ℂ) • B)⁻¹
      ≤ (α : ℂ) • A⁻¹ + ((1 - α : ℝ) : ℂ) • B⁻¹ := by
  -- The block-matrix lemma.
  have hM := inv_operator_convex_block_lemma A B hA hB α hα₀ hα₁
  -- The top-left block is `α A + (1-α) B`, which is PosDef.
  have h1mα_R : (0 : ℝ) ≤ 1 - α := by linarith
  have h1mα_C : (0 : ℂ) ≤ ((1 - α : ℝ) : ℂ) :=
    complex_nonneg_of_real_nonneg h1mα_R
  -- For positive definiteness of the convex combination of PosDefs:
  --   - either α > 0 (and (1-α) ≥ 0) — then α • A is PosDef.
  --   - or  α = 0 — then 1 - α = 1 > 0, so (1-α) • B is PosDef.
  -- In either case `α • A + (1-α) • B` is PosDef.
  have hConv : ((α : ℂ) • A + ((1 - α : ℝ) : ℂ) • B).PosDef := by
    rcases lt_or_eq_of_le hα₀ with hα_pos | hα_zero
    · -- α > 0: (α • A).PosDef and ((1-α) • B).PosSemidef
      have hαC_pos : (0 : ℂ) < (α : ℂ) := complex_pos_of_real_pos hα_pos
      have hαA_PD : ((α : ℂ) • A).PosDef := hA.smul hαC_pos
      have h1mαB_PSD : (((1 - α : ℝ) : ℂ) • B).PosSemidef :=
        hB.posSemidef.smul h1mα_C
      exact hαA_PD.add_posSemidef h1mαB_PSD
    · -- α = 0: 1 - α = 1 > 0, so (1-α) • B is PosDef.
      have h_eq : α = 0 := hα_zero.symm
      subst h_eq
      have h1mαC_pos : (0 : ℂ) < ((1 - (0 : ℝ) : ℝ) : ℂ) :=
        complex_pos_of_real_pos (by norm_num)
      have h_PD : (((1 - (0 : ℝ) : ℝ) : ℂ) • B).PosDef := hB.smul h1mαC_pos
      have h_simp :
          ((0 : ℝ) : ℂ) • A + (((1 - (0 : ℝ) : ℝ) : ℂ)) • B
            = (((1 - (0 : ℝ) : ℝ) : ℂ)) • B := by
        simp
      rw [h_simp]
      exact h_PD
  -- `αA + (1-α)B` is invertible.
  haveI hInv : Invertible ((α : ℂ) • A + ((1 - α : ℝ) : ℂ) • B) :=
    hConv.isUnit.invertible
  -- Rewrite off-diagonal `1` as `1ᴴ`.
  have hConj : (1 : Matrix (Fin n) (Fin n) ℂ)ᴴ = 1 := one_conjTranspose
  -- Cast hM into the form expected by fromBlocks₁₁ (off-diag = 1ᴴ).
  have hM' :
      (Matrix.fromBlocks
        ((α : ℂ) • A + ((1 - α : ℝ) : ℂ) • B)
        (1 : Matrix (Fin n) (Fin n) ℂ)
        ((1 : Matrix (Fin n) (Fin n) ℂ)ᴴ)
        ((α : ℂ) • A⁻¹ + ((1 - α : ℝ) : ℂ) • B⁻¹)).PosSemidef := by
    rw [hConj]; exact hM
  have hSchur := (Matrix.PosDef.fromBlocks₁₁
    (1 : Matrix (Fin n) (Fin n) ℂ)
    ((α : ℂ) • A⁻¹ + ((1 - α : ℝ) : ℂ) • B⁻¹)
    hConv).mp hM'
  -- `hSchur : ((αA⁻¹ + (1-α)B⁻¹) - 1ᴴ * (αA+(1-α)B)⁻¹ * 1).PosSemidef`.
  -- Simplify `1ᴴ * _ * 1 = _`.
  rw [hConj, one_mul, mul_one] at hSchur
  -- This is exactly `(αA + (1-α)B)⁻¹ ≤ αA⁻¹ + (1-α)B⁻¹` in MatrixOrder.
  exact hSchur

/-! ## 4. Axiom audit.

    The next `#print axioms` directives are commented out to keep the
    build output quiet; uncomment locally to verify that no `sorry`
    or custom `axiom` is used. -/

-- #print axioms block_psd_pair
-- #print axioms inv_operator_convex_block_lemma
-- #print axioms inv_operator_convex
-- VERIFIED 2026-05-31: all three depend only on
--   `propext, Classical.choice, Quot.sound`
-- (Lean's three standard axioms).  No `sorry`, no custom `axiom`.

end UnifiedTheory.LayerB.OperatorConvexInverse
