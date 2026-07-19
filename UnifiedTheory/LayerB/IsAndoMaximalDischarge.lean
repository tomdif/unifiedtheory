/-
  LayerB/IsAndoMaximalDischarge.lean
  ───────────────────────────────────

  **Unconditional discharge of `IsAndoMaximal`** (Hansen–Pedersen /
  Ando 1979 maximum characterisation) via the Schur complement +
  operator monotonicity of the square root.

  This file closes the analytic gap left as a `Prop`-hypothesis in
  `UnifiedTheory.LayerB.AndoGeometricMean`, thereby promoting
  joint concavity of the matrix geometric mean from "conditional on
  `IsAndoMaximal`" to UNCONDITIONAL.

  ## Mathematical content

  **Theorem (Ando 1979, maximum characterisation).** For positive
  definite `A, B` and any positive semidefinite `X` such that the
  2×2 block matrix `⎡A X; X B⎤` is positive semidefinite, we have

      X ≤ A # B :=  A^{1/2} · (A^{-1/2} · B · A^{-1/2})^{1/2} · A^{1/2}.

  **Proof.**
  Step 1 (Schur complement, `Matrix.PosDef.fromBlocks₁₁`):
    `⎡A X; X B⎤ ≥ 0  ⇔  B - X · A⁻¹ · X ≥ 0`.
  So `X · A⁻¹ · X ≤ B`.

  Step 2 (conjugate by `A^{-1/2}`):
  Let `S' := √(A⁻¹)`, `Y := S' · X · S'`, `M := S' · B · S'`.
  Multiplying `X · A⁻¹ · X ≤ B` on left and right by `S'` (Hermitian,
  positive) preserves the order:
    `S' · (X · A⁻¹ · X) · S' ≤ S' · B · S'`.
  The LHS equals `(S' · X · S') · (S' · X · S') = Y²` (using
  `S' · S' = A⁻¹`).  Hence `Y² ≤ M`.

  Step 3 (operator monotonicity of √):
  Since `Y` is self-adjoint, `Y ≤ |Y|` (from `abs_sub_self : |a| - a = 2 • a⁻`
  and `a⁻ ≥ 0`).  Also `|Y|² = Y² ≤ M`, so by `CFC.sqrt_le_sqrt`,
  `|Y| = √(|Y|²) ≤ √M`.  Combining, `Y ≤ √M`.

  Step 4 (conjugate back by `√A`):
  Let `S := √A`.  Then `S · S' = 1 = S' · S`, so
    `S · Y · S  =  S · (S' · X · S') · S  =  (S·S') · X · (S'·S)  =  X`.
  And by monotonicity of conjugation:
    `X = S · Y · S ≤ S · √M · S = A # B`.   ∎

  ## What is shipped (zero `sorry`, zero custom `axiom`)

  • `conj_le_of_le` — conjugation by a self-adjoint matrix preserves the
    matrix order: `M ≤ N → Q · M · Q ≤ Q · N · Q`.
  • `ando_block_PSD_le_geometricMean` — the maximum characterisation
    as a stand-alone theorem.
  • `isAndoMaximal_unconditional` — discharge of the `IsAndoMaximal`
    `Prop`-hypothesis from `AndoGeometricMean.lean`.
  • `geometricMean_jointly_concave_unconditional` — joint concavity
    of Ando's geometric mean, UNCONDITIONAL.

  ## Key Mathlib infrastructure used

  • `Matrix.PosDef.fromBlocks₁₁` — Schur complement criterion.
  • `Matrix.PosSemidef.conjTranspose_mul_mul_same` — `Bᴴ · A · B ≥ 0`.
  • `CFC.sqrt_le_sqrt` — operator monotonicity of √ on a C⋆-algebra
    (Löwner–Heinz at p = 1/2).
  • `CFC.abs`, `CFC.abs_sub_self`, `CFC.abs_sq`, `CFC.negPart_nonneg`
    — the absolute-value decomposition for self-adjoint elements.
-/

import UnifiedTheory.LayerB.AndoGeometricMean
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Order
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Abs
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.LinearAlgebra.Matrix.PosDef

set_option relaxedAutoImplicit false

namespace UnifiedTheory.LayerB.IsAndoMaximalDischarge

open Matrix Complex
open scoped MatrixOrder Matrix.Norms.L2Operator ComplexOrder
open UnifiedTheory.LayerB.AndoGeometricMean

variable {n : ℕ}

/-! ## 1. A C⋆-algebra instance on `Matrix (Fin n) (Fin n) ℂ`.

    The scoped `Matrix.Norms.L2Operator` instances assemble all
    `NormedRing`, `NormedAlgebra ℂ`, `CStarRing`, `StarModule ℂ`
    structure.  `CompleteSpace` is automatic in finite dimension.
    All that remains is to bundle these into the `CStarAlgebra` class.
    Same trick as in `OperatorMonotoneLog.lean`. -/
noncomputable instance matrixCStarAlgebra :
    CStarAlgebra (Matrix (Fin n) (Fin n) ℂ) where

/-! ## 2. Conjugation preserves the matrix order. -/

/-- For any matrix `Q` and PosSemidef matrices with `M ≤ N` in the
    matrix order, we have `Qᴴ · M · Q ≤ Qᴴ · N · Q`. -/
private lemma conjTranspose_conj_le_of_le
    {M N Q : Matrix (Fin n) (Fin n) ℂ} (h : M ≤ N) :
    Qᴴ * M * Q ≤ Qᴴ * N * Q := by
  -- `M ≤ N` means `(N - M).PosSemidef`.
  have hSub : (N - M).PosSemidef := h
  -- Conjugating PSD by `Q` (with `Qᴴ` on left, `Q` on right) yields PSD.
  have hConj : (Qᴴ * (N - M) * Q).PosSemidef :=
    hSub.conjTranspose_mul_mul_same Q
  -- Distribute: `Qᴴ · (N - M) · Q = Qᴴ · N · Q - Qᴴ · M · Q`.
  have h_distrib :
      Qᴴ * (N - M) * Q = Qᴴ * N * Q - Qᴴ * M * Q := by
    rw [Matrix.mul_sub, Matrix.sub_mul]
  rw [h_distrib] at hConj
  -- This is the desired inequality.
  exact hConj

/-- Conjugation by a Hermitian matrix `Q` preserves the matrix order. -/
private lemma conj_le_of_le
    {M N Q : Matrix (Fin n) (Fin n) ℂ} (hQ : Q.IsHermitian) (h : M ≤ N) :
    Q * M * Q ≤ Q * N * Q := by
  have := conjTranspose_conj_le_of_le (Q := Q) h
  rwa [hQ.eq] at this

/-! ## 3. Auxiliary identities about `√A`, `√(A⁻¹)`. -/

/-- `√A · √(A⁻¹) = 1` for `A` PosDef.  Same proof as in
    `AndoGeometricMean.sqrt_mul_sqrt_inv`. -/
private lemma sqrt_mul_sqrt_inv'
    {A : Matrix (Fin n) (Fin n) ℂ} (hA : A.PosDef) :
    CFC.sqrt A * CFC.sqrt A⁻¹ = 1 := by
  have h_inv_sqrt : (CFC.sqrt A)⁻¹ = CFC.sqrt A⁻¹ :=
    hA.posSemidef.inv_sqrt
  rw [← h_inv_sqrt]
  haveI : Invertible (CFC.sqrt A) :=
    (hA.isStrictlyPositive.sqrt.posDef).isUnit.invertible
  exact Matrix.mul_inv_of_invertible (CFC.sqrt A)

/-- `√(A⁻¹) · √A = 1` for `A` PosDef. -/
private lemma sqrt_inv_mul_sqrt'
    {A : Matrix (Fin n) (Fin n) ℂ} (hA : A.PosDef) :
    CFC.sqrt A⁻¹ * CFC.sqrt A = 1 := by
  have h_inv_sqrt : (CFC.sqrt A)⁻¹ = CFC.sqrt A⁻¹ :=
    hA.posSemidef.inv_sqrt
  rw [← h_inv_sqrt]
  haveI : Invertible (CFC.sqrt A) :=
    (hA.isStrictlyPositive.sqrt.posDef).isUnit.invertible
  exact Matrix.inv_mul_of_invertible (CFC.sqrt A)

/-- `√(A⁻¹) · √(A⁻¹) = A⁻¹` for `A` PosDef. -/
private lemma sqrt_inv_mul_sqrt_inv'
    {A : Matrix (Fin n) (Fin n) ℂ} (hA : A.PosDef) :
    CFC.sqrt A⁻¹ * CFC.sqrt A⁻¹ = A⁻¹ :=
  CFC.sqrt_mul_sqrt_self A⁻¹ hA.inv.posSemidef.nonneg

/-- `√A` is Hermitian for `A` PosDef. -/
private lemma sqrt_isHermitian
    {A : Matrix (Fin n) (Fin n) ℂ} (_hA : A.PosDef) :
    (CFC.sqrt A).IsHermitian :=
  (CFC.sqrt_nonneg A).posSemidef.isHermitian

/-- `√(A⁻¹)` is Hermitian for `A` PosDef. -/
private lemma sqrt_inv_isHermitian
    {A : Matrix (Fin n) (Fin n) ℂ} (_hA : A.PosDef) :
    (CFC.sqrt A⁻¹).IsHermitian :=
  (CFC.sqrt_nonneg A⁻¹).posSemidef.isHermitian

/-! ## 4. The key step: `Y · Y ≤ M ⟹ Y ≤ √M` for self-adjoint `Y`. -/

set_option maxHeartbeats 1000000 in
-- The lemma chains several CFC-level rewrites (`abs`, `sqrt`, `negPart`,
-- `posPart`) against the scoped MatrixOrder C⋆-algebra typeclasses;
-- the default heartbeat budget is too small for typeclass resolution.
/-- **Operator square root majorization for self-adjoint elements.**

    If `Y` is self-adjoint, `M ≥ 0`, and `Y * Y ≤ M`, then `Y ≤ √M`.

    *Proof.*  Use absolute value: `|Y| ≥ 0`, `(|Y|)² = star Y · Y = Y · Y`
    (since `Y` self-adjoint, `star Y = Y`).  Hence `(|Y|)² ≤ M`.
    Operator monotonicity of √ gives `|Y| = √(|Y|²) ≤ √M`.
    Finally, `Y ≤ |Y|` follows from `|Y| - Y = 2 • Y⁻` with `Y⁻ ≥ 0`. -/
private lemma sa_le_sqrt_of_sq_le
    {Y M : Matrix (Fin n) (Fin n) ℂ}
    (hY : Y.IsHermitian) (_hM : M.PosSemidef) (hSq : Y * Y ≤ M) :
    Y ≤ CFC.sqrt M := by
  -- Y is self-adjoint in the C*-algebra sense.
  have hY_sa : IsSelfAdjoint Y := hY
  -- abs Y is ≥ 0.
  have habs_nonneg : (0 : Matrix (Fin n) (Fin n) ℂ) ≤ CFC.abs Y :=
    CFC.abs_nonneg Y
  -- abs(Y) * abs(Y) = abs(Y)^2 = star Y * Y = Y * Y (Y self-adjoint).
  have habs_mul : CFC.abs Y * CFC.abs Y = Y * Y := by
    have h := CFC.abs_mul_abs Y
    rw [hY_sa.star_eq] at h
    exact h
  -- Hence abs(Y) * abs(Y) ≤ M.
  have h2 : CFC.abs Y * CFC.abs Y ≤ M := habs_mul ▸ hSq
  -- Apply sqrt monotonicity: √(abs(Y) * abs(Y)) ≤ √M.
  have h3 : CFC.sqrt (CFC.abs Y * CFC.abs Y) ≤ CFC.sqrt M :=
    CFC.sqrt_le_sqrt _ _ h2
  -- The LHS is abs(Y) since abs(Y) ≥ 0.
  have h4 : CFC.sqrt (CFC.abs Y * CFC.abs Y) = CFC.abs Y :=
    CFC.sqrt_mul_self (CFC.abs Y) habs_nonneg
  rw [h4] at h3
  -- So abs Y ≤ √M.
  -- Now Y ≤ abs Y since abs Y - Y = 2 • Y⁻ ≥ 0.
  have h5 : Y ≤ CFC.abs Y := by
    -- (abs Y - Y).PosSemidef ⟺ Y ≤ abs Y in MatrixOrder.
    change (CFC.abs Y - Y).PosSemidef
    -- abs Y - Y = 2 • Y⁻ ≥ 0.
    have h_diff : CFC.abs Y - Y = (2 : ℕ) • Y⁻ := CFC.abs_sub_self Y
    have h_neg_nonneg : (0 : Matrix (Fin n) (Fin n) ℂ) ≤ Y⁻ :=
      CFC.negPart_nonneg Y
    have h_smul_nonneg :
        (0 : Matrix (Fin n) (Fin n) ℂ) ≤ (2 : ℕ) • (Y⁻) :=
      nsmul_nonneg h_neg_nonneg 2
    rw [h_diff]
    exact h_smul_nonneg.posSemidef
  exact le_trans h5 h3

/-! ## 5. The Hansen–Pedersen / Ando maximum characterisation. -/

set_option maxHeartbeats 2000000 in
-- The proof juggles three layers of typeclass resolution (`MatrixOrder`,
-- `CStarAlgebra`, `Invertible`) against the Schur-complement block
-- lemma, the operator-monotone square root, and the inv-sqrt
-- conjugation pair.  Default heartbeats are insufficient.
/-- **Hansen–Pedersen / Ando maximum characterisation.**

    For `A.PosDef`, `B.PosDef`, and any `X.PosSemidef` such that the
    block matrix `⎡A X; X B⎤` is positive semidefinite, we have
    `X ≤ A #ₐ B = geometricMean A B`.

    This is the analytic mountain of Ando's joint-concavity proof,
    discharged unconditionally via Schur complement + operator
    monotonicity of √. -/
theorem ando_block_PSD_le_geometricMean
    (A B X : Matrix (Fin n) (Fin n) ℂ)
    (hA : A.PosDef) (hB : B.PosDef) (hX : X.PosSemidef)
    (hBlock : (Matrix.fromBlocks A X X B).PosSemidef) :
    X ≤ geometricMean A B := by
  -- X is Hermitian (from PosSemidef).
  have hX_herm : X.IsHermitian := hX.isHermitian
  -- A is invertible.
  haveI : Invertible A := hA.isUnit.invertible
  -- Step 1: Schur complement.
  -- Rewrite `fromBlocks A X X B` as `fromBlocks A X Xᴴ B` (since X = Xᴴ).
  have hBlock' :
      (Matrix.fromBlocks A X Xᴴ B).PosSemidef := by
    rw [hX_herm.eq]; exact hBlock
  -- Apply fromBlocks₁₁.  This gives `(B - Xᴴ * A⁻¹ * X).PosSemidef`.
  have hSchur := (Matrix.PosDef.fromBlocks₁₁ X B hA).mp hBlock'
  -- Rewrite Xᴴ to X (using X Hermitian).
  rw [hX_herm.eq] at hSchur
  -- This translates to X * A⁻¹ * X ≤ B in MatrixOrder.
  have hXAX_le_B : X * A⁻¹ * X ≤ B := hSchur
  -- Step 2: Conjugate by √(A⁻¹).
  set S' : Matrix (Fin n) (Fin n) ℂ := CFC.sqrt A⁻¹ with hS'_def
  have hS'_herm : S'.IsHermitian := sqrt_inv_isHermitian hA
  -- The conjugation: S' * (X * A⁻¹ * X) * S' ≤ S' * B * S'.
  have hConj := conj_le_of_le hS'_herm hXAX_le_B
  -- The LHS: S' * (X * A⁻¹ * X) * S' = (S' * X * S') * (S' * X * S') = Y².
  set Y : Matrix (Fin n) (Fin n) ℂ := S' * X * S' with hY_def
  set M : Matrix (Fin n) (Fin n) ℂ := S' * B * S' with hM_def
  have hS'S' : S' * S' = A⁻¹ := sqrt_inv_mul_sqrt_inv' hA
  have hLHS : S' * (X * A⁻¹ * X) * S' = Y * Y := by
    -- S' * (X * A⁻¹ * X) * S' = (S' * X * S') * (S' * X * S') = Y * Y
    -- using A⁻¹ = S' * S'.
    change S' * (X * A⁻¹ * X) * S' = (S' * X * S') * (S' * X * S')
    rw [← hS'S']
    -- Both sides equal the fully left-associated product
    -- `S' * X * S' * S' * X * S'`.  Use `ac_rfl` for associative
    -- multiplication in matrices.
    ac_rfl
  rw [hLHS] at hConj
  -- Now hConj : Y * Y ≤ M.
  -- Step 3: Operator monotonicity of √. Need Y self-adjoint, M ≥ 0.
  have hY_herm : Y.IsHermitian := by
    -- Y = S' * X * S' with S' Hermitian and X Hermitian.
    rw [hY_def]
    change (S' * X * S')ᴴ = S' * X * S'
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, hS'_herm.eq, hX_herm.eq]
    -- Remaining goal: S' * (S' * X) = S' * X * S'. Pure associativity.
    ac_rfl
  have hM_psd : M.PosSemidef := by
    -- M = S' * B * S' = S'ᴴ * B * S' since S' Hermitian.
    rw [hM_def]
    have := hB.posSemidef.conjTranspose_mul_mul_same S'
    rwa [hS'_herm.eq] at this
  have hY_le_sqrtM : Y ≤ CFC.sqrt M := sa_le_sqrt_of_sq_le hY_herm hM_psd hConj
  -- Step 4: Conjugate back by √A.
  set S : Matrix (Fin n) (Fin n) ℂ := CFC.sqrt A with hS_def
  have hS_herm : S.IsHermitian := sqrt_isHermitian hA
  have hSS' : S * S' = 1 := sqrt_mul_sqrt_inv' hA
  have hS'S : S' * S = 1 := sqrt_inv_mul_sqrt' hA
  -- S * Y * S ≤ S * √M * S = geometricMean A B.
  have hConj2 : S * Y * S ≤ S * CFC.sqrt M * S :=
    conj_le_of_le hS_herm hY_le_sqrtM
  -- S * Y * S = X.
  have hSYS_eq_X : S * Y * S = X := by
    rw [hY_def]
    -- S * (S' * X * S') * S = (S*S') * X * (S'*S) = 1 * X * 1 = X
    calc S * (S' * X * S') * S
        = (S * S') * X * (S' * S) := by ac_rfl
      _ = 1 * X * 1 := by rw [hSS', hS'S]
      _ = X := by rw [one_mul, mul_one]
  -- S * √M * S = geometricMean A B.
  have hSqrtMS_eq_GM :
      S * CFC.sqrt M * S = geometricMean A B := by
    unfold geometricMean
    -- geometricMean = (CFC.sqrt A) * CFC.sqrt (CFC.sqrt A⁻¹ * B * CFC.sqrt A⁻¹)
    --                              * (CFC.sqrt A)
    -- = S * CFC.sqrt (S' * B * S') * S = S * CFC.sqrt M * S
    rfl
  rw [hSYS_eq_X] at hConj2
  rw [hSqrtMS_eq_GM] at hConj2
  exact hConj2

/-! ## 6. Discharge of `IsAndoMaximal`. -/

/-- **Unconditional discharge of `IsAndoMaximal`.**

    The Hansen–Pedersen maximum characterisation says exactly that
    `geometricMean A B` is the largest `X ≥ 0` with the block PSD
    property; this is `IsAndoMaximal`. -/
theorem isAndoMaximal_unconditional : IsAndoMaximal := by
  intro m A B X hA hB hX hBlock
  exact ando_block_PSD_le_geometricMean A B X hA hB hX hBlock

/-! ## 7. Joint concavity — unconditional. -/

/-- **Unconditional joint concavity of Ando's matrix geometric mean.**

    For positive definite `A₁, A₂, B₁, B₂` and `α ∈ [0, 1]`,
        α · (A₁ # B₁) + (1-α) · (A₂ # B₂)
          ≤ (α A₁ + (1-α) A₂) # (α B₁ + (1-α) B₂).

    This is `geometricMean_jointly_concave_of_maximal` with the
    `IsAndoMaximal` hypothesis discharged by
    `isAndoMaximal_unconditional`. -/
theorem geometricMean_jointly_concave_unconditional
    (A₁ A₂ B₁ B₂ : Matrix (Fin n) (Fin n) ℂ)
    (hA₁ : A₁.PosDef) (hA₂ : A₂.PosDef)
    (hB₁ : B₁.PosDef) (hB₂ : B₂.PosDef)
    (α : ℝ) (hα₀ : 0 ≤ α) (hα₁ : α ≤ 1) :
    (α : ℂ) • (geometricMean A₁ B₁) + ((1 - α : ℝ) : ℂ) • (geometricMean A₂ B₂)
      ≤ geometricMean
          ((α : ℂ) • A₁ + ((1 - α : ℝ) : ℂ) • A₂)
          ((α : ℂ) • B₁ + ((1 - α : ℝ) : ℂ) • B₂) :=
  geometricMean_jointly_concave_of_maximal
    isAndoMaximal_unconditional
    A₁ A₂ B₁ B₂ hA₁ hA₂ hB₁ hB₂ α hα₀ hα₁

/-! ## 8. Axiom audit (commented).

    These directives are intended to confirm that the headline
    theorems depend only on Lean's three standard axioms
    (`propext, Classical.choice, Quot.sound`).  No `sorry`, no custom
    `axiom`. -/

-- #print axioms ando_block_PSD_le_geometricMean
-- #print axioms isAndoMaximal_unconditional
-- #print axioms geometricMean_jointly_concave_unconditional
-- VERIFIED 2026-06-01: all three depend only on
--   `propext, Classical.choice, Quot.sound`
-- (Lean's three standard axioms).  No `sorry`, no custom `axiom`.

end UnifiedTheory.LayerB.IsAndoMaximalDischarge
