/-
  LayerB/AndoGeometricMean.lean
  ──────────────────────────────

  **Ando's matrix geometric mean and its joint concavity** (Phase B9
  of the Lindblad-Uhlmann roadmap).

  ## Mathematical statement

  For positive-definite complex matrices `A`, `B`, define the
  **matrix geometric mean**

      A # B  :=  A^{1/2} · (A^{-1/2} · B · A^{-1/2})^{1/2} · A^{1/2}.

  **Ando 1979 (block characterisation).**  `A # B` is the largest
  `X ≥ 0` such that the 2×2 block matrix `⎡A X; X B⎤` is positive
  semidefinite.

  **Ando 1979 (joint concavity).** The map `(A, B) ↦ A # B` is
  jointly concave on the cone of pairs of positive-definite matrices:
  for `α ∈ [0, 1]`,

      α·(A₁#B₁) + (1-α)·(A₂#B₂)  ≤  (αA₁+(1-α)A₂) # (αA₂+(1-α)B₂).

  ## What is proved in this file (zero `sorry`, zero custom `axiom`)

  • `geometricMean` — the matrix geometric mean, defined via the
    continuous functional calculus `CFC.sqrt`.

  • `geometricMean_posSemidef` — `A # B` is positive semidefinite.

  • `geometricMean_isHermitian` — `A # B` is Hermitian.

  • `geometricMean_block_psd` — the **PSD half** of Ando's
    characterisation: `⎡A   A#B; A#B   B⎤` is positive semidefinite.

  • `geometricMean_jointly_concave_of_maximal` — joint concavity,
    assuming the **maximum characterisation** as a `Prop`-shaped
    hypothesis `IsAndoMaximal` (defined below).

  ## What is *scoped* (deferred to a future phase)

  The **maximum half** of Ando's characterisation
      `⎡A X; X B⎤ ≥ 0 ⟹ X ≤ A # B`
  is the analytic mountain of the theory (Hansen–Pedersen-style
  spectral arguments).  It is **declared but not proved** in this
  file; instead we package it as a `Prop` named `IsAndoMaximal`,
  which the (small, purely algebraic) joint-concavity proof then
  takes as a hypothesis.

  This isolates the open analytic step in a single named statement,
  with no `sorry` and no custom `axiom`.

  ## Key Mathlib infrastructure used

  • `CFC.sqrt`, `CFC.sqrt_mul_sqrt_self`, `CFC.sqrt_nonneg`
    — the continuous-functional-calculus square root on
    a C⋆-algebra, which restricts to `Matrix (Fin n) (Fin n) ℂ`.

  • `IsStrictlyPositive.sqrt` (for PosDef → PosDef sqrt) and
    `IsStrictlyPositive.posDef`.

  • `Matrix.posSemidef_self_mul_conjTranspose` (the elementary fact
    `Q · Qᴴ ≥ 0`), the workhorse of the block-PSD direction.

  • `Matrix.fromBlocks_multiply`, `Matrix.fromBlocks_conjTranspose`,
    `Matrix.fromBlocks_smul`, `Matrix.fromBlocks_add` — algebraic
    rewrites for the block constructor.
-/

import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.LinearAlgebra.Matrix.PosDef

set_option relaxedAutoImplicit false

namespace UnifiedTheory.LayerB.AndoGeometricMean

open Matrix Complex
open scoped MatrixOrder ComplexOrder

variable {n : ℕ}

/-! ## 1. Definition of the matrix geometric mean. -/

/-- The **matrix geometric mean** `A # B` for positive-definite
    complex `n × n` matrices `A`, `B`.

    Defined as `A^{1/2} · (A^{-1/2} · B · A^{-1/2})^{1/2} · A^{1/2}`
    via the C⋆-algebra continuous functional calculus `CFC.sqrt`. -/
noncomputable def geometricMean
    (A B : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  let S  := CFC.sqrt A
  let S' := CFC.sqrt A⁻¹
  S * CFC.sqrt (S' * B * S') * S

@[inherit_doc] scoped infix:70 " #ₐ " => geometricMean

/-! ## 2. Basic regularity: `A # B` is PSD and Hermitian. -/

/-- Hermitian-adjoint of `CFC.sqrt M` equals itself
    (the matrix square root is always self-adjoint, since it is
    nonneg in the matrix order). -/
private lemma sqrt_conjTranspose_self
    (M : Matrix (Fin n) (Fin n) ℂ) :
    (CFC.sqrt M)ᴴ = CFC.sqrt M :=
  (CFC.sqrt_nonneg M).isSelfAdjoint

/-- For PosDef `A`, the matrix `√A` is PosDef. -/
private lemma posDef_sqrt
    {A : Matrix (Fin n) (Fin n) ℂ} (hA : A.PosDef) :
    (CFC.sqrt A).PosDef :=
  hA.isStrictlyPositive.sqrt.posDef

/-- For PosDef `A`, the matrix `A⁻¹` is PosDef. -/
private lemma posDef_inv
    {A : Matrix (Fin n) (Fin n) ℂ} (hA : A.PosDef) :
    A⁻¹.PosDef := hA.inv

/-- For PosDef `A`, both `A` and `A⁻¹` (and hence `√A`, `√(A⁻¹)`)
    are nonneg in the matrix order. -/
private lemma nonneg_of_posDef
    {A : Matrix (Fin n) (Fin n) ℂ} (hA : A.PosDef) :
    (0 : Matrix (Fin n) (Fin n) ℂ) ≤ A :=
  hA.posSemidef.nonneg

/-- For PosDef `A`, `√A · √A = A`. -/
private lemma sqrt_mul_sqrt_self_posDef
    {A : Matrix (Fin n) (Fin n) ℂ} (hA : A.PosDef) :
    CFC.sqrt A * CFC.sqrt A = A :=
  CFC.sqrt_mul_sqrt_self A (nonneg_of_posDef hA)

/-- For PosDef `A`, the matrix `√(A⁻¹) · √(A⁻¹) = A⁻¹`. -/
private lemma sqrt_inv_mul_sqrt_inv
    {A : Matrix (Fin n) (Fin n) ℂ} (hA : A.PosDef) :
    CFC.sqrt A⁻¹ * CFC.sqrt A⁻¹ = A⁻¹ :=
  CFC.sqrt_mul_sqrt_self A⁻¹ (nonneg_of_posDef hA.inv)

/-- `√A · √(A⁻¹) = 1` for `A` PosDef.

    Proof: both sides are nonneg matrices whose square is `A · A⁻¹ = 1`.
    Use `CFC.sqrt_unique` (uniqueness of the nonneg sqrt). -/
private lemma sqrt_mul_sqrt_inv
    {A : Matrix (Fin n) (Fin n) ℂ} (hA : A.PosDef) :
    CFC.sqrt A * CFC.sqrt A⁻¹ = 1 := by
  -- A and A⁻¹ commute, and √ is a CFC function in A so it commutes with A⁻¹? Easier:
  -- both √A and √(A⁻¹) are CFC images of A (since A⁻¹ ∈ Algebra-gen by A), so they commute.
  -- Use sqrt_unique on `(√A · √(A⁻¹))^2 = √A·(√(A⁻¹)·√A)·√(A⁻¹) = √A·√(A⁻¹·A)·√(A⁻¹)`...
  -- Cleanest: `√A * √(A⁻¹) = √(A * A⁻¹)` requires commutation. Use that the sqrt of
  -- a PosDef A is the polynomial in A on its spectrum, hence commutes with A⁻¹.
  --
  -- Instead, we prove the equivalent direction using `sqrt_unique` and the fact that
  -- (√A * √(A⁻¹))² = 1 — provided √A and √(A⁻¹) commute.  In a C⋆-algebra they do
  -- (both are CFC images of A: √(A⁻¹) = (√A)⁻¹).
  --
  -- Mathlib already has `Matrix.PosSemidef.inv_sqrt`:
  --   `(CFC.sqrt A)⁻¹ = CFC.sqrt A⁻¹`  (for A PosSemidef).
  have h_inv_sqrt : (CFC.sqrt A)⁻¹ = CFC.sqrt A⁻¹ :=
    hA.posSemidef.inv_sqrt
  -- Hence `CFC.sqrt A * CFC.sqrt A⁻¹ = (CFC.sqrt A) * (CFC.sqrt A)⁻¹`.
  rw [← h_inv_sqrt]
  -- This is `mul_inv_of_invertible` once we know `CFC.sqrt A` is invertible.
  haveI : Invertible (CFC.sqrt A) := (posDef_sqrt hA).isUnit.invertible
  exact Matrix.mul_inv_of_invertible (CFC.sqrt A)

/-- `√(A⁻¹) · √A = 1` for `A` PosDef. -/
private lemma sqrt_inv_mul_sqrt
    {A : Matrix (Fin n) (Fin n) ℂ} (hA : A.PosDef) :
    CFC.sqrt A⁻¹ * CFC.sqrt A = 1 := by
  have h_inv_sqrt : (CFC.sqrt A)⁻¹ = CFC.sqrt A⁻¹ :=
    hA.posSemidef.inv_sqrt
  rw [← h_inv_sqrt]
  haveI : Invertible (CFC.sqrt A) := (posDef_sqrt hA).isUnit.invertible
  exact Matrix.inv_mul_of_invertible (CFC.sqrt A)

/-- The **inner argument** `√(A⁻¹) · B · √(A⁻¹)` is positive semidefinite.
    (Hypothesis `hA` on `A` is kept for API consistency at call sites,
    though the conclusion only requires `B.PosDef`.) -/
private lemma inner_arg_posSemidef
    {A B : Matrix (Fin n) (Fin n) ℂ}
    (_hA : A.PosDef) (hB : B.PosDef) :
    (CFC.sqrt A⁻¹ * B * CFC.sqrt A⁻¹).PosSemidef := by
  -- `√(A⁻¹) · B · √(A⁻¹) = (√(A⁻¹))ᴴ · B · √(A⁻¹)` since `√(A⁻¹)ᴴ = √(A⁻¹)`.
  have hConj : (CFC.sqrt A⁻¹)ᴴ = CFC.sqrt A⁻¹ :=
    sqrt_conjTranspose_self _
  -- `PosSemidef.conjTranspose_mul_mul_same : (Bᴴ · A · B).PosSemidef`.
  -- We need `(Q · B · Q).PosSemidef` where Q = √(A⁻¹) is Hermitian.
  have := hB.posSemidef.conjTranspose_mul_mul_same (CFC.sqrt A⁻¹)
  -- `this : ((CFC.sqrt A⁻¹)ᴴ * B * (CFC.sqrt A⁻¹)).PosSemidef`.
  rwa [hConj] at this

/-- `(geometricMean A B)` is positive semidefinite. -/
theorem geometricMean_posSemidef
    {A B : Matrix (Fin n) (Fin n) ℂ}
    (hA : A.PosDef) (hB : B.PosDef) :
    (geometricMean A B).PosSemidef := by
  -- `A # B = √A · √(M) · √A` where `M = √(A⁻¹) · B · √(A⁻¹)`.
  -- This has the form `Sᴴ · X · S` with `S = √A` Hermitian and `X = √M ≥ 0`.
  unfold geometricMean
  -- name the inner sqrt for clarity
  set M := CFC.sqrt A⁻¹ * B * CFC.sqrt A⁻¹ with hM_def
  have hM_psd : M.PosSemidef := inner_arg_posSemidef hA hB
  have hN_psd : (CFC.sqrt M).PosSemidef := (CFC.sqrt_nonneg M).posSemidef
  -- `√A · √M · √A = (√A)ᴴ · √M · √A` (since √A Hermitian)
  have hConj : (CFC.sqrt A)ᴴ = CFC.sqrt A :=
    sqrt_conjTranspose_self _
  have := hN_psd.conjTranspose_mul_mul_same (CFC.sqrt A)
  -- `this : ((CFC.sqrt A)ᴴ * CFC.sqrt M * CFC.sqrt A).PosSemidef`
  rw [hConj] at this
  -- The goal is `(CFC.sqrt A * CFC.sqrt M * CFC.sqrt A).PosSemidef`
  -- matching `this` exactly.
  exact this

/-- `(geometricMean A B)` is Hermitian. -/
theorem geometricMean_isHermitian
    {A B : Matrix (Fin n) (Fin n) ℂ}
    (hA : A.PosDef) (hB : B.PosDef) :
    (geometricMean A B).IsHermitian :=
  (geometricMean_posSemidef hA hB).isHermitian

/-! ## 3. Block-PSD direction of Ando's characterisation.

    **Theorem.** For PosDef `A`, `B`, the block matrix
        ⎡ A     A#B ⎤
        ⎣ A#B   B   ⎦
    is positive semidefinite.

    **Proof.** Let `S := √A`, `M := √(A⁻¹)·B·√(A⁻¹)`, `N := √M`.
    Set `X := A # B = S · N · S`. Define the block matrix
        Q := ⎡ S    0 ⎤
             ⎣ S·N  0 ⎦  ∈ Mat_{2n × 2n}.
    Then `Q · Qᴴ = ⎡ A   A#B ⎤
                   ⎣ A#B  B  ⎦` by direct computation, using
    `S · S = A`, `S · N · S = X`, and `(S·N) · (N·S) = S·M·S = B`
    (the last because `S · √(A⁻¹) = 1` so `S·M·S = B`).
    Since `Q · Qᴴ` is always PSD, the result follows.
-/

/-- Algebraic identity: with `S := √A`, `N := √(√(A⁻¹)·B·√(A⁻¹))`,
    we have `S · N · N · S = B`. -/
private lemma SN_NS_eq_B
    {A B : Matrix (Fin n) (Fin n) ℂ}
    (hA : A.PosDef) (hB : B.PosDef) :
    CFC.sqrt A * CFC.sqrt (CFC.sqrt A⁻¹ * B * CFC.sqrt A⁻¹)
        * CFC.sqrt (CFC.sqrt A⁻¹ * B * CFC.sqrt A⁻¹) * CFC.sqrt A
      = B := by
  -- step 1: N · N = M  (sqrt mul sqrt self).
  have hM_psd : (CFC.sqrt A⁻¹ * B * CFC.sqrt A⁻¹).PosSemidef :=
    inner_arg_posSemidef hA hB
  have hNN : CFC.sqrt (CFC.sqrt A⁻¹ * B * CFC.sqrt A⁻¹)
                * CFC.sqrt (CFC.sqrt A⁻¹ * B * CFC.sqrt A⁻¹)
              = CFC.sqrt A⁻¹ * B * CFC.sqrt A⁻¹ :=
    CFC.sqrt_mul_sqrt_self _ hM_psd.nonneg
  -- step 2: rewrite `S · N · N · S = S · (N · N) · S = S · M · S`.
  have h_assoc :
      CFC.sqrt A * CFC.sqrt (CFC.sqrt A⁻¹ * B * CFC.sqrt A⁻¹)
        * CFC.sqrt (CFC.sqrt A⁻¹ * B * CFC.sqrt A⁻¹) * CFC.sqrt A
      = CFC.sqrt A *
          (CFC.sqrt (CFC.sqrt A⁻¹ * B * CFC.sqrt A⁻¹) *
            CFC.sqrt (CFC.sqrt A⁻¹ * B * CFC.sqrt A⁻¹)) * CFC.sqrt A := by
    ac_rfl
  rw [h_assoc, hNN]
  -- step 3: S · (√(A⁻¹) · B · √(A⁻¹)) · S = (S · √(A⁻¹)) · B · (√(A⁻¹) · S)
  --       = 1 · B · 1 = B.
  have h_S_sqrtinv : CFC.sqrt A * CFC.sqrt A⁻¹ = 1 := sqrt_mul_sqrt_inv hA
  have h_sqrtinv_S : CFC.sqrt A⁻¹ * CFC.sqrt A = 1 := sqrt_inv_mul_sqrt hA
  -- Reorganise: `S · (√(A⁻¹) · B · √(A⁻¹)) · S`
  --           = `(S · √(A⁻¹)) · B · (√(A⁻¹) · S)`.
  calc CFC.sqrt A * (CFC.sqrt A⁻¹ * B * CFC.sqrt A⁻¹) * CFC.sqrt A
      = (CFC.sqrt A * CFC.sqrt A⁻¹) * B * (CFC.sqrt A⁻¹ * CFC.sqrt A) := by
        ac_rfl
    _ = (1 : Matrix (Fin n) (Fin n) ℂ) * B * (1 : Matrix (Fin n) (Fin n) ℂ) := by
        rw [h_S_sqrtinv, h_sqrtinv_S]
    _ = B := by rw [one_mul, mul_one]

/-- The block matrix `⎡A  A#B; A#B  B⎤` is positive semidefinite,
    realised as `Q · Qᴴ` with `Q := ⎡S 0; S·N 0⎤` for
    `S := √A`, `N := √(√(A⁻¹) · B · √(A⁻¹))`. -/
theorem geometricMean_block_psd
    {A B : Matrix (Fin n) (Fin n) ℂ}
    (hA : A.PosDef) (hB : B.PosDef) :
    (Matrix.fromBlocks A (geometricMean A B) (geometricMean A B) B).PosSemidef := by
  -- The witness Q.
  set S  : Matrix (Fin n) (Fin n) ℂ := CFC.sqrt A with hS_def
  set M  : Matrix (Fin n) (Fin n) ℂ := CFC.sqrt A⁻¹ * B * CFC.sqrt A⁻¹ with hM_def
  set N  : Matrix (Fin n) (Fin n) ℂ := CFC.sqrt M with hN_def
  set X  : Matrix (Fin n) (Fin n) ℂ := geometricMean A B with hX_def
  -- We have X = S · N · S.
  have hX : X = S * N * S := by
    simp [hX_def, geometricMean, hS_def, hN_def, hM_def]
  -- Set Q.
  set Q : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℂ :=
    Matrix.fromBlocks S 0 (S * N) 0 with hQ_def
  -- Claim 1: Q · Qᴴ = fromBlocks A X X B.
  have hQQH :
      Q * Qᴴ = Matrix.fromBlocks A X X B := by
    -- Compute conjTranspose of Q.
    have hConj_S : Sᴴ = S := sqrt_conjTranspose_self _
    have hM_psd : M.PosSemidef := inner_arg_posSemidef hA hB
    have hConj_N : Nᴴ = N := sqrt_conjTranspose_self _
    have hConj_SN : (S * N)ᴴ = N * S := by
      rw [Matrix.conjTranspose_mul, hConj_S, hConj_N]
    -- `Qᴴ = fromBlocks Sᴴ (SN)ᴴ 0ᴴ 0ᴴ = fromBlocks S (NS) 0 0`.
    have hQH : Qᴴ = Matrix.fromBlocks S (N * S) 0 0 := by
      rw [hQ_def, Matrix.fromBlocks_conjTranspose, hConj_S, hConj_SN]
      simp
    -- Block-multiply: `fromBlocks S 0 (SN) 0 · fromBlocks S (NS) 0 0`.
    rw [hQH, hQ_def, Matrix.fromBlocks_multiply]
    -- Targets per block.
    -- Top-left: S·S + 0·0 = A.
    -- Top-right: S·(NS) + 0·0 = S·N·S = X.
    -- Bot-left: SN·S + 0·0 = SNS = X.
    -- Bot-right: SN·NS + 0·0 = B.
    have hTL : S * S + 0 * 0 = A := by
      have : S * S = A := sqrt_mul_sqrt_self_posDef hA
      simp [this]
    have hTR : S * (N * S) + 0 * 0 = X := by
      have : S * (N * S) = S * N * S := by rw [← mul_assoc]
      rw [zero_mul, add_zero, this, hX]
    have hBL : S * N * S + 0 * 0 = X := by
      rw [zero_mul, add_zero, hX]
    have hBR : S * N * (N * S) + 0 * 0 = B := by
      rw [zero_mul, add_zero]
      have h_assoc : S * N * (N * S) = S * N * N * S := by
        rw [mul_assoc (S * N) N S]
      rw [h_assoc]
      simpa [hS_def, hN_def, hM_def] using SN_NS_eq_B hA hB
    -- Apply each rewrite to the corresponding block.
    rw [hTL, hTR, hBL, hBR]
  -- Claim 2: Q · Qᴴ is PSD (always).
  have hPSD : (Q * Qᴴ).PosSemidef := Matrix.posSemidef_self_mul_conjTranspose Q
  -- Combine.
  rw [hQQH] at hPSD
  exact hPSD

/-! ## 4. Maximum characterisation (scoped as a `Prop`-hypothesis).

    The other direction of Ando's characterisation — that `A # B`
    is the largest `X ≥ 0` such that `⎡A X; X B⎤ ≥ 0` — is the
    deep analytic ingredient (Hansen–Pedersen, Ando 1979 §3).

    We **package** it as a `Prop` so that joint concavity becomes a
    one-line algebraic consequence; we do **not** prove this `Prop`
    in this file (no `sorry`, no custom `axiom`).
-/

/-- The **maximum characterisation** of `A # B`: for any PosSemidef
    `X` such that `⎡A X; X B⎤` is PSD, we have `X ≤ A # B`.

    This is *the* analytic ingredient of Ando's theorem.  Stated
    here as a `Prop`-hypothesis, to be discharged in a later phase
    by a spectral / Hansen–Pedersen argument. -/
def IsAndoMaximal : Prop :=
  ∀ {m : ℕ} (A B X : Matrix (Fin m) (Fin m) ℂ),
    A.PosDef → B.PosDef → X.PosSemidef →
    (Matrix.fromBlocks A X X B).PosSemidef →
    X ≤ geometricMean A B

/-! ## 5. Joint concavity (one-liner from the maximum characterisation). -/

/-- Off-diagonal arithmetic: `α • X + (1 - α) • Y` for `α ∈ [0, 1]`
    is PosSemidef whenever both `X` and `Y` are. -/
private lemma psd_convex_combo
    {X Y : Matrix (Fin n) (Fin n) ℂ}
    (hX : X.PosSemidef) (hY : Y.PosSemidef)
    {α : ℝ} (hα₀ : 0 ≤ α) (hα₁ : α ≤ 1) :
    ((α : ℂ) • X + ((1 - α : ℝ) : ℂ) • Y).PosSemidef := by
  have hαC : (0 : ℂ) ≤ (α : ℂ) := by
    rw [Complex.le_def]; refine ⟨by simpa using hα₀, ?_⟩; simp
  have h1mα : (0 : ℝ) ≤ 1 - α := by linarith
  have h1mαC : (0 : ℂ) ≤ ((1 - α : ℝ) : ℂ) := by
    rw [Complex.le_def]; refine ⟨by simpa using h1mα, ?_⟩; simp
  exact (hX.smul hαC).add (hY.smul h1mαC)

/-- Convex combination of PosDef matrices is PosDef when `α ∈ [0, 1]`. -/
private lemma posDef_convex_combo
    {X Y : Matrix (Fin n) (Fin n) ℂ}
    (hX : X.PosDef) (hY : Y.PosDef)
    {α : ℝ} (hα₀ : 0 ≤ α) (hα₁ : α ≤ 1) :
    ((α : ℂ) • X + ((1 - α : ℝ) : ℂ) • Y).PosDef := by
  have h1mα : (0 : ℝ) ≤ 1 - α := by linarith
  have h1mαC : (0 : ℂ) ≤ ((1 - α : ℝ) : ℂ) := by
    rw [Complex.le_def]; refine ⟨by simpa using h1mα, ?_⟩; simp
  -- Case α = 0: 1 - α = 1 > 0, so combo = Y is PosDef.
  -- Case α > 0: α • X is PosDef and (1 - α) • Y is PSD.
  rcases lt_or_eq_of_le hα₀ with hα_pos | hα_zero
  · have hαC_pos : (0 : ℂ) < (α : ℂ) := by
      rw [Complex.lt_def]; refine ⟨by simpa using hα_pos, ?_⟩; simp
    have hαX_PD : ((α : ℂ) • X).PosDef := hX.smul hαC_pos
    have h1mαY_PSD : (((1 - α : ℝ) : ℂ) • Y).PosSemidef :=
      hY.posSemidef.smul h1mαC
    exact hαX_PD.add_posSemidef h1mαY_PSD
  · have h_eq : α = 0 := hα_zero.symm
    subst h_eq
    have : (1 - (0 : ℝ) : ℝ) = 1 := by norm_num
    have h1mαC_pos : (0 : ℂ) < ((1 - (0 : ℝ) : ℝ) : ℂ) := by
      rw [Complex.lt_def]; refine ⟨by simp, ?_⟩; simp
    have h_PD : (((1 - (0 : ℝ) : ℝ) : ℂ) • Y).PosDef := hY.smul h1mαC_pos
    have h_simp :
        ((0 : ℝ) : ℂ) • X + (((1 - (0 : ℝ) : ℝ) : ℂ)) • Y
          = (((1 - (0 : ℝ) : ℝ) : ℂ)) • Y := by simp
    rw [h_simp]; exact h_PD

/-- **Joint concavity of the matrix geometric mean** (Ando 1979),
    conditional on the maximum-characterisation hypothesis.

    For PosDef `A₁, A₂, B₁, B₂` and `α ∈ [0, 1]`,
        α · (A₁ # B₁) + (1-α) · (A₂ # B₂)
          ≤ (α A₁ + (1-α) A₂) # (α B₁ + (1-α) B₂).

    **Proof.**
    (1) By `geometricMean_block_psd`, each block `⎡Aᵢ Xᵢ; Xᵢ Bᵢ⎤`
        is PSD where `Xᵢ := Aᵢ # Bᵢ`.
    (2) Convex combinations of PSD are PSD:
        `⎡αA₁+(1-α)A₂   αX₁+(1-α)X₂
          αX₁+(1-α)X₂   αB₁+(1-α)B₂⎤` is PSD.
    (3) The convex-combination top-left and bottom-right blocks are
        PosDef (positive convex combination of PosDef), and
        `αX₁ + (1-α)X₂` is PSD.
    (4) Apply `hMax` (the maximum characterisation) to conclude
        `αX₁ + (1-α)X₂ ≤ (αA₁+(1-α)A₂) # (αB₁+(1-α)B₂)`. -/
theorem geometricMean_jointly_concave_of_maximal
    (hMax : IsAndoMaximal)
    (A₁ A₂ B₁ B₂ : Matrix (Fin n) (Fin n) ℂ)
    (hA₁ : A₁.PosDef) (hA₂ : A₂.PosDef)
    (hB₁ : B₁.PosDef) (hB₂ : B₂.PosDef)
    (α : ℝ) (hα₀ : 0 ≤ α) (hα₁ : α ≤ 1) :
    (α : ℂ) • (geometricMean A₁ B₁) + ((1 - α : ℝ) : ℂ) • (geometricMean A₂ B₂)
      ≤ geometricMean
          ((α : ℂ) • A₁ + ((1 - α : ℝ) : ℂ) • A₂)
          ((α : ℂ) • B₁ + ((1 - α : ℝ) : ℂ) • B₂) := by
  -- (1) Block PSD for each pair.
  have hM₁ := geometricMean_block_psd hA₁ hB₁
  have hM₂ := geometricMean_block_psd hA₂ hB₂
  -- (2) Convex combination of PSDs in the block matrix world.
  have hαC : (0 : ℂ) ≤ (α : ℂ) := by
    rw [Complex.le_def]; refine ⟨by simpa using hα₀, ?_⟩; simp
  have h1mα : (0 : ℝ) ≤ 1 - α := by linarith
  have h1mαC : (0 : ℂ) ≤ ((1 - α : ℝ) : ℂ) := by
    rw [Complex.le_def]; refine ⟨by simpa using h1mα, ?_⟩; simp
  have hα_scaled := hM₁.smul hαC
  have h1mα_scaled := hM₂.smul h1mαC
  have hSum := hα_scaled.add h1mα_scaled
  -- Rewrite as a single fromBlocks.
  have h_lin :
      (α : ℂ) • Matrix.fromBlocks A₁ (geometricMean A₁ B₁) (geometricMean A₁ B₁) B₁
        + ((1 - α : ℝ) : ℂ) • Matrix.fromBlocks A₂ (geometricMean A₂ B₂)
            (geometricMean A₂ B₂) B₂
      = Matrix.fromBlocks
          ((α : ℂ) • A₁ + ((1 - α : ℝ) : ℂ) • A₂)
          ((α : ℂ) • geometricMean A₁ B₁
            + ((1 - α : ℝ) : ℂ) • geometricMean A₂ B₂)
          ((α : ℂ) • geometricMean A₁ B₁
            + ((1 - α : ℝ) : ℂ) • geometricMean A₂ B₂)
          ((α : ℂ) • B₁ + ((1 - α : ℝ) : ℂ) • B₂) := by
    rw [Matrix.fromBlocks_smul, Matrix.fromBlocks_smul, Matrix.fromBlocks_add]
  rw [h_lin] at hSum
  -- (3) Convex combinations of PosDef are PosDef; combinations of PSD are PSD.
  have hA_combo : ((α : ℂ) • A₁ + ((1 - α : ℝ) : ℂ) • A₂).PosDef :=
    posDef_convex_combo hA₁ hA₂ hα₀ hα₁
  have hB_combo : ((α : ℂ) • B₁ + ((1 - α : ℝ) : ℂ) • B₂).PosDef :=
    posDef_convex_combo hB₁ hB₂ hα₀ hα₁
  have hX_combo : ((α : ℂ) • geometricMean A₁ B₁
                    + ((1 - α : ℝ) : ℂ) • geometricMean A₂ B₂).PosSemidef :=
    psd_convex_combo (geometricMean_posSemidef hA₁ hB₁)
      (geometricMean_posSemidef hA₂ hB₂) hα₀ hα₁
  -- (4) Apply hMax.
  exact hMax _ _ _ hA_combo hB_combo hX_combo hSum

/-! ## 6. Axiom audit (commented).

    The following are intended to print only `propext, Classical.choice,
    Quot.sound` (Lean's three standard axioms).  No `sorry`, no custom
    `axiom`.  `geometricMean_jointly_concave_of_maximal` additionally
    threads the `IsAndoMaximal` hypothesis through its conclusion. -/

-- #print axioms geometricMean_posSemidef
-- #print axioms geometricMean_block_psd
-- #print axioms geometricMean_jointly_concave_of_maximal

end UnifiedTheory.LayerB.AndoGeometricMean
