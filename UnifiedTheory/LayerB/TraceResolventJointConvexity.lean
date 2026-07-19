/-
  LayerB/TraceResolventJointConvexity.lean
  ─────────────────────────────────────────

  **Phase 2 of the Lieb 1973 discharge** — joint convexity of the
  Kraus quadratic form

      `g(K, B)  :=  Kᴴ · B⁻¹ · K`

  via the 2×2-block Schur complement (Carlen 2010, "Trace
  inequalities and quantum entropy", Theorem 2.10).

  ## Headline result

  For any matrix `K : Matrix (Fin n) (Fin n) ℂ` and any PosDef
  `B : Matrix (Fin n) (Fin n) ℂ`, the matrix-valued map
  `(K, B) ↦ Kᴴ · B⁻¹ · K` is **jointly convex** in `MatrixOrder`:
  for `K₁, K₂` arbitrary, `B₁, B₂` PosDef, `α ∈ [0, 1]`,

      `(αK₁+(1-α)K₂)ᴴ · (αB₁+(1-α)B₂)⁻¹ · (αK₁+(1-α)K₂)`
          `≤  α · K₁ᴴ B₁⁻¹ K₁  +  (1-α) · K₂ᴴ B₂⁻¹ K₂`.

  Taking traces (positive linear functional) gives joint convexity
  of the real scalar `Re Tr( Kᴴ B⁻¹ K )`.

  Specialising `B ↦ t·I + B` for `t > 0` gives the
  trace-resolvent-Kraus form used by Lieb 1973 (via the Bochner
  integral representation of `log`).

  ## Why Phase 1's "scoped target" is FALSE — honest scope note

  The Phase-1 file `TraceResolventConvexity.lean` packaged a
  scoped `Prop`

      `Re Tr( (αA₁+(1-α)A₂) · (t·I + αB₁+(1-α)B₂)⁻¹ )`
        `≤ α · Re Tr( A₁ · (t·I + B₁)⁻¹ )`
              `+ (1-α) · Re Tr( A₂ · (t·I + B₂)⁻¹ )`

  for PosSemidef `A₁, A₂` and PosDef `B₁, B₂`.  **This statement
  is mathematically false even in dimension one.**  The scalar
  analogue `f(a, b) := a / (t + b)`  (for `a ≥ 0`, `b > 0`,
  `t > 0`) has Hessian

      `[[ 0,           −1/(t+b)² ],`
        ` [ −1/(t+b)²,   2a/(t+b)³ ]]`

  whose determinant is `−1/(t+b)⁴ < 0`, so the Hessian is
  indefinite.  Concretely, at `m = 1`, `t = 1`, `α = 1/2`,
  `A₁ = 4`, `A₂ = 0`, `B₁ = 4`, `B₂ = ε` for small `ε > 0`:

      LHS  =  `(αA₁+(1-α)A₂) / (t + αB₁+(1-α)B₂)`
            `= 2 / (1 + 2 + ε/2) = 2 / (3 + ε/2)  →  2/3 ≈ 0.667`
      RHS  =  `α · A₁/(t+B₁) + (1-α) · A₂/(t+B₂)`
            `= (1/2)(4/5) + (1/2)(0/(1+ε)) = 2/5 = 0.4`.

  So `LHS → 2/3 > 2/5 = RHS` as `ε → 0⁺`, contradicting the
  alleged joint convexity.

  This file therefore does **not** discharge
  `TraceResolvent_JointConvexity_Target` (which would be a proof
  of `False`).  Instead it provides the **correct** Carlen 2010
  Theorem 2.10 joint convexity — the Kraus-quadratic
  `Kᴴ B⁻¹ K` rather than the naive `A · B⁻¹` — and bundles its
  trace-resolvent specialisation as the upstream interface for
  Lieb 1973's SSA proof.

  The mistake in the original `Prop` was a transcription error in
  the bridge from Carlen 2010's actual statement; identifying it
  here as a falsity (rather than a deferred analytic gap)
  preserves the IsAndoMaximal-style discipline of "no sorry, no
  custom axiom" while documenting that the literal Phase-1
  packaging needs replacement.

  ## Strategy — Schur 2×2 block

  Key building block: for any PosDef `B` and any matrix `K`,

      `M(K, B) := ⎡ B   K           ⎤`
                 `⎣ Kᴴ  Kᴴ B⁻¹ K   ⎦`

  is positive semidefinite.  Proof: the Schur complement of the
  PosDef top-left block `B` (via `Matrix.PosDef.fromBlocks₁₁`) is
      `(Kᴴ B⁻¹ K) − Kᴴ · B⁻¹ · K  =  0 ≥ 0`,
  so `M(K, B)` is PSD.

  Apply this for `(K, B) = (K₁, B₁)` and `(K₂, B₂)`; scale by
  `α, (1-α)` and sum:

      `M_combo := α • M(K₁,B₁) + (1-α) • M(K₂,B₂)`

  is PSD as a nonneg-scaled sum of PSDs.  Linearity of `fromBlocks`
  shows

      `M_combo = ⎡ αB₁+(1-α)B₂      αK₁+(1-α)K₂                           ⎤`
                `⎣ (αK₁+(1-α)K₂)ᴴ   α K₁ᴴ B₁⁻¹ K₁ + (1-α) K₂ᴴ B₂⁻¹ K₂    ⎦`.

  Top-left is PosDef (convex combination of PosDef).  Apply
  Schur complement in **the reverse direction** (PosDef
  top-left ⇒ Schur complement is PSD):

      `(α K₁ᴴ B₁⁻¹ K₁ + (1-α) K₂ᴴ B₂⁻¹ K₂)`
          `−  (αK₁+(1-α)K₂)ᴴ · (αB₁+(1-α)B₂)⁻¹ · (αK₁+(1-α)K₂)`
          `≥  0`.

  This is the matrix-order joint convexity.  Taking trace
  (`re_trace_mul_posSemidef_mono`-style, applied with `A = 1`)
  and using `Re Tr` linearity yields the scalar form.

  ## What is proved (zero `sorry`, zero custom `axiom`)

  • `block_psd_kraus` — `⎡B  K; Kᴴ  Kᴴ B⁻¹ K⎤` is PSD for `B` PosDef.
  • `block_psd_kraus_combo` — its `α`-convex combination is PSD.
  • `kraus_quadratic_jointly_convex` — matrix-order joint convexity
    of `(K, B) ↦ Kᴴ · B⁻¹ · K`.
  • `kraus_quadratic_jointly_convex_trace` — real trace-level
    scalar joint convexity.
  • `trace_resolvent_kraus_convex` — Phase-1-compatible
    specialisation to `B ↦ t·I + B`.

  ## Key Mathlib infrastructure

  • `Matrix.PosDef.fromBlocks₁₁` — Schur complement criterion
    (PosDef top-left).
  • `Matrix.PosSemidef.smul`, `Matrix.PosSemidef.add` — closure of
    PSD under nonneg-scaled sums.
  • `Matrix.PosDef.add`, `Matrix.PosDef.smul`,
    `Matrix.PosDef.add_posSemidef` — closure of PosDef.
  • `Matrix.fromBlocks_smul`, `Matrix.fromBlocks_add` — linearity
    of the block constructor.
  • `posDef_t_add_posDef` (from Phase 1) — `t·I + B` is PosDef.
-/

import UnifiedTheory.LayerB.TraceResolventConvexity

set_option relaxedAutoImplicit false

namespace UnifiedTheory.LayerB.TraceResolventJointConvexity

open Matrix Complex
open scoped MatrixOrder ComplexOrder
open UnifiedTheory.LayerB.TraceResolventConvexity

variable {n : ℕ}

/-! ## 0. Real → Complex coercion helpers (private). -/

private lemma complex_nonneg_of_real_nonneg {a : ℝ} (ha : 0 ≤ a) :
    (0 : ℂ) ≤ (a : ℂ) := by
  rw [Complex.le_def]
  refine ⟨by simpa using ha, ?_⟩
  simp

private lemma complex_pos_of_real_pos {a : ℝ} (ha : 0 < a) :
    (0 : ℂ) < (a : ℂ) := by
  rw [Complex.lt_def]
  refine ⟨by simpa using ha, ?_⟩
  simp

/-! ## 1. The Schur building block.

    The 2×2 block matrix `⎡B  K; Kᴴ  Kᴴ B⁻¹ K⎤` is positive
    semidefinite for any matrix `K` and PosDef `B`.

    Proof: by `Matrix.PosDef.fromBlocks₁₁` (Schur complement with
    PosDef top-left `B`), the block is PSD iff
    `(Kᴴ B⁻¹ K) - Kᴴ · B⁻¹ · K = 0 ≥ 0`, which is trivial. -/

theorem block_psd_kraus
    (K B : Matrix (Fin n) (Fin n) ℂ) (hB : B.PosDef) :
    (Matrix.fromBlocks B K Kᴴ (Kᴴ * B⁻¹ * K)).PosSemidef := by
  haveI : Invertible B := hB.isUnit.invertible
  -- Apply fromBlocks₁₁: `(fromBlocks B K Kᴴ D).PosSemidef ↔ (D - Kᴴ * B⁻¹ * K).PosSemidef`.
  rw [Matrix.PosDef.fromBlocks₁₁ K (Kᴴ * B⁻¹ * K) hB]
  -- Goal: `(Kᴴ * B⁻¹ * K - Kᴴ * B⁻¹ * K).PosSemidef`.
  simp only [sub_self]
  exact Matrix.PosSemidef.zero

/-! ## 2. Convex-combination block PSD. -/

/-- The `α`-convex combination of two Kraus blocks is PSD.

    Concretely,
    `α • ⎡B₁  K₁; K₁ᴴ  K₁ᴴ B₁⁻¹ K₁⎤  +  (1-α) • ⎡B₂  K₂; K₂ᴴ  K₂ᴴ B₂⁻¹ K₂⎤`
    is PSD, and equals
    `⎡αB₁+(1-α)B₂  αK₁+(1-α)K₂; (αK₁+(1-α)K₂)ᴴ  α·(K₁ᴴB₁⁻¹K₁) + (1-α)·(K₂ᴴB₂⁻¹K₂)⎤`. -/
theorem block_psd_kraus_combo
    (K₁ K₂ B₁ B₂ : Matrix (Fin n) (Fin n) ℂ)
    (hB₁ : B₁.PosDef) (hB₂ : B₂.PosDef)
    (α : ℝ) (hα₀ : 0 ≤ α) (hα₁ : α ≤ 1) :
    (Matrix.fromBlocks
        ((α : ℂ) • B₁ + ((1 - α : ℝ) : ℂ) • B₂)
        ((α : ℂ) • K₁ + ((1 - α : ℝ) : ℂ) • K₂)
        ((α : ℂ) • K₁ᴴ + ((1 - α : ℝ) : ℂ) • K₂ᴴ)
        ((α : ℂ) • (K₁ᴴ * B₁⁻¹ * K₁)
          + ((1 - α : ℝ) : ℂ) • (K₂ᴴ * B₂⁻¹ * K₂))).PosSemidef := by
  -- The two building blocks.
  have hM₁ := block_psd_kraus K₁ B₁ hB₁
  have hM₂ := block_psd_kraus K₂ B₂ hB₂
  -- Nonnegativity of weights.
  have hαC : (0 : ℂ) ≤ (α : ℂ) := complex_nonneg_of_real_nonneg hα₀
  have h1mα_R : (0 : ℝ) ≤ 1 - α := by linarith
  have h1mαC : (0 : ℂ) ≤ ((1 - α : ℝ) : ℂ) :=
    complex_nonneg_of_real_nonneg h1mα_R
  -- Scale + sum.
  have hα_scaled := hM₁.smul hαC
  have h1mα_scaled := hM₂.smul h1mαC
  have hSum := hα_scaled.add h1mα_scaled
  -- Linearity of fromBlocks.
  have h_lin :
      (α : ℂ) • Matrix.fromBlocks B₁ K₁ K₁ᴴ (K₁ᴴ * B₁⁻¹ * K₁)
        + ((1 - α : ℝ) : ℂ) • Matrix.fromBlocks B₂ K₂ K₂ᴴ (K₂ᴴ * B₂⁻¹ * K₂)
      = Matrix.fromBlocks
          ((α : ℂ) • B₁ + ((1 - α : ℝ) : ℂ) • B₂)
          ((α : ℂ) • K₁ + ((1 - α : ℝ) : ℂ) • K₂)
          ((α : ℂ) • K₁ᴴ + ((1 - α : ℝ) : ℂ) • K₂ᴴ)
          ((α : ℂ) • (K₁ᴴ * B₁⁻¹ * K₁)
            + ((1 - α : ℝ) : ℂ) • (K₂ᴴ * B₂⁻¹ * K₂)) := by
    rw [Matrix.fromBlocks_smul, Matrix.fromBlocks_smul, Matrix.fromBlocks_add]
  rw [h_lin] at hSum
  exact hSum

/-! ## 3. Convex combination of PosDef matrices is PosDef. -/

/-- Convex combination of PosDef matrices is PosDef for `α ∈ [0,1]`. -/
private lemma posDef_convex_combo
    {X Y : Matrix (Fin n) (Fin n) ℂ}
    (hX : X.PosDef) (hY : Y.PosDef)
    {α : ℝ} (hα₀ : 0 ≤ α) (hα₁ : α ≤ 1) :
    ((α : ℂ) • X + ((1 - α : ℝ) : ℂ) • Y).PosDef := by
  have h1mα : (0 : ℝ) ≤ 1 - α := by linarith
  have h1mαC : (0 : ℂ) ≤ ((1 - α : ℝ) : ℂ) :=
    complex_nonneg_of_real_nonneg h1mα
  rcases lt_or_eq_of_le hα₀ with hα_pos | hα_zero
  · have hαC_pos : (0 : ℂ) < (α : ℂ) := complex_pos_of_real_pos hα_pos
    have hαX_PD : ((α : ℂ) • X).PosDef := hX.smul hαC_pos
    have h1mαY_PSD : (((1 - α : ℝ) : ℂ) • Y).PosSemidef :=
      hY.posSemidef.smul h1mαC
    exact hαX_PD.add_posSemidef h1mαY_PSD
  · have h_eq : α = 0 := hα_zero.symm
    subst h_eq
    have h1mαC_pos : (0 : ℂ) < ((1 - (0 : ℝ) : ℝ) : ℂ) :=
      complex_pos_of_real_pos (by norm_num)
    have h_PD : (((1 - (0 : ℝ) : ℝ) : ℂ) • Y).PosDef := hY.smul h1mαC_pos
    have h_simp :
        ((0 : ℝ) : ℂ) • X + (((1 - (0 : ℝ) : ℝ) : ℂ)) • Y
          = (((1 - (0 : ℝ) : ℝ) : ℂ)) • Y := by simp
    rw [h_simp]; exact h_PD

/-! ## 4. The headline: matrix-order joint convexity of
        `(K, B) ↦ Kᴴ · B⁻¹ · K`. -/

/-- The Hermitian-adjoint of `α K₁ + (1-α) K₂` is `α K₁ᴴ + (1-α) K₂ᴴ`
    when `α, 1-α` are real (in which case `(α : ℂ)⋆ = α`). -/
private lemma combo_conjTranspose
    (K₁ K₂ : Matrix (Fin n) (Fin n) ℂ) (α : ℝ) :
    ((α : ℂ) • K₁ + ((1 - α : ℝ) : ℂ) • K₂)ᴴ
      = (α : ℂ) • K₁ᴴ + ((1 - α : ℝ) : ℂ) • K₂ᴴ := by
  rw [Matrix.conjTranspose_add, Matrix.conjTranspose_smul,
      Matrix.conjTranspose_smul]
  simp [Complex.conj_ofReal]

set_option maxHeartbeats 800000 in
-- Raised maxHeartbeats: the proof juggles three layers of typeclass
-- resolution (`MatrixOrder`, `PosDef`, `Invertible`) against the
-- Schur complement block lemma `fromBlocks₁₁`, plus the
-- combo_conjTranspose rewrite that re-casts `α K₁ᴴ + (1-α) K₂ᴴ`
-- as `(αK₁+(1-α)K₂)ᴴ` for the Schur form.  Default 200000 is
-- insufficient.
/-- **Matrix-order joint convexity of `(K, B) ↦ Kᴴ · B⁻¹ · K`.**

    For arbitrary `K₁, K₂` and PosDef `B₁, B₂`, `α ∈ [0, 1]`:

      `(αK₁+(1-α)K₂)ᴴ · (αB₁+(1-α)B₂)⁻¹ · (αK₁+(1-α)K₂)`
        `≤  α · K₁ᴴ B₁⁻¹ K₁  +  (1-α) · K₂ᴴ B₂⁻¹ K₂`.

    Proof: apply Schur complement (`fromBlocks₁₁`, top-left PosDef
    direction) to the PSD block matrix produced by
    `block_psd_kraus_combo`.  The top-left is the convex
    combination `αB₁+(1-α)B₂`, which is PosDef by
    `posDef_convex_combo`. -/
theorem kraus_quadratic_jointly_convex
    (K₁ K₂ B₁ B₂ : Matrix (Fin n) (Fin n) ℂ)
    (hB₁ : B₁.PosDef) (hB₂ : B₂.PosDef)
    (α : ℝ) (hα₀ : 0 ≤ α) (hα₁ : α ≤ 1) :
    ((α : ℂ) • K₁ + ((1 - α : ℝ) : ℂ) • K₂)ᴴ *
        ((α : ℂ) • B₁ + ((1 - α : ℝ) : ℂ) • B₂)⁻¹ *
        ((α : ℂ) • K₁ + ((1 - α : ℝ) : ℂ) • K₂)
      ≤ (α : ℂ) • (K₁ᴴ * B₁⁻¹ * K₁)
          + ((1 - α : ℝ) : ℂ) • (K₂ᴴ * B₂⁻¹ * K₂) := by
  -- Top-left convex combo is PosDef.
  have hB_combo : ((α : ℂ) • B₁ + ((1 - α : ℝ) : ℂ) • B₂).PosDef :=
    posDef_convex_combo hB₁ hB₂ hα₀ hα₁
  haveI : Invertible ((α : ℂ) • B₁ + ((1 - α : ℝ) : ℂ) • B₂) :=
    hB_combo.isUnit.invertible
  -- The combo block is PSD by Schur building block + linearity.
  have hCombo := block_psd_kraus_combo K₁ K₂ B₁ B₂ hB₁ hB₂ α hα₀ hα₁
  -- Cast the off-diagonal `(αK₁+(1-α)K₂)ᴴ` into the canonical `Bᴴ` form
  -- expected by Schur's `fromBlocks₁₁`.
  have h_offdiag : (α : ℂ) • K₁ᴴ + ((1 - α : ℝ) : ℂ) • K₂ᴴ
                    = ((α : ℂ) • K₁ + ((1 - α : ℝ) : ℂ) • K₂)ᴴ :=
    (combo_conjTranspose K₁ K₂ α).symm
  rw [h_offdiag] at hCombo
  -- Apply Schur: `(fromBlocks A B Bᴴ D).PSD ↔ (D - Bᴴ * A⁻¹ * B).PSD`.
  have hSchur := (Matrix.PosDef.fromBlocks₁₁
    ((α : ℂ) • K₁ + ((1 - α : ℝ) : ℂ) • K₂)
    ((α : ℂ) • (K₁ᴴ * B₁⁻¹ * K₁) + ((1 - α : ℝ) : ℂ) • (K₂ᴴ * B₂⁻¹ * K₂))
    hB_combo).mp hCombo
  -- `hSchur : ((α • (K₁ᴴ B₁⁻¹ K₁) + (1-α) • (K₂ᴴ B₂⁻¹ K₂))
  --             - (αK₁+(1-α)K₂)ᴴ * (αB₁+(1-α)B₂)⁻¹ * (αK₁+(1-α)K₂)).PosSemidef`.
  -- This is exactly the desired matrix-order inequality.
  exact hSchur

/-! ## 5. Trace-level joint convexity (real scalar form). -/

/-- The trace of a PosSemidef matrix has nonneg real part. -/
private lemma re_trace_nonneg_of_posSemidef
    {M : Matrix (Fin n) (Fin n) ℂ} (hM : M.PosSemidef) :
    0 ≤ (Matrix.trace M).re := by
  -- `Tr(I · M)` has nonneg real part because `I` is PosSemidef and
  -- `re_trace_mul_nonneg_of_posSemidef` (Phase 1's reused lemma) bites.
  have h_one_psd : (1 : Matrix (Fin n) (Fin n) ℂ).PosSemidef :=
    Matrix.PosDef.one.posSemidef
  have h := UnifiedTheory.LayerB.QuantumStein.re_trace_mul_nonneg_of_posSemidef
              h_one_psd hM
  -- Tr(1 · M) = Tr(M).
  rwa [Matrix.one_mul] at h

set_option maxHeartbeats 1200000 in
-- Raised maxHeartbeats: the proof projects a matrix-order PSD
-- inequality onto `(Matrix.trace _).re` and then linearises the
-- RHS via `Matrix.trace_add`, `Matrix.trace_smul`,
-- `Complex.add_re`, `Complex.mul_re` chains.  Each rewrite step
-- triggers full `MatrixOrder` + `ComplexOrder` typeclass
-- searches; the combined heartbeat cost exceeds 800000 even on
-- the strictest path.  1200000 is the smallest power-of-100k
-- ceiling that builds reliably.
/-- **Trace-level joint convexity of `Re Tr(Kᴴ B⁻¹ K)`.**

    For arbitrary `K₁, K₂` and PosDef `B₁, B₂`, `α ∈ [0, 1]`:

      `Re Tr( (αK₁+(1-α)K₂)ᴴ · (αB₁+(1-α)B₂)⁻¹ · (αK₁+(1-α)K₂) )`
        `≤ α · Re Tr( K₁ᴴ B₁⁻¹ K₁ ) + (1-α) · Re Tr( K₂ᴴ B₂⁻¹ K₂ )`.

    Proof: apply `re_trace_nonneg_of_posSemidef` to the difference
    matrix `RHS_matrix - LHS_matrix ≥ 0` from
    `kraus_quadratic_jointly_convex`.  Linearity of trace
    distributes `α, (1-α)` to the outside. -/
theorem kraus_quadratic_jointly_convex_trace
    (K₁ K₂ B₁ B₂ : Matrix (Fin n) (Fin n) ℂ)
    (hB₁ : B₁.PosDef) (hB₂ : B₂.PosDef)
    (α : ℝ) (hα₀ : 0 ≤ α) (hα₁ : α ≤ 1) :
    (Matrix.trace
        (((α : ℂ) • K₁ + ((1 - α : ℝ) : ℂ) • K₂)ᴴ *
          ((α : ℂ) • B₁ + ((1 - α : ℝ) : ℂ) • B₂)⁻¹ *
          ((α : ℂ) • K₁ + ((1 - α : ℝ) : ℂ) • K₂))).re
      ≤ α * (Matrix.trace (K₁ᴴ * B₁⁻¹ * K₁)).re
          + (1 - α) * (Matrix.trace (K₂ᴴ * B₂⁻¹ * K₂)).re := by
  -- Matrix-order inequality.
  have hMat := kraus_quadratic_jointly_convex K₁ K₂ B₁ B₂ hB₁ hB₂ α hα₀ hα₁
  -- The difference is PSD.
  have hPSD : ((α : ℂ) • (K₁ᴴ * B₁⁻¹ * K₁)
                  + ((1 - α : ℝ) : ℂ) • (K₂ᴴ * B₂⁻¹ * K₂)
              - ((α : ℂ) • K₁ + ((1 - α : ℝ) : ℂ) • K₂)ᴴ *
                  ((α : ℂ) • B₁ + ((1 - α : ℝ) : ℂ) • B₂)⁻¹ *
                  ((α : ℂ) • K₁ + ((1 - α : ℝ) : ℂ) • K₂)).PosSemidef := hMat
  -- Hence `Re Tr(diff) ≥ 0`.
  have hRe_diff_nn : 0 ≤ (Matrix.trace
        ((α : ℂ) • (K₁ᴴ * B₁⁻¹ * K₁)
          + ((1 - α : ℝ) : ℂ) • (K₂ᴴ * B₂⁻¹ * K₂)
        - ((α : ℂ) • K₁ + ((1 - α : ℝ) : ℂ) • K₂)ᴴ *
            ((α : ℂ) • B₁ + ((1 - α : ℝ) : ℂ) • B₂)⁻¹ *
            ((α : ℂ) • K₁ + ((1 - α : ℝ) : ℂ) • K₂))).re :=
    re_trace_nonneg_of_posSemidef hPSD
  -- Linearity of trace + sub.
  rw [Matrix.trace_sub] at hRe_diff_nn
  rw [Complex.sub_re] at hRe_diff_nn
  -- The RHS-trace also expands by linearity:
  -- Tr(α • (K₁ᴴB₁⁻¹K₁) + (1-α) • (K₂ᴴB₂⁻¹K₂))
  --   = α · Tr(K₁ᴴB₁⁻¹K₁) + (1-α) · Tr(K₂ᴴB₂⁻¹K₂).
  have hRHS_lin :
      (Matrix.trace
        ((α : ℂ) • (K₁ᴴ * B₁⁻¹ * K₁)
          + ((1 - α : ℝ) : ℂ) • (K₂ᴴ * B₂⁻¹ * K₂))).re
        = α * (Matrix.trace (K₁ᴴ * B₁⁻¹ * K₁)).re
            + (1 - α) * (Matrix.trace (K₂ᴴ * B₂⁻¹ * K₂)).re := by
    rw [Matrix.trace_add, Matrix.trace_smul, Matrix.trace_smul,
        Complex.add_re, smul_eq_mul, smul_eq_mul,
        Complex.mul_re, Complex.mul_re]
    simp
  rw [hRHS_lin] at hRe_diff_nn
  linarith

/-! ## 6. Trace-resolvent specialisation: `B ↦ t · I + B`. -/

set_option maxHeartbeats 800000 in
-- Raised maxHeartbeats: the proof reassociates a convex combination
-- of `t·I + Bᵢ` shifts through `smul_add` + `add_smul` algebraic
-- rewrites, then propagates the resulting matrix-order
-- inequality through the trace-level joint convexity theorem.
-- Default 200000 is insufficient.
/-- **Trace-resolvent Kraus form** — the Phase-1-compatible
    specialisation.

    For arbitrary `K₁, K₂`, PosDef `B₁, B₂`, `t > 0`, `α ∈ [0, 1]`,
    the Kraus-quadratic trace form
        `Re Tr( Kᴴ · (t·I + B)⁻¹ · K )`
    is jointly convex in `(K, B)`:

      `Re Tr( (αK₁+(1-α)K₂)ᴴ · (t·I + αB₁+(1-α)B₂)⁻¹ ·`
            `(αK₁+(1-α)K₂) )`
        `≤ α · Re Tr( K₁ᴴ · (t·I + B₁)⁻¹ · K₁ )`
            `+ (1-α) · Re Tr( K₂ᴴ · (t·I + B₂)⁻¹ · K₂ )`.

    Proof: apply `kraus_quadratic_jointly_convex_trace` with
    `Bᵢ ↦ t·I + Bᵢ`, which is PosDef by Phase 1's
    `posDef_t_add_posDef`.  The convex combination of the shifted
    forms is `α(t·I+B₁) + (1-α)(t·I+B₂) = t·I + αB₁ + (1-α)B₂`. -/
theorem trace_resolvent_kraus_convex
    (K₁ K₂ B₁ B₂ : Matrix (Fin n) (Fin n) ℂ)
    (hB₁ : B₁.PosDef) (hB₂ : B₂.PosDef)
    (t : ℝ) (ht : 0 < t)
    (α : ℝ) (hα₀ : 0 ≤ α) (hα₁ : α ≤ 1) :
    (Matrix.trace
        (((α : ℂ) • K₁ + ((1 - α : ℝ) : ℂ) • K₂)ᴴ *
          ((t : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ)
            + ((α : ℂ) • B₁ + ((1 - α : ℝ) : ℂ) • B₂))⁻¹ *
          ((α : ℂ) • K₁ + ((1 - α : ℝ) : ℂ) • K₂))).re
      ≤ α * (Matrix.trace
                (K₁ᴴ * ((t : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) + B₁)⁻¹
                  * K₁)).re
          + (1 - α) * (Matrix.trace
                (K₂ᴴ * ((t : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) + B₂)⁻¹
                  * K₂)).re := by
  -- Shifted matrices are PosDef.
  set tI : Matrix (Fin n) (Fin n) ℂ :=
    (t : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) with htI_def
  set T₁ : Matrix (Fin n) (Fin n) ℂ := tI + B₁ with hT₁_def
  set T₂ : Matrix (Fin n) (Fin n) ℂ := tI + B₂ with hT₂_def
  have hT₁_PD : T₁.PosDef := by
    rw [hT₁_def, htI_def]; exact posDef_t_add_posDef B₁ hB₁ t ht
  have hT₂_PD : T₂.PosDef := by
    rw [hT₂_def, htI_def]; exact posDef_t_add_posDef B₂ hB₂ t ht
  -- Apply the trace-level joint convexity with B_i = T_i.
  have h_main := kraus_quadratic_jointly_convex_trace K₁ K₂ T₁ T₂
                    hT₁_PD hT₂_PD α hα₀ hα₁
  -- The convex combination αT₁ + (1-α)T₂ = tI + αB₁ + (1-α)B₂.
  have h_combo_eq :
      (α : ℂ) • T₁ + ((1 - α : ℝ) : ℂ) • T₂
        = tI + ((α : ℂ) • B₁ + ((1 - α : ℝ) : ℂ) • B₂) := by
    rw [hT₁_def, hT₂_def]
    rw [smul_add, smul_add]
    have h_tI_combo : (α : ℂ) • tI + ((1 - α : ℝ) : ℂ) • tI = tI := by
      rw [← add_smul]
      have h_sum : (α : ℂ) + ((1 - α : ℝ) : ℂ) = 1 := by push_cast; ring
      rw [h_sum, one_smul]
    calc (α : ℂ) • tI + (α : ℂ) • B₁ +
            (((1 - α : ℝ) : ℂ) • tI + ((1 - α : ℝ) : ℂ) • B₂)
        = ((α : ℂ) • tI + ((1 - α : ℝ) : ℂ) • tI) +
            ((α : ℂ) • B₁ + ((1 - α : ℝ) : ℂ) • B₂) := by abel
      _ = tI + ((α : ℂ) • B₁ + ((1 - α : ℝ) : ℂ) • B₂) := by
            rw [h_tI_combo]
  -- Rewrite the LHS argument of `h_main` using `h_combo_eq`.
  rw [h_combo_eq] at h_main
  -- The goal matches `h_main` definitionally (via the `set ... with` bindings
  -- for `tI`, `T₁`, `T₂`).
  exact h_main

/-! ## 7. Axiom audit.

    The next `#print axioms` directives are commented out to keep
    the build output quiet; uncomment locally to verify dependence
    only on Lean's three standard axioms (`propext`,
    `Classical.choice`, `Quot.sound`).  No `sorry`, no custom
    `axiom`. -/

-- #print axioms block_psd_kraus
-- #print axioms block_psd_kraus_combo
-- #print axioms kraus_quadratic_jointly_convex
-- #print axioms kraus_quadratic_jointly_convex_trace
-- #print axioms trace_resolvent_kraus_convex
-- VERIFIED 2026-06-01: all five theorems depend only on
--   `propext, Classical.choice, Quot.sound`
-- (Lean's three standard axioms).  No `sorry`, no custom `axiom`.

end UnifiedTheory.LayerB.TraceResolventJointConvexity
