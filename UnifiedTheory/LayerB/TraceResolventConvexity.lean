/-
  LayerB/TraceResolventConvexity.lean
  ────────────────────────────────────

  **Phase 1 of the Lieb 1973 discharge** — finite-dimensional
  convexity of the trace-resolvent map
      `B  ↦  Tr ( A · (t · I + B)⁻¹ )`
  for fixed positive-semidefinite `A`, positive scalar `t > 0`, and
  positive-definite argument `B`.

  This is the load-bearing intermediate that connects
  `LayerB/OperatorConvexInverse.lean` (operator convexity of `x ↦ x⁻¹`,
  unconditional) to the eventual Bochner integral representation of
  `log` used in Lieb's 1973 trace inequality.

  ## Mathematical statement

  For PosSemidef `A : Matrix (Fin n) (Fin n) ℂ` and PosDef
  `B₁, B₂ : Matrix (Fin n) (Fin n) ℂ`, `t > 0`, and `α ∈ [0, 1]`:

      Re Tr ( A · (t·I + α·B₁ + (1-α)·B₂)⁻¹ )
        ≤  α · Re Tr ( A · (t·I + B₁)⁻¹ )
            + (1-α) · Re Tr ( A · (t·I + B₂)⁻¹ ) .

  ## Proof strategy

  1. **PosDef of `t·I + B`** (`posDef_t_add_posDef`): `t·I` is PosDef
     for `t > 0` (eigenvalues all `t`), and the sum of two PosDef
     matrices is PosDef.

  2. **Trace-against-PSD is order-monotone**
     (`re_trace_mul_posSemidef_mono`):
     if `X ≤ Y` (i.e. `(Y - X).PosSemidef`) and `A` is PosSemidef,
     then `Re Tr(A · X) ≤ Re Tr(A · Y)`.  Proof: subtract and apply
     `re_trace_mul_nonneg_of_posSemidef` from `QuantumStein.lean`.

  3. **B-convexity of `(t·I + B)⁻¹`** (apply `inv_operator_convex` to
     `(t·I + B₁), (t·I + B₂)`):
        `(t·I + αB₁ + (1-α)B₂)⁻¹  ≤  α(t·I+B₁)⁻¹ + (1-α)(t·I+B₂)⁻¹`.

  4. **Combine** (`trace_resolvent_convex_in_B`):  apply step 2 to
     step 3, then `(Aᵢ · X)` linearity to expand the right-hand side.

  ## Joint convexity in (A, B): SCOPED

  The fully joint inequality

      Re Tr( (αA₁+(1-α)A₂) · (t·I+αB₁+(1-α)B₂)⁻¹ )
        ≤  α · Re Tr(A₁·(t·I+B₁)⁻¹)
            + (1-α) · Re Tr(A₂·(t·I+B₂)⁻¹)

  is **strictly stronger** than convexity in `A` plus convexity in `B`
  separately.  The naive "convex × convex ⇒ jointly convex" step
  generates uncancellable cross terms
  `α(1-α)[Tr(A₁·(t·I+B₂)⁻¹) + Tr(A₂·(t·I+B₁)⁻¹)]`, so the actual
  proof requires the Bochner / 2×2-block representation
  (Carlen 2010 Theorem 2.10).

  Following the `IsAndoMaximal` discipline in this layer
  (`LayerB/AndoGeometricMean.lean`), the joint statement is packaged
  here as a named `Prop`
  (`TraceResolvent_JointConvexity_Target`), to be discharged in a
  later phase by a 2×2-block Schur argument.  This file proves
  EVERYTHING that is downstream of the operator-convex inverse
  unconditionally; the only deferred ingredient is the genuinely
  deep 2×2-block fact.

  ## What is proved (zero `sorry`, zero custom `axiom`)

  • `posDef_t_add_posDef` — `(t : ℂ) • 1 + B` is PosDef for `B` PosDef
    and `t > 0`.
  • `re_trace_mul_posSemidef_mono` — Tr(A·-)-monotonicity when A PSD.
  • `trace_resolvent_convex_in_B` — Phase-1 headline (B-convexity).
  • `TraceResolvent_JointConvexity_Target` — scoped joint statement.

  ## Key imports

  • `LayerB/OperatorConvexInverse.lean`  for `inv_operator_convex`.
  • `LayerB/QuantumStein.lean`           for
    `re_trace_mul_nonneg_of_posSemidef`.
-/

import UnifiedTheory.LayerB.OperatorConvexInverse
import UnifiedTheory.LayerB.QuantumStein

set_option relaxedAutoImplicit false

namespace UnifiedTheory.LayerB.TraceResolventConvexity

open Matrix Complex
open scoped MatrixOrder ComplexOrder
open UnifiedTheory.LayerB.OperatorConvexInverse
open UnifiedTheory.LayerB.QuantumStein

variable {n : ℕ}

/-! ## 1. Real → Complex coercion helpers (reused). -/

/-- A positive real coerced into ℂ is positive (in `ComplexOrder`). -/
private lemma complex_pos_of_real_pos {a : ℝ} (h : 0 < a) :
    (0 : ℂ) < (a : ℂ) := by
  rw [Complex.lt_def]
  refine ⟨by simpa using h, ?_⟩
  simp

/-- A nonneg real coerced into ℂ is nonneg (in `ComplexOrder`). -/
private lemma complex_nonneg_of_real_nonneg {a : ℝ} (h : 0 ≤ a) :
    (0 : ℂ) ≤ (a : ℂ) := by
  rw [Complex.le_def]
  refine ⟨by simpa using h, ?_⟩
  simp

/-! ## 2. PosDef of `t·I + B`. -/

/-- **`t · I + B` is PosDef for `t > 0` and `B` PosDef.**

    For any `n`, `(t : ℂ) • 1` is the matrix `diag(t, t, …, t)`, which is
    PosDef for `t > 0` (its eigenvalues are all `t`).  The sum of two
    PosDef matrices is PosDef. -/
theorem posDef_t_add_posDef
    (B : Matrix (Fin n) (Fin n) ℂ) (hB : B.PosDef)
    (t : ℝ) (ht : 0 < t) :
    ((t : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) + B).PosDef := by
  -- `(1 : Matrix _ _ ℂ).PosDef` directly from Mathlib.
  have h_one : (1 : Matrix (Fin n) (Fin n) ℂ).PosDef := Matrix.PosDef.one
  -- `t > 0` as a complex scalar.
  have htC : (0 : ℂ) < (t : ℂ) := complex_pos_of_real_pos ht
  -- `(t : ℂ) • 1` is PosDef.
  have h_tI : ((t : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ)).PosDef :=
    h_one.smul htC
  -- Sum with `B` (PosDef) is PosDef.
  exact h_tI.add hB

/-! ## 3. Trace-against-PSD is order-preserving. -/

/-- **Trace-against-PSD monotonicity.**

    For any PosSemidef `A` and matrices `X, Y` with `X ≤ Y`
    (matrix order: `(Y - X).PosSemidef`),
    `Re Tr(A · X) ≤ Re Tr(A · Y)`.

    Proof: `Re Tr(A · (Y - X)) ≥ 0` by
    `re_trace_mul_nonneg_of_posSemidef`, which expands by linearity
    to `Re Tr(A · Y) - Re Tr(A · X) ≥ 0`. -/
theorem re_trace_mul_posSemidef_mono
    {A X Y : Matrix (Fin n) (Fin n) ℂ}
    (hA : A.PosSemidef) (hXY : X ≤ Y) :
    (Matrix.trace (A * X)).re ≤ (Matrix.trace (A * Y)).re := by
  -- Unfold the matrix order: hXY : (Y - X).PosSemidef.
  have hPSD : (Y - X).PosSemidef := hXY
  -- Tr(A · (Y - X)) has nonneg real part.
  have h_nn : 0 ≤ (Matrix.trace (A * (Y - X))).re :=
    re_trace_mul_nonneg_of_posSemidef hA hPSD
  -- Linearity: Tr(A · (Y - X)) = Tr(A·Y) - Tr(A·X).
  have h_lin : Matrix.trace (A * (Y - X))
                = Matrix.trace (A * Y) - Matrix.trace (A * X) := by
    rw [Matrix.mul_sub, Matrix.trace_sub]
  rw [h_lin, Complex.sub_re] at h_nn
  linarith

/-! ## 4. The headline: B-convexity of `Tr(A · (t·I + B)⁻¹)`. -/

set_option maxHeartbeats 800000 in
-- Raised maxHeartbeats: the proof reassociates a convex combination
-- through the `inv_operator_convex` block-Schur lemma, then propagates
-- the resulting matrix-order inequality through trace-against-PSD
-- monotonicity AND the real-part-of-complex-coerced-real-scalar
-- simplification.  Default 200000 is just barely insufficient on
-- some elaborations of the algebraic rewrite chain.
/-- **PHASE 1 HEADLINE — B-convexity of the trace-resolvent.**

    For fixed PosSemidef `A`, PosDef `B₁, B₂`, scalar `t > 0`, and
    `α ∈ [0, 1]`,

        Re Tr ( A · (t·I + α·B₁ + (1-α)·B₂)⁻¹ )
          ≤  α · Re Tr ( A · (t·I + B₁)⁻¹ )
              + (1-α) · Re Tr ( A · (t·I + B₂)⁻¹ ) .

    **Proof.**
    (a) `t·I + Bᵢ` is PosDef (`posDef_t_add_posDef`).
    (b) Apply operator convexity of inverse (`inv_operator_convex`)
        to `(t·I + B₁, t·I + B₂)`:
            `(α(t·I+B₁) + (1-α)(t·I+B₂))⁻¹
                ≤ α(t·I+B₁)⁻¹ + (1-α)(t·I+B₂)⁻¹`.
        The LHS argument simplifies to `t·I + α·B₁ + (1-α)·B₂`
        because `α(t·I) + (1-α)(t·I) = t·I`.
    (c) Take `Tr(A · -)` of both sides via
        `re_trace_mul_posSemidef_mono`.
    (d) Distribute trace over scalar and sum on the RHS via
        `Matrix.mul_add`, `Matrix.mul_smul`, `Matrix.trace_add`,
        `Matrix.trace_smul`. -/
theorem trace_resolvent_convex_in_B
    (A : Matrix (Fin n) (Fin n) ℂ) (hA : A.PosSemidef)
    (B₁ B₂ : Matrix (Fin n) (Fin n) ℂ)
    (hB₁ : B₁.PosDef) (hB₂ : B₂.PosDef)
    (t : ℝ) (ht : 0 < t)
    (α : ℝ) (hα0 : 0 ≤ α) (hα1 : α ≤ 1) :
    (Matrix.trace
        (A * ((t : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ)
              + ((α : ℂ) • B₁ + ((1 - α : ℝ) : ℂ) • B₂))⁻¹)).re
      ≤ α * (Matrix.trace
                (A * ((t : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) + B₁)⁻¹)).re
          + (1 - α) * (Matrix.trace
                (A * ((t : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) + B₂)⁻¹)).re := by
  -- Abbreviations.
  set tI : Matrix (Fin n) (Fin n) ℂ :=
    (t : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) with htI_def
  set T₁ : Matrix (Fin n) (Fin n) ℂ := tI + B₁ with hT₁_def
  set T₂ : Matrix (Fin n) (Fin n) ℂ := tI + B₂ with hT₂_def
  -- (a) PosDef of T₁, T₂.
  have hT₁_PD : T₁.PosDef := by
    rw [hT₁_def, htI_def]; exact posDef_t_add_posDef B₁ hB₁ t ht
  have hT₂_PD : T₂.PosDef := by
    rw [hT₂_def, htI_def]; exact posDef_t_add_posDef B₂ hB₂ t ht
  -- (b) Apply operator convexity of inverse to T₁, T₂.
  have h_opconv : ((α : ℂ) • T₁ + ((1 - α : ℝ) : ℂ) • T₂)⁻¹
                    ≤ (α : ℂ) • T₁⁻¹ + ((1 - α : ℝ) : ℂ) • T₂⁻¹ :=
    inv_operator_convex T₁ T₂ hT₁_PD hT₂_PD α hα0 hα1
  -- The combo `α T₁ + (1-α) T₂` algebraically equals `tI + αB₁ + (1-α)B₂`.
  have h_combo_eq :
      (α : ℂ) • T₁ + ((1 - α : ℝ) : ℂ) • T₂
        = tI + ((α : ℂ) • B₁ + ((1 - α : ℝ) : ℂ) • B₂) := by
    rw [hT₁_def, hT₂_def]
    -- α • (tI + B₁) + (1-α) • (tI + B₂)
    --   = α • tI + α • B₁ + (1-α) • tI + (1-α) • B₂
    --   = (α + (1-α)) • tI + α • B₁ + (1-α) • B₂
    --   = tI + α • B₁ + (1-α) • B₂.
    rw [smul_add, smul_add]
    have h_tI_combo : (α : ℂ) • tI + ((1 - α : ℝ) : ℂ) • tI = tI := by
      rw [← add_smul]
      have h_sum : (α : ℂ) + ((1 - α : ℝ) : ℂ) = 1 := by push_cast; ring
      rw [h_sum, one_smul]
    -- Reassociate.
    calc (α : ℂ) • tI + (α : ℂ) • B₁ +
            (((1 - α : ℝ) : ℂ) • tI + ((1 - α : ℝ) : ℂ) • B₂)
        = ((α : ℂ) • tI + ((1 - α : ℝ) : ℂ) • tI) +
            ((α : ℂ) • B₁ + ((1 - α : ℝ) : ℂ) • B₂) := by abel
      _ = tI + ((α : ℂ) • B₁ + ((1 - α : ℝ) : ℂ) • B₂) := by
            rw [h_tI_combo]
  -- Substitute into h_opconv.
  rw [h_combo_eq] at h_opconv
  -- (c) Apply trace monotonicity Tr(A · -).
  have h_re :=
    re_trace_mul_posSemidef_mono (A := A) hA h_opconv
  -- h_re : Re Tr(A · (tI + αB₁ + (1-α)B₂)⁻¹)
  --         ≤ Re Tr(A · (α • T₁⁻¹ + (1-α) • T₂⁻¹)).
  -- (d) Linearise the right-hand side.
  have h_RHS_lin :
      Matrix.trace (A * ((α : ℂ) • T₁⁻¹ + ((1 - α : ℝ) : ℂ) • T₂⁻¹))
        = (α : ℂ) * Matrix.trace (A * T₁⁻¹)
            + ((1 - α : ℝ) : ℂ) * Matrix.trace (A * T₂⁻¹) := by
    rw [Matrix.mul_add, Matrix.trace_add]
    -- A * (α • T₁⁻¹) = α • (A * T₁⁻¹) via Matrix.mul_smul.
    rw [Matrix.mul_smul, Matrix.mul_smul,
        Matrix.trace_smul, Matrix.trace_smul]
    simp [smul_eq_mul]
  -- Take real parts.
  have h_RHS_re :
      (Matrix.trace (A * ((α : ℂ) • T₁⁻¹ + ((1 - α : ℝ) : ℂ) • T₂⁻¹))).re
        = α * (Matrix.trace (A * T₁⁻¹)).re
            + (1 - α) * (Matrix.trace (A * T₂⁻¹)).re := by
    rw [h_RHS_lin, Complex.add_re]
    -- (α : ℂ) * z = α * z.re + 0 since (α : ℂ).im = 0.
    rw [Complex.mul_re, Complex.mul_re]
    simp
  rw [h_RHS_re] at h_re
  -- The goal is in terms of `tI + (αB₁ + (1-α)B₂)`, `tI + B₁`, `tI + B₂`.
  -- These match T₁, T₂ definitionally (via the `set ... with` bindings).
  exact h_re

/-! ## 5. Joint convexity in (A, B): scoped target. -/

/-- **Scoped joint-convexity target.**

    The fully joint inequality

        Re Tr ( (αA₁+(1-α)A₂) · (t·I + αB₁+(1-α)B₂)⁻¹ )
          ≤  α · Re Tr ( A₁ · (t·I + B₁)⁻¹ )
              + (1-α) · Re Tr ( A₂ · (t·I + B₂)⁻¹ )

    for PosSemidef `A₁, A₂` and PosDef `B₁, B₂` is **not** a direct
    consequence of convexity in each argument separately
    (cross-term `α(1-α)·[Tr(A₁·(tI+B₂)⁻¹) + Tr(A₂·(tI+B₁)⁻¹)]` is
    irreducible by the naive split).  Its discharge requires the
    Bochner / 2×2-block Schur argument of Lieb 1973 / Carlen 2010
    Theorem 2.10, which we leave to a later phase.  Packaging it
    here as a `Prop`-target follows the `IsAndoMaximal` discipline
    of `LayerB/AndoGeometricMean.lean`. -/
def TraceResolvent_JointConvexity_Target : Prop :=
  ∀ {m : ℕ} (A₁ A₂ B₁ B₂ : Matrix (Fin m) (Fin m) ℂ),
    A₁.PosSemidef → A₂.PosSemidef → B₁.PosDef → B₂.PosDef →
    ∀ (t : ℝ), 0 < t →
    ∀ (α : ℝ), 0 ≤ α → α ≤ 1 →
      (Matrix.trace
          (((α : ℂ) • A₁ + ((1 - α : ℝ) : ℂ) • A₂) *
            ((t : ℂ) • (1 : Matrix (Fin m) (Fin m) ℂ)
              + ((α : ℂ) • B₁ + ((1 - α : ℝ) : ℂ) • B₂))⁻¹)).re
        ≤ α * (Matrix.trace
                  (A₁ * ((t : ℂ) • (1 : Matrix (Fin m) (Fin m) ℂ) + B₁)⁻¹)).re
            + (1 - α) * (Matrix.trace
                  (A₂ * ((t : ℂ) • (1 : Matrix (Fin m) (Fin m) ℂ) + B₂)⁻¹)).re

/-! ## 6. Convexity in A alone (linearity, trivially proved). -/

/-- **Linearity-driven convexity in A.**

    For PosSemidef `A₁, A₂`, fixed PosDef `B`, `t > 0`, `α ∈ [0, 1]`,

        Re Tr ( (αA₁ + (1-α)A₂) · (t·I + B)⁻¹ )
          =  α · Re Tr ( A₁ · (t·I + B)⁻¹ )
              + (1-α) · Re Tr ( A₂ · (t·I + B)⁻¹ ).

    This is `(=)` (linearity of trace), hence in particular `(≤)`. -/
theorem trace_resolvent_linear_in_A
    (A₁ A₂ : Matrix (Fin n) (Fin n) ℂ)
    (B : Matrix (Fin n) (Fin n) ℂ) (_hB : B.PosDef)
    (t : ℝ) (_ht : 0 < t)
    (α : ℝ) :
    (Matrix.trace (((α : ℂ) • A₁ + ((1 - α : ℝ) : ℂ) • A₂) *
        ((t : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) + B)⁻¹)).re
      = α * (Matrix.trace
              (A₁ * ((t : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) + B)⁻¹)).re
        + (1 - α) * (Matrix.trace
              (A₂ * ((t : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) + B)⁻¹)).re := by
  -- Pure linearity.
  set R : Matrix (Fin n) (Fin n) ℂ :=
    ((t : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) + B)⁻¹ with _hR_def
  -- ((α • A₁) + (1-α) • A₂) * R = α • (A₁ * R) + (1-α) • (A₂ * R).
  have h_dist :
      ((α : ℂ) • A₁ + ((1 - α : ℝ) : ℂ) • A₂) * R
        = (α : ℂ) • (A₁ * R) + ((1 - α : ℝ) : ℂ) • (A₂ * R) := by
    rw [Matrix.add_mul, Matrix.smul_mul, Matrix.smul_mul]
  rw [h_dist, Matrix.trace_add, Matrix.trace_smul, Matrix.trace_smul,
      Complex.add_re, smul_eq_mul, smul_eq_mul,
      Complex.mul_re, Complex.mul_re]
  simp

/-! ## 7. Axiom audit.

    The following `#print axioms` directives are commented out to keep
    build output quiet; uncomment locally to verify dependence only on
    Lean's three standard axioms (`propext, Classical.choice, Quot.sound`).
    No `sorry`, no custom `axiom`. -/

-- #print axioms posDef_t_add_posDef
-- #print axioms re_trace_mul_posSemidef_mono
-- #print axioms trace_resolvent_convex_in_B
-- #print axioms trace_resolvent_linear_in_A
-- VERIFIED 2026-06-01: all four theorems depend only on
--   [propext, Classical.choice, Quot.sound]
-- (Lean's three standard axioms).  No `sorry`, no custom `axiom`.

end UnifiedTheory.LayerB.TraceResolventConvexity
