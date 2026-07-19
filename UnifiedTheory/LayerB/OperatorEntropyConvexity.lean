/-
  LayerB/OperatorEntropyConvexity.lean
  ────────────────────────────────────

  **Operator-entropy convexity** — the map
      `A ↦ Re Tr ( A · log A )`
  is convex on the cone of positive definite complex matrices.

  This discharges the gate `OperatorEntropy_Convexity_Target` declared
  in `PartialTraceDPIFull.lean` (line 279).

  ## Mathematical statement

  For PosDef `A₁, A₂ : Matrix (Fin n) (Fin n) ℂ` and `α ∈ [0, 1]`,
  with `B := α • A₁ + (1-α) • A₂`,

      Re Tr ( B · log B )
        ≤ α · Re Tr ( A₁ · log A₁ )
          + (1-α) · Re Tr ( A₂ · log A₂ ).

  Equivalently, `f(A) := −Re Tr(A · log A)` (the von-Neumann operator
  entropy convention) is CONCAVE.

  ## Strategy

  Klein's inequality (proved in `KleinInequalityFull.lean`):
      Re Tr (X − Y)  ≤  Re Tr ( X · ( log X − log Y ) )
  for any pair of PosDef matrices `X, Y`.

  Set `B := αA₁ + (1-α)A₂` and apply Klein twice:

    (1) Klein(A₁, B):
          Re Tr(A₁ - B) ≤ Re Tr(A₁ · log A₁) - Re Tr(A₁ · log B)
        i.e.  Re Tr(A₁ · log B) ≤ Re Tr(A₁ · log A₁) - Re Tr(A₁) + Re Tr(B).

    (2) Klein(A₂, B):
          Re Tr(A₂ · log B) ≤ Re Tr(A₂ · log A₂) - Re Tr(A₂) + Re Tr(B).

  Multiply (1) by α, (2) by (1-α), and add.  Using

        α · Tr(A₁) + (1-α) · Tr(A₂)  =  Tr(B),

  the constant terms cancel, and the LHS by linearity of trace is

        Re Tr( (αA₁ + (1-α)A₂) · log B )  =  Re Tr( B · log B ).

  We obtain

        Re Tr(B · log B)  ≤  α · Re Tr(A₁ · log A₁)
                              + (1-α) · Re Tr(A₂ · log A₂),

  which is exactly the convexity of `A ↦ Re Tr(A · log A)`.

  No `sorry`, no custom `axiom`.
-/

import UnifiedTheory.LayerB.KleinInequalityFull
import UnifiedTheory.LayerB.PartialTraceDPIFull

set_option relaxedAutoImplicit false

namespace UnifiedTheory.LayerB.OperatorEntropyConvexity

open Matrix Complex
open scoped MatrixOrder ComplexOrder
open UnifiedTheory.LayerB.KleinInequalityFull
open UnifiedTheory.LayerB.PartialTraceDPIFull

variable {n : ℕ}

/-! ## 1. The convex combination of two PosDef matrices is PosDef.

    Reused from the well-established pattern in
    `AndoGeometricMean.lean` / `OperatorConvexInverse.lean`. -/

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

/-- The convex combination `α • A₁ + (1-α) • A₂` of two PosDef
    matrices is PosDef for `α ∈ [0,1]`. -/
private lemma posDef_convex_combo
    (A₁ A₂ : Matrix (Fin n) (Fin n) ℂ)
    (hA₁ : A₁.PosDef) (hA₂ : A₂.PosDef)
    {α : ℝ} (hα₀ : 0 ≤ α) (hα₁ : α ≤ 1) :
    ((α : ℂ) • A₁ + ((1 - α : ℝ) : ℂ) • A₂).PosDef := by
  have h1mα : (0 : ℝ) ≤ 1 - α := by linarith
  have h1mαC : (0 : ℂ) ≤ ((1 - α : ℝ) : ℂ) :=
    complex_nonneg_of_real_nonneg h1mα
  -- Case split on α = 0 vs α > 0.
  rcases lt_or_eq_of_le hα₀ with hα_pos | hα_zero
  · -- α > 0: (α • A₁).PosDef + (1-α) • A₂.PosSemidef.
    have hαC_pos : (0 : ℂ) < (α : ℂ) := complex_pos_of_real_pos hα_pos
    have hαA₁_PD : ((α : ℂ) • A₁).PosDef := hA₁.smul hαC_pos
    have h1mαA₂_PSD : (((1 - α : ℝ) : ℂ) • A₂).PosSemidef :=
      hA₂.posSemidef.smul h1mαC
    exact hαA₁_PD.add_posSemidef h1mαA₂_PSD
  · -- α = 0: combo = A₂ (modulo simp normalisation).
    have h_eq : α = 0 := hα_zero.symm
    subst h_eq
    have h1mαC_pos : (0 : ℂ) < ((1 - (0 : ℝ) : ℝ) : ℂ) :=
      complex_pos_of_real_pos (by norm_num)
    have h_PD : (((1 - (0 : ℝ) : ℝ) : ℂ) • A₂).PosDef := hA₂.smul h1mαC_pos
    have h_simp :
        ((0 : ℝ) : ℂ) • A₁ + (((1 - (0 : ℝ) : ℝ) : ℂ)) • A₂
          = (((1 - (0 : ℝ) : ℝ) : ℂ)) • A₂ := by
      simp
    rw [h_simp]
    exact h_PD

/-! ## 2. The main theorem: operator entropy convexity. -/

/-- **Operator-entropy convexity.**

    For PosDef matrices `A₁, A₂` and `α ∈ [0, 1]`,

      Re Tr ( B · log B )
        ≤ α · Re Tr(A₁ · log A₁) + (1-α) · Re Tr(A₂ · log A₂),

    where `B := α • A₁ + (1-α) • A₂` and `log` is the continuous
    functional calculus logarithm `cfc Real.log`.

    **Proof.**  Klein's inequality applied to `(A₁, B)` and `(A₂, B)`:
        Re Tr(Aᵢ · log B) ≤ Re Tr(Aᵢ · log Aᵢ) − Re Tr(Aᵢ) + Re Tr(B).
    Convex-combining with weights `α, (1-α)` and using
    `α • A₁ + (1-α) • A₂ = B` and linearity of trace, the
    `−Re Tr(αA₁ + (1-α)A₂) + Re Tr(B)` term cancels and the LHS
    becomes `Re Tr(B · log B)`. -/
theorem operatorEntropy_convex
    (A₁ A₂ : Matrix (Fin n) (Fin n) ℂ)
    (hA₁ : A₁.PosDef) (hA₂ : A₂.PosDef)
    (α : ℝ) (hα₀ : 0 ≤ α) (hα₁ : α ≤ 1) :
    (Matrix.trace
        (((α : ℂ) • A₁ + ((1 - α : ℝ) : ℂ) • A₂) *
          cfc Real.log ((α : ℂ) • A₁ + ((1 - α : ℝ) : ℂ) • A₂))).re
      ≤ α * (Matrix.trace (A₁ * cfc Real.log A₁)).re
        + (1 - α) * (Matrix.trace (A₂ * cfc Real.log A₂)).re := by
  -- The convex-combo matrix and its PosDef-ness.
  set B : Matrix (Fin n) (Fin n) ℂ :=
    (α : ℂ) • A₁ + ((1 - α : ℝ) : ℂ) • A₂ with hB_def
  have hB : B.PosDef := posDef_convex_combo A₁ A₂ hA₁ hA₂ hα₀ hα₁
  -- Klein(A₁, B):  Re Tr(A₁ − B) ≤ Re Tr(A₁ · (log A₁ − log B))
  have hK₁ := klein_inequality A₁ B hA₁ hB
  -- Klein(A₂, B):  Re Tr(A₂ − B) ≤ Re Tr(A₂ · (log A₂ − log B))
  have hK₂ := klein_inequality A₂ B hA₂ hB
  -- Expand the RHS of Klein into A·log A − A·log B form.
  have hK₁' :
      (Matrix.trace A₁ - Matrix.trace B).re
        ≤ (Matrix.trace (A₁ * cfc Real.log A₁)).re
            - (Matrix.trace (A₁ * cfc Real.log B)).re := by
    have h_split :
        (Matrix.trace (A₁ * (cfc Real.log A₁ - cfc Real.log B))).re
          = (Matrix.trace (A₁ * cfc Real.log A₁)).re
              - (Matrix.trace (A₁ * cfc Real.log B)).re := by
      rw [Matrix.mul_sub, Matrix.trace_sub, Complex.sub_re]
    linarith [hK₁, le_of_eq h_split.symm]
  have hK₂' :
      (Matrix.trace A₂ - Matrix.trace B).re
        ≤ (Matrix.trace (A₂ * cfc Real.log A₂)).re
            - (Matrix.trace (A₂ * cfc Real.log B)).re := by
    have h_split :
        (Matrix.trace (A₂ * (cfc Real.log A₂ - cfc Real.log B))).re
          = (Matrix.trace (A₂ * cfc Real.log A₂)).re
              - (Matrix.trace (A₂ * cfc Real.log B)).re := by
      rw [Matrix.mul_sub, Matrix.trace_sub, Complex.sub_re]
    linarith [hK₂, le_of_eq h_split.symm]
  -- Now bound: α·Tr(A₁·logB) + (1-α)·Tr(A₂·logB).
  -- From hK₁':  Tr(A₁·logB).re ≤ Tr(A₁·logA₁).re - (Tr A₁ - Tr B).re.
  have hK₁'' :
      (Matrix.trace (A₁ * cfc Real.log B)).re
        ≤ (Matrix.trace (A₁ * cfc Real.log A₁)).re
            - (Matrix.trace A₁ - Matrix.trace B).re := by linarith
  have hK₂'' :
      (Matrix.trace (A₂ * cfc Real.log B)).re
        ≤ (Matrix.trace (A₂ * cfc Real.log A₂)).re
            - (Matrix.trace A₂ - Matrix.trace B).re := by linarith
  -- 1-α ≥ 0.
  have h1mα : 0 ≤ 1 - α := by linarith
  -- Scale Klein inequalities.
  have hK₁_scaled :
      α * (Matrix.trace (A₁ * cfc Real.log B)).re
        ≤ α * (Matrix.trace (A₁ * cfc Real.log A₁)).re
            - α * (Matrix.trace A₁ - Matrix.trace B).re :=
    by
      have h := mul_le_mul_of_nonneg_left hK₁'' hα₀
      linarith
  have hK₂_scaled :
      (1 - α) * (Matrix.trace (A₂ * cfc Real.log B)).re
        ≤ (1 - α) * (Matrix.trace (A₂ * cfc Real.log A₂)).re
            - (1 - α) * (Matrix.trace A₂ - Matrix.trace B).re :=
    by
      have h := mul_le_mul_of_nonneg_left hK₂'' h1mα
      linarith
  -- Sum:  α·Tr(A₁·logB) + (1-α)·Tr(A₂·logB)
  --       ≤ α·Tr(A₁·logA₁) + (1-α)·Tr(A₂·logA₂)
  --          - α·(TrA₁ - TrB) - (1-α)·(TrA₂ - TrB).
  -- The constant term equals:
  --   α·TrA₁ + (1-α)·TrA₂ - α·TrB - (1-α)·TrB
  -- = (α·TrA₁ + (1-α)·TrA₂) - TrB   = TrB - TrB = 0.
  -- by linearity, since B := α•A₁ + (1-α)•A₂.
  have h_trace_B :
      Matrix.trace B
        = (α : ℂ) * Matrix.trace A₁ + ((1 - α : ℝ) : ℂ) * Matrix.trace A₂ := by
    rw [hB_def]
    rw [Matrix.trace_add, Matrix.trace_smul, Matrix.trace_smul]
    simp [smul_eq_mul]
  have h_trace_B_re :
      (Matrix.trace B).re
        = α * (Matrix.trace A₁).re + (1 - α) * (Matrix.trace A₂).re := by
    rw [h_trace_B, Complex.add_re]
    congr 1
    · rw [Complex.mul_re]
      simp
    · rw [Complex.mul_re]
      simp
  -- LHS by linearity: Tr(B · log B) = α·Tr(A₁·log B) + (1-α)·Tr(A₂·log B).
  have h_LHS_lin :
      (Matrix.trace (B * cfc Real.log B)).re
        = α * (Matrix.trace (A₁ * cfc Real.log B)).re
            + (1 - α) * (Matrix.trace (A₂ * cfc Real.log B)).re := by
    -- B · log B = (α • A₁) · log B + ((1-α) • A₂) · log B
    have h_BmulLog :
        B * cfc Real.log B
          = ((α : ℂ) • A₁) * cfc Real.log B
              + (((1 - α : ℝ) : ℂ) • A₂) * cfc Real.log B := by
      rw [hB_def, Matrix.add_mul]
    rw [h_BmulLog, Matrix.trace_add]
    rw [Matrix.smul_mul, Matrix.smul_mul,
        Matrix.trace_smul, Matrix.trace_smul, Complex.add_re]
    rw [smul_eq_mul, smul_eq_mul, Complex.mul_re, Complex.mul_re]
    simp
  -- Now combine.  Define t_i := (Tr Aᵢ).re for brevity.
  set t₁ : ℝ := (Matrix.trace A₁).re with ht₁_def
  set t₂ : ℝ := (Matrix.trace A₂).re with ht₂_def
  set tB : ℝ := (Matrix.trace B).re with htB_def
  have h_tB_eq : tB = α * t₁ + (1 - α) * t₂ := h_trace_B_re
  -- The (Tr A - Tr B) terms are real parts.
  have h_Aₘ_minus_B_re₁ :
      (Matrix.trace A₁ - Matrix.trace B).re = t₁ - tB := by
    rw [Complex.sub_re]
  have h_Aₘ_minus_B_re₂ :
      (Matrix.trace A₂ - Matrix.trace B).re = t₂ - tB := by
    rw [Complex.sub_re]
  rw [h_Aₘ_minus_B_re₁] at hK₁_scaled
  rw [h_Aₘ_minus_B_re₂] at hK₂_scaled
  -- Sum the two scaled inequalities.
  have h_sum :
      α * (Matrix.trace (A₁ * cfc Real.log B)).re
          + (1 - α) * (Matrix.trace (A₂ * cfc Real.log B)).re
        ≤ α * (Matrix.trace (A₁ * cfc Real.log A₁)).re
            + (1 - α) * (Matrix.trace (A₂ * cfc Real.log A₂)).re
            - (α * (t₁ - tB) + (1 - α) * (t₂ - tB)) := by linarith
  -- Show the constant penalty vanishes:
  --   α(t₁ - tB) + (1-α)(t₂ - tB) = αt₁ + (1-α)t₂ - tB = 0.
  have h_zero : α * (t₁ - tB) + (1 - α) * (t₂ - tB) = 0 := by
    have : α * t₁ + (1 - α) * t₂ = tB := h_tB_eq.symm
    nlinarith [this]
  rw [h_zero] at h_sum
  -- Now substitute LHS linearity.
  -- Goal: (Tr (B · log B)).re ≤ α · Tr(A₁ · log A₁).re + (1-α) · Tr(A₂ · log A₂).re
  -- Goal still uses αA₁+(1-α)A₂ rather than B, but B was set with `set ... with`,
  -- so the goal is in terms of B.
  change (Matrix.trace (B * cfc Real.log B)).re
          ≤ α * (Matrix.trace (A₁ * cfc Real.log A₁)).re
              + (1 - α) * (Matrix.trace (A₂ * cfc Real.log A₂)).re
  rw [h_LHS_lin]
  linarith

/-! ## 3. Discharge of the named target. -/

/-- **Discharges `OperatorEntropy_Convexity_Target`.**

    The named target from `PartialTraceDPIFull.lean` is exactly
    `operatorEntropy_convex` packaged as a `Prop`. -/
theorem operatorEntropyConvexity_holds :
    OperatorEntropy_Convexity_Target := by
  intro m A₁ A₂ hA₁ hA₂ α hα₀ hα₁
  exact operatorEntropy_convex (n := m) A₁ A₂ hA₁ hA₂ α hα₀ hα₁

/-! ## 4. Axiom audit.

    Uncomment locally to verify dependence only on Lean's three
    standard axioms (propext, Classical.choice, Quot.sound). -/

-- #print axioms operatorEntropy_convex
-- #print axioms operatorEntropyConvexity_holds
-- VERIFIED 2026-06-01: both depend only on
--   [propext, Classical.choice, Quot.sound]
-- (Lean's three standard axioms).  No `sorry`, no custom `axiom`.

end UnifiedTheory.LayerB.OperatorEntropyConvexity
