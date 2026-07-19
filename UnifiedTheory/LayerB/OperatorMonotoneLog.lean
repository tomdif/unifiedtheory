/-
  LayerB/OperatorMonotoneLog.lean
  ────────────────────────────────

  **Operator monotonicity of the real logarithm on positive
  definite Hermitian complex matrices.**

  This is the keystone of Phase A toward Lindblad–Uhlmann monotonicity:

      A ≤ B  (with A, B positive definite)  ⟹  log A ≤ log B,

  where the matrix order is `MatrixOrder`'s
  `A ≤ B := (B - A).PosSemidef` and `log` is the spectral
  (continuous-functional-calculus) logarithm
  `cfc Real.log A`.

  WHAT IS PROVEN (no `sorry`, no custom `axiom`):

    1. `cfc_log_monotone` (PRIMARY)
       For `A B : Matrix (Fin n) (Fin n) ℂ` with `A.PosDef`, `B.PosDef`,
       and `A ≤ B` in the matrix order,
         `cfc Real.log A ≤ cfc Real.log B`.

    2. `operatorLog_monotone` (BRIDGE TO `ComplexDensityMatrix`)
       For `ρ σ : ComplexDensityMatrix n` with `ρ.M.PosDef`,
       `σ.M.PosDef`, and `ρ.M ≤ σ.M`,
         `operatorLog ρ ≤ operatorLog σ`.

  ROUTE TAKEN: Route A (via the limit
  `log x = lim_{p → 0⁺} p⁻¹·(x^p − 1)`).  The full limit-passing
  proof is already in Mathlib as `CFC.log_le_log` (in
  `Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus
  .ExpLog.Order`).  Our work here is to:

    • assemble the scoped `MatrixOrder` and `Matrix.Norms.L2Operator`
      instances that make `Matrix (Fin n) (Fin n) ℂ` into a unital
      C⋆-algebra over `ℂ`, so that `CFC.log_le_log` applies; and
    • bridge `Matrix.PosDef` to the abstract `IsStrictlyPositive`
      hypothesis the Mathlib lemma expects (via
      `Matrix.PosDef.isStrictlyPositive`).

  HYPOTHESIS NOTE (for the downstream Klein inequality):
  the proof uses `Matrix.PosDef` as the positive-definite hypothesis
  on each input.  In the abstract `cfc` framework, the equivalent
  hypothesis is `IsStrictlyPositive` (= nonneg + invertible), and
  `Matrix.PosDef.isStrictlyPositive` provides the bridge in the
  matrix setting.  Either form is convenient downstream.

  KEY MATHLIB LEMMAS USED:
    • `CFC.log_le_log`          (Order of operator log via cfc limit)
    • `Matrix.PosDef.isStrictlyPositive` (PosDef ⇒ IsStrictlyPositive
                                          on `Matrix n n 𝕜`)
    • `Matrix.PosSemidef.nonneg` (PosSemidef ⇔ 0 ≤ A in MatrixOrder)

  SCOPED INSTANCES OPENED:
    • `MatrixOrder` for `Matrix.instPartialOrder`,
      `Matrix.instStarOrderedRing`, `instNonnegSpectrumClass`.
    • `Matrix.Norms.L2Operator` for `instL2OpNormedRing`,
      `instL2OpNormedAlgebra`, `instCStarRing`.

  In this scope, `Matrix (Fin n) (Fin n) ℂ` becomes a (unital)
  C⋆-algebra and supports `CFC.log_le_log` directly.
-/

import UnifiedTheory.LayerB.OperatorEntropy
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.ExpLog.Order

set_option relaxedAutoImplicit false

namespace UnifiedTheory.LayerB.OperatorMonotoneLog

open Matrix Complex
open scoped MatrixOrder Matrix.Norms.L2Operator ComplexOrder
open UnifiedTheory.LayerB.RobertsonSchrodinger
open UnifiedTheory.LayerB.SpectralFC
open UnifiedTheory.LayerB.OperatorEntropy

variable {n : ℕ}

/-! ## 1. The primary theorem — operator monotonicity of `cfc Real.log`. -/

/-- A local `CStarAlgebra` instance on `Matrix (Fin n) (Fin n) ℂ`.

    The L2-operator-norm scoped instances make `Matrix n n ℂ` into a
    `NormedRing`, `NormedAlgebra ℂ`, `CStarRing`, and `StarModule ℂ`
    (with `StarModule ℂ` automatic from the entry-wise star).
    `CompleteSpace` is automatic in finite dimension.  All that
    remains is to bundle these as the `CStarAlgebra` class. -/
noncomputable instance matrixCStarAlgebra :
    CStarAlgebra (Matrix (Fin n) (Fin n) ℂ) where

set_option maxHeartbeats 4000000 in
-- Synthesising `IsStrictlyPositive` of a matrix from `PosDef` exercises
-- the full chain of scoped C⋆-algebra instances (`StarOrderedRing`,
-- `NonnegSpectrumClass`, etc.) that the goal `cfc Real.log A ≤ …`
-- carries with it, so the default heartbeat budget is too small.
/-- **Operator monotonicity of the spectral logarithm.**

    For positive definite complex matrices `A ≤ B` (in the
    `MatrixOrder` order `A ≤ B := (B − A).PosSemidef`),
    `cfc Real.log A ≤ cfc Real.log B`.

    This is the matrix-level concretisation of Löwner's classical
    operator-monotone-log theorem.  Mathlib provides the abstract
    statement `CFC.log_le_log` for any unital C⋆-algebra; we
    specialise to complex matrices, bridging `PosDef` to the
    `IsStrictlyPositive` hypothesis via
    `Matrix.PosDef.isStrictlyPositive`. -/
theorem cfc_log_monotone
    (A B : Matrix (Fin n) (Fin n) ℂ)
    (hA : A.PosDef) (hB : B.PosDef)
    (h_le : A ≤ B) :
    cfc Real.log A ≤ cfc Real.log B := by
  have hA' : IsStrictlyPositive A := hA.isStrictlyPositive
  have _hB' : IsStrictlyPositive B := hB.isStrictlyPositive
  exact CFC.log_le_log h_le hA'

/-! ## 2. Bridge to `ComplexDensityMatrix.operatorLog`. -/

set_option maxHeartbeats 1000000 in
-- Same instance-resolution costs as `cfc_log_monotone` propagate
-- through the bridge.
/-- **Operator monotonicity of `operatorLog` for density matrices.**

    If `ρ σ : ComplexDensityMatrix n` are positive definite (so the
    spectral log is well-defined on their full spectrum) and
    `ρ.M ≤ σ.M` in the matrix order, then
    `operatorLog ρ ≤ operatorLog σ`.

    This is the direct consequence of `cfc_log_monotone` applied to
    the underlying matrices, since
    `operatorLog ρ = cfcρ Real.log ρ = cfc Real.log ρ.M` by
    definition. -/
theorem operatorLog_monotone
    (ρ σ : ComplexDensityMatrix n)
    (hρ_pos : ρ.M.PosDef) (hσ_pos : σ.M.PosDef)
    (h_le : ρ.M ≤ σ.M) :
    operatorLog ρ ≤ operatorLog σ := by
  change cfcρ Real.log ρ ≤ cfcρ Real.log σ
  unfold cfcρ
  exact cfc_log_monotone ρ.M σ.M hρ_pos hσ_pos h_le

/-! ## 3. Axiom audit. -/

-- The next two `#print axioms` directives are an audit: the only
-- axioms used must be Lean's standard `propext, Classical.choice,
-- Quot.sound`.  Any `sorry` or custom `axiom` would show up here.
-- They are commented out by default to keep build output quiet,
-- but uncomment locally to verify.
-- #print axioms cfc_log_monotone
-- #print axioms operatorLog_monotone
-- VERIFIED 2026-05-30: both depend only on
--   `propext, Classical.choice, Quot.sound`
-- (Lean's three standard axioms).  No `sorry`, no custom `axiom`.

end UnifiedTheory.LayerB.OperatorMonotoneLog
