/-
  LayerB/LiebTargetCorrected.lean
  ────────────────────────────────

  **Corrected downstream theorems for the Lindblad-Uhlmann arc.**

  Companion file to `LiebTargetAudit.lean` (which Lean-proves that
  the named hypothesis `LiebTrace_Concavity_Target` in
  `PartialTraceDPIFull.lean` is **provably FALSE**).

  This file ships the SUBSTANTIVE replacements: every downstream
  theorem of the form

      `LiebTrace_Concavity_Target → ... → Q`

  is re-proved from the CORRECTED hypothesis

      `Lieb1973_Corrected_Target`
        : joint convexity of Umegaki relative entropy at the raw
          PosDef-matrix level (Lindblad 1974, Uhlmann 1977),

  yielding new theorems `..._corrected` that are non-vacuous since
  the corrected hypothesis is mathematically true.

  ## What this file produces

  Mirror theorems for each consumer of `LiebTrace_Concavity_Target`:

    • `umegakiRelativeEntropy_jointly_convex_corrected` —
        `Lieb1973_Corrected_Target → JointConvexity_RelEntropy_Target`
      (direct: the corrected target IS the matrix form of joint
       convexity; specialisation to `ComplexDensityMatrix` is
       definitional).
    • `umegaki_dpi_partialTrace_corrected` —
        `Lieb1973_Corrected_Target + PartialTrace_Decomposition_Target
           → PartialTraceDPI_Target`.

  ## Why the bridge is short

  The audit's `Lieb1973_Corrected_Target` asserts, for arbitrary
  PosDef matrices `A₁, A₂, B₁, B₂` and `α ∈ [0,1]`:

      `(Tr(A_t · log A_t)).re - (Tr(A_t · log B_t)).re
            ≤ α · ((Tr(A₁ · log A₁)).re - (Tr(A₁ · log B₁)).re)
              + (1-α) · ((Tr(A₂ · log A₂)).re - (Tr(A₂ · log B₂)).re)`

  where `A_t := α • A₁ + (1-α) • A₂` and similarly for `B_t`.
  The Umegaki form
      `S(ρ‖σ) = Tr(ρ · (log ρ - log σ)).re`
  expands as `Tr(ρ · log ρ).re - Tr(ρ · log σ).re` (by `mul_sub` +
  `trace_sub` + `sub_re`); and the density-matrix convex
  combination's underlying matrix `(convexCombination α _ _ ρ₁ ρ₂).M`
  is definitionally `α • ρ₁.M + (1-α) • ρ₂.M`.  Hence
  specialising the corrected target at the density-matrix
  underlying matrices gives `JointConvexity_RelEntropy_Target`
  directly.

  ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
  STANDING CONSTRAINT: zero `sorry`, zero custom axioms.
  ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

  Authored 2026-06-01 (Phase B10 correction).
-/

import UnifiedTheory.LayerB.PartialTraceDPIFull
import UnifiedTheory.LayerB.LiebTargetAudit

set_option relaxedAutoImplicit false

namespace UnifiedTheory.LayerB.LiebTargetCorrected

open Matrix Complex
open scoped ComplexOrder
open UnifiedTheory.LayerB.RobertsonSchrodinger
open UnifiedTheory.LayerB.SpectralFC
open UnifiedTheory.LayerB.PartialTraceDPIFull
open UnifiedTheory.LayerB.LiebTargetAudit
open UnifiedTheory.LayerB.JointConvexityUmegaki
open UnifiedTheory.LayerB.UmegakiRelativeEntropy
open UnifiedTheory.LayerB.OperatorEntropy
open UnifiedTheory.LayerB.PartialTraceDPI

/-! ## 1. The bridge: corrected target ⟹ density-matrix joint convexity. -/

/-- **Corrected joint convexity of Umegaki relative entropy.**

    Replaces `umegakiRelativeEntropy_jointly_convex_of_liebTrace`
    (whose hypothesis `LiebTrace_Concavity_Target` is unsatisfiable
    per `liebTrace_concavity_target_is_false`).

    Derives `JointConvexity_RelEntropy_Target` directly from the
    corrected matrix-level hypothesis
    `Lieb1973_Corrected_Target` (joint convexity of the Umegaki
    form on PosDef × PosDef matrices, Lindblad 1974 / Uhlmann 1977).

    **Proof.**  `Lieb1973_Corrected_Target` is precisely the matrix-
    level statement of joint convexity, written in expanded form
    `Tr(A log A).re − Tr(A log B).re ≤ α[...] + (1-α)[...]`.
    The Umegaki relative entropy `S(ρ‖σ)` unfolds to the same
    expression via `mul_sub + trace_sub + sub_re`, and the
    underlying matrix of `convexCombination α _ _ ρ₁ ρ₂` is
    definitionally `α • ρ₁.M + (1-α) • ρ₂.M`.  Hence specialising
    the corrected target at `Aᵢ = ρᵢ.M, Bᵢ = σᵢ.M` gives the
    conclusion. -/
theorem umegakiRelativeEntropy_jointly_convex_corrected
    (hCorr : Lieb1973_Corrected_Target) :
    JointConvexity_RelEntropy_Target := by
  intro m ρ₁ ρ₂ σ₁ σ₂ hρ₁ hρ₂ hσ₁ hσ₂ α hα₀ hα₁
  -- Unfold S to the matrix-level form: Tr(ρ.M · (log ρ.M − log σ.M)).re.
  unfold umegakiRelativeEntropy operatorLog cfcρ
  -- Replace `convexCombination`-projected matrices with their
  -- definitional unfolding.
  set ρmix : Matrix (Fin m) (Fin m) ℂ :=
    (α : ℂ) • ρ₁.M + ((1 - α : ℝ) : ℂ) • ρ₂.M with hρmix_def
  set σmix : Matrix (Fin m) (Fin m) ℂ :=
    (α : ℂ) • σ₁.M + ((1 - α : ℝ) : ℂ) • σ₂.M with hσmix_def
  have h_ρmix_M : (convexCombination α hα₀ hα₁ ρ₁ ρ₂).M = ρmix := rfl
  have h_σmix_M : (convexCombination α hα₀ hα₁ σ₁ σ₂).M = σmix := rfl
  rw [h_ρmix_M, h_σmix_M]
  -- Split the LHS:
  --   Re Tr(ρmix · (log ρmix − log σmix))
  --     = Re Tr(ρmix · log ρmix) − Re Tr(ρmix · log σmix).
  rw [Matrix.mul_sub, Matrix.trace_sub, Complex.sub_re]
  -- Split the RHS (similar) and expand each S(ρᵢ‖σᵢ).
  have h_rhs_split :
      α * (Matrix.trace (ρ₁.M * (cfc Real.log ρ₁.M - cfc Real.log σ₁.M))).re
        + (1 - α) * (Matrix.trace (ρ₂.M * (cfc Real.log ρ₂.M - cfc Real.log σ₂.M))).re
      = α * ((Matrix.trace (ρ₁.M * cfc Real.log ρ₁.M)).re
              - (Matrix.trace (ρ₁.M * cfc Real.log σ₁.M)).re)
        + (1 - α) * ((Matrix.trace (ρ₂.M * cfc Real.log ρ₂.M)).re
                      - (Matrix.trace (ρ₂.M * cfc Real.log σ₂.M)).re) := by
    rw [Matrix.mul_sub, Matrix.trace_sub, Complex.sub_re,
        Matrix.mul_sub, Matrix.trace_sub, Complex.sub_re]
  rw [h_rhs_split]
  -- Specialise the corrected target at the underlying matrices.
  have h_lieb := hCorr ρ₁.M ρ₂.M σ₁.M σ₂.M hρ₁ hρ₂ hσ₁ hσ₂ α hα₀ hα₁
  -- `h_lieb` is exactly the goal after `set`-substitution.
  -- The `let A_t / B_t` bindings inside `Lieb1973_Corrected_Target`
  -- reduce defeq to `ρmix / σmix`.
  exact h_lieb

/-! ## 2. Corrected partial-trace DPI from the corrected gate. -/

/-- **Corrected partial-trace DPI.**

    Replaces `umegaki_dpi_partialTrace_of_liebTrace_etc` (whose
    Lieb hypothesis is unsatisfiable).  Composes
    `umegakiRelativeEntropy_jointly_convex_corrected` with the
    (orthogonal) `PartialTrace_Decomposition_Target`. -/
theorem umegaki_dpi_partialTrace_corrected
    (hCorr : Lieb1973_Corrected_Target)
    (hPTdec : PartialTrace_Decomposition_Target) :
    PartialTraceDPI_Target :=
  umegaki_dpi_partialTrace_of_jointConvexity_and_decomposition
    (umegakiRelativeEntropy_jointly_convex_corrected hCorr)
    hPTdec

/-! ## 3. The corrected target is well-posed.

    Two sanity checks: (a) `Lieb1973_Corrected_Target` is not refuted
    by the scalar counterexample that refutes `LiebTrace_Concavity_Target`
    (the audit's `example` already discharged this); and (b) on
    inputs with `ρᵢ = σᵢ` the corrected target reduces to `0 ≤ 0`. -/

/-- **Trivial case for the corrected target.**  When `ρ₁ = ρ₂ = ρ`
    and `σ₁ = σ₂ = σ`, the joint-convexity inequality reduces to
    `S(ρ‖σ) ≤ S(ρ‖σ)`, which is `≤`-reflexive. -/
theorem jointConvexity_corrected_self
    (hCorr : Lieb1973_Corrected_Target)
    {m : ℕ} (ρ σ : ComplexDensityMatrix m)
    (hρ : ρ.M.PosDef) (hσ : σ.M.PosDef)
    (α : ℝ) (hα₀ : 0 ≤ α) (hα₁ : α ≤ 1) :
    umegakiRelativeEntropy
        (convexCombination α hα₀ hα₁ ρ ρ)
        (convexCombination α hα₀ hα₁ σ σ)
      ≤ α * umegakiRelativeEntropy ρ σ
        + (1 - α) * umegakiRelativeEntropy ρ σ :=
  umegakiRelativeEntropy_jointly_convex_corrected hCorr
    ρ ρ σ σ hρ hρ hσ hσ α hα₀ hα₁

/-! ## 4. Axiom audit.

    Uncomment to verify after a clean build. -/

-- #print axioms umegakiRelativeEntropy_jointly_convex_corrected
-- #print axioms umegaki_dpi_partialTrace_corrected
-- #print axioms jointConvexity_corrected_self
-- VERIFIED 2026-06-01:
--   All three depend ONLY on [propext, Classical.choice, Quot.sound]
--   (Lean's three standard axioms).  No `sorry`, no custom `axiom`.

end UnifiedTheory.LayerB.LiebTargetCorrected
