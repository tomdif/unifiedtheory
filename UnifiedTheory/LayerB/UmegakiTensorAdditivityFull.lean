/-
  LayerB/UmegakiTensorAdditivityFull.lean
  ────────────────────────────────────────

  **Discharge of `UmegakiTensorAdditivity_FullFromSpectral_Target`.**

  Given `CFC_LogTensor_Identity_Target` (now unconditionally available
  via `cfcLogTensorIdentity_holds` from `LayerB/CFCLogTensor.lean`), we
  derive the full tensor additivity of Umegaki relative entropy:

      `S(ρ ⊗ τ ‖ σ ⊗ τ) = S(ρ ‖ σ)`

  for any positive-definite `ρ, σ : ComplexDensityMatrix n` and
  `τ : ComplexDensityMatrix m`, without any commutativity / diagonal /
  dimension restriction.

  ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
  Mathematical content (pure trace algebra):

  By the residual spectral identity (the hypothesis):

      `cfc log ((ρ.M ⊗ₖ τ.M).submatrix e e)
          = ((cfc log ρ.M) ⊗ₖ I_m + I_n ⊗ₖ (cfc log τ.M)).submatrix e e`
      `cfc log ((σ.M ⊗ₖ τ.M).submatrix e e)
          = ((cfc log σ.M) ⊗ₖ I_m + I_n ⊗ₖ (cfc log τ.M)).submatrix e e`

  Subtracting, the `I_n ⊗ₖ cfc log τ.M` term cancels:

      `operatorLog (kroneckerDM ρ τ) − operatorLog (kroneckerDM σ τ)
          = ((cfc log ρ.M − cfc log σ.M) ⊗ₖ I_m).submatrix e e`.

  Multiplying by `(kroneckerDM ρ τ).M = (ρ.M ⊗ₖ τ.M).submatrix e e`
  and using `submatrix_mul_equiv` + `mul_kronecker_mul`:

      `(kroneckerDM ρ τ).M · (...)
          = ((ρ.M · (cfc log ρ.M − cfc log σ.M)) ⊗ₖ τ.M).submatrix e e`.

  Taking the trace (which is invariant under reindexing via the
  bijective equivalence `e.symm`) and applying `trace_kronecker`:

      `Tr(LHS) = Tr(ρ.M · (cfc log ρ.M − cfc log σ.M)) · Tr(τ.M)
              = Tr(ρ.M · (cfc log ρ.M − cfc log σ.M)) · 1`.

  Taking the real part gives `umegakiRelativeEntropy ρ σ`.
  ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

  STANDING CONSTRAINT (NON-NEGOTIABLE): zero `sorry`, zero custom
  `axiom`.

  ## Build target

      `lake build UnifiedTheory.LayerB.UmegakiTensorAdditivityFull`
-/

import UnifiedTheory.LayerB.UmegakiTensorAdditivity
import UnifiedTheory.LayerB.CFCLogTensor
import Mathlib.LinearAlgebra.Matrix.Kronecker

set_option relaxedAutoImplicit false

namespace UnifiedTheory.LayerB.UmegakiTensorAdditivityFull

open Matrix Complex
open scoped Kronecker ComplexOrder
open UnifiedTheory.LayerB.RobertsonSchrodinger
open UnifiedTheory.LayerB.SpectralFC
open UnifiedTheory.LayerB.OperatorEntropy
open UnifiedTheory.LayerB.UmegakiRelativeEntropy
open UnifiedTheory.LayerB.UmegakiTensorAdditivity
open UnifiedTheory.LayerB.CFCLogTensor

variable {n m : ℕ}

/-! ## 1.  Trace through `Equiv.sum_comp`. -/

/-- Trace of a matrix reindexed along an equivalence equals the original
    trace.  Specialised to `finProdFinEquiv.symm`. -/
lemma trace_submatrix_finProdFinEquiv_symm
    (M : Matrix (Fin n × Fin m) (Fin n × Fin m) ℂ) :
    Matrix.trace (M.submatrix finProdFinEquiv.symm finProdFinEquiv.symm)
      = Matrix.trace M := by
  unfold Matrix.trace
  simp only [Matrix.diag_apply, Matrix.submatrix_apply]
  exact Equiv.sum_comp finProdFinEquiv.symm (fun p => M p p)

/-! ## 2.  Kronecker minus kronecker collapses. -/

/-- `(A ⊗ₖ C) − (B ⊗ₖ C) = (A − B) ⊗ₖ C` (right-distributivity of
    Kronecker over subtraction). -/
lemma sub_kronecker_right
    {α : Type*} [Ring α] (A B : Matrix (Fin n) (Fin n) α)
    (C : Matrix (Fin m) (Fin m) α) :
    A ⊗ₖ C - B ⊗ₖ C = (A - B) ⊗ₖ C := by
  ext ⟨i, j⟩ ⟨i', j'⟩
  simp [Matrix.kroneckerMap_apply, Matrix.sub_apply, sub_mul]

/-! ## 3.  The headline trace identity (pure linear algebra). -/

/-- **Core trace identity** — purely algebraic.  For any matrices
    `A : Matrix (Fin n) (Fin n) ℂ`, `B : Matrix (Fin m) (Fin m) ℂ`,
    `X : Matrix (Fin n) (Fin n) ℂ`, and assuming `Tr B = 1`, we have

      `Tr (((A ⊗ₖ B).submatrix e.symm e.symm) ·
            ((X ⊗ₖ (1 : Matrix (Fin m) (Fin m) ℂ)).submatrix e.symm e.symm))
        = Tr (A · X)`

    where `e = finProdFinEquiv`.  This is the trace of the LHS Kronecker
    product, reduced to a one-factor trace via:

      • `submatrix_mul_equiv` (combine submatrices through the product),
      • `mul_kronecker_mul` ((A ⊗ B)(C ⊗ D) = (AC) ⊗ (BD)),
      • `Matrix.mul_one` (B · 1 = B),
      • `trace_submatrix_finProdFinEquiv_symm` (trace invariant),
      • `Matrix.trace_kronecker` (Tr (P ⊗ Q) = Tr P · Tr Q),
      • the hypothesis `Tr B = 1`. -/
lemma trace_kronecker_subm_mul
    (A : Matrix (Fin n) (Fin n) ℂ)
    (B : Matrix (Fin m) (Fin m) ℂ)
    (X : Matrix (Fin n) (Fin n) ℂ) (hB : Matrix.trace B = 1) :
    Matrix.trace
        (((A ⊗ₖ B).submatrix finProdFinEquiv.symm finProdFinEquiv.symm) *
          ((X ⊗ₖ (1 : Matrix (Fin m) (Fin m) ℂ)).submatrix
              finProdFinEquiv.symm finProdFinEquiv.symm))
      = Matrix.trace (A * X) := by
  -- Combine the two submatrices through the product.
  rw [Matrix.submatrix_mul_equiv (A ⊗ₖ B) (X ⊗ₖ (1 : Matrix (Fin m) (Fin m) ℂ))
        finProdFinEquiv.symm finProdFinEquiv.symm finProdFinEquiv.symm]
  -- Factor (A ⊗ B)(X ⊗ 1) = (A · X) ⊗ (B · 1) = (A · X) ⊗ B.
  rw [← Matrix.mul_kronecker_mul]
  rw [Matrix.mul_one]
  -- Trace invariant under reindex.
  rw [trace_submatrix_finProdFinEquiv_symm]
  -- Trace kronecker = product of traces.
  rw [Matrix.trace_kronecker, hB, mul_one]

/-! ## 4.  Logs of the Kronecker densities — via the spectral hypothesis. -/

/-- Apply the spectral hypothesis to compute the `operatorLog` of
    `kroneckerDM ρ τ`. -/
lemma operatorLog_kroneckerDM
    (H : CFC_LogTensor_Identity_Target)
    (ρ : ComplexDensityMatrix n) (τ : ComplexDensityMatrix m)
    (hρ : ρ.M.PosDef) (hτ : τ.M.PosDef) :
    operatorLog (kroneckerDM ρ τ)
      = ((cfc Real.log ρ.M) ⊗ₖ (1 : Matrix (Fin m) (Fin m) ℂ)
          + (1 : Matrix (Fin n) (Fin n) ℂ) ⊗ₖ (cfc Real.log τ.M)).submatrix
            finProdFinEquiv.symm finProdFinEquiv.symm := by
  unfold operatorLog cfcρ
  -- (kroneckerDM ρ τ).M = (ρ.M ⊗ₖ τ.M).submatrix e.symm e.symm.
  change cfc Real.log
            ((ρ.M ⊗ₖ τ.M).submatrix finProdFinEquiv.symm finProdFinEquiv.symm)
        = _
  exact H ρ.M τ.M hρ hτ

/-! ## 5.  Headline theorem. -/

/-- **TENSOR ADDITIVITY OF UMEGAKI (FULL, conditional on the spectral
    identity)**.  For any positive-definite densities `ρ, σ` on
    `Fin n` and any positive-definite density `τ` on `Fin m`:

      `S(ρ ⊗ τ ‖ σ ⊗ τ) = S(ρ ‖ σ)`. -/
theorem umegakiRelativeEntropy_tensor_additive_full
    (H : CFC_LogTensor_Identity_Target)
    (ρ σ : ComplexDensityMatrix n) (τ : ComplexDensityMatrix m)
    (hρ : ρ.M.PosDef) (hσ : σ.M.PosDef) (hτ : τ.M.PosDef) :
    umegakiRelativeEntropy (kroneckerDM ρ τ) (kroneckerDM σ τ)
      = umegakiRelativeEntropy ρ σ := by
  -- Abbreviate the logs.
  set Lρ : Matrix (Fin n) (Fin n) ℂ := cfc Real.log ρ.M with hLρ_def
  set Lσ : Matrix (Fin n) (Fin n) ℂ := cfc Real.log σ.M with hLσ_def
  set Lτ : Matrix (Fin m) (Fin m) ℂ := cfc Real.log τ.M with hLτ_def
  -- Logs of the Kronecker densities.
  have h_logρτ : operatorLog (kroneckerDM ρ τ)
      = (Lρ ⊗ₖ (1 : Matrix (Fin m) (Fin m) ℂ)
          + (1 : Matrix (Fin n) (Fin n) ℂ) ⊗ₖ Lτ).submatrix
            finProdFinEquiv.symm finProdFinEquiv.symm :=
    operatorLog_kroneckerDM H ρ τ hρ hτ
  have h_logστ : operatorLog (kroneckerDM σ τ)
      = (Lσ ⊗ₖ (1 : Matrix (Fin m) (Fin m) ℂ)
          + (1 : Matrix (Fin n) (Fin n) ℂ) ⊗ₖ Lτ).submatrix
            finProdFinEquiv.symm finProdFinEquiv.symm :=
    operatorLog_kroneckerDM H σ τ hσ hτ
  -- Compute the log difference: the `I_n ⊗ₖ Lτ` term cancels.
  have h_log_diff :
      operatorLog (kroneckerDM ρ τ) - operatorLog (kroneckerDM σ τ)
        = ((Lρ - Lσ) ⊗ₖ (1 : Matrix (Fin m) (Fin m) ℂ)).submatrix
            finProdFinEquiv.symm finProdFinEquiv.symm := by
    rw [h_logρτ, h_logστ]
    -- Combine the two submatrices using submatrix_sub (functional form).
    have h_subm_sub :
        ((Lρ ⊗ₖ (1 : Matrix (Fin m) (Fin m) ℂ)
              + (1 : Matrix (Fin n) (Fin n) ℂ) ⊗ₖ Lτ)).submatrix
              finProdFinEquiv.symm finProdFinEquiv.symm
          - ((Lσ ⊗ₖ (1 : Matrix (Fin m) (Fin m) ℂ)
              + (1 : Matrix (Fin n) (Fin n) ℂ) ⊗ₖ Lτ)).submatrix
              finProdFinEquiv.symm finProdFinEquiv.symm
          = ((Lρ ⊗ₖ (1 : Matrix (Fin m) (Fin m) ℂ)
              + (1 : Matrix (Fin n) (Fin n) ℂ) ⊗ₖ Lτ)
              - (Lσ ⊗ₖ (1 : Matrix (Fin m) (Fin m) ℂ)
              + (1 : Matrix (Fin n) (Fin n) ℂ) ⊗ₖ Lτ)).submatrix
              finProdFinEquiv.symm finProdFinEquiv.symm := by
      ext i j
      simp [Matrix.submatrix_apply, Matrix.sub_apply]
    rw [h_subm_sub]
    congr 1
    -- (Lρ ⊗ 1 + 1 ⊗ Lτ) - (Lσ ⊗ 1 + 1 ⊗ Lτ) = Lρ ⊗ 1 - Lσ ⊗ 1 = (Lρ - Lσ) ⊗ 1
    rw [show (Lρ ⊗ₖ (1 : Matrix (Fin m) (Fin m) ℂ)
              + (1 : Matrix (Fin n) (Fin n) ℂ) ⊗ₖ Lτ)
            - (Lσ ⊗ₖ (1 : Matrix (Fin m) (Fin m) ℂ)
              + (1 : Matrix (Fin n) (Fin n) ℂ) ⊗ₖ Lτ)
            = Lρ ⊗ₖ (1 : Matrix (Fin m) (Fin m) ℂ)
              - Lσ ⊗ₖ (1 : Matrix (Fin m) (Fin m) ℂ) by abel]
    exact sub_kronecker_right Lρ Lσ (1 : Matrix (Fin m) (Fin m) ℂ)
  -- Now unfold umegakiRelativeEntropy and route through the core trace identity.
  unfold umegakiRelativeEntropy
  rw [h_log_diff]
  -- (kroneckerDM ρ τ).M = (ρ.M ⊗ₖ τ.M).submatrix e.symm e.symm.
  change (Matrix.trace
            (((ρ.M ⊗ₖ τ.M).submatrix finProdFinEquiv.symm finProdFinEquiv.symm)
              * (((Lρ - Lσ) ⊗ₖ (1 : Matrix (Fin m) (Fin m) ℂ)).submatrix
                  finProdFinEquiv.symm finProdFinEquiv.symm))).re
        = (Matrix.trace (ρ.M * (operatorLog ρ - operatorLog σ))).re
  -- Apply the core trace identity.
  rw [trace_kronecker_subm_mul ρ.M τ.M (Lρ - Lσ) τ.hTrace]
  -- Goal: Tr(ρ.M * (Lρ - Lσ)) = Tr(ρ.M * (operatorLog ρ - operatorLog σ))
  -- Lρ = cfc log ρ.M = cfcρ log ρ = operatorLog ρ (by definition).
  have h_Lρ : Lρ = operatorLog ρ := rfl
  have h_Lσ : Lσ = operatorLog σ := rfl
  rw [h_Lρ, h_Lσ]

/-! ## 6.  Discharge of the named gate. -/

/-- **Discharges `UmegakiTensorAdditivity_FullFromSpectral_Target`.**

    The target is the implication
      `CFC_LogTensor_Identity_Target → ∀ ρ σ τ PosDef, identity`,
    which is exactly what `umegakiRelativeEntropy_tensor_additive_full`
    proves. -/
theorem umegakiTensorAdditivityFull_holds :
    UmegakiTensorAdditivity_FullFromSpectral_Target := by
  intro H _ _ ρ σ τ hρ hσ hτ
  exact umegakiRelativeEntropy_tensor_additive_full H ρ σ τ hρ hσ hτ

/-! ## 7.  Unconditional headline.

Since `CFC_LogTensor_Identity_Target` is now itself discharged
unconditionally (`cfcLogTensorIdentity_holds`), the headline tensor
additivity is unconditional. -/

/-- **UNCONDITIONAL TENSOR ADDITIVITY**: `S(ρ ⊗ τ ‖ σ ⊗ τ) = S(ρ ‖ σ)`
    for any positive-definite density matrices `ρ, σ, τ`. -/
theorem umegakiRelativeEntropy_tensor_additive
    (ρ σ : ComplexDensityMatrix n) (τ : ComplexDensityMatrix m)
    (hρ : ρ.M.PosDef) (hσ : σ.M.PosDef) (hτ : τ.M.PosDef) :
    umegakiRelativeEntropy (kroneckerDM ρ τ) (kroneckerDM σ τ)
      = umegakiRelativeEntropy ρ σ :=
  umegakiRelativeEntropy_tensor_additive_full
    cfcLogTensorIdentity_holds ρ σ τ hρ hσ hτ

/-! ## 8.  Axiom audit. -/

#print axioms umegakiTensorAdditivityFull_holds
#print axioms umegakiRelativeEntropy_tensor_additive

end UnifiedTheory.LayerB.UmegakiTensorAdditivityFull
