/-
  LayerB/UnitaryInvariance.lean
  ──────────────────────────────

  **Unitary invariance of the continuous functional calculus**
  and **of Umegaki relative entropy**.  Phase B7 of the
  Lindblad-Uhlmann roadmap.

  The keystone identity: for any unitary `U` and Hermitian matrix
  `M`,

      cfc f (U · M · star U)  =  U · (cfc f M) · star U.

  Proof: conjugation by a unitary is a *-algebra automorphism
  (`Unitary.conjStarAlgAut`), and the continuous functional
  calculus is NATURAL with respect to *-algebra homomorphisms
  (`StarAlgHomClass.map_cfc`).

  Specialised to `Real.log` and density matrices, this gives
  unitary invariance of Umegaki relative entropy:

      S(U ρ U* ‖ U σ U*)  =  S(ρ ‖ σ).

  WHAT IS PROVEN (no sorry, no custom axioms):
    1. `cfc_unitary_conj`                    — naturality on matrices.
    2. `cfc_log_unitary_conj`                — specialised to `Real.log`.
    3. `unitaryConjugate U ρ`                — `U ρ U*` as a
                                                `ComplexDensityMatrix`.
    4. `operatorLog_unitary_conj`            — `log (U ρ U*) = U (log ρ) U*`.
    5. `umegakiRelativeEntropy_unitary_invariant` —
                                                `S(U ρ U* ‖ U σ U*) = S(ρ ‖ σ)`.
-/

import UnifiedTheory.LayerB.UmegakiRelativeEntropy
import UnifiedTheory.LayerB.OperatorMonotoneLog
import Mathlib.Algebra.Star.UnitaryStarAlgAut
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Unique

set_option relaxedAutoImplicit false

namespace UnifiedTheory.LayerB.UnitaryInvariance

open Matrix Complex Unitary
open scoped MatrixOrder ComplexOrder
open UnifiedTheory.LayerB.RobertsonSchrodinger
open UnifiedTheory.LayerB.SpectralFC
open UnifiedTheory.LayerB.OperatorEntropy
open UnifiedTheory.LayerB.UmegakiRelativeEntropy

variable {n : ℕ}

/-- Re-declare the matrix CStarAlgebra instance (mirrors
    `OperatorMonotoneLog.lean`'s pattern). -/
noncomputable scoped instance matrixCStarAlgebra :
    CStarAlgebra (Matrix (Fin n) (Fin n) ℂ) where

/-! ## 1. CFC commutes with unitary conjugation -/

/-- **CFC naturality for unitary conjugation.**  For any unitary
    `U`, Hermitian matrix `M`, and continuous `f : ℝ → ℝ`:

      `cfc f (U · M · star U)  =  U · cfc f M · star U`. -/
theorem cfc_unitary_conj
    (U : Matrix.unitaryGroup (Fin n) ℂ)
    (M : Matrix (Fin n) (Fin n) ℂ) (f : ℝ → ℝ)
    (hM : IsSelfAdjoint M)
    (hf : ContinuousOn f (spectrum ℝ M) := by cfc_cont_tac) :
    cfc f (U.val * M * star U.val) = U.val * (cfc f M) * star U.val := by
  let φ : (Matrix (Fin n) (Fin n) ℂ) ≃⋆ₐ[ℂ] (Matrix (Fin n) (Fin n) ℂ) :=
    Unitary.conjStarAlgAut ℂ _ U
  have h_phi_M : φ M = U.val * M * star U.val := by
    simp [φ, Unitary.conjStarAlgAut_apply]
  have h_phi_cfc : φ (cfc f M) = U.val * (cfc f M) * star U.val := by
    simp [φ, Unitary.conjStarAlgAut_apply]
  have h_phi_cont : Continuous φ := by
    have h_eq : (φ : Matrix (Fin n) (Fin n) ℂ → Matrix (Fin n) (Fin n) ℂ)
              = fun M => U.val * M * star U.val := by
      funext M
      simp [φ, Unitary.conjStarAlgAut_apply]
    rw [h_eq]
    fun_prop
  have h_phi_M_SA : IsSelfAdjoint (φ M) := by
    rw [h_phi_M]; exact hM.conjugate U.val
  have key : φ (cfc f M) = cfc f (φ M) :=
    StarAlgHomClass.map_cfc (S := ℂ) (R := ℝ) φ f M hf h_phi_cont hM h_phi_M_SA
  rw [h_phi_M, h_phi_cfc] at key
  exact key.symm

/-- Specialised to `Real.log`. -/
theorem cfc_log_unitary_conj
    (U : Matrix.unitaryGroup (Fin n) ℂ)
    (M : Matrix (Fin n) (Fin n) ℂ) (hM : IsSelfAdjoint M) :
    cfc Real.log (U.val * M * star U.val)
      = U.val * (cfc Real.log M) * star U.val := by
  exact cfc_unitary_conj U M Real.log hM (by
    exact (Set.toFinite _).continuousOn _)

/-! ## 2. Package `U ρ U*` as a `ComplexDensityMatrix` -/

/-- The unitary conjugate of a density matrix: `U ρ U*` packaged
    with proofs of Hermiticity, trace 1, and the trace-PSD field. -/
noncomputable def unitaryConjugate
    (U : Matrix.unitaryGroup (Fin n) ℂ) (ρ : ComplexDensityMatrix n) :
    ComplexDensityMatrix n where
  M := U.val * ρ.M * star U.val
  hHerm := by
    change (U.val * ρ.M * star U.val).conjTranspose = U.val * ρ.M * star U.val
    rw [conjTranspose_mul, conjTranspose_mul]
    -- (star U.val).conjTranspose = U.val
    have h_star_star :
        (star U.val : Matrix (Fin n) (Fin n) ℂ).conjTranspose = U.val := by
      change star (star U.val) = U.val
      exact star_star _
    have h_U_ct : (U.val : Matrix (Fin n) (Fin n) ℂ).conjTranspose = star U.val := rfl
    rw [h_star_star, ρ.hHerm.eq, h_U_ct]
    -- Now reassociate
    rw [Matrix.mul_assoc]
  hTrace := by
    -- Tr(U ρ (star U)) = Tr((star U) U ρ) = Tr(ρ) = 1.
    have h : Matrix.trace (U.val * ρ.M * star U.val)
           = Matrix.trace (star U.val * U.val * ρ.M) := by
      rw [Matrix.trace_mul_cycle]
    rw [h, Matrix.mem_unitaryGroup_iff'.mp U.property, Matrix.one_mul, ρ.hTrace]
  hTracePSD := by
    intro X
    -- Goal: 0 ≤ Re(Tr(U ρ (star U) · X† · X))
    -- Use trace cyclicity to bring U to the right: Tr(U · M) = Tr(M · U) where M = ρ (star U) X† X.
    have h_eq :
        Matrix.trace (U.val * ρ.M * star U.val * X.conjTranspose * X)
          = Matrix.trace
              (ρ.M * (X * U.val).conjTranspose * (X * U.val)) := by
      -- LHS = U · (ρ (star U) X† X); cycle U to the right.
      rw [show U.val * ρ.M * star U.val * X.conjTranspose * X
              = U.val * (ρ.M * star U.val * X.conjTranspose * X) from by
            simp only [Matrix.mul_assoc]]
      rw [Matrix.trace_mul_comm]
      -- Now: Tr((ρ (star U) X† X) · U) — show this equals RHS.
      rw [conjTranspose_mul]
      have h_U_ct :
          (U.val : Matrix (Fin n) (Fin n) ℂ).conjTranspose = star U.val := rfl
      rw [h_U_ct]
      -- RHS = ρ · (star U · X†) · (X · U); reassociate to match.
      congr 1
      simp only [Matrix.mul_assoc]
    rw [h_eq]
    exact ρ.hTracePSD (X * U.val)

/-! ## 3. `operatorLog` commutes with unitary conjugation -/

/-- **`operatorLog (U ρ U*) = U (operatorLog ρ) U*`.** -/
theorem operatorLog_unitaryConjugate
    (U : Matrix.unitaryGroup (Fin n) ℂ) (ρ : ComplexDensityMatrix n) :
    operatorLog (unitaryConjugate U ρ)
      = U.val * (operatorLog ρ) * star U.val := by
  unfold operatorLog cfcρ
  change cfc Real.log (U.val * ρ.M * star U.val)
       = U.val * cfc Real.log ρ.M * star U.val
  exact cfc_log_unitary_conj U ρ.M ρ.hHerm

/-! ## 4. Unitary invariance of Umegaki relative entropy -/

/-- **`S(U ρ U* ‖ U σ U*) = S(ρ ‖ σ)`.**

    By trace cyclicity, after rewriting both `operatorLog`s using
    `operatorLog_unitaryConjugate`:
      `Tr(U ρ U* · (U log ρ U* − U log σ U*))
        = Tr(U ρ (log ρ − log σ) U*)`  [factor U, star U out, cancel]
        = `Tr(ρ (log ρ − log σ))`. -/
theorem umegakiRelativeEntropy_unitary_invariant
    (U : Matrix.unitaryGroup (Fin n) ℂ) (ρ σ : ComplexDensityMatrix n) :
    umegakiRelativeEntropy (unitaryConjugate U ρ) (unitaryConjugate U σ)
      = umegakiRelativeEntropy ρ σ := by
  unfold umegakiRelativeEntropy
  rw [operatorLog_unitaryConjugate U ρ, operatorLog_unitaryConjugate U σ]
  congr 1
  -- Per-term cancellation lemma: Tr(U ρ U* · U X U*) = Tr(ρ X) for any X.
  have h_cancel : ∀ X : Matrix (Fin n) (Fin n) ℂ,
      Matrix.trace (U.val * ρ.M * star U.val * (U.val * X * star U.val))
        = Matrix.trace (ρ.M * X) := by
    intro X
    have h_eq : U.val * ρ.M * star U.val * (U.val * X * star U.val)
              = U.val * (ρ.M * X) * star U.val := by
      calc U.val * ρ.M * star U.val * (U.val * X * star U.val)
          = U.val * ρ.M * (star U.val * U.val) * X * star U.val := by
              simp only [Matrix.mul_assoc]
        _ = U.val * ρ.M * 1 * X * star U.val := by
              rw [Matrix.mem_unitaryGroup_iff'.mp U.property]
        _ = U.val * (ρ.M * X) * star U.val := by
              rw [Matrix.mul_one]; simp only [Matrix.mul_assoc]
    rw [h_eq, Matrix.trace_mul_cycle, ← Matrix.mul_assoc,
        Matrix.mem_unitaryGroup_iff'.mp U.property, Matrix.one_mul]
  -- Distribute the inner subtraction, apply h_cancel per term.
  change Matrix.trace
          (U.val * ρ.M * star U.val *
            (U.val * operatorLog ρ * star U.val - U.val * operatorLog σ * star U.val))
       = Matrix.trace (ρ.M * (operatorLog ρ - operatorLog σ))
  rw [Matrix.mul_sub, Matrix.trace_sub, h_cancel (operatorLog ρ),
      h_cancel (operatorLog σ), ← Matrix.trace_sub, ← Matrix.mul_sub]

end UnifiedTheory.LayerB.UnitaryInvariance
