/-
  LayerB/LiebThirring.lean
  ─────────────────────────

  **The Lieb–Thirring trace inequality** (Lieb–Thirring 1976).

  For positive semidefinite matrices `A, B` and `q ≥ 1`:

      `Tr((B^{1/2} A B^{1/2})^q) ≤ Tr(B^{q/2} A^q B^{q/2})`
                                 `= Tr(A^q B^q)`   (by cyclicity).

  For `0 < q ≤ 1` the inequality reverses.  At `q = 1` it is an
  *equality* — `Tr(B^{1/2} A B^{1/2}) = Tr(A B)` — by trace
  cyclicity, requiring nothing beyond the existence of `B^{1/2}`.

  This is a trace-power rearrangement inequality, a generalisation
  of (the trace side of) the Golden–Thompson direction.  The deep
  general inequality (Lieb–Thirring 1976; Araki 1990 for the
  log-majorisation refinement) is one of the cornerstones of the
  proof of stability of matter.

  ## What this file ships

  **UNCONDITIONAL (load-bearing):**

    *   `liebThirring_q_one` — the `q = 1` case:
        `Tr(√B · A · √B) = Tr(A · B)` by trace cyclicity, for any
        PSD `B` (only `√B · √B = B` is used).  Headline.

    *   `liebThirring_q_one_le` / `liebThirring_q_one_ge` — the
        `q = 1` equality re-exported as the (degenerate) inequality
        in both directions.

    *   `comm_eigenvalue_identity` — the scalar rearrangement
        `(b · a) ^ q = b^{q/2} · a^q · b^{q/2}` for `a, b ≥ 0`,
        `q ≥ 0`; the per-eigenvalue heart of the commuting case.

    *   `liebThirring_commuting_eq_matrix` — the **commuting case**
        at the *matrix* level: for commuting PSD `A, B` and `q ≥ 0`,
        `(√B A √B)^q = B^{q/2} A^q B^{q/2}` as matrices, via joint
        diagonalisation.

    *   `liebThirring_commuting_eq` — the commuting case at the
        *trace* level: `liebThirringLHS A B q = liebThirringRHS A B q`.
        Hence Lieb–Thirring holds with equality for commuting PSD
        pairs, for every `q ≥ 0`.

    *   `liebThirring_commuting_target_holds` — discharge of the
        named commuting gate.

  **NAMED TARGETS (the deep non-commuting directions):**

    *   `LiebThirring_Commuting_Target` — commuting case as a gate
        (discharged).
    *   `LiebThirring_Target` — the general `q ≥ 1` inequality.
    *   `LiebThirring_Reverse_Target` — the reverse `0 < q ≤ 1`
        inequality.
    *   `lieb_thirring_master` — composite: the general target,
        restricted to commuting pairs, follows from the commuting
        case; the residual obligation is purely non-commuting.

  ## Conventions

    *   `√B  :=  CFC.sqrt B`                    (`B^{1/2}`)
    *   `B ^ r  :=  CFC.rpow B r`               (real powers)

  We reuse the project's joint-diagonalisation infrastructure
  (`JointDiagonalisationCommuting`), fed the quadruple `(A, B, 0, 0)`.

  ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
  STANDING CONSTRAINT: zero `sorry`, zero custom axioms.
  ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

  Authored 2026-06-02.
-/

import UnifiedTheory.LayerB.JointDiagonalisationCommuting
import UnifiedTheory.LayerB.UnitaryInvariance
import UnifiedTheory.LayerB.CFCDiagonalDischarge
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic

set_option relaxedAutoImplicit false

namespace UnifiedTheory.LayerB.LiebThirring

open Matrix Complex
open scoped MatrixOrder ComplexOrder
open UnifiedTheory.LayerB.JointDiagonalisationCommuting
open UnifiedTheory.LayerB.LiebCorrectedCommutingFull
open UnifiedTheory.LayerB.UnitaryInvariance
open UnifiedTheory.LayerB.CFCDiagonalDischarge

/-! ## 0. The two sides of the inequality. -/

section Sides

variable {n : ℕ}

/-- The "sandwiched" matrix `√B · A · √B`. -/
noncomputable def sandwich (A B : Matrix (Fin n) (Fin n) ℂ) :
    Matrix (Fin n) (Fin n) ℂ :=
  CFC.sqrt B * A * CFC.sqrt B

/-- LHS matrix: `(√B · A · √B) ^ q`. -/
noncomputable def liebThirringLHSMatrix
    (A B : Matrix (Fin n) (Fin n) ℂ) (q : ℝ) :
    Matrix (Fin n) (Fin n) ℂ :=
  CFC.rpow (sandwich A B) q

/-- RHS matrix: `B^{q/2} · A^q · B^{q/2}`. -/
noncomputable def liebThirringRHSMatrix
    (A B : Matrix (Fin n) (Fin n) ℂ) (q : ℝ) :
    Matrix (Fin n) (Fin n) ℂ :=
  CFC.rpow B (q / 2) * CFC.rpow A q * CFC.rpow B (q / 2)

/-- LHS scalar: `Tr((√B · A · √B) ^ q)`. -/
noncomputable def liebThirringLHS
    (A B : Matrix (Fin n) (Fin n) ℂ) (q : ℝ) : ℂ :=
  Matrix.trace (liebThirringLHSMatrix A B q)

/-- RHS scalar: `Tr(B^{q/2} · A^q · B^{q/2})`. -/
noncomputable def liebThirringRHS
    (A B : Matrix (Fin n) (Fin n) ℂ) (q : ℝ) : ℂ :=
  Matrix.trace (liebThirringRHSMatrix A B q)

end Sides

/-! ## 1. The `q = 1` case (UNCONDITIONAL equality via cyclicity). -/

section QOne

variable {n : ℕ}

/-- **`q = 1` Lieb–Thirring (the headline unconditional result).**

    For positive semidefinite `B`,
    `Tr(√B · A · √B) = Tr(A · B)`.

    Pure trace cyclicity: `Tr(√B · A · √B) = Tr(√B · √B · A)`
    by `Matrix.trace_mul_cycle`, and `√B · √B = B` by
    `CFC.sqrt_mul_sqrt_self`. -/
theorem liebThirring_q_one
    (A B : Matrix (Fin n) (Fin n) ℂ) (hB : B.PosSemidef) :
    Matrix.trace (CFC.sqrt B * A * CFC.sqrt B) = Matrix.trace (A * B) := by
  -- Cyclic rotation:  Tr(√B · A · √B) = Tr(√B · √B · A).
  rw [Matrix.trace_mul_cycle (CFC.sqrt B) A (CFC.sqrt B)]
  -- Now collapse √B · √B = B.
  have hsq : CFC.sqrt B * CFC.sqrt B = B :=
    CFC.sqrt_mul_sqrt_self B hB.nonneg
  rw [hsq, Matrix.trace_mul_comm]

/-- `q = 1` inequality (≤) — degenerate from the equality. -/
theorem liebThirring_q_one_le
    (A B : Matrix (Fin n) (Fin n) ℂ) (hB : B.PosSemidef) :
    (Matrix.trace (CFC.sqrt B * A * CFC.sqrt B)).re
      ≤ (Matrix.trace (A * B)).re := by
  rw [liebThirring_q_one A B hB]

/-- `q = 1` inequality (≥) — degenerate from the equality. -/
theorem liebThirring_q_one_ge
    (A B : Matrix (Fin n) (Fin n) ℂ) (hB : B.PosSemidef) :
    (Matrix.trace (A * B)).re
      ≤ (Matrix.trace (CFC.sqrt B * A * CFC.sqrt B)).re := by
  rw [liebThirring_q_one A B hB]

/-- The `q = 1` LHS scalar (via the definitions) equals `Tr(A · B)`. -/
theorem liebThirring_q_one_def
    (A B : Matrix (Fin n) (Fin n) ℂ)
    (hA : A.PosSemidef) (hB : B.PosSemidef) :
    liebThirringLHS A B 1 = Matrix.trace (A * B) := by
  unfold liebThirringLHS liebThirringLHSMatrix sandwich
  -- (√B · A · √B) ^ 1 = √B · A · √B, since the sandwich is PSD.
  have hsqrtB : (CFC.sqrt B).PosSemidef := (CFC.sqrt_nonneg B).posSemidef
  have h_sand_psd : (CFC.sqrt B * A * CFC.sqrt B).PosSemidef := by
    have h := hA.mul_mul_conjTranspose_same (B := CFC.sqrt B)
    simpa [hsqrtB.isHermitian.eq] using h
  rw [show CFC.rpow (CFC.sqrt B * A * CFC.sqrt B) 1 = CFC.sqrt B * A * CFC.sqrt B from
        CFC.rpow_one (CFC.sqrt B * A * CFC.sqrt B) h_sand_psd.nonneg]
  exact liebThirring_q_one A B hB

end QOne

/-! ## 2. The scalar eigenvalue identity. -/

section ScalarIdentity

/-- Scalar lemma behind the commuting case: for nonnegative reals
    `a, b` and `q ≥ 0`,

        `(b · a) ^ q = b ^ (q/2) · a ^ q · b ^ (q/2)`.

    On jointly diagonalised `A, B`, the `i`-th eigenvalues
    `a_i, b_i ≥ 0` satisfy this exactly, so the two trace sides
    agree term by term. -/
theorem comm_eigenvalue_identity
    (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (q : ℝ) (hq : 0 ≤ q) :
    (b * a) ^ q = b ^ (q / 2) * a ^ q * b ^ (q / 2) := by
  have hbsplit : b ^ (q / 2) * b ^ (q / 2) = b ^ q := by
    rw [← Real.rpow_add_of_nonneg hb (by linarith) (by linarith)]
    ring_nf
  rw [Real.mul_rpow hb ha, ← hbsplit]
  ring

end ScalarIdentity

/-! ## 3. The commuting case (UNCONDITIONAL equality of matrices).

    When `A, B` commute and are PSD, joint diagonalisation gives a
    shared unitary `U` with `A = U·diag(dA)·U*`, `B = U·diag(dB)·U*`,
    eigenvalues `dA, dB ≥ 0`.  Every CFC operation (`sqrt`, `rpow`)
    and matrix product respects this resolution, reducing the
    matrix identity to the scalar identity entrywise. -/

section Commuting

variable {n : ℕ}

/-! ### 3a. Diagonal-conjugation building blocks. -/

/-- `(A, B, 0, 0)` pairwise commute whenever `Commute A B`. -/
private lemma allCommute_pair_zero_zero
    (A B : Matrix (Fin n) (Fin n) ℂ) (h : Commute A B) :
    AllCommute A B (0 : Matrix (Fin n) (Fin n) ℂ)
      (0 : Matrix (Fin n) (Fin n) ℂ) :=
  ⟨h, Commute.zero_right A, Commute.zero_right A,
    Commute.zero_right B, Commute.zero_right B, Commute.zero_right 0⟩

/-- PSD analogue of `diag_pos_of_posDef_conj`: if `U·diag(d)·U*` is
    PSD then every entry `d i ≥ 0`. -/
private lemma diag_nonneg_of_posSemidef_conj
    (U : Matrix.unitaryGroup (Fin n) ℂ) (d : Fin n → ℝ)
    (X : Matrix (Fin n) (Fin n) ℂ) (hX : X.PosSemidef)
    (h_eq : U.val * Matrix.diagonal (fun i => ((d i : ℝ) : ℂ)) * (star U.val) = X) :
    ∀ i, 0 ≤ d i := by
  intro i
  set D : Matrix (Fin n) (Fin n) ℂ :=
    Matrix.diagonal (fun j => ((d j : ℝ) : ℂ)) with hD_def
  have hUstarU : (star U.val) * U.val = 1 :=
    Matrix.mem_unitaryGroup_iff'.mp U.property
  -- D = star U * X * U = (U)ᴴ * X * U.
  have hD_eq : D = (star U.val) * X * U.val := by
    rw [← h_eq]
    calc D = 1 * D * 1 := by rw [Matrix.one_mul, Matrix.mul_one]
      _ = (star U.val * U.val) * D * (star U.val * U.val) := by rw [hUstarU]
      _ = (star U.val) * (U.val * D * (star U.val)) * U.val := by
            simp only [Matrix.mul_assoc]
  have h_conjT : (U.val).conjTranspose = star U.val := rfl
  have hD_PSD : D.PosSemidef := by
    rw [hD_eq]
    have key := hX.conjTranspose_mul_mul_same (B := U.val)
    rw [h_conjT] at key
    exact key
  have h_nonneg_complex : ∀ j, (0 : ℂ) ≤ ((d j : ℝ) : ℂ) :=
    Matrix.posSemidef_diagonal_iff.mp (hD_def ▸ hD_PSD)
  exact_mod_cast h_nonneg_complex i

/-- `CFC.rpow` of a unitary conjugate of a Hermitian matrix is the
    conjugate of the `CFC.rpow`.  Proven by reducing `rpow` to the
    real-valued CFC `(· ^ y)` and invoking `cfc_unitary_conj`. -/
private lemma rpow_unitary_conj
    (U : Matrix.unitaryGroup (Fin n) ℂ)
    (M : Matrix (Fin n) (Fin n) ℂ) (hM : (M).PosSemidef) (y : ℝ) :
    CFC.rpow (U.val * M * star U.val) y
      = U.val * (CFC.rpow M y) * star U.val := by
  -- The conjugate is PSD, so both rpow's are the real CFC of (· ^ y).
  have hMnn : 0 ≤ M := hM.nonneg
  have hconj_psd : (U.val * M * star U.val).PosSemidef := by
    have h := hM.mul_mul_conjTranspose_same (B := U.val)
    have h_conjT : (U.val).conjTranspose = star U.val := rfl
    rw [h_conjT] at h
    exact h
  have hconj_nn : 0 ≤ U.val * M * star U.val := hconj_psd.nonneg
  rw [show CFC.rpow (U.val * M * star U.val) y
        = cfc (fun x : ℝ => x ^ y) (U.val * M * star U.val) from
      CFC.rpow_eq_cfc_real (a := U.val * M * star U.val) hconj_nn,
      show CFC.rpow M y = cfc (fun x : ℝ => x ^ y) M from
      CFC.rpow_eq_cfc_real (a := M) hMnn]
  exact cfc_unitary_conj U M (fun x : ℝ => x ^ y) hM.isHermitian.isSelfAdjoint
    (by exact (Set.toFinite _).continuousOn _)

/-- `CFC.rpow` of a real diagonal matrix is the entrywise `(· ^ y)`. -/
private lemma rpow_diagonal_ofReal (d : Fin n → ℝ) (hd : ∀ i, 0 ≤ d i) (y : ℝ) :
    CFC.rpow (Matrix.diagonal (fun i => ((d i : ℝ) : ℂ))) y
      = Matrix.diagonal (fun i => ((d i ^ y : ℝ) : ℂ)) := by
  have hdiag_nn : (0 : Matrix (Fin n) (Fin n) ℂ)
      ≤ Matrix.diagonal (fun i => ((d i : ℝ) : ℂ)) := by
    rw [Matrix.nonneg_iff_posSemidef]
    rw [Matrix.posSemidef_diagonal_iff]
    intro i
    exact_mod_cast hd i
  rw [show CFC.rpow (Matrix.diagonal (fun i => ((d i : ℝ) : ℂ))) y
        = cfc (fun x : ℝ => x ^ y) (Matrix.diagonal (fun i => ((d i : ℝ) : ℂ))) from
      CFC.rpow_eq_cfc_real (a := Matrix.diagonal (fun i => ((d i : ℝ) : ℂ))) hdiag_nn]
  exact cfcOnDiagonalIsEntrywise_real n (fun x : ℝ => x ^ y) d

/-! ### 3b. The matrix-level commuting equality. -/

/-- **Commuting Lieb–Thirring (matrix equality).**

    For commuting PSD `A, B` and `q ≥ 0`,
    `(√B · A · √B) ^ q = B^{q/2} · A^q · B^{q/2}` as matrices. -/
theorem liebThirring_commuting_eq_matrix
    (A B : Matrix (Fin n) (Fin n) ℂ) (q : ℝ) (hq : 0 ≤ q)
    (hA : A.PosSemidef) (hB : B.PosSemidef) (hComm : Commute A B) :
    liebThirringLHSMatrix A B q = liebThirringRHSMatrix A B q := by
  -- Joint diagonalisation of (A, B, 0, 0).
  obtain ⟨J⟩ := jointDiagonalisation_exists_of_allCommute A B
    (0 : Matrix (Fin n) (Fin n) ℂ) (0 : Matrix (Fin n) (Fin n) ℂ)
    hA.isHermitian hB.isHermitian Matrix.isHermitian_zero Matrix.isHermitian_zero
    (allCommute_pair_zero_zero A B hComm)
  set U : Matrix.unitaryGroup (Fin n) ℂ := J.U with hU
  set DA : Matrix (Fin n) (Fin n) ℂ :=
    Matrix.diagonal (fun i => ((J.dA i : ℝ) : ℂ)) with hDA
  set DB : Matrix (Fin n) (Fin n) ℂ :=
    Matrix.diagonal (fun i => ((J.dB i : ℝ) : ℂ)) with hDB
  have hA_eq : U.val * DA * star U.val = A := J.hA
  have hB_eq : U.val * DB * star U.val = B := J.hB
  -- Eigenvalues are nonnegative.
  have hdA_nn : ∀ i, 0 ≤ J.dA i :=
    diag_nonneg_of_posSemidef_conj U J.dA A hA hA_eq
  have hdB_nn : ∀ i, 0 ≤ J.dB i :=
    diag_nonneg_of_posSemidef_conj U J.dB B hB hB_eq
  -- Unitary identities.
  have hUstarU : star U.val * U.val = 1 :=
    Matrix.mem_unitaryGroup_iff'.mp U.property
  have hDA_psd : DA.PosSemidef := by
    rw [hDA]
    apply Matrix.posSemidef_diagonal_iff.mpr
    intro i; exact_mod_cast hdA_nn i
  have hDB_psd : DB.PosSemidef := by
    rw [hDB]
    apply Matrix.posSemidef_diagonal_iff.mpr
    intro i; exact_mod_cast hdB_nn i
  -- √B = B^{1/2} = U · diag(dB^{1/2}) · U*.
  have hsqrtB : CFC.sqrt B
      = U.val * Matrix.diagonal (fun i => ((J.dB i ^ (1/2 : ℝ) : ℝ) : ℂ)) * star U.val := by
    rw [show CFC.sqrt B = CFC.rpow B (1/2 : ℝ) from CFC.sqrt_eq_rpow]
    conv_lhs => rw [← hB_eq]
    rw [rpow_unitary_conj U DB hDB_psd (1/2), hDB,
        rpow_diagonal_ofReal J.dB hdB_nn (1/2)]
  -- Sandwich = U · diag(dB^{1/2} · dA · dB^{1/2}) · U*.
  set SDB : Matrix (Fin n) (Fin n) ℂ :=
    Matrix.diagonal (fun i => ((J.dB i ^ (1/2 : ℝ) : ℝ) : ℂ)) with hSDB
  have h_sandwich : sandwich A B = U.val * (SDB * DA * SDB) * star U.val := by
    unfold sandwich
    rw [hsqrtB, ← hA_eq]
    -- (U SDB U*)(U DA U*)(U SDB U*) collapses the inner U* U = 1 pairs.
    rw [Matrix.mul_assoc, Matrix.mul_assoc, Matrix.mul_assoc]
    rw [show star U.val * (U.val * DA * star U.val * (U.val * SDB * star U.val))
          = (star U.val * U.val) * DA * star U.val * (U.val * SDB * star U.val) by
        simp only [Matrix.mul_assoc]]
    rw [hUstarU]
    rw [show (1 : Matrix (Fin n) (Fin n) ℂ) * DA * star U.val * (U.val * SDB * star U.val)
          = DA * (star U.val * U.val) * SDB * star U.val by
        simp only [Matrix.one_mul, Matrix.mul_assoc]]
    rw [hUstarU]
    simp only [Matrix.mul_one, Matrix.mul_assoc]
  -- diag(dB^{1/2}) · DA · diag(dB^{1/2}) = diag(dB^{1/2} · dA · dB^{1/2}) = diag(dB · dA).
  have h_diag_sandwich : SDB * DA * SDB
      = Matrix.diagonal (fun i => ((J.dB i * J.dA i : ℝ) : ℂ)) := by
    rw [hSDB, hDA, Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
    refine congrArg _ ?_
    funext i
    have hsq : J.dB i ^ (1/2 : ℝ) * J.dB i ^ (1/2 : ℝ) = J.dB i := by
      rw [← Real.rpow_add_of_nonneg (hdB_nn i) (by norm_num) (by norm_num)]
      norm_num
    have hcast :
        ((J.dB i ^ (1/2 : ℝ) : ℝ) : ℂ) * (J.dA i : ℂ) * ((J.dB i ^ (1/2 : ℝ) : ℝ) : ℂ)
          = (((J.dB i ^ (1/2 : ℝ) * J.dB i ^ (1/2 : ℝ)) * J.dA i : ℝ) : ℂ) := by
      push_cast; ring
    rw [hcast, hsq]
  -- LHS matrix = (sandwich)^q = U · diag((dB·dA)^q) · U*.
  have h_sand_diag_nn : ∀ i, 0 ≤ J.dB i * J.dA i :=
    fun i => mul_nonneg (hdB_nn i) (hdA_nn i)
  have h_LHS : liebThirringLHSMatrix A B q
      = U.val * Matrix.diagonal (fun i => (((J.dB i * J.dA i) ^ q : ℝ) : ℂ)) * star U.val := by
    unfold liebThirringLHSMatrix
    rw [h_sandwich, h_diag_sandwich]
    -- sandwich = U · diag(dB·dA) · U*, conjugate the diagonal which is PSD.
    have hdiag_psd : (Matrix.diagonal (fun i => ((J.dB i * J.dA i : ℝ) : ℂ))).PosSemidef := by
      apply Matrix.posSemidef_diagonal_iff.mpr
      intro i; exact_mod_cast h_sand_diag_nn i
    rw [rpow_unitary_conj U _ hdiag_psd q,
        rpow_diagonal_ofReal (fun i => J.dB i * J.dA i) h_sand_diag_nn q]
  -- RHS matrix = B^{q/2} · A^q · B^{q/2} = U · diag(dB^{q/2} · dA^q · dB^{q/2}) · U*.
  have hAq : CFC.rpow A q
      = U.val * Matrix.diagonal (fun i => ((J.dA i ^ q : ℝ) : ℂ)) * star U.val := by
    conv_lhs => rw [← hA_eq]
    rw [rpow_unitary_conj U DA hDA_psd q, hDA,
        rpow_diagonal_ofReal J.dA hdA_nn q]
  have hBq2 : CFC.rpow B (q / 2)
      = U.val * Matrix.diagonal (fun i => ((J.dB i ^ (q / 2) : ℝ) : ℂ)) * star U.val := by
    conv_lhs => rw [← hB_eq]
    rw [rpow_unitary_conj U DB hDB_psd (q / 2), hDB,
        rpow_diagonal_ofReal J.dB hdB_nn (q / 2)]
  set PA : Matrix (Fin n) (Fin n) ℂ :=
    Matrix.diagonal (fun i => ((J.dA i ^ q : ℝ) : ℂ)) with hPA
  set PB : Matrix (Fin n) (Fin n) ℂ :=
    Matrix.diagonal (fun i => ((J.dB i ^ (q / 2) : ℝ) : ℂ)) with hPB
  have h_RHS : liebThirringRHSMatrix A B q
      = U.val * (PB * PA * PB) * star U.val := by
    unfold liebThirringRHSMatrix
    rw [hBq2, hAq]
    calc
      U.val * PB * star U.val * (U.val * PA * star U.val) * (U.val * PB * star U.val)
          = U.val * PB * (star U.val * U.val) * PA * (star U.val * U.val) * PB
              * star U.val := by
            simp only [Matrix.mul_assoc]
      _ = U.val * (PB * PA * PB) * star U.val := by
            rw [hUstarU]; simp only [Matrix.mul_one, Matrix.mul_assoc]
  -- PB · PA · PB = diag(dB^{q/2} · dA^q · dB^{q/2}).
  have h_diag_RHS : PB * PA * PB
      = Matrix.diagonal
          (fun i => (((J.dB i) ^ (q/2) * (J.dA i) ^ q * (J.dB i) ^ (q/2) : ℝ) : ℂ)) := by
    rw [hPB, hPA, Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
    refine congrArg _ ?_
    funext i
    push_cast
    ring
  -- Compare diagonals via the scalar identity.
  rw [h_LHS, h_RHS, h_diag_RHS]
  refine congrArg (fun M => U.val * M * star U.val) ?_
  refine congrArg _ ?_
  funext i
  have hid := comm_eigenvalue_identity (J.dA i) (J.dB i) (hdA_nn i) (hdB_nn i) q hq
  rw [hid]

/-- **Commuting Lieb–Thirring (trace equality).**

    For commuting PSD `A, B` and `q ≥ 0`,
    `liebThirringLHS A B q = liebThirringRHS A B q`. -/
theorem liebThirring_commuting_eq
    (A B : Matrix (Fin n) (Fin n) ℂ) (q : ℝ) (hq : 0 ≤ q)
    (hA : A.PosSemidef) (hB : B.PosSemidef) (hComm : Commute A B) :
    liebThirringLHS A B q = liebThirringRHS A B q := by
  unfold liebThirringLHS liebThirringRHS
  rw [liebThirring_commuting_eq_matrix A B q hq hA hB hComm]

end Commuting

/-! ## 4. Named gates and the master reduction. -/

/-- **Named gate**: the Lieb–Thirring *equality* in the commuting,
    PSD case. -/
def LiebThirring_Commuting_Target : Prop :=
  ∀ {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℂ) (q : ℝ),
    0 ≤ q → A.PosSemidef → B.PosSemidef → Commute A B →
      liebThirringLHS A B q = liebThirringRHS A B q

/-- **Unconditional discharge of the commuting gate.** -/
theorem liebThirring_commuting_target_holds :
    LiebThirring_Commuting_Target := by
  intro n A B q hq hA hB hComm
  exact liebThirring_commuting_eq A B q hq hA hB hComm

/-- **Named target**: the general `q ≥ 1` Lieb–Thirring inequality,

      `Re Tr((√B A √B)^q) ≤ Re Tr(B^{q/2} A^q B^{q/2})`,

    for PSD `A, B`.  This is the deep direction (Lieb–Thirring 1976;
    Araki 1990).  Stated as a named obligation. -/
def LiebThirring_Target : Prop :=
  ∀ {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℂ) (q : ℝ),
    1 ≤ q → A.PosSemidef → B.PosSemidef →
      (liebThirringLHS A B q).re ≤ (liebThirringRHS A B q).re

/-- **Named target**: the reverse Lieb–Thirring inequality for
    `0 < q ≤ 1`,

      `Re Tr(B^{q/2} A^q B^{q/2}) ≤ Re Tr((√B A √B)^q)`,

    for PSD `A, B`.  Named obligation. -/
def LiebThirring_Reverse_Target : Prop :=
  ∀ {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℂ) (q : ℝ),
    0 < q → q ≤ 1 → A.PosSemidef → B.PosSemidef →
      (liebThirringRHS A B q).re ≤ (liebThirringLHS A B q).re

/-- **The residual non-commuting subgate** for the forward `q ≥ 1`
    inequality.  This is where the genuine analytic content of
    Lieb–Thirring lives. -/
def LiebThirring_NonCommuting_Subgate : Prop :=
  ∀ {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℂ) (q : ℝ),
    1 ≤ q → A.PosSemidef → B.PosSemidef → ¬ Commute A B →
      (liebThirringLHS A B q).re ≤ (liebThirringRHS A B q).re

/-- **Master reduction.**

    The full forward `LiebThirring_Target` follows from the
    (unconditional) commuting equality combined with the named
    non-commuting subgate.  Concretely: on commuting pairs the two
    sides are *equal* (so the `≤` holds with equality, via
    `liebThirring_commuting_eq`); on non-commuting pairs the subgate
    supplies the inequality. -/
theorem lieb_thirring_master
    (h_sub : LiebThirring_NonCommuting_Subgate) :
    LiebThirring_Target := by
  intro n A B q hq hA hB
  by_cases hComm : Commute A B
  · -- Commuting case: equality, hence ≤.
    rw [liebThirring_commuting_eq A B q (le_trans zero_le_one hq) hA hB hComm]
  · exact h_sub A B q hq hA hB hComm

/-- **Master reduction (∧-form).** -/
theorem lieb_thirring_master_and
    (h : LiebThirring_Commuting_Target ∧ LiebThirring_NonCommuting_Subgate) :
    LiebThirring_Target :=
  lieb_thirring_master h.2

/-! ## 5. Honest scope summary.

    **UNCONDITIONAL (this file)**:

      * `liebThirring_q_one` — `Tr(√B A √B) = Tr(A B)` for PSD `B`
        (trace cyclicity).  HEADLINE.
      * `liebThirring_q_one_le` / `liebThirring_q_one_ge` — degenerate
        inequalities at `q = 1`.
      * `liebThirring_q_one_def` — the `q = 1` LHS via the named
        definitions equals `Tr(A B)`.
      * `comm_eigenvalue_identity` — scalar `(ba)^q = b^{q/2} a^q b^{q/2}`.
      * `liebThirring_commuting_eq_matrix` — MATRIX equality of both
        sides for commuting PSD `A, B`, every `q ≥ 0`, via joint
        diagonalisation.
      * `liebThirring_commuting_eq` — the trace-level consequence.
      * `LiebThirring_Commuting_Target` /
        `liebThirring_commuting_target_holds` — commuting gate +
        discharge.
      * `lieb_thirring_master` — reduction of the full forward target
        to the non-commuting subgate.

    **NAMED OBLIGATIONS (this file)**:

      * `LiebThirring_Target` — general forward `q ≥ 1` inequality.
      * `LiebThirring_Reverse_Target` — reverse `0 < q ≤ 1` inequality.
      * `LiebThirring_NonCommuting_Subgate` — the residual
        non-commuting analytic content.

    **DISTANCE TO `LiebThirring_Target`**:

      One named obligation remains: `LiebThirring_NonCommuting_Subgate`.
      The `q = 1` case and the entire commuting case (all `q ≥ 0`,
      as a matrix equality) are unconditionally discharged here.
-/

/-! ## 6. Axiom audit (commented; uncomment locally). -/

-- #print axioms liebThirring_q_one
-- #print axioms liebThirring_commuting_eq_matrix
-- #print axioms liebThirring_commuting_eq
-- #print axioms liebThirring_commuting_target_holds
-- #print axioms lieb_thirring_master
-- VERIFIED 2026-06-02:
--   All five headline theorems depend ONLY on Lean's three standard
--   axioms [propext, Classical.choice, Quot.sound].
--   Zero `sorry`, zero custom `axiom`.

end UnifiedTheory.LayerB.LiebThirring
