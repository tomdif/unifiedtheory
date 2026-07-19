/-
  LayerB/GoldenThompsonInequality.lean
  ─────────────────────────────────────

  **Partial discharge of `GoldenThompson_Target`** (defined in
  `LayerB.LiebGoldenThompson`).

  `GoldenThompson_Target` reads: for every dimension `n` and every
  pair of Hermitian matrices `A, B : Matrix (Fin n) (Fin n) ℂ`,

      `Re Tr(cfc Real.exp (A + B))
          ≤ Re Tr(cfc Real.exp A * cfc Real.exp B)`.

  Classical proofs of Golden–Thompson (Golden 1965, Thompson 1965,
  Symanzik 1965, Lieb 1973, Araki 1990, …) typically use one of
  four routes:

    1. **Lie–Trotter product formula** + logarithmic-norm
       estimates;
    2. **Bernstein's trick** — log-convexity of
       `f(t) := Tr(e^{tA} · e^{(1-t)B})` on `[0, 1]`;
    3. **Schwartz integral representation** of fractional powers
       (Carlen–Lieb 2008);
    4. **Trivial COMMUTING case** — when `Commute A B`, equality
       holds because `e^{A+B} = e^A · e^B`.

  This file ships:

    *   `golden_thompson_commuting`            — equality form for
                                                 commuting Hermitian
                                                 `A, B`.
    *   `golden_thompson_commuting_le`         — inequality form
                                                 (immediate from the
                                                 equality).
    *   `GoldenThompson_Commuting_Target`      — the commuting case
                                                 as a named gate.
    *   `goldenThompson_commuting_target_holds`
                                               — unconditional
                                                 discharge of the
                                                 commuting gate.
    *   `GoldenThompson_NonCommuting_Subgate`  — the residual
                                                 non-commuting
                                                 obligation as a
                                                 named subgate.
    *   `goldenThompson_target_from_subgate`   — composite reduction
                                                 (commuting case +
                                                 non-commuting
                                                 subgate ⇒ full
                                                 target).

  The proof of the commuting case is via **simultaneous
  diagonalisation**: commuting Hermitian matrices share a real
  spectral resolution `A = U · diagonal(dA) · U*`,
  `B = U · diagonal(dB) · U*`.  Then

      `cfc Real.exp (A + B)
        = U · diagonal(Real.exp ∘ (dA + dB)) · U*
        = U · diagonal((Real.exp ∘ dA) * (Real.exp ∘ dB)) · U*
        = cfc Real.exp A * cfc Real.exp B`,

  and traces of equal matrices are equal.

  We reuse the project's existing 4-matrix joint-diagonalisation
  infrastructure (`JointDiagonalisationCommuting`) by feeding it
  `(A, B, 0, 0)`, which all trivially commute pairwise as soon as
  `Commute A B` holds.

  ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
  STANDING CONSTRAINT: zero `sorry`, zero custom axioms.
  ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

  Authored 2026-06-02.
-/

import UnifiedTheory.LayerB.LiebGoldenThompson
import UnifiedTheory.LayerB.AndoInterpolation
import UnifiedTheory.LayerB.JointDiagonalisationCommuting
import UnifiedTheory.LayerB.LiebCorrectedCommutingFull
import UnifiedTheory.LayerB.UnitaryInvariance
import UnifiedTheory.LayerB.CFCDiagonalDischarge
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.ExpLog.Basic

set_option relaxedAutoImplicit false

namespace UnifiedTheory.LayerB.GoldenThompsonInequality

open Matrix Complex
open scoped MatrixOrder ComplexOrder
open UnifiedTheory.LayerB.LiebGoldenThompson
open UnifiedTheory.LayerB.AndoInterpolation
open UnifiedTheory.LayerB.JointDiagonalisationCommuting
open UnifiedTheory.LayerB.LiebCorrectedCommutingFull
open UnifiedTheory.LayerB.UnitaryInvariance
open UnifiedTheory.LayerB.CFCDiagonalDischarge

/-! ## 1. Helpers: unitary trace cycling and diagonal CFC. -/

section Helpers

variable {n : ℕ}

/-- `Tr(U · X · star U) = Tr(X)`. -/
private lemma trace_unitary_conj
    (U : Matrix.unitaryGroup (Fin n) ℂ)
    (X : Matrix (Fin n) (Fin n) ℂ) :
    Matrix.trace (U.val * X * (star U.val)) = Matrix.trace X := by
  rw [Matrix.trace_mul_cycle]
  rw [Matrix.mem_unitaryGroup_iff'.mp U.property, Matrix.one_mul]

/-- `cfc Real.exp` of a real-diagonal complex matrix is the
    entrywise exponential. -/
private lemma cfc_exp_diagonal_ofReal (d : Fin n → ℝ) :
    cfc Real.exp (Matrix.diagonal (fun i => ((d i : ℝ) : ℂ)))
      = Matrix.diagonal (fun i => ((Real.exp (d i) : ℝ) : ℂ)) :=
  cfcOnDiagonalIsEntrywise_real n Real.exp d

/-- `cfc Real.exp` of a unitary conjugate of a Hermitian matrix is
    the unitary conjugate of the CFC. -/
private lemma cfc_exp_unitary_conj
    (U : Matrix.unitaryGroup (Fin n) ℂ)
    (M : Matrix (Fin n) (Fin n) ℂ) (hM : IsSelfAdjoint M) :
    cfc Real.exp (U.val * M * star U.val)
      = U.val * (cfc Real.exp M) * star U.val :=
  cfc_unitary_conj U M Real.exp hM
    (Real.continuous_exp.continuousOn)

end Helpers

/-! ## 2. Auxiliary: `(A, B, 0, 0)` satisfy `AllCommute`. -/

section TwoToFour

variable {n : ℕ}

/-- `(A, B, 0, 0)` pairwise commute whenever `Commute A B`. -/
private lemma allCommute_pair_zero_zero
    (A B : Matrix (Fin n) (Fin n) ℂ) (h : Commute A B) :
    AllCommute A B (0 : Matrix (Fin n) (Fin n) ℂ)
      (0 : Matrix (Fin n) (Fin n) ℂ) := by
  refine ⟨h, ?_, ?_, ?_, ?_, ?_⟩
  · exact Commute.zero_right A
  · exact Commute.zero_right A
  · exact Commute.zero_right B
  · exact Commute.zero_right B
  · exact Commute.zero_right 0

end TwoToFour

/-! ## 3. The commuting case (equality form). -/

section Commuting

variable {n : ℕ}

/-- **Golden–Thompson for commuting Hermitians (equality).**

    For Hermitian `A, B` with `Commute A B`,
    `cfc Real.exp (A + B) = cfc Real.exp A * cfc Real.exp B`. -/
theorem cfc_exp_add_eq_mul_of_commute
    (A B : Matrix (Fin n) (Fin n) ℂ)
    (hA : A.IsHermitian) (hB : B.IsHermitian)
    (hComm : Commute A B) :
    cfc Real.exp (A + B) = cfc Real.exp A * cfc Real.exp B := by
  -- Obtain a joint diagonalisation of (A, B, 0, 0).
  have h_comm4 :
      AllCommute A B (0 : Matrix (Fin n) (Fin n) ℂ)
        (0 : Matrix (Fin n) (Fin n) ℂ) :=
    allCommute_pair_zero_zero A B hComm
  have hExists := jointDiagonalisation_exists_of_allCommute
    A B (0 : Matrix (Fin n) (Fin n) ℂ) (0 : Matrix (Fin n) (Fin n) ℂ)
    hA hB Matrix.isHermitian_zero Matrix.isHermitian_zero h_comm4
  obtain ⟨J⟩ := hExists
  -- Notation for the diagonal blocks.
  set U : Matrix.unitaryGroup (Fin n) ℂ := J.U with hU_def
  set DA : Matrix (Fin n) (Fin n) ℂ :=
    Matrix.diagonal (fun i => ((J.dA i : ℝ) : ℂ)) with hDA_def
  set DB : Matrix (Fin n) (Fin n) ℂ :=
    Matrix.diagonal (fun i => ((J.dB i : ℝ) : ℂ)) with hDB_def
  -- Self-adjointness of DA, DB.
  have hDA_sa : IsSelfAdjoint DA :=
    isSelfAdjoint_diagonal_ofReal J.dA
  have hDB_sa : IsSelfAdjoint DB :=
    isSelfAdjoint_diagonal_ofReal J.dB
  -- Conjugation identities.
  have hA_eq : U.val * DA * star U.val = A := J.hA
  have hB_eq : U.val * DB * star U.val = B := J.hB
  -- The sum equals the unitary conjugate of (DA + DB).
  have hAplusB : A + B = U.val * (DA + DB) * star U.val := by
    rw [← hA_eq, ← hB_eq]
    rw [Matrix.mul_add, Matrix.add_mul]
  -- DA + DB is also diagonal: diagonal of (dA + dB).
  have hDAB_diag : DA + DB =
      Matrix.diagonal (fun i => (((J.dA i + J.dB i : ℝ)) : ℂ)) := by
    rw [hDA_def, hDB_def, Matrix.diagonal_add]
    refine congrArg _ ?_
    funext i
    push_cast
    ring
  -- Self-adjointness of DA + DB.
  have hDAB_sa : IsSelfAdjoint (DA + DB) := hDA_sa.add hDB_sa
  -- cfc exp on A + B.
  have h_lhs : cfc Real.exp (A + B)
      = U.val * cfc Real.exp (DA + DB) * star U.val := by
    rw [hAplusB]
    exact cfc_exp_unitary_conj U (DA + DB) hDAB_sa
  -- cfc exp on A.
  have h_cfcA : cfc Real.exp A = U.val * cfc Real.exp DA * star U.val := by
    rw [← hA_eq]
    exact cfc_exp_unitary_conj U DA hDA_sa
  -- cfc exp on B.
  have h_cfcB : cfc Real.exp B = U.val * cfc Real.exp DB * star U.val := by
    rw [← hB_eq]
    exact cfc_exp_unitary_conj U DB hDB_sa
  -- Diagonal exponentials.
  have h_expDA :
      cfc Real.exp DA
        = Matrix.diagonal (fun i => ((Real.exp (J.dA i) : ℝ) : ℂ)) := by
    rw [hDA_def]
    exact cfc_exp_diagonal_ofReal J.dA
  have h_expDB :
      cfc Real.exp DB
        = Matrix.diagonal (fun i => ((Real.exp (J.dB i) : ℝ) : ℂ)) := by
    rw [hDB_def]
    exact cfc_exp_diagonal_ofReal J.dB
  have h_expDAB :
      cfc Real.exp (DA + DB)
        = Matrix.diagonal
            (fun i => ((Real.exp (J.dA i + J.dB i) : ℝ) : ℂ)) := by
    rw [hDAB_diag]
    exact cfcOnDiagonalIsEntrywise_real n Real.exp
      (fun i => J.dA i + J.dB i)
  -- LHS = U · diag(exp(dA+dB)) · star U.
  rw [h_lhs, h_expDAB]
  -- RHS step 1: rewrite each cfc exp factor.
  rw [h_cfcA, h_cfcB, h_expDA, h_expDB]
  -- Goal:
  --   U · diag(exp(dA+dB)) · star U
  --     = (U · diag(exp dA) · star U) * (U · diag(exp dB) · star U)
  -- Use unitary identities.
  have hUstarU : star U.val * U.val = 1 :=
    Matrix.mem_unitaryGroup_iff'.mp U.property
  -- First, collapse the RHS product to U · (diag exp dA · diag exp dB) · star U.
  have h_collapse :
      (U.val * Matrix.diagonal (fun i => ((Real.exp (J.dA i) : ℝ) : ℂ))
            * star U.val)
        * (U.val * Matrix.diagonal (fun i => ((Real.exp (J.dB i) : ℝ) : ℂ))
            * star U.val)
        = U.val * (Matrix.diagonal (fun i => ((Real.exp (J.dA i) : ℝ) : ℂ))
                     * Matrix.diagonal
                         (fun i => ((Real.exp (J.dB i) : ℝ) : ℂ)))
              * star U.val := by
    calc (U.val * Matrix.diagonal (fun i => ((Real.exp (J.dA i) : ℝ) : ℂ))
              * star U.val)
            * (U.val * Matrix.diagonal (fun i => ((Real.exp (J.dB i) : ℝ) : ℂ))
              * star U.val)
        = U.val * Matrix.diagonal (fun i => ((Real.exp (J.dA i) : ℝ) : ℂ))
            * (star U.val * U.val)
            * Matrix.diagonal (fun i => ((Real.exp (J.dB i) : ℝ) : ℂ))
              * star U.val := by
              simp only [Matrix.mul_assoc]
      _ = U.val * Matrix.diagonal (fun i => ((Real.exp (J.dA i) : ℝ) : ℂ))
            * 1
            * Matrix.diagonal (fun i => ((Real.exp (J.dB i) : ℝ) : ℂ))
              * star U.val := by rw [hUstarU]
      _ = U.val * (Matrix.diagonal (fun i => ((Real.exp (J.dA i) : ℝ) : ℂ))
                     * Matrix.diagonal
                         (fun i => ((Real.exp (J.dB i) : ℝ) : ℂ)))
              * star U.val := by
              rw [Matrix.mul_one]; simp only [Matrix.mul_assoc]
  rw [h_collapse]
  -- Reduce the diagonal product.
  have h_diag_prod :
      Matrix.diagonal (fun i => ((Real.exp (J.dA i) : ℝ) : ℂ))
        * Matrix.diagonal (fun i => ((Real.exp (J.dB i) : ℝ) : ℂ))
        = Matrix.diagonal
            (fun i => ((Real.exp (J.dA i + J.dB i) : ℝ) : ℂ)) := by
    rw [Matrix.diagonal_mul_diagonal]
    refine congrArg _ ?_
    funext i
    have : Real.exp (J.dA i + J.dB i) = Real.exp (J.dA i) * Real.exp (J.dB i) :=
      Real.exp_add _ _
    rw [this]
    push_cast
    ring
  rw [h_diag_prod]

/-- **Golden–Thompson for commuting Hermitians (inequality).**

    Immediate corollary of `cfc_exp_add_eq_mul_of_commute`: the
    Re-trace inequality becomes an equality, hence holds. -/
theorem golden_thompson_commuting_le
    (A B : Matrix (Fin n) (Fin n) ℂ)
    (hA : A.IsHermitian) (hB : B.IsHermitian)
    (hComm : Commute A B) :
    (Matrix.trace (cfc Real.exp (A + B))).re
      ≤ (Matrix.trace (cfc Real.exp A * cfc Real.exp B)).re := by
  have h_eq := cfc_exp_add_eq_mul_of_commute A B hA hB hComm
  rw [h_eq]

/-- **Golden–Thompson for commuting Hermitians (equality form on
    `Re Tr`).** -/
theorem golden_thompson_commuting_eq
    (A B : Matrix (Fin n) (Fin n) ℂ)
    (hA : A.IsHermitian) (hB : B.IsHermitian)
    (hComm : Commute A B) :
    (Matrix.trace (cfc Real.exp (A + B))).re
      = (Matrix.trace (cfc Real.exp A * cfc Real.exp B)).re := by
  rw [cfc_exp_add_eq_mul_of_commute A B hA hB hComm]

end Commuting

/-! ## 4. The commuting case as a named gate. -/

/-- **Named gate**: Golden–Thompson restricted to commuting pairs. -/
def GoldenThompson_Commuting_Target : Prop :=
  ∀ {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℂ),
    A.IsHermitian → B.IsHermitian → Commute A B →
      (Matrix.trace (cfc Real.exp (A + B))).re
        ≤ (Matrix.trace (cfc Real.exp A * cfc Real.exp B)).re

/-- **Unconditional discharge of the commuting gate.**

    The commuting case is trivial: `e^{A+B} = e^A · e^B` whenever
    `A, B` commute, so the inequality becomes an equality. -/
theorem goldenThompson_commuting_target_holds :
    GoldenThompson_Commuting_Target := by
  intro n A B hA hB hComm
  exact golden_thompson_commuting_le A B hA hB hComm

/-! ## 5. The non-commuting residual subgate. -/

/-- **The residual non-commuting subgate.**

    Golden–Thompson for non-commuting Hermitian pairs.  This is
    where the deep analytic content lives (Bernstein log-convexity,
    Lie–Trotter, Carlen–Lieb integral representation, etc.).  We
    package it as a named obligation. -/
def GoldenThompson_NonCommuting_Subgate : Prop :=
  ∀ {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℂ),
    A.IsHermitian → B.IsHermitian → ¬ Commute A B →
      (Matrix.trace (cfc Real.exp (A + B))).re
        ≤ (Matrix.trace (cfc Real.exp A * cfc Real.exp B)).re

/-- Canonical interface for `GoldenThompson_NonCommuting_Subgate`. -/
theorem goldenThompson_nonCommuting_subgate_holds
    (h : GoldenThompson_NonCommuting_Subgate) :
    GoldenThompson_NonCommuting_Subgate := h

/-! ## 6. Composite reduction: commuting case + non-commuting
       subgate ⇒ full `GoldenThompson_Target`. -/

/-- **Composite reduction.**

    The full `GoldenThompson_Target` from `LiebGoldenThompson`
    follows from the (unconditional) commuting case combined with
    the named non-commuting subgate. -/
theorem goldenThompson_target_from_subgate
    (h_sub : GoldenThompson_NonCommuting_Subgate) :
    GoldenThompson_Target := by
  intro n A B hA hB
  by_cases hComm : Commute A B
  · exact golden_thompson_commuting_le A B hA hB hComm
  · exact h_sub A B hA hB hComm

/-- **Composite reduction (∧-form).** -/
theorem goldenThompson_target_from_commuting_and_subgate
    (h : GoldenThompson_Commuting_Target
          ∧ GoldenThompson_NonCommuting_Subgate) :
    GoldenThompson_Target :=
  goldenThompson_target_from_subgate h.2

/-! ## 7. Downstream: GT-route closure conditional on the
       non-commuting subgate. -/

/-- **Lieb 1973 tracial sub-gate from the GT non-commuting subgate
    plus the Carlen–Lieb integral reduction target.**

    Combines `goldenThompson_target_from_subgate` with
    `lieb_tracial_subgate_from_GT_route` from `LiebGoldenThompson`. -/
theorem lieb_tracial_subgate_from_GT_nonCommuting_subgate
    (h_sub : GoldenThompson_NonCommuting_Subgate)
    (h_red : CarlenLieb_Integral_Reduction_Target) :
    Lieb1973_Tracial_NonCommuting_Subgate :=
  lieb_tracial_subgate_from_GT_route
    (goldenThompson_target_from_subgate h_sub) h_red

/-! ## 8. Honest scope summary.

    **UNCONDITIONAL (this file)**:

      * `cfc_exp_add_eq_mul_of_commute` — `cfc exp (A+B)
        = cfc exp A · cfc exp B` for commuting Hermitian `A, B`.
      * `golden_thompson_commuting_eq` — equality of `Re Tr` in the
        commuting case.
      * `golden_thompson_commuting_le` — inequality form
        (immediate from equality).
      * `GoldenThompson_Commuting_Target` /
        `goldenThompson_commuting_target_holds` — named gate +
        unconditional discharge for the commuting case.
      * `goldenThompson_target_from_subgate` — composite reduction.
      * `lieb_tracial_subgate_from_GT_nonCommuting_subgate` —
        downstream link to the Lieb 1973 chain.

    **NAMED SUBGATE (this file)**:

      * `GoldenThompson_NonCommuting_Subgate` — Golden–Thompson for
        non-commuting Hermitian pairs.  Classical content (Lieb 1973
        Theorem 7, multiple known proofs).

    **DISTANCE TO `GoldenThompson_Target`**:

      One named obligation remains:
      `GoldenThompson_NonCommuting_Subgate`.  The commuting case is
      unconditionally discharged in this file.
-/

/-! ## 9. Axiom audit (commented).

    Uncomment locally to confirm that the schematic composites and
    the commuting discharge depend only on Lean's three standard
    axioms `[propext, Classical.choice, Quot.sound]`.  Zero `sorry`,
    zero custom `axiom`. -/

-- #print axioms cfc_exp_add_eq_mul_of_commute
-- #print axioms golden_thompson_commuting_eq
-- #print axioms golden_thompson_commuting_le
-- #print axioms goldenThompson_commuting_target_holds
-- #print axioms goldenThompson_target_from_subgate
-- #print axioms goldenThompson_target_from_commuting_and_subgate
-- #print axioms lieb_tracial_subgate_from_GT_nonCommuting_subgate

-- VERIFIED 2026-06-02:
--   All seven headline theorems above depend only on Lean's three
--   standard axioms `[propext, Classical.choice, Quot.sound]`.
--   Zero `sorry`, zero custom `axiom`.

end UnifiedTheory.LayerB.GoldenThompsonInequality
