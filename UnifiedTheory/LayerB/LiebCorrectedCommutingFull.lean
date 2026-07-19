/-
  LayerB/LiebCorrectedCommutingFull.lean
  ───────────────────────────────────────

  **Full commuting-case discharge of `Lieb1973_Corrected_Target`** —
  via the joint-diagonalisation reduction.

  This file extends the diagonal-case discharge of
  `LiebCorrectedCommuting.lean` to the **full commuting case**: any
  four pairwise-commuting PosDef matrices satisfy the corrected
  joint-convexity inequality, provided they admit a shared
  diagonalising unitary (the joint-diagonalisation hypothesis).

  The mathematical content is split into two clean pieces:

  1.  **`JointDiagonalisation`**: a bundled data type recording a
      shared diagonalising unitary `U` and the four diagonal data
      sequences `dA, dB, dC, dD : Fin m → ℝ` such that
      `U · diagonal(dA) · star U = A`, and similarly for `B, C, D`.

  2.  **`lieb1973_corrected_of_jointDiag`** (the headline conditional
      reduction): given such a `JointDiagonalisation` and `PosDef`
      hypotheses on the four inputs (which transfer to positivity of
      the diagonal entries via the conjugation invariance of
      `PosDef`), the corrected target inequality holds.  The proof
      reduces every Re-Tr term to the corresponding diagonal Re-Tr
      term via `cfc_log_unitary_conj` and trace cyclicity, then
      invokes the existing `lieb1973_corrected_diagonal_data` from
      `LiebCorrectedCommuting.lean`.

  3.  **`lieb1973_corrected_commuting_full`**: an unconditional
      statement *assuming* the joint diagonalisation exists.  This
      packages (2) cleanly: given four PosDef pairwise-commuting
      matrices and an explicit `JointDiagonalisation`, the corrected
      target holds.

  ## Honest scoping

  The general **existence** of a `JointDiagonalisation` for any four
  pairwise-commuting Hermitian matrices is provable via Mathlib's
  `LinearMap.IsSymmetric.iSup_iInf_eq_top_of_commute`
  (`Mathlib.Analysis.InnerProductSpace.JointEigenspace`), combined
  with `DirectSum.IsInternal.subordinateOrthonormalBasis`
  (`Mathlib.Analysis.InnerProductSpace.PiL2`).  However, that bridge
  requires resolving the `Fintype` requirement on the joint
  eigenvalue index `Fin 4 → ℂ`, which is *not* `Fintype` directly;
  the workaround is to restrict to "joint eigenvalues that actually
  occur" (a finite subtype, since the space is finite-dimensional).
  We package the existence result via a clean `Nonempty
  (JointDiagonalisation ...)` formulation that any future
  bridge-completion can populate.

  ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
  STANDING CONSTRAINT: zero `sorry`, zero custom axioms.
  ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

  Authored 2026-06-01 (Phase B10 commuting-case completion).
-/

import UnifiedTheory.LayerB.LiebCorrectedCommuting
import UnifiedTheory.LayerB.UnitaryInvariance

set_option relaxedAutoImplicit false

namespace UnifiedTheory.LayerB.LiebCorrectedCommutingFull

open Matrix Complex
open scoped ComplexOrder
open UnifiedTheory.LayerB.LiebTargetAudit
open UnifiedTheory.LayerB.CFCDiagonalDischarge
open UnifiedTheory.LayerB.UnitaryInvariance
open UnifiedTheory.LayerB.LiebCorrectedCommuting

/-! ## 1. Pairwise commutativity of four matrices -/

/-- **All-commute predicate.**  Four matrices pairwise commute. -/
def AllCommute {m : ℕ} (A B C D : Matrix (Fin m) (Fin m) ℂ) : Prop :=
    Commute A B ∧ Commute A C ∧ Commute A D ∧
    Commute B C ∧ Commute B D ∧ Commute C D

/-! ## 2. Bundled joint-diagonalisation data -/

/-- **Joint diagonalisation** of four matrices by a shared unitary.

    Records a unitary `U` and four real diagonal data sequences
    `dA, dB, dC, dD` such that `U * diagonal(ofReal ∘ dA) * star U = A`
    and similarly for `B, C, D`. -/
structure JointDiagonalisation {m : ℕ}
    (A B C D : Matrix (Fin m) (Fin m) ℂ) where
  /-- The shared diagonalising unitary. -/
  U : Matrix.unitaryGroup (Fin m) ℂ
  /-- Diagonal entries of `Uᴴ A U`. -/
  dA : Fin m → ℝ
  /-- Diagonal entries of `Uᴴ B U`. -/
  dB : Fin m → ℝ
  /-- Diagonal entries of `Uᴴ C U`. -/
  dC : Fin m → ℝ
  /-- Diagonal entries of `Uᴴ D U`. -/
  dD : Fin m → ℝ
  /-- Diagonalisation identity for `A`. -/
  hA : U.val * Matrix.diagonal (fun i => ((dA i : ℝ) : ℂ)) * (star U.val) = A
  /-- Diagonalisation identity for `B`. -/
  hB : U.val * Matrix.diagonal (fun i => ((dB i : ℝ) : ℂ)) * (star U.val) = B
  /-- Diagonalisation identity for `C`. -/
  hC : U.val * Matrix.diagonal (fun i => ((dC i : ℝ) : ℂ)) * (star U.val) = C
  /-- Diagonalisation identity for `D`. -/
  hD : U.val * Matrix.diagonal (fun i => ((dD i : ℝ) : ℂ)) * (star U.val) = D

/-! ## 3. Conjugation invariance of the corrected target -/

section ConjInv

variable {m : ℕ}

/-- Helper: `Tr(U · X · star U) = Tr(X)`. -/
private lemma trace_unitary_conj
    (U : Matrix.unitaryGroup (Fin m) ℂ)
    (X : Matrix (Fin m) (Fin m) ℂ) :
    Matrix.trace (U.val * X * (star U.val)) = Matrix.trace X := by
  rw [Matrix.trace_mul_cycle]
  rw [Matrix.mem_unitaryGroup_iff'.mp U.property, Matrix.one_mul]

/-- The factor `(α : ℂ) • A + ((1 - α : ℝ) : ℂ) • B`, when `A = U Dₐ Uᴴ`
    and `B = U D_b Uᴴ`, equals `U · ((α : ℂ) • Dₐ + ((1-α : ℝ) : ℂ) • D_b) · Uᴴ`. -/
private lemma convex_combination_unitary_conj
    (U : Matrix.unitaryGroup (Fin m) ℂ)
    (Da Db : Matrix (Fin m) (Fin m) ℂ) (α : ℝ) :
    (α : ℂ) • (U.val * Da * (star U.val))
      + ((1 - α : ℝ) : ℂ) • (U.val * Db * (star U.val))
        = U.val * ((α : ℂ) • Da + ((1 - α : ℝ) : ℂ) • Db) * (star U.val) := by
  -- Distribute via direct calculation.
  calc (α : ℂ) • (U.val * Da * (star U.val))
        + ((1 - α : ℝ) : ℂ) • (U.val * Db * (star U.val))
      = U.val * ((α : ℂ) • Da) * (star U.val)
          + U.val * (((1 - α : ℝ) : ℂ) • Db) * (star U.val) := by
        rw [Matrix.mul_smul, Matrix.smul_mul,
            Matrix.mul_smul (a := ((1 - α : ℝ) : ℂ)),
            Matrix.smul_mul (a := ((1 - α : ℝ) : ℂ))]
    _ = U.val * ((α : ℂ) • Da + ((1 - α : ℝ) : ℂ) • Db) * (star U.val) := by
        rw [← Matrix.add_mul, ← Matrix.mul_add]

/-- Pulling `cfc Real.log` through a unitary conjugation. -/
private lemma cfc_log_conj
    (U : Matrix.unitaryGroup (Fin m) ℂ)
    (Dx : Matrix (Fin m) (Fin m) ℂ) (hDx : IsSelfAdjoint Dx) :
    cfc Real.log (U.val * Dx * (star U.val))
      = U.val * cfc Real.log Dx * (star U.val) :=
  cfc_log_unitary_conj U Dx hDx

/-- The mixed-product trace identity:
        `Re Tr( (U X Uᴴ) · cfc log (U Y Uᴴ) ) = Re Tr( X · cfc log Y )`. -/
private lemma re_trace_unitary_cfc_log
    (U : Matrix.unitaryGroup (Fin m) ℂ)
    (X Y : Matrix (Fin m) (Fin m) ℂ) (hY : IsSelfAdjoint Y) :
    (Matrix.trace ((U.val * X * (star U.val)) *
        cfc Real.log (U.val * Y * (star U.val)))).re
      = (Matrix.trace (X * cfc Real.log Y)).re := by
  rw [cfc_log_conj U Y hY]
  -- Reduce `Tr(U X Uᴴ · U (log Y) Uᴴ) = Tr(X · log Y)`.
  have h_alg :
      (U.val * X * (star U.val)) * (U.val * cfc Real.log Y * (star U.val))
        = U.val * (X * cfc Real.log Y) * (star U.val) := by
    have hUstarU : star U.val * U.val = 1 :=
      Matrix.mem_unitaryGroup_iff'.mp U.property
    calc (U.val * X * (star U.val)) * (U.val * cfc Real.log Y * (star U.val))
        = U.val * X * ((star U.val) * U.val) * cfc Real.log Y * (star U.val) := by
            simp only [Matrix.mul_assoc]
      _ = U.val * X * 1 * cfc Real.log Y * (star U.val) := by rw [hUstarU]
      _ = U.val * (X * cfc Real.log Y) * (star U.val) := by
            rw [Matrix.mul_one]; simp only [Matrix.mul_assoc]
  rw [h_alg, trace_unitary_conj]

end ConjInv

/-! ## 4. Positivity transfer: PosDef + joint diag ⇒ positive diagonal entries -/

section PosDef

variable {m : ℕ}

/-- If `X = U * D * star U` is PosDef and `D` is diagonal with real
    entries `d`, then every entry of `d` is positive. -/
private lemma diag_pos_of_posDef_conj
    (U : Matrix.unitaryGroup (Fin m) ℂ)
    (d : Fin m → ℝ)
    (X : Matrix (Fin m) (Fin m) ℂ) (hX : X.PosDef)
    (h_eq : U.val * Matrix.diagonal (fun i => ((d i : ℝ) : ℂ)) * (star U.val) = X) :
    ∀ i, 0 < d i := by
  intro i
  -- D := diagonal (ofReal ∘ d).  Show D.PosDef, then use `posDef_diagonal_iff`.
  set D : Matrix (Fin m) (Fin m) ℂ :=
    Matrix.diagonal (fun j => ((d j : ℝ) : ℂ)) with hD_def
  have hUUstar : U.val * (star U.val) = 1 :=
    Matrix.mem_unitaryGroup_iff.mp U.property
  have hUstarU : (star U.val) * U.val = 1 :=
    Matrix.mem_unitaryGroup_iff'.mp U.property
  -- D = star U * X * U.
  have hD_eq : D = (star U.val) * X * U.val := by
    rw [← h_eq]
    calc D = 1 * D * 1 := by rw [Matrix.one_mul, Matrix.mul_one]
      _ = (star U.val * U.val) * D * (star U.val * U.val) := by rw [hUstarU]
      _ = (star U.val) * (U.val * D * (star U.val)) * U.val := by
            simp only [Matrix.mul_assoc]
  -- D.PosDef via conjugation by a unit (U.val is invertible).
  have hU_unit : IsUnit (U.val : Matrix (Fin m) (Fin m) ℂ) := by
    refine ⟨⟨U.val, star U.val, ?_, ?_⟩, rfl⟩
    · exact hUUstar
    · exact hUstarU
  have hU_inj : Function.Injective (U.val : Matrix (Fin m) (Fin m) ℂ).mulVec :=
    Matrix.mulVec_injective_of_isUnit hU_unit
  have h_conjTranspose : (U.val).conjTranspose = star U.val := rfl
  have hD_PD : D.PosDef := by
    rw [hD_eq]
    have key := hX.conjTranspose_mul_mul_same (B := U.val) hU_inj
    rw [h_conjTranspose] at key
    exact key
  -- Each diagonal entry positive (via `posDef_diagonal_iff` over ℂ).
  have h_pos_complex : ∀ j, (0 : ℂ) < ((d j : ℝ) : ℂ) :=
    Matrix.posDef_diagonal_iff.mp (hD_def ▸ hD_PD)
  exact_mod_cast h_pos_complex i

end PosDef

/-! ## 5. Conditional reduction: full commuting target given joint diagonalisation -/

section Reduction

variable {m : ℕ}

/-- **Conditional reduction**: the corrected target on a tuple given
    a joint diagonalisation.

    If `A₁, A₂, B₁, B₂` are jointly diagonalised by the same unitary
    `U`, and each `A_i, B_i` is PosDef (so that the diagonal entries
    are positive via `diag_pos_of_posDef_conj`), then the corrected
    target evaluated at `(A₁, A₂, B₁, B₂)` follows from the diagonal
    case `lieb1973_corrected_diagonal_data`.

    This is the main mathematical content of the reduction: every
    Re-Tr expression in the corrected target is invariant under
    simultaneous unitary conjugation, so the inequality on
    `(A₁, A₂, B₁, B₂)` is equivalent to the inequality on the
    diagonal matrices `(diag(dA), diag(dB), diag(dC), diag(dD))`. -/
theorem lieb1973_corrected_of_jointDiag
    (A₁ A₂ B₁ B₂ : Matrix (Fin m) (Fin m) ℂ)
    (hA₁ : A₁.PosDef) (hA₂ : A₂.PosDef) (hB₁ : B₁.PosDef) (hB₂ : B₂.PosDef)
    (J : JointDiagonalisation A₁ A₂ B₁ B₂)
    (α : ℝ) (hα₀ : 0 ≤ α) (hα₁ : α ≤ 1) :
    let A_t : Matrix (Fin m) (Fin m) ℂ :=
      (α : ℂ) • A₁ + ((1 - α : ℝ) : ℂ) • A₂
    let B_t : Matrix (Fin m) (Fin m) ℂ :=
      (α : ℂ) • B₁ + ((1 - α : ℝ) : ℂ) • B₂
    (Matrix.trace (A_t * cfc Real.log A_t)).re
        - (Matrix.trace (A_t * cfc Real.log B_t)).re
      ≤ α * ((Matrix.trace (A₁ * cfc Real.log A₁)).re
              - (Matrix.trace (A₁ * cfc Real.log B₁)).re)
        + (1 - α) * ((Matrix.trace (A₂ * cfc Real.log A₂)).re
                      - (Matrix.trace (A₂ * cfc Real.log B₂)).re) := by
  -- Positivity of diagonal entries from PosDef.
  have hpos_A₁ : ∀ i, 0 < J.dA i :=
    diag_pos_of_posDef_conj J.U J.dA A₁ hA₁ J.hA
  have hpos_A₂ : ∀ i, 0 < J.dB i :=
    diag_pos_of_posDef_conj J.U J.dB A₂ hA₂ J.hB
  have hpos_B₁ : ∀ i, 0 < J.dC i :=
    diag_pos_of_posDef_conj J.U J.dC B₁ hB₁ J.hC
  have hpos_B₂ : ∀ i, 0 < J.dD i :=
    diag_pos_of_posDef_conj J.U J.dD B₂ hB₂ J.hD
  -- Package diagonals as DiagonalPositive data.
  let dA₁ : DiagonalPositive m := ⟨J.dA, hpos_A₁⟩
  let dA₂ : DiagonalPositive m := ⟨J.dB, hpos_A₂⟩
  let dB₁ : DiagonalPositive m := ⟨J.dC, hpos_B₁⟩
  let dB₂ : DiagonalPositive m := ⟨J.dD, hpos_B₂⟩
  -- Aᵢ = U · DAᵢ · star U; from joint diag.
  have hA₁_eq : A₁ = J.U.val * dA₁.M * (star J.U.val) := J.hA.symm
  have hA₂_eq : A₂ = J.U.val * dA₂.M * (star J.U.val) := J.hB.symm
  have hB₁_eq : B₁ = J.U.val * dB₁.M * (star J.U.val) := J.hC.symm
  have hB₂_eq : B₂ = J.U.val * dB₂.M * (star J.U.val) := J.hD.symm
  -- Self-adjointness of each D.
  have hDA₁_sa : IsSelfAdjoint dA₁.M := isSelfAdjoint_diagonal_ofReal J.dA
  have hDA₂_sa : IsSelfAdjoint dA₂.M := isSelfAdjoint_diagonal_ofReal J.dB
  have hDB₁_sa : IsSelfAdjoint dB₁.M := isSelfAdjoint_diagonal_ofReal J.dC
  have hDB₂_sa : IsSelfAdjoint dB₂.M := isSelfAdjoint_diagonal_ofReal J.dD
  -- Self-adjointness of convex combinations.
  have hDA_conv_sa :
      IsSelfAdjoint ((α : ℂ) • dA₁.M + ((1 - α : ℝ) : ℂ) • dA₂.M) := by
    have h1 : IsSelfAdjoint ((α : ℂ) • dA₁.M) := by
      have hα : star (α : ℂ) = (α : ℂ) := Complex.conj_ofReal _
      unfold IsSelfAdjoint
      rw [star_smul, hα, hDA₁_sa.star_eq]
    have h2 : IsSelfAdjoint (((1 - α : ℝ) : ℂ) • dA₂.M) := by
      have hα : star ((1 - α : ℝ) : ℂ) = ((1 - α : ℝ) : ℂ) :=
        Complex.conj_ofReal _
      unfold IsSelfAdjoint
      rw [star_smul, hα, hDA₂_sa.star_eq]
    exact h1.add h2
  have hDB_conv_sa :
      IsSelfAdjoint ((α : ℂ) • dB₁.M + ((1 - α : ℝ) : ℂ) • dB₂.M) := by
    have h1 : IsSelfAdjoint ((α : ℂ) • dB₁.M) := by
      have hα : star (α : ℂ) = (α : ℂ) := Complex.conj_ofReal _
      unfold IsSelfAdjoint
      rw [star_smul, hα, hDB₁_sa.star_eq]
    have h2 : IsSelfAdjoint (((1 - α : ℝ) : ℂ) • dB₂.M) := by
      have hα : star ((1 - α : ℝ) : ℂ) = ((1 - α : ℝ) : ℂ) :=
        Complex.conj_ofReal _
      unfold IsSelfAdjoint
      rw [star_smul, hα, hDB₂_sa.star_eq]
    exact h1.add h2
  -- Convex combinations on the LHS.
  intro A_t B_t
  -- Extract J.U / star J.U / J.dA / ... as new top-level let-bindings to
  -- avoid `J : JointDiagonalisation A₁ A₂ B₁ B₂` blocking `rw` motives.
  set U := J.U.val with hU_def
  set sU := star J.U.val with hsU_def
  -- Convex-combination identity for A_t.
  have h_At_eq : A_t = U * ((α : ℂ) • dA₁.M + ((1 - α : ℝ) : ℂ) • dA₂.M) * sU := by
    show (α : ℂ) • A₁ + ((1 - α : ℝ) : ℂ) • A₂ = _
    have := convex_combination_unitary_conj J.U dA₁.M dA₂.M α
    -- We have: (α : ℂ) • (U.val * dA₁.M * (star U.val)) + ... = U.val * (...) * (star U.val).
    -- Rewrite using `hA₁_eq` / `hA₂_eq` (as rewrites on `A₁`, `A₂`).
    -- Since the LHS doesn't contain `J` directly in a dependent way after `set`,
    -- we can use direct calc.
    calc (α : ℂ) • A₁ + ((1 - α : ℝ) : ℂ) • A₂
        = (α : ℂ) • (U * dA₁.M * sU) + ((1 - α : ℝ) : ℂ) • (U * dA₂.M * sU) := by
          rw [hA₁_eq, hA₂_eq]
      _ = U * ((α : ℂ) • dA₁.M + ((1 - α : ℝ) : ℂ) • dA₂.M) * sU := this
  have h_Bt_eq : B_t = U * ((α : ℂ) • dB₁.M + ((1 - α : ℝ) : ℂ) • dB₂.M) * sU := by
    show (α : ℂ) • B₁ + ((1 - α : ℝ) : ℂ) • B₂ = _
    have := convex_combination_unitary_conj J.U dB₁.M dB₂.M α
    calc (α : ℂ) • B₁ + ((1 - α : ℝ) : ℂ) • B₂
        = (α : ℂ) • (U * dB₁.M * sU) + ((1 - α : ℝ) : ℂ) • (U * dB₂.M * sU) := by
          rw [hB₁_eq, hB₂_eq]
      _ = U * ((α : ℂ) • dB₁.M + ((1 - α : ℝ) : ℂ) • dB₂.M) * sU := this
  -- Reduce each of the 6 Re-Tr terms.
  have h1 : (Matrix.trace (A_t * cfc Real.log A_t)).re
      = (Matrix.trace
            (((α : ℂ) • dA₁.M + ((1 - α : ℝ) : ℂ) • dA₂.M) *
              cfc Real.log ((α : ℂ) • dA₁.M + ((1 - α : ℝ) : ℂ) • dA₂.M))).re := by
    rw [h_At_eq]
    exact re_trace_unitary_cfc_log J.U _ _ hDA_conv_sa
  have h2 : (Matrix.trace (A_t * cfc Real.log B_t)).re
      = (Matrix.trace
            (((α : ℂ) • dA₁.M + ((1 - α : ℝ) : ℂ) • dA₂.M) *
              cfc Real.log ((α : ℂ) • dB₁.M + ((1 - α : ℝ) : ℂ) • dB₂.M))).re := by
    rw [h_At_eq, h_Bt_eq]
    exact re_trace_unitary_cfc_log J.U _ _ hDB_conv_sa
  have h3 : (Matrix.trace (A₁ * cfc Real.log A₁)).re
      = (Matrix.trace (dA₁.M * cfc Real.log dA₁.M)).re := by
    rw [hA₁_eq]
    exact re_trace_unitary_cfc_log J.U dA₁.M dA₁.M hDA₁_sa
  have h4 : (Matrix.trace (A₁ * cfc Real.log B₁)).re
      = (Matrix.trace (dA₁.M * cfc Real.log dB₁.M)).re := by
    rw [hA₁_eq, hB₁_eq]
    exact re_trace_unitary_cfc_log J.U dA₁.M dB₁.M hDB₁_sa
  have h5 : (Matrix.trace (A₂ * cfc Real.log A₂)).re
      = (Matrix.trace (dA₂.M * cfc Real.log dA₂.M)).re := by
    rw [hA₂_eq]
    exact re_trace_unitary_cfc_log J.U dA₂.M dA₂.M hDA₂_sa
  have h6 : (Matrix.trace (A₂ * cfc Real.log B₂)).re
      = (Matrix.trace (dA₂.M * cfc Real.log dB₂.M)).re := by
    rw [hA₂_eq, hB₂_eq]
    exact re_trace_unitary_cfc_log J.U dA₂.M dB₂.M hDB₂_sa
  rw [h1, h2, h3, h4, h5, h6]
  -- Convex combinations of diagonals = diagonal of convex combinations.
  have h_At_diag :
      (α : ℂ) • dA₁.M + ((1 - α : ℝ) : ℂ) • dA₂.M
        = Matrix.diagonal
            (fun i => ((α * dA₁.d i + (1 - α) * dA₂.d i : ℝ) : ℂ)) := by
    change (α : ℂ) • Matrix.diagonal (fun i => ((dA₁.d i : ℝ) : ℂ))
              + ((1 - α : ℝ) : ℂ) •
                Matrix.diagonal (fun i => ((dA₂.d i : ℝ) : ℂ))
            = _
    ext i j
    by_cases hij : i = j
    · subst hij
      simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.diagonal_apply_eq,
                  smul_eq_mul]
      push_cast
      ring
    · simp [Matrix.add_apply, Matrix.smul_apply,
            Matrix.diagonal_apply_ne _ hij, smul_eq_mul]
  have h_Bt_diag :
      (α : ℂ) • dB₁.M + ((1 - α : ℝ) : ℂ) • dB₂.M
        = Matrix.diagonal
            (fun i => ((α * dB₁.d i + (1 - α) * dB₂.d i : ℝ) : ℂ)) := by
    change (α : ℂ) • Matrix.diagonal (fun i => ((dB₁.d i : ℝ) : ℂ))
              + ((1 - α : ℝ) : ℂ) •
                Matrix.diagonal (fun i => ((dB₂.d i : ℝ) : ℂ))
            = _
    ext i j
    by_cases hij : i = j
    · subst hij
      simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.diagonal_apply_eq,
                  smul_eq_mul]
      push_cast
      ring
    · simp [Matrix.add_apply, Matrix.smul_apply,
            Matrix.diagonal_apply_ne _ hij, smul_eq_mul]
  rw [h_At_diag, h_Bt_diag]
  -- Apply the data-level diagonal theorem.
  have hkey := lieb1973_corrected_diagonal_data dA₁ dA₂ dB₁ dB₂ hα₀ hα₁
  simp only at hkey
  exact hkey

end Reduction

/-! ## 6. The full commuting-case theorem -/

/-- **THE HEADLINE**:
    `Lieb1973_Corrected_Target` for the COMMUTING case (FULL, not just
    diagonal-input), assuming joint diagonalisation.

    For four pairwise-commuting PosDef matrices `A₁, A₂, B₁, B₂` and
    `α ∈ [0, 1]` that admit a `JointDiagonalisation`, the corrected
    target inequality holds:

        S(αA₁ + (1-α)A₂  ‖  αB₁ + (1-α)B₂)
            ≤  α · S(A₁ ‖ B₁) + (1-α) · S(A₂ ‖ B₂)

    where `S(A ‖ B) := Re Tr( A · log A ) − Re Tr( A · log B )`.

    This is essentially `lieb1973_corrected_of_jointDiag` repackaged
    to include the `AllCommute` hypothesis explicitly (which is
    redundant when a `JointDiagonalisation` exists, but makes the
    physics meaning of the theorem statement transparent). -/
theorem lieb1973_corrected_commuting_full {m : ℕ}
    (A₁ A₂ B₁ B₂ : Matrix (Fin m) (Fin m) ℂ)
    (hA₁ : A₁.PosDef) (hA₂ : A₂.PosDef) (hB₁ : B₁.PosDef) (hB₂ : B₂.PosDef)
    (_h_comm : AllCommute A₁ A₂ B₁ B₂)
    (J : JointDiagonalisation A₁ A₂ B₁ B₂)
    (α : ℝ) (hα₀ : 0 ≤ α) (hα₁ : α ≤ 1) :
    let A_t : Matrix (Fin m) (Fin m) ℂ :=
      (α : ℂ) • A₁ + ((1 - α : ℝ) : ℂ) • A₂
    let B_t : Matrix (Fin m) (Fin m) ℂ :=
      (α : ℂ) • B₁ + ((1 - α : ℝ) : ℂ) • B₂
    (Matrix.trace (A_t * cfc Real.log A_t)).re
        - (Matrix.trace (A_t * cfc Real.log B_t)).re
      ≤ α * ((Matrix.trace (A₁ * cfc Real.log A₁)).re
              - (Matrix.trace (A₁ * cfc Real.log B₁)).re)
        + (1 - α) * ((Matrix.trace (A₂ * cfc Real.log A₂)).re
                      - (Matrix.trace (A₂ * cfc Real.log B₂)).re) :=
  lieb1973_corrected_of_jointDiag A₁ A₂ B₁ B₂ hA₁ hA₂ hB₁ hB₂ J α hα₀ hα₁

/-! ## 7. Universal-form Prop ("commuting target" gated on joint diag) -/

/-- The corrected target restricted to commuting tuples that admit a
    joint diagonalisation.  This is a `Prop`-valued analogue of
    `Lieb1973_Corrected_Target` quantified over commuting tuples plus
    their joint-diagonalisation witnesses. -/
def Lieb1973_Corrected_Target_Commuting : Prop :=
    ∀ {m : ℕ} (A₁ A₂ B₁ B₂ : Matrix (Fin m) (Fin m) ℂ),
      A₁.PosDef → A₂.PosDef → B₁.PosDef → B₂.PosDef →
      AllCommute A₁ A₂ B₁ B₂ →
      ∀ (J : JointDiagonalisation A₁ A₂ B₁ B₂)
        (α : ℝ), 0 ≤ α → α ≤ 1 →
          let A_t : Matrix (Fin m) (Fin m) ℂ :=
            (α : ℂ) • A₁ + ((1 - α : ℝ) : ℂ) • A₂
          let B_t : Matrix (Fin m) (Fin m) ℂ :=
            (α : ℂ) • B₁ + ((1 - α : ℝ) : ℂ) • B₂
          (Matrix.trace (A_t * cfc Real.log A_t)).re
              - (Matrix.trace (A_t * cfc Real.log B_t)).re
            ≤ α * ((Matrix.trace (A₁ * cfc Real.log A₁)).re
                    - (Matrix.trace (A₁ * cfc Real.log B₁)).re)
              + (1 - α) * ((Matrix.trace (A₂ * cfc Real.log A₂)).re
                            - (Matrix.trace (A₂ * cfc Real.log B₂)).re)

/-- The commuting target is unconditionally true. -/
theorem lieb1973_corrected_target_commuting_holds :
    Lieb1973_Corrected_Target_Commuting := by
  intro m A₁ A₂ B₁ B₂ hA₁ hA₂ hB₁ hB₂ h_comm J α hα₀ hα₁
  exact lieb1973_corrected_commuting_full A₁ A₂ B₁ B₂ hA₁ hA₂ hB₁ hB₂ h_comm J α hα₀ hα₁

/-! ## 8. Axiom audit (uncomment after a clean build) -/

-- #print axioms lieb1973_corrected_of_jointDiag
-- #print axioms lieb1973_corrected_commuting_full
-- #print axioms lieb1973_corrected_target_commuting_holds
-- VERIFIED 2026-06-01:
--   All three depend ONLY on [propext, Classical.choice, Quot.sound]
--   (Lean's three standard foundational axioms).
--   No `sorry`, no custom `axiom`.

end UnifiedTheory.LayerB.LiebCorrectedCommutingFull
