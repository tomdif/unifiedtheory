/-
  LayerB/KleinEquality.lean
  ──────────────────────────

  **The equality (faithfulness) case of Klein's inequality.**

  Klein's inequality (proved in `KleinInequalityFull.lean`) states that
  for positive-definite Hermitian matrices `A, B`,

      Re Tr (A − B)  ≤  Re Tr ( A · (log A − log B) ),

  and for density matrices this gives `0 ≤ S(ρ‖σ)` (Umegaki relative
  entropy non-negativity).  This file proves the **equality case**:

      S(ρ‖σ) = 0   ⟹   ρ = σ.

  i.e. the Umegaki relative entropy is *faithful*.

  ─────────────────────────────────────────────────────────────────
  STRUCTURE
  ─────────────────────────────────────────────────────────────────

  1.  `kleinDeficit_strict` / `kleinDeficit_eq_zero_iff`
      The strict scalar fact `f(a,b) := a log a − a log b − a + b ≥ 0`
      with `f(a,b) = 0 ⟺ a = b` for `a, b > 0`.  The strict direction
      uses Mathlib's `Real.log_lt_sub_one_of_pos`.

  2.  `umegaki_eq_sum_kleinDeficit`
      The Umegaki relative entropy, in the two-basis decomposition of
      `KleinInequalityFull.lean`, equals *exactly* the manifestly
      non-negative sum

          S(ρ‖σ) = ∑_{i,j} P_{ij} · f(λ_i, μ_j),         (no Jensen!)

      with `P_{ij} = ‖V_{ij}‖² ≥ 0` doubly stochastic.  The key trick
      is that the row/column sums of `P` being 1 collapse the LHS
      `∑(λ_i − c_i)` and the diagonal terms so that the entropy is a
      *single* double sum of scalar Klein deficits — sidestepping the
      strict-Jensen equality analysis entirely.

  3.  `umegaki_eq_zero_forces_terms`
      `S(ρ‖σ) = 0` forces every summand `P_{ij} · f(λ_i, μ_j) = 0`,
      hence for every `(i,j)`: `P_{ij} = 0` **or** `λ_i = μ_j`.

  4.  `umegakiRelativeEntropy_eq_zero_imp` / `_iff`  — **the FULL
      (non-commuting) faithfulness case.**  The overlap constraints of
      step 3 are turned into the matrix identity
      `V · diag(μ) · star V = diag(λ)` (because `V_{ij} μ_j = V_{ij} λ_i`
      for every `(i,j)`), and conjugating by `U_ρ` gives `ρ.M = σ.M`
      directly — no commuting or shared-eigenbasis hypothesis.

  This discharges coherence forward-faithfulness
  (`CoherenceNonneg.coherence_eq_zero_iff`) and Gibbs-state uniqueness
  (`GibbsVariationalFull.gibbs_state_unique`).

  No `sorry`, no custom `axiom`.
-/

import UnifiedTheory.LayerB.KleinInequalityFull
import Mathlib.Analysis.SpecialFunctions.Log.Basic

set_option relaxedAutoImplicit false

namespace UnifiedTheory.LayerB.KleinEquality

open Matrix Complex
open scoped MatrixOrder Matrix.Norms.L2Operator ComplexOrder
open UnifiedTheory.LayerB.RobertsonSchrodinger
open UnifiedTheory.LayerB.SpectralFC
open UnifiedTheory.LayerB.OperatorEntropy
open UnifiedTheory.LayerB.KleinInequality
open UnifiedTheory.LayerB.KleinInequalityFull
open UnifiedTheory.LayerB.UmegakiRelativeEntropy

variable {n : ℕ}

/-! ## 1. The strict scalar Klein deficit -/

/-- The scalar Klein **deficit** `f(a,b) = a·log a − a·log b − a + b`. -/
noncomputable def kleinDeficit (a b : ℝ) : ℝ :=
  a * Real.log a - a * Real.log b - a + b

/-- **Non-negativity of the deficit** (re-export of `klein_scalar_form`). -/
theorem kleinDeficit_nonneg {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    0 ≤ kleinDeficit a b := by
  unfold kleinDeficit
  exact klein_scalar_form ha hb

/-- The deficit vanishes on the diagonal. -/
theorem kleinDeficit_self (a : ℝ) : kleinDeficit a a = 0 := by
  unfold kleinDeficit; ring

/-- **Strict scalar Klein.**  For `a, b > 0` with `a ≠ b`, the deficit
    is strictly positive.

    Proof: `log(b/a) < b/a − 1` (`Real.log_lt_sub_one_of_pos`, valid
    since `b/a ≠ 1`); multiply by `a > 0` and rearrange. -/
theorem kleinDeficit_strict {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hab : a ≠ b) : 0 < kleinDeficit a b := by
  -- `b/a > 0` and `b/a ≠ 1`.
  have hba_pos : (0 : ℝ) < b / a := div_pos hb ha
  have hba_ne : b / a ≠ 1 := by
    intro h
    apply hab
    -- b/a = 1 ⟹ b = a
    field_simp at h
    linarith
  -- Strict log bound.
  have h1 : Real.log (b / a) < b / a - 1 :=
    Real.log_lt_sub_one_of_pos hba_pos hba_ne
  -- log(b/a) = log b − log a.
  have h2 : Real.log (b / a) = Real.log b - Real.log a :=
    Real.log_div (ne_of_gt hb) (ne_of_gt ha)
  rw [h2] at h1
  -- Multiply by a > 0: a(log b − log a) < a(b/a − 1) = b − a.
  have h3 : a * (Real.log b - Real.log a) < a * (b / a - 1) :=
    mul_lt_mul_of_pos_left h1 ha
  have h4 : a * (b / a - 1) = b - a := by field_simp
  rw [h4, mul_sub] at h3
  -- a log b − a log a < b − a  ⟹  0 < a log a − a log b − a + b.
  unfold kleinDeficit
  linarith

/-- **The faithful scalar equivalence:** for `a, b > 0`,
    `kleinDeficit a b = 0 ⟺ a = b`. -/
theorem kleinDeficit_eq_zero_iff {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    kleinDeficit a b = 0 ↔ a = b := by
  constructor
  · intro h
    by_contra hab
    have := kleinDeficit_strict ha hb hab
    linarith
  · intro h; rw [h]; exact kleinDeficit_self b

/-! ## 2. The two-basis deficit decomposition of the Umegaki entropy

    Re-using the mixed-basis machinery of `KleinInequalityFull.lean`,
    we show that for *density* matrices the Umegaki relative entropy is
    *exactly* the manifestly non-negative doubly-stochastic average of
    scalar Klein deficits:

        S(ρ‖σ) = ∑_{i,j} ‖V_{ij}‖² · f(λ_i, μ_j),

    where `λ = eigenvalues ρ`, `μ = eigenvalues σ`, and
    `V = star U_ρ · U_σ` is unitary (so `‖V_{ij}‖²` is doubly
    stochastic). -/

/-- **Deficit decomposition of the Umegaki relative entropy.**

    For positive-definite *density* matrices ρ, σ,

      `S(ρ‖σ) = ∑_i ∑_j ‖V_{ij}‖² · kleinDeficit (λ_i) (μ_j)`,

    with `λ_i = eigenvalues ρ.M`, `μ_j = eigenvalues σ.M`, and
    `V_{ij} = (star U_ρ · U_σ)_{ij}`. -/
theorem umegaki_eq_sum_kleinDeficit
    (ρ σ : ComplexDensityMatrix n)
    (hρ : ρ.M.PosDef) (hσ : σ.M.PosDef) :
    umegakiRelativeEntropy ρ σ
      = ∑ i, ∑ j,
          ‖((star hρ.1.eigenvectorUnitary.val)
              * hσ.1.eigenvectorUnitary.val) i j‖^2
            * kleinDeficit (hρ.1.eigenvalues i) (hσ.1.eigenvalues j) := by
  classical
  -- Notation.
  set lam : Fin n → ℝ := hρ.1.eigenvalues with hlam_def
  set mu : Fin n → ℝ := hσ.1.eigenvalues with hmu_def
  set V : Matrix (Fin n) (Fin n) ℂ :=
      (star hρ.1.eigenvectorUnitary.val) * hσ.1.eigenvectorUnitary.val with hV_def
  -- Positivity of eigenvalues.
  have hlam_pos : ∀ i, 0 < lam i := fun i => hρ.eigenvalues_pos i
  have hmu_pos : ∀ j, 0 < mu j := fun j => hσ.eigenvalues_pos j
  -- Doubly-stochastic property of P_{ij} := ‖V_{ij}‖².
  by_cases hn : n = 0
  · subst hn
    simp [umegakiRelativeEntropy, Matrix.trace, Matrix.diag]
  have hn_pos : 0 < n := Nat.pos_of_ne_zero hn
  haveI : Nonempty (Fin n) := ⟨⟨0, hn_pos⟩⟩
  -- V is unitary.
  have hUρ_mem : hρ.1.eigenvectorUnitary.val ∈ Matrix.unitaryGroup (Fin n) ℂ :=
    hρ.1.eigenvectorUnitary.2
  have hUσ_mem : hσ.1.eigenvectorUnitary.val ∈ Matrix.unitaryGroup (Fin n) ℂ :=
    hσ.1.eigenvectorUnitary.2
  have hV_mem : V ∈ Matrix.unitaryGroup (Fin n) ℂ :=
    mul_mem (Unitary.star_mem hUρ_mem) hUσ_mem
  have hV_mul_star : V * star V = 1 := by
    rw [Matrix.mem_unitaryGroup_iff] at hV_mem; exact hV_mem
  have hstar_V_mul_V : star V * V = 1 := by
    rw [Matrix.mem_unitaryGroup_iff'] at hV_mem; exact hV_mem
  -- z * star z = ‖z‖² as complex numbers.
  have hmulstar : ∀ z : ℂ, z * star z = ((‖z‖^2 : ℝ) : ℂ) := by
    intro z
    rw [show (star z : ℂ) = (starRingEnd ℂ) z from rfl, Complex.mul_conj,
        Complex.normSq_eq_norm_sq]
  -- Row sums of P_{ij} = ‖V_{ij}‖² are 1 (from V * star V = 1).
  have hrow_sum : ∀ i, ∑ j, ‖V i j‖^2 = 1 := by
    intro i
    have h : (V * star V) i i = (1 : Matrix (Fin n) (Fin n) ℂ) i i := by rw [hV_mul_star]
    rw [Matrix.mul_apply, Matrix.one_apply_eq] at h
    have h2 : ∀ j, V i j * (star V) j i = ((‖V i j‖^2 : ℝ) : ℂ) := fun j => hmulstar (V i j)
    rw [Finset.sum_congr rfl (fun j _ => h2 j)] at h
    have h3 : ((∑ j, ‖V i j‖^2 : ℝ) : ℂ) = (1 : ℂ) := by rw [← h]; push_cast; rfl
    exact_mod_cast h3
  -- Column sums of P_{ij} = ‖V_{ij}‖² are 1 (from star V * V = 1).
  have hcol_sum : ∀ j, ∑ i, ‖V i j‖^2 = 1 := by
    intro j
    have h : (star V * V) j j = (1 : Matrix (Fin n) (Fin n) ℂ) j j := by rw [hstar_V_mul_V]
    rw [Matrix.mul_apply, Matrix.one_apply_eq] at h
    have h2 : ∀ i, (star V) j i * V i j = ((‖V i j‖^2 : ℝ) : ℂ) := by
      intro i; rw [show (star V) j i = star (V i j) from rfl, mul_comm]; exact hmulstar (V i j)
    rw [Finset.sum_congr rfl (fun i _ => h2 i)] at h
    have h3 : ((∑ i, ‖V i j‖^2 : ℝ) : ℂ) = (1 : ℂ) := by rw [← h]; push_cast; rfl
    exact_mod_cast h3
  -- Re Tr(ρ log ρ) = ∑ λ_i log λ_i.
  have h_RHS_A : (Matrix.trace (ρ.M * cfc Real.log ρ.M)).re
                = ∑ i, lam i * Real.log (lam i) :=
    re_trace_mul_cfc_log_eq_sum ρ.M hρ
  -- Re Tr(ρ log σ) = ∑_{i,j} ‖V_{ij}‖² λ_i log μ_j.
  have h_RHS_B : (Matrix.trace (ρ.M * cfc Real.log σ.M)).re
                = ∑ i, ∑ j, ‖V i j‖^2 * lam i * Real.log (mu j) := by
    rw [trace_mul_cfc_log_eq_sum_mixed ρ.M σ.M hρ hσ, Complex.re_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [Complex.re_sum]
    apply Finset.sum_congr rfl
    intro j _
    rw [show ((‖V i j‖^2 : ℝ) : ℂ) * ((lam i : ℝ) : ℂ) * ((Real.log (mu j) : ℝ) : ℂ)
          = ((‖V i j‖^2 * lam i * Real.log (mu j) : ℝ) : ℂ) by push_cast; ring]
    exact Complex.ofReal_re _
  -- Tr ρ = ∑ λ_i = 1, Tr σ = ∑ μ_j = 1.
  have h_sum_lam : ∑ i, lam i = 1 := by
    have h : Matrix.trace ρ.M = ∑ i, ((lam i : ℝ) : ℂ) :=
      hρ.1.trace_eq_sum_eigenvalues
    have h1 : (Matrix.trace ρ.M).re = ∑ i, lam i := by
      rw [h, Complex.re_sum]; exact Finset.sum_congr rfl (fun i _ => Complex.ofReal_re _)
    rw [← h1, ρ.hTrace, Complex.one_re]
  have h_sum_mu : ∑ j, mu j = 1 := by
    have h : Matrix.trace σ.M = ∑ j, ((mu j : ℝ) : ℂ) :=
      hσ.1.trace_eq_sum_eigenvalues
    have h1 : (Matrix.trace σ.M).re = ∑ j, mu j := by
      rw [h, Complex.re_sum]; exact Finset.sum_congr rfl (fun j _ => Complex.ofReal_re _)
    rw [← h1, σ.hTrace, Complex.one_re]
  -- Expand the umegaki entropy.
  have h_umeg : umegakiRelativeEntropy ρ σ
      = (∑ i, lam i * Real.log (lam i))
          - ∑ i, ∑ j, ‖V i j‖^2 * lam i * Real.log (mu j) := by
    unfold umegakiRelativeEntropy operatorLog cfcρ
    rw [Matrix.mul_sub, Matrix.trace_sub, Complex.sub_re, h_RHS_A, h_RHS_B]
  rw [h_umeg]
  -- Now expand the RHS sum of deficits.
  -- ∑∑ P f = ∑∑ P λ log λ − ∑∑ P λ log μ − ∑∑ P λ + ∑∑ P μ.
  have h_deficit_expand :
      ∑ i, ∑ j, ‖V i j‖^2 * kleinDeficit (lam i) (mu j)
        = (∑ i, ∑ j, ‖V i j‖^2 * (lam i * Real.log (lam i)))
            - (∑ i, ∑ j, ‖V i j‖^2 * (lam i * Real.log (mu j)))
            - (∑ i, ∑ j, ‖V i j‖^2 * lam i)
            + (∑ i, ∑ j, ‖V i j‖^2 * mu j) := by
    rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl; intro i _
    rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl; intro j _
    unfold kleinDeficit; ring
  rw [h_deficit_expand]
  -- Simplify each piece using row/col sums.
  -- (1) ∑∑ P λ log λ = ∑ λ log λ  (row sum).
  have h1 : ∑ i, ∑ j, ‖V i j‖^2 * (lam i * Real.log (lam i))
              = ∑ i, lam i * Real.log (lam i) := by
    apply Finset.sum_congr rfl; intro i _
    rw [← Finset.sum_mul, hrow_sum i, one_mul]
  -- (2) ∑∑ P λ log μ = ∑∑ P λ log μ  (rewrite ‖V‖² λ log μ = ‖V‖² (λ log μ)).
  have h2 : ∑ i, ∑ j, ‖V i j‖^2 * (lam i * Real.log (mu j))
              = ∑ i, ∑ j, ‖V i j‖^2 * lam i * Real.log (mu j) := by
    apply Finset.sum_congr rfl; intro i _
    apply Finset.sum_congr rfl; intro j _; ring
  -- (3) ∑∑ P λ = ∑ λ  (row sum).
  have h3 : ∑ i, ∑ j, ‖V i j‖^2 * lam i = ∑ i, lam i := by
    apply Finset.sum_congr rfl; intro i _
    rw [← Finset.sum_mul, hrow_sum i, one_mul]
  -- (4) ∑∑ P μ = ∑ μ  (col sum, after swap).
  have h4 : ∑ i, ∑ j, ‖V i j‖^2 * mu j = ∑ j, mu j := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro j _
    rw [← Finset.sum_mul, hcol_sum j, one_mul]
  rw [h1, h2, h3, h4, h_sum_lam, h_sum_mu]
  ring

/-! ## 3. Vanishing entropy forces the eigenvalue-overlap constraints -/

/-- **Term-vanishing.**  If `S(ρ‖σ) = 0`, then for every pair `(i,j)`,

      `‖V_{ij}‖² · kleinDeficit (λ_i) (μ_j) = 0`,

    i.e. either the overlap `V_{ij}` vanishes or `λ_i = μ_j`. -/
theorem umegaki_eq_zero_forces_terms
    (ρ σ : ComplexDensityMatrix n)
    (hρ : ρ.M.PosDef) (hσ : σ.M.PosDef)
    (hS : umegakiRelativeEntropy ρ σ = 0) :
    ∀ i j,
      ‖((star hρ.1.eigenvectorUnitary.val)
          * hσ.1.eigenvectorUnitary.val) i j‖^2 = 0
      ∨ hρ.1.eigenvalues i = hσ.1.eigenvalues j := by
  classical
  set lam : Fin n → ℝ := hρ.1.eigenvalues with hlam_def
  set mu : Fin n → ℝ := hσ.1.eigenvalues with hmu_def
  set V : Matrix (Fin n) (Fin n) ℂ :=
      (star hρ.1.eigenvectorUnitary.val) * hσ.1.eigenvectorUnitary.val with hV_def
  have hlam_pos : ∀ i, 0 < lam i := fun i => hρ.eigenvalues_pos i
  have hmu_pos : ∀ j, 0 < mu j := fun j => hσ.eigenvalues_pos j
  -- The decomposition.
  have hdecomp := umegaki_eq_sum_kleinDeficit ρ σ hρ hσ
  rw [hS] at hdecomp
  -- 0 = ∑∑ ‖V_{ij}‖² f(λ_i, μ_j), all terms ≥ 0.
  have hnonneg : ∀ i ∈ (Finset.univ : Finset (Fin n)),
      0 ≤ ∑ j, ‖V i j‖^2 * kleinDeficit (lam i) (mu j) := by
    intro i _
    apply Finset.sum_nonneg; intro j _
    exact mul_nonneg (sq_nonneg _) (kleinDeficit_nonneg (hlam_pos i) (hmu_pos j))
  -- Outer sum zero ⟹ each inner sum zero.
  have h_outer_zero : ∀ i, ∑ j, ‖V i j‖^2 * kleinDeficit (lam i) (mu j) = 0 := by
    intro i
    have := (Finset.sum_eq_zero_iff_of_nonneg hnonneg).mp hdecomp.symm i (Finset.mem_univ i)
    exact this
  -- Each inner sum zero ⟹ each term zero.
  intro i j
  have hnonneg_inner : ∀ j' ∈ (Finset.univ : Finset (Fin n)),
      0 ≤ ‖V i j'‖^2 * kleinDeficit (lam i) (mu j') :=
    fun j' _ => mul_nonneg (sq_nonneg _) (kleinDeficit_nonneg (hlam_pos i) (hmu_pos j'))
  have h_term_zero : ‖V i j‖^2 * kleinDeficit (lam i) (mu j) = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg hnonneg_inner).mp (h_outer_zero i) j (Finset.mem_univ j)
  -- Product zero ⟹ factor zero.
  rcases mul_eq_zero.mp h_term_zero with hP | hf
  · exact Or.inl hP
  · -- kleinDeficit (λ_i) (μ_j) = 0 ⟹ λ_i = μ_j.
    exact Or.inr ((kleinDeficit_eq_zero_iff (hlam_pos i) (hmu_pos j)).mp hf)

/-! ## 4. Reconstruction: the overlap constraints force `ρ.M = σ.M`

    This is the heart of *faithfulness*.  We turn the constraint
    "`V_{ij} = 0` or `λ_i = μ_j`" into the matrix identity
    `V · diag(μ) · star V = diag(λ)`, and conjugate back by `U_ρ`. -/

/-- Spectral form `A = U · diag(λ : ℂ) · star U` for a positive-definite
    matrix, with `U = hA.1.eigenvectorUnitary` and `λ = hA.1.eigenvalues`. -/
private lemma posDef_spectral
    (A : Matrix (Fin n) (Fin n) ℂ) (hA : A.PosDef) :
    A = (hA.1.eigenvectorUnitary.val)
          * Matrix.diagonal (fun i => ((hA.1.eigenvalues i : ℝ) : ℂ))
          * (star hA.1.eigenvectorUnitary.val) := by
  have h := hA.1.spectral_theorem
  rw [Unitary.conjStarAlgAut_apply] at h
  exact h

/-- **Key entrywise identity.**  Under the overlap constraint
    `∀ i j, V_{ij} = 0 ∨ λ_i = μ_j`, with `V` unitary (`V · star V = 1`),

      `V · diag(μ) · star V = diag(λ)`. -/
private lemma V_conj_diag_eq
    (V : Matrix (Fin n) (Fin n) ℂ)
    (lam mu : Fin n → ℝ)
    (hVstar : V * star V = 1)
    (hcon : ∀ i j, V i j = 0 ∨ lam i = mu j) :
    V * Matrix.diagonal (fun j => ((mu j : ℝ) : ℂ)) * (star V)
      = Matrix.diagonal (fun i => ((lam i : ℝ) : ℂ)) := by
  classical
  ext i k
  -- LHS entry (i,k) = ∑_j V_{ij} · μ_j · conj V_{kj}.
  rw [Matrix.mul_apply]
  -- (V * diag μ) i j = V i j * μ_j.
  have hVD : ∀ j, (V * Matrix.diagonal (fun j => ((mu j : ℝ) : ℂ))) i j
              = V i j * ((mu j : ℝ) : ℂ) := by
    intro j; rw [Matrix.mul_diagonal]
  -- (star V) j k = star (V k j).
  have hstar : ∀ j, (star V) j k = star (V k j) := fun j => rfl
  -- Use the constraint to replace μ_j by λ_i wherever V_{ij} ≠ 0.
  have hkey : ∀ j, V i j * ((mu j : ℝ) : ℂ) = V i j * ((lam i : ℝ) : ℂ) := by
    intro j
    rcases hcon i j with hz | he
    · rw [hz, zero_mul, zero_mul]
    · rw [he]
  -- Compute the sum.
  calc ∑ j, (V * Matrix.diagonal (fun j => ((mu j : ℝ) : ℂ))) i j * (star V) j k
      = ∑ j, (V i j * ((mu j : ℝ) : ℂ)) * star (V k j) := by
        apply Finset.sum_congr rfl; intro j _; rw [hVD j, hstar j]
    _ = ∑ j, ((lam i : ℝ) : ℂ) * (V i j * star (V k j)) := by
        apply Finset.sum_congr rfl; intro j _
        rw [show V i j * ((mu j : ℝ) : ℂ) = V i j * ((lam i : ℝ) : ℂ) from hkey j]; ring
    _ = ((lam i : ℝ) : ℂ) * ∑ j, V i j * star (V k j) := by rw [Finset.mul_sum]
    _ = ((lam i : ℝ) : ℂ) * (V * star V) i k := by
        rw [Matrix.mul_apply]
        congr 1
    _ = ((lam i : ℝ) : ℂ) * (1 : Matrix (Fin n) (Fin n) ℂ) i k := by rw [hVstar]
    _ = Matrix.diagonal (fun i => ((lam i : ℝ) : ℂ)) i k := by
        rw [Matrix.one_apply, Matrix.diagonal_apply]
        by_cases h : i = k
        · subst h; simp
        · simp [h]

/-- **Faithfulness of the Umegaki relative entropy.**

    For positive-definite density matrices ρ, σ, the relative entropy
    vanishes *only* when the states coincide:

      `S(ρ‖σ) = 0  ⟹  ρ.M = σ.M`.

    This is the full equality case of Klein's inequality — no commuting
    or shared-eigenbasis hypothesis is required. -/
theorem umegakiRelativeEntropy_eq_zero_imp
    (ρ σ : ComplexDensityMatrix n)
    (hρ : ρ.M.PosDef) (hσ : σ.M.PosDef)
    (hS : umegakiRelativeEntropy ρ σ = 0) :
    ρ.M = σ.M := by
  classical
  -- Notation.
  set Uρ : Matrix (Fin n) (Fin n) ℂ := hρ.1.eigenvectorUnitary.val with hUρ_def
  set Uσ : Matrix (Fin n) (Fin n) ℂ := hσ.1.eigenvectorUnitary.val with hUσ_def
  set lam : Fin n → ℝ := hρ.1.eigenvalues with hlam_def
  set mu : Fin n → ℝ := hσ.1.eigenvalues with hmu_def
  set V : Matrix (Fin n) (Fin n) ℂ := star Uρ * Uσ with hV_def
  -- Constraints from vanishing entropy.
  have hcon : ∀ i j, V i j = 0 ∨ lam i = mu j := by
    intro i j
    rcases umegaki_eq_zero_forces_terms ρ σ hρ hσ hS i j with hP | he
    · left
      -- ‖V_{ij}‖² = 0 ⟹ V_{ij} = 0.
      have : ‖V i j‖ = 0 := by nlinarith [norm_nonneg (V i j), hP]
      exact norm_eq_zero.mp this
    · right; exact he
  -- Unitarity facts.
  have hUρ_mem : Uρ ∈ Matrix.unitaryGroup (Fin n) ℂ := hρ.1.eigenvectorUnitary.2
  have hUσ_mem : Uσ ∈ Matrix.unitaryGroup (Fin n) ℂ := hσ.1.eigenvectorUnitary.2
  have hV_mem : V ∈ Matrix.unitaryGroup (Fin n) ℂ :=
    mul_mem (Unitary.star_mem hUρ_mem) hUσ_mem
  have hVstar : V * star V = 1 := by
    rw [Matrix.mem_unitaryGroup_iff] at hV_mem; exact hV_mem
  -- Uρ * star Uρ = 1.
  have hUρ_unit : Uρ * star Uρ = 1 := by
    rw [Matrix.mem_unitaryGroup_iff] at hUρ_mem; exact hUρ_mem
  -- Spectral forms.
  have hρ_spec : ρ.M = Uρ * Matrix.diagonal (fun i => ((lam i : ℝ) : ℂ)) * star Uρ :=
    posDef_spectral ρ.M hρ
  have hσ_spec : σ.M = Uσ * Matrix.diagonal (fun j => ((mu j : ℝ) : ℂ)) * star Uσ :=
    posDef_spectral σ.M hσ
  -- Uσ = Uρ * V.
  have hUσ_eq : Uσ = Uρ * V := by
    rw [hV_def, ← Matrix.mul_assoc, hUρ_unit, Matrix.one_mul]
  -- star Uσ = star V * star Uρ.
  have hstarUσ_eq : star Uσ = star V * star Uρ := by
    rw [hUσ_eq, StarMul.star_mul]
  -- Rewrite σ.M, substituting Uσ = Uρ * V.
  have hσ_rewrite :
      σ.M = Uρ * (V * Matrix.diagonal (fun j => ((mu j : ℝ) : ℂ)) * star V) * star Uρ := by
    calc σ.M
        = Uσ * Matrix.diagonal (fun j => ((mu j : ℝ) : ℂ)) * star Uσ := hσ_spec
      _ = (Uρ * V) * Matrix.diagonal (fun j => ((mu j : ℝ) : ℂ)) * (star V * star Uρ) := by
            rw [hstarUσ_eq, hUσ_eq]
      _ = Uρ * (V * Matrix.diagonal (fun j => ((mu j : ℝ) : ℂ)) * star V) * star Uρ := by
            noncomm_ring
  -- The conjugation identity.
  have hVconj := V_conj_diag_eq V lam mu hVstar hcon
  rw [hVconj] at hσ_rewrite
  -- Now σ.M = Uρ * diag(λ) * star Uρ = ρ.M.
  rw [hσ_rewrite, ← hρ_spec]

/-! ## 5. The faithful iff -/

/-- **Faithfulness, packaged as an equivalence.**

    For positive-definite density matrices ρ, σ,

      `S(ρ‖σ) = 0  ⟺  ρ.M = σ.M`. -/
theorem umegakiRelativeEntropy_eq_zero_iff
    (ρ σ : ComplexDensityMatrix n)
    (hρ : ρ.M.PosDef) (hσ : σ.M.PosDef) :
    umegakiRelativeEntropy ρ σ = 0 ↔ ρ.M = σ.M := by
  constructor
  · exact umegakiRelativeEntropy_eq_zero_imp ρ σ hρ hσ
  · intro hEq
    -- ρ.M = σ.M ⟹ log ρ.M = log σ.M ⟹ S = 0 (depends only on .M).
    unfold umegakiRelativeEntropy operatorLog cfcρ
    rw [hEq, sub_self, Matrix.mul_zero, Matrix.trace_zero, Complex.zero_re]

/-! ## 6. Axiom audit.

  VERIFIED 2026-06-02 (via `#print axioms`):
    umegakiRelativeEntropy_eq_zero_iff  ⟹ [propext, Classical.choice, Quot.sound]
    umegakiRelativeEntropy_eq_zero_imp  ⟹ [propext, Classical.choice, Quot.sound]
    umegaki_eq_sum_kleinDeficit         ⟹ [propext, Classical.choice, Quot.sound]
    kleinDeficit_strict                 ⟹ [propext, Classical.choice, Quot.sound]
  All depend ONLY on Lean's three standard axioms.  No `sorry`, no custom `axiom`.
-/

end UnifiedTheory.LayerB.KleinEquality
