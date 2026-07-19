/-
  LayerB/PartialTrace.lean
  ─────────────────────────

  Partial trace API for matrices over a tensor-product index type
  `m × n`.  Foundational infrastructure for the Lindblad–Uhlmann
  roadmap (Phase B3).  This file ships only the **structural** API:

    • definition of `partialTrace_right` (trace out the second factor)
      and `partialTrace_left` (trace out the first factor);
    • trace preservation: `Tr (Tr_B M) = Tr M`;
    • Hermitian preservation: `M.IsHermitian → (Tr_B M).IsHermitian`;
    • PSD preservation: `M.PosSemidef → (Tr_B M).PosSemidef`;
    • a `ComplexDensityMatrix` bridge in dimension `n_A * n_B` via
      reindexing through `finProdFinEquiv`.

  WHAT IS NOT PROVEN HERE:
    • The data-processing inequality `S(Tr_B M ‖ Tr_B N) ≤ S(M ‖ N)`
      (Lindblad–Uhlmann) is the deep theorem; this file only provides
      the structural definitions and basic invariants it will need.
    • `Tr_B` of a `PosDef` matrix is in general only `PosSemidef`
      (e.g. `|00⟩⟨00|` is rank-1, hence its partial trace is rank-1
      on the first factor).  We do not attempt the full-rank claim.

  All theorems are proved with **zero `sorry`** and **zero custom
  `axiom`**, in line with the project's standing constraint.
-/

import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Complex.Basic
import Mathlib.Analysis.Complex.Order
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Analysis.Matrix.Hermitian
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import UnifiedTheory.LayerB.RobertsonSchrodinger

set_option relaxedAutoImplicit false

namespace UnifiedTheory.LayerB.PartialTrace

open Matrix Complex
open scoped BigOperators ComplexOrder

/-! ## 1. Definitions -/

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

/-- **Partial trace over the second factor** (trace out the `n`-system).

    `(Tr_B M)_{i j} := ∑_k M_{(i,k),(j,k)}`. -/
noncomputable def partialTrace_right (M : Matrix (m × n) (m × n) ℂ) :
    Matrix m m ℂ :=
  fun i j => ∑ k, M (i, k) (j, k)

/-- **Partial trace over the first factor** (trace out the `m`-system).

    `(Tr_A M)_{i j} := ∑_k M_{(k,i),(k,j)}`. -/
noncomputable def partialTrace_left (M : Matrix (m × n) (m × n) ℂ) :
    Matrix n n ℂ :=
  fun i j => ∑ k, M (k, i) (k, j)

/-! ## 2. Trace preservation -/

/-- The trace of the right-partial trace is the trace of the original
    matrix.  In particular `Tr_B` preserves trace-1. -/
theorem trace_partialTrace_right (M : Matrix (m × n) (m × n) ℂ) :
    (partialTrace_right M).trace = M.trace := by
  unfold partialTrace_right
  rw [Matrix.trace]
  simp only [Matrix.diag_apply]
  rw [Matrix.trace]
  simp only [Matrix.diag_apply]
  rw [Fintype.sum_prod_type]

/-- Trace of the left-partial trace equals the trace of `M`. -/
theorem trace_partialTrace_left (M : Matrix (m × n) (m × n) ℂ) :
    (partialTrace_left M).trace = M.trace := by
  unfold partialTrace_left
  rw [Matrix.trace]
  simp only [Matrix.diag_apply]
  rw [Matrix.trace]
  simp only [Matrix.diag_apply]
  rw [Fintype.sum_prod_type_right]

/-! ## 3. Hermitian preservation -/

/-- The right-partial trace preserves Hermiticity. -/
theorem isHermitian_partialTrace_right
    {M : Matrix (m × n) (m × n) ℂ} (hM : M.IsHermitian) :
    (partialTrace_right M).IsHermitian := by
  ext i j
  change star ((partialTrace_right M) j i) = (partialTrace_right M) i j
  unfold partialTrace_right
  rw [star_sum]
  apply Finset.sum_congr rfl
  intro k _
  change star (M (j, k) (i, k)) = M (i, k) (j, k)
  have h := congrFun (congrFun hM (i, k)) (j, k)
  simpa [Matrix.conjTranspose_apply] using h

/-- The left-partial trace preserves Hermiticity. -/
theorem isHermitian_partialTrace_left
    {M : Matrix (m × n) (m × n) ℂ} (hM : M.IsHermitian) :
    (partialTrace_left M).IsHermitian := by
  ext i j
  change star ((partialTrace_left M) j i) = (partialTrace_left M) i j
  unfold partialTrace_left
  rw [star_sum]
  apply Finset.sum_congr rfl
  intro k _
  change star (M (k, j) (k, i)) = M (k, i) (k, j)
  have h := congrFun (congrFun hM (k, i)) (k, j)
  simpa [Matrix.conjTranspose_apply] using h

/-! ## 4. Positive-semidefiniteness preservation

For the right partial trace, the key identity is:

  `star x ⬝ᵥ (Tr_B M) *ᵥ x  =  ∑_{k₀ : n} star x̃_{k₀} ⬝ᵥ M *ᵥ x̃_{k₀}`

where for each `k₀ : n`, `x̃_{k₀} : m × n → ℂ` is the lift
`x̃_{k₀}(i, k) := if k = k₀ then x i else 0`.  Each slice is
nonnegative by `M.PosSemidef`; the sum is therefore nonnegative. -/

/-- The right-partial trace of a PSD matrix is PSD. -/
theorem posSemidef_partialTrace_right
    {M : Matrix (m × n) (m × n) ℂ} (hM : M.PosSemidef) :
    (partialTrace_right M).PosSemidef := by
  refine PosSemidef.of_dotProduct_mulVec_nonneg
      (isHermitian_partialTrace_right hM.isHermitian) ?_
  intro x
  classical
  let lift : n → (m × n) → ℂ := fun k₀ p => if p.2 = k₀ then x p.1 else 0
  -- ── Step 1: For each k₀, the quadratic form of M on `lift k₀` equals
  --    the "k₀-slice" of the partial-trace quadratic form.
  have h_slice : ∀ k₀ : n,
      star (lift k₀) ⬝ᵥ M *ᵥ (lift k₀)
        = ∑ i, ∑ j, star (x i) * M (i, k₀) (j, k₀) * x j := by
    intro k₀
    rw [dotProduct, Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.sum_eq_single k₀]
    · simp only [Pi.star_apply, lift, if_true]
      rw [Matrix.mulVec, dotProduct, Fintype.sum_prod_type]
      have h_inner : ∀ j,
          (∑ l, M (i, k₀) (j, l) * (if l = k₀ then x j else 0))
            = M (i, k₀) (j, k₀) * x j := by
        intro j
        rw [Finset.sum_eq_single k₀]
        · simp
        · intro l _ hl; simp [hl]
        · intro h; exact absurd (Finset.mem_univ _) h
      simp only [h_inner]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      ring
    · intro k _ hk
      simp only [Pi.star_apply, lift, if_neg hk, star_zero, zero_mul]
    · intro h; exact absurd (Finset.mem_univ _) h
  -- ── Step 2: Sum the slices to recover the partial-trace quadratic form.
  have h_sum_slices :
      ∑ k₀, star (lift k₀) ⬝ᵥ M *ᵥ (lift k₀)
        = star x ⬝ᵥ (partialTrace_right M) *ᵥ x := by
    simp only [h_slice]
    rw [dotProduct]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    simp only [Pi.star_apply, Matrix.mulVec, dotProduct, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    unfold partialTrace_right
    rw [Finset.sum_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    ring
  -- ── Step 3: Each slice is ≥ 0; sum of ≥ 0 is ≥ 0.
  have h_each_nn : ∀ k₀, 0 ≤ star (lift k₀) ⬝ᵥ M *ᵥ (lift k₀) :=
    fun k₀ => hM.dotProduct_mulVec_nonneg (lift k₀)
  rw [← h_sum_slices]
  exact Finset.sum_nonneg (fun k₀ _ => h_each_nn k₀)

/-- The left-partial trace of a PSD matrix is PSD. -/
theorem posSemidef_partialTrace_left
    {M : Matrix (m × n) (m × n) ℂ} (hM : M.PosSemidef) :
    (partialTrace_left M).PosSemidef := by
  refine PosSemidef.of_dotProduct_mulVec_nonneg
      (isHermitian_partialTrace_left hM.isHermitian) ?_
  intro x
  classical
  let lift : m → (m × n) → ℂ := fun k₀ p => if p.1 = k₀ then x p.2 else 0
  have h_slice : ∀ k₀ : m,
      star (lift k₀) ⬝ᵥ M *ᵥ (lift k₀)
        = ∑ i, ∑ j, star (x i) * M (k₀, i) (k₀, j) * x j := by
    intro k₀
    rw [dotProduct, Fintype.sum_prod_type_right]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.sum_eq_single k₀]
    · simp only [Pi.star_apply, lift, if_true]
      rw [Matrix.mulVec, dotProduct, Fintype.sum_prod_type_right]
      have h_inner : ∀ j,
          (∑ l, M (k₀, i) (l, j) * (if l = k₀ then x j else 0))
            = M (k₀, i) (k₀, j) * x j := by
        intro j
        rw [Finset.sum_eq_single k₀]
        · simp
        · intro l _ hl; simp [hl]
        · intro h; exact absurd (Finset.mem_univ _) h
      simp only [h_inner]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      ring
    · intro k _ hk
      simp only [Pi.star_apply, lift, if_neg hk, star_zero, zero_mul]
    · intro h; exact absurd (Finset.mem_univ _) h
  have h_sum_slices :
      ∑ k₀, star (lift k₀) ⬝ᵥ M *ᵥ (lift k₀)
        = star x ⬝ᵥ (partialTrace_left M) *ᵥ x := by
    simp only [h_slice]
    rw [dotProduct]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    simp only [Pi.star_apply, Matrix.mulVec, dotProduct, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    unfold partialTrace_left
    rw [Finset.sum_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    ring
  have h_each_nn : ∀ k₀, 0 ≤ star (lift k₀) ⬝ᵥ M *ᵥ (lift k₀) :=
    fun k₀ => hM.dotProduct_mulVec_nonneg (lift k₀)
  rw [← h_sum_slices]
  exact Finset.sum_nonneg (fun k₀ _ => h_each_nn k₀)

/-! ## 5. Bridge to `ComplexDensityMatrix` of dimension `n_A * n_B`

A `ComplexDensityMatrix (n_A * n_B)` lives on the index type
`Fin (n_A * n_B)`.  To take its partial trace we first reindex via
`finProdFinEquiv : Fin n_A × Fin n_B ≃ Fin (n_A * n_B)` using
`Matrix.submatrix`, then apply `partialTrace_right` / `_left`.

The output is a `Matrix (Fin n_A) (Fin n_A) ℂ` (resp.
`Matrix (Fin n_B) (Fin n_B) ℂ`) that is Hermitian, trace-1, and
PSD.  We do not (here) wrap it into a fresh `ComplexDensityMatrix`
because the latter requires the `trace-PSD via X†X` field, which is
implied by — but not definitionally equal to — `Matrix.PosSemidef`.
A cleaner bridge would re-prove the trace-PSD field from `PosSemidef`;
that small bookkeeping step is deferred. -/

open UnifiedTheory.LayerB.RobertsonSchrodinger

/-- **From the trace-PSD field to full `Matrix.PosSemidef`.**

    The `hTracePSD` field of `ComplexDensityMatrix` asserts
    `0 ≤ Re(Tr(ρ · X† · X))` for every n×n matrix X.  Specialising
    X to the matrix whose row `i₀` is `star x` (and all other rows
    zero) gives `Tr(ρ · X† · X) = star x ⬝ᵥ ρ *ᵥ x`, the standard
    PSD quadratic form.

    This is the same bridge proved in `OperatorEntropy` as
    `posSemidef_of_ComplexDensityMatrix`; we inline a copy here to
    avoid pulling in the spectral-functional-calculus stack just for
    the partial-trace bridge. -/
private theorem posSemidef_of_ComplexDensityMatrix {n : ℕ}
    (ρ : ComplexDensityMatrix n) : ρ.M.PosSemidef := by
  refine PosSemidef.of_dotProduct_mulVec_nonneg ρ.hHerm ?_
  intro x
  by_cases hn : Nonempty (Fin n)
  · classical
    obtain ⟨i₀⟩ := hn
    let X : Matrix (Fin n) (Fin n) ℂ :=
      Matrix.of (fun i j => if i = i₀ then star (x j) else 0)
    have hXt : X.conjTranspose =
        Matrix.of (fun i j => if j = i₀ then x i else 0) := by
      ext i j
      change star (X j i) = if j = i₀ then x i else 0
      simp only [X, Matrix.of_apply]
      split_ifs with h
      · simp
      · simp
    have hXtX : ∀ i j, (X.conjTranspose * X) i j = x i * star (x j) := by
      intro i j
      rw [Matrix.mul_apply]
      simp only [hXt, Matrix.of_apply, X]
      rw [Finset.sum_eq_single i₀]
      · simp
      · intro k _ hk; simp [hk]
      · intro h; exact absurd (Finset.mem_univ _) h
    set z : ℂ := star x ⬝ᵥ ρ.M *ᵥ x with hz_def
    have h_tr_eq : Matrix.trace (ρ.M * (X.conjTranspose * X)) = z := by
      rw [Matrix.trace]
      simp only [Matrix.diag_apply]
      have h_per : ∀ i, (ρ.M * (X.conjTranspose * X)) i i
                      = ∑ j, ρ.M i j * x j * star (x i) := by
        intro i
        rw [Matrix.mul_apply]
        apply Finset.sum_congr rfl
        intro j _
        rw [hXtX]
        ring
      simp_rw [h_per]
      rw [hz_def]
      change ∑ i, ∑ j, ρ.M i j * x j * star (x i)
           = star x ⬝ᵥ ρ.M *ᵥ x
      simp only [dotProduct, Matrix.mulVec, Pi.star_apply, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      ring
    have h_assoc :
        Matrix.trace (ρ.M * X.conjTranspose * X) = z := by
      rw [Matrix.mul_assoc]; exact h_tr_eq
    have h_psd := ρ.hTracePSD X
    rw [h_assoc] at h_psd
    have h_z_im : z.im = 0 := ρ.hHerm.im_star_dotProduct_mulVec_self x
    rw [Complex.nonneg_iff]
    exact ⟨h_psd, h_z_im.symm⟩
  · have hempty : IsEmpty (Fin n) := not_nonempty_iff.mp hn
    have h0 : star x ⬝ᵥ ρ.M *ᵥ x = 0 := by
      simp [dotProduct]
    rw [h0]

variable {n_A n_B : ℕ}

/-- Reindex a matrix indexed by `Fin (n_A * n_B)` to one indexed by
    `Fin n_A × Fin n_B` via `finProdFinEquiv`. -/
noncomputable def reindexFactor
    (M : Matrix (Fin (n_A * n_B)) (Fin (n_A * n_B)) ℂ) :
    Matrix (Fin n_A × Fin n_B) (Fin n_A × Fin n_B) ℂ :=
  M.submatrix finProdFinEquiv finProdFinEquiv

/-- Reindexing preserves Hermiticity. -/
theorem isHermitian_reindexFactor
    {M : Matrix (Fin (n_A * n_B)) (Fin (n_A * n_B)) ℂ} (hM : M.IsHermitian) :
    (reindexFactor M).IsHermitian :=
  hM.submatrix finProdFinEquiv

/-- Reindexing preserves PSD. -/
theorem posSemidef_reindexFactor
    {M : Matrix (Fin (n_A * n_B)) (Fin (n_A * n_B)) ℂ} (hM : M.PosSemidef) :
    (reindexFactor M).PosSemidef :=
  hM.submatrix finProdFinEquiv

/-- Reindexing preserves trace.  Equivalent rearrangement of the
    diagonal sum via `finProdFinEquiv`. -/
theorem trace_reindexFactor
    (M : Matrix (Fin (n_A * n_B)) (Fin (n_A * n_B)) ℂ) :
    (reindexFactor M).trace = M.trace := by
  unfold reindexFactor
  rw [Matrix.trace, Matrix.trace]
  simp only [Matrix.diag_apply, Matrix.submatrix_apply]
  exact Equiv.sum_comp finProdFinEquiv (fun i => M i i)

/-! ## 6. Partial trace of a density matrix as a matrix

These wrappers chain the bridge: reindex, then take partial trace.
They produce Hermitian, trace-1, PSD matrices on the surviving factor. -/

/-- Right partial trace of a density matrix as a raw matrix on the
    first factor `Fin n_A`. -/
noncomputable def densityPartialTrace_right
    (ρ : ComplexDensityMatrix (n_A * n_B)) :
    Matrix (Fin n_A) (Fin n_A) ℂ :=
  partialTrace_right (reindexFactor ρ.M)

/-- Left partial trace of a density matrix as a raw matrix on the
    second factor `Fin n_B`. -/
noncomputable def densityPartialTrace_left
    (ρ : ComplexDensityMatrix (n_A * n_B)) :
    Matrix (Fin n_B) (Fin n_B) ℂ :=
  partialTrace_left (reindexFactor ρ.M)

/-- The right partial trace of a density matrix is Hermitian. -/
theorem densityPartialTrace_right_isHermitian
    (ρ : ComplexDensityMatrix (n_A * n_B)) :
    (densityPartialTrace_right ρ).IsHermitian :=
  isHermitian_partialTrace_right (isHermitian_reindexFactor ρ.hHerm)

/-- The left partial trace of a density matrix is Hermitian. -/
theorem densityPartialTrace_left_isHermitian
    (ρ : ComplexDensityMatrix (n_A * n_B)) :
    (densityPartialTrace_left ρ).IsHermitian :=
  isHermitian_partialTrace_left (isHermitian_reindexFactor ρ.hHerm)

/-- The right partial trace of a density matrix has trace 1. -/
theorem densityPartialTrace_right_trace
    (ρ : ComplexDensityMatrix (n_A * n_B)) :
    (densityPartialTrace_right ρ).trace = 1 := by
  unfold densityPartialTrace_right
  rw [trace_partialTrace_right, trace_reindexFactor, ρ.hTrace]

/-- The left partial trace of a density matrix has trace 1. -/
theorem densityPartialTrace_left_trace
    (ρ : ComplexDensityMatrix (n_A * n_B)) :
    (densityPartialTrace_left ρ).trace = 1 := by
  unfold densityPartialTrace_left
  rw [trace_partialTrace_left, trace_reindexFactor, ρ.hTrace]

/-- The right partial trace of a density matrix is PSD. -/
theorem densityPartialTrace_right_posSemidef
    (ρ : ComplexDensityMatrix (n_A * n_B)) :
    (densityPartialTrace_right ρ).PosSemidef :=
  posSemidef_partialTrace_right
    (posSemidef_reindexFactor (posSemidef_of_ComplexDensityMatrix ρ))

/-- The left partial trace of a density matrix is PSD. -/
theorem densityPartialTrace_left_posSemidef
    (ρ : ComplexDensityMatrix (n_A * n_B)) :
    (densityPartialTrace_left ρ).PosSemidef :=
  posSemidef_partialTrace_left
    (posSemidef_reindexFactor (posSemidef_of_ComplexDensityMatrix ρ))

end UnifiedTheory.LayerB.PartialTrace
