/-
  LayerB/DensityMatrixHonestN.lean — Honest n-qubit density matrices.

  ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
  CONTEXT — n-DIMENSIONAL EXTENSION OF THE HONEST FIX

  `LayerB/DensityMatrixHonest.lean` corrected the qubit (n=2) density-matrix
  type by enforcing trace-1 and PSD as TYPE FIELDS rather than docstring
  claims. This file extends that fix to ARBITRARY DIMENSION.

  An honest n-qubit density matrix is a real symmetric n×n matrix that is
  positive semidefinite and has trace 1. We bundle these constraints into
  a structure whose fields are the constraints themselves, so an
  `(M, hSymm, hTrace, hPSD)` term cannot be constructed unless M actually
  is a density matrix.

  We use Mathlib's `Matrix.PosSemidef` (defined for any star-ring; on ℝ
  with the trivial star this coincides with the usual notion: M = Mᵀ
  and ∀ v, vᵀ · M · v ≥ 0).

  ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
  WHAT THIS FILE PROVES

  (1) `DensityMatrixN n` — the structure with four fields:
        M       : Matrix (Fin n) (Fin n) ℝ
        hSymm   : M.IsSymm
        hTrace  : trace M = 1
        hPSD    : M.PosSemidef

  (2) `pure` : a constructor turning a unit-norm vector v into the
      pure-state density matrix |v⟩⟨v| = vecMulVec v v. We prove
      symmetry, trace = ‖v‖² = 1, and PSD (as the outer product of a
      real vector with itself).

  (3) `pathological_zero_rejected` and `pathological_neg_diag_rejected`:
      examples of matrices the type rejects (zero matrix has trace 0,
      not 1; matrices with a negative diagonal entry violate PSD).

  (4) `convex_combination` : if ρ₁, ρ₂ are honest density matrices and
      0 ≤ t ≤ 1, then t • ρ₁.M + (1-t) • ρ₂.M is also an honest density
      matrix. This is convexity of the state space.

  (5) Bridge to the n=2 case: an explicit map
        toN2 : DensityMatrix2Honest (with coh_im = 0) → DensityMatrixN 2
      and its inverse on the image. Note the n=2 bridge can only be
      stated for the REAL slice (coh_im = 0); complex coherences would
      require complex Hermitian matrices, which is outside the scope
      of this honest real-symmetric extension.

  (6) `honest_density_matrix_n_master` — bundling the structural facts.

  ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
  HONEST SCOPE

  – Real symmetric matrices only. A complex Hermitian extension would
    require swapping ℝ for ℂ everywhere and using `IsHermitian` instead
    of `IsSymm`; the structural pattern is identical.
  – The n=2 bridge is to the REAL slice of `DensityMatrix2Honest`
    (where `coh_im = 0`). This is the largest honest bridge available
    without the complex-Hermitian extension.
  – For the pure-state constructor we accept any v with `v ⬝ᵥ v = 1`
    (i.e. ‖v‖² = 1 in the standard inner product on ℝⁿ).

  Zero `sorry`. Zero custom axioms.
-/
import UnifiedTheory.LayerB.DensityMatrixHonest
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.Symmetric
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Real.Star
import Mathlib.Data.Real.StarOrdered

set_option relaxedAutoImplicit false

namespace UnifiedTheory.LayerB.DensityMatrixHonestN

open Matrix

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 1: REAL-CASE LEMMAS — IsSymm ↔ IsHermitian, etc.
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    On `ℝ`, `star = id`, so the conjugate transpose is the transpose
    and `IsHermitian ↔ IsSymm`. We prove this once so the rest of the
    file can move freely between the two notions.
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

variable {n : ℕ}

/-- On `ℝ` (where `star = id` by `TrivialStar ℝ`), the conjugate
    transpose equals the transpose. -/
theorem conjTranspose_eq_transpose_real (M : Matrix (Fin n) (Fin n) ℝ) :
    Mᴴ = Mᵀ := by
  ext i j
  simp [Matrix.conjTranspose_apply, star_trivial]

/-- On `ℝ`, `IsHermitian` is the same as `IsSymm`. -/
theorem isHermitian_iff_isSymm_real (M : Matrix (Fin n) (Fin n) ℝ) :
    M.IsHermitian ↔ M.IsSymm := by
  unfold Matrix.IsHermitian Matrix.IsSymm
  rw [conjTranspose_eq_transpose_real]

theorem isSymm_to_isHermitian_real {M : Matrix (Fin n) (Fin n) ℝ}
    (h : M.IsSymm) : M.IsHermitian :=
  (isHermitian_iff_isSymm_real M).mpr h

theorem isHermitian_to_isSymm_real {M : Matrix (Fin n) (Fin n) ℝ}
    (h : M.IsHermitian) : M.IsSymm :=
  (isHermitian_iff_isSymm_real M).mp h

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 2: THE HONEST n-DIMENSIONAL DENSITY-MATRIX TYPE
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- A **genuine n×n real density matrix.** Unlike a bare matrix, the
    fields enforce symmetry, trace-1, AND positive semi-definiteness
    as TYPE-LEVEL constraints. -/
structure DensityMatrixN (n : ℕ) where
  /-- The underlying real n×n matrix. -/
  M : Matrix (Fin n) (Fin n) ℝ
  /-- Symmetry: `Mᵀ = M` (the real version of Hermiticity). -/
  hSymm : M.IsSymm
  /-- Trace-1: probabilities sum to one. -/
  hTrace : Matrix.trace M = 1
  /-- Positive semi-definite: `vᵀ · M · v ≥ 0` for every real vector v
      (using Mathlib's `Matrix.PosSemidef`, which on ℝ unfolds to this). -/
  hPSD : M.PosSemidef

namespace DensityMatrixN

/-- Convenience: extract the dot-product PSD inequality directly. -/
theorem quadForm_nonneg (ρ : DensityMatrixN n) (v : Fin n → ℝ) :
    0 ≤ v ⬝ᵥ (ρ.M *ᵥ v) := by
  -- For real vectors, `star v = v`, so the Mathlib statement
  -- `0 ≤ star v ⬝ᵥ (M *ᵥ v)` becomes `0 ≤ v ⬝ᵥ (M *ᵥ v)`.
  have h := ρ.hPSD.dotProduct_mulVec_nonneg v
  have hstar : (star v : Fin n → ℝ) = v := by
    funext i; simp [star_trivial]
  rw [hstar] at h
  exact h

/-- Each diagonal entry of an honest density matrix is non-negative. -/
theorem diag_nonneg (ρ : DensityMatrixN n) (i : Fin n) : 0 ≤ ρ.M i i :=
  ρ.hPSD.diag_nonneg

/-- The trace of an honest density matrix is exactly 1. (Restatement.) -/
theorem trace_eq_one (ρ : DensityMatrixN n) : Matrix.trace ρ.M = 1 := ρ.hTrace

end DensityMatrixN

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 3: PATHOLOGICAL CASES ARE REJECTED
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- **The zero matrix is not a density matrix** because its trace is 0,
    not 1. -/
theorem pathological_zero_rejected :
    ¬ ∃ ρ : DensityMatrixN n, ρ.M = 0 := by
  rintro ⟨ρ, hM⟩
  have ht : Matrix.trace ρ.M = 1 := ρ.hTrace
  rw [hM] at ht
  rw [Matrix.trace_zero] at ht
  exact absurd ht (by norm_num)

/-- **A matrix with a negative diagonal entry is not a density matrix.**
    PSD forces every diagonal entry to be non-negative. -/
theorem pathological_neg_diag_rejected :
    ¬ ∃ ρ : DensityMatrixN n, ∃ i : Fin n, ρ.M i i < 0 := by
  rintro ⟨ρ, i, hneg⟩
  have hnn : 0 ≤ ρ.M i i := ρ.diag_nonneg i
  linarith

/-- **Even with the right trace, a non-PSD matrix is rejected.** Concretely,
    `I/n` has trace 1 only when scaled correctly, but a matrix like
    `diag (2, -1)` with trace 1 still fails PSD because of the negative
    entry — captured by `pathological_neg_diag_rejected`. -/
theorem pathological_trace_one_but_not_PSD :
    ¬ ∃ ρ : DensityMatrixN 2,
      ρ.M 0 0 = 2 ∧ ρ.M 1 1 = -1 := by
  rintro ⟨ρ, _, h11⟩
  have hnn : 0 ≤ ρ.M 1 1 := ρ.diag_nonneg 1
  rw [h11] at hnn
  linarith

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 4: PURE-STATE CONSTRUCTOR
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    For a unit-norm real vector v ∈ ℝⁿ, the outer product vecMulVec v v
    (i.e. the matrix M with `M i j = v i * v j`) is the rank-1
    projector |v⟩⟨v| onto the line spanned by v.
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- The outer product `vecMulVec v v` is symmetric for any real vector. -/
theorem vecMulVec_self_isSymm (v : Fin n → ℝ) :
    (Matrix.vecMulVec v v).IsSymm := by
  unfold Matrix.IsSymm
  rw [Matrix.transpose_vecMulVec]

/-- The outer product `vecMulVec v v` is positive semidefinite. (Mathlib
    has this as `posSemidef_vecMulVec_self_star`; on ℝ with trivial
    star it specializes to the bare outer product.) -/
theorem vecMulVec_self_posSemidef (v : Fin n → ℝ) :
    (Matrix.vecMulVec v v).PosSemidef := by
  have h := Matrix.posSemidef_vecMulVec_self_star (R := ℝ) (n := Fin n) v
  -- star v = v on ℝ
  have hstar : (star v : Fin n → ℝ) = v := by funext i; simp [star_trivial]
  rw [hstar] at h
  exact h

/-- **Pure-state constructor.** Given a unit-norm vector `v` (i.e.
    `v ⬝ᵥ v = 1`), `pure v hnorm` is the rank-1 projector `|v⟩⟨v|`,
    which is a genuine `DensityMatrixN n`. -/
noncomputable def pure (v : Fin n → ℝ) (hnorm : v ⬝ᵥ v = 1) :
    DensityMatrixN n where
  M := Matrix.vecMulVec v v
  hSymm := vecMulVec_self_isSymm v
  hTrace := by
    rw [Matrix.trace_vecMulVec]
    exact hnorm
  hPSD := vecMulVec_self_posSemidef v

/-- The pure-state constructor's matrix is `M i j = v i * v j`. -/
@[simp] theorem pure_apply (v : Fin n → ℝ) (hnorm : v ⬝ᵥ v = 1)
    (i j : Fin n) : (pure v hnorm).M i j = v i * v j := rfl

/-- A pure state has trace exactly 1 (this is the defining condition
    of the constructor). -/
theorem pure_trace (v : Fin n → ℝ) (hnorm : v ⬝ᵥ v = 1) :
    Matrix.trace (pure v hnorm).M = 1 := (pure v hnorm).hTrace

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 5: CONVEX COMBINATION OF DENSITY MATRICES
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    The set of density matrices is convex: if ρ₁, ρ₂ are density
    matrices and t ∈ [0,1], then t·ρ₁ + (1-t)·ρ₂ is again a density
    matrix. We prove this by combining `Matrix.PosSemidef.smul`
    and `Matrix.PosSemidef.add` from Mathlib.
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- **Convex combination of density matrices is a density matrix.** -/
noncomputable def convexCombination (ρ₁ ρ₂ : DensityMatrixN n)
    (t : ℝ) (ht_nn : 0 ≤ t) (ht_le_one : t ≤ 1) :
    DensityMatrixN n where
  M := t • ρ₁.M + (1 - t) • ρ₂.M
  hSymm := by
    have h1 : (t • ρ₁.M).IsSymm := ρ₁.hSymm.smul t
    have h2 : ((1 - t) • ρ₂.M).IsSymm := ρ₂.hSymm.smul (1 - t)
    exact h1.add h2
  hTrace := by
    rw [Matrix.trace_add, Matrix.trace_smul, Matrix.trace_smul,
        ρ₁.hTrace, ρ₂.hTrace]
    -- t • 1 + (1-t) • 1 = 1
    simp [smul_eq_mul]
  hPSD := by
    have hone_minus : (0 : ℝ) ≤ 1 - t := by linarith
    have h1 : (t • ρ₁.M).PosSemidef := ρ₁.hPSD.smul ht_nn
    have h2 : ((1 - t) • ρ₂.M).PosSemidef := ρ₂.hPSD.smul hone_minus
    exact h1.add h2

/-- The convex-combination matrix is the obvious linear combination. -/
@[simp] theorem convexCombination_M (ρ₁ ρ₂ : DensityMatrixN n)
    (t : ℝ) (ht_nn : 0 ≤ t) (ht_le_one : t ≤ 1) :
    (convexCombination ρ₁ ρ₂ t ht_nn ht_le_one).M =
      t • ρ₁.M + (1 - t) • ρ₂.M := rfl

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 6: BRIDGE TO THE n=2 HONEST DENSITY MATRIX
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    The 2×2 honest type uses the parameterization

        ρ = [[p₁, c_re], [c_re, p₂]]

    (with c_im = 0 in the real-symmetric slice). This is exactly the
    matrix shape captured by DensityMatrixN 2. We give the bridge map
    in the real slice; complex Hermitian extension would carry c_im
    additionally and is outside the honest scope.
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

open UnifiedTheory.LayerB.DensityMatrixHonest

/-- **The 2×2 matrix arising from a 2-state honest density matrix's
    real slice (coh_im = 0).** -/
def matrixOf2 (ρ : DensityMatrix2Honest) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![ρ.p₁, ρ.coh_re; ρ.coh_re, ρ.p₂]

@[simp] theorem matrixOf2_00 (ρ : DensityMatrix2Honest) :
    matrixOf2 ρ 0 0 = ρ.p₁ := rfl
@[simp] theorem matrixOf2_01 (ρ : DensityMatrix2Honest) :
    matrixOf2 ρ 0 1 = ρ.coh_re := rfl
@[simp] theorem matrixOf2_10 (ρ : DensityMatrix2Honest) :
    matrixOf2 ρ 1 0 = ρ.coh_re := rfl
@[simp] theorem matrixOf2_11 (ρ : DensityMatrix2Honest) :
    matrixOf2 ρ 1 1 = ρ.p₂ := rfl

theorem matrixOf2_isSymm (ρ : DensityMatrix2Honest) :
    (matrixOf2 ρ).IsSymm := by
  unfold Matrix.IsSymm
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

theorem matrixOf2_trace (ρ : DensityMatrix2Honest) :
    Matrix.trace (matrixOf2 ρ) = 1 := by
  rw [Matrix.trace_fin_two]
  change ρ.p₁ + ρ.p₂ = 1
  exact ρ.htrace

/-- The PSD claim for the bridge matrix uses the standard 2×2 fact:
    a real symmetric 2×2 matrix is PSD iff diagonal entries are ≥ 0
    AND determinant is ≥ 0. The honest type guarantees both
    (`hp₁_nn`, `hp₂_nn`, `hPSD` with `coh_im = 0`). -/
theorem matrixOf2_posSemidef (ρ : DensityMatrix2Honest)
    (hcim : ρ.coh_im = 0) : (matrixOf2 ρ).PosSemidef := by
  -- Use the dotProduct characterization.
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg ?_ ?_
  · -- Hermitian: on ℝ this is symmetry.
    exact isSymm_to_isHermitian_real (matrixOf2_isSymm ρ)
  · intro v
    -- Compute v ⬝ᵥ (M *ᵥ v) explicitly.
    have hexpand : (star v) ⬝ᵥ (matrixOf2 ρ *ᵥ v)
      = ρ.p₁ * v 0 ^ 2 + 2 * ρ.coh_re * v 0 * v 1 + ρ.p₂ * v 1 ^ 2 := by
      simp [dotProduct, Matrix.mulVec, matrixOf2, Fin.sum_univ_two,
            star_trivial, mul_comm, mul_assoc]
      ring
    rw [hexpand]
    -- This is non-negative because, combining hp₁_nn, hp₂_nn, hPSD
    -- (with coh_im = 0): the discriminant 4·c² - 4·p₁·p₂ ≤ 0, so the
    -- quadratic form in (v 0, v 1) is non-negative.
    have hp1 := ρ.hp₁_nn
    have hp2 := ρ.hp₂_nn
    have hPSD := ρ.hPSD
    rw [hcim] at hPSD
    -- hPSD : ρ.coh_re² + 0² ≤ ρ.p₁ * ρ.p₂, i.e. coh_re² ≤ p₁ p₂
    have hcoh_sq_le : ρ.coh_re ^ 2 ≤ ρ.p₁ * ρ.p₂ := by
      have : ρ.coh_re ^ 2 + (0 : ℝ) ^ 2 ≤ ρ.p₁ * ρ.p₂ := hPSD
      simpa using this
    -- Standard quadratic-form argument:
    -- p₁ x² + 2c x y + p₂ y² = (sqrt p₁ x + sign(c)·sqrt p₂ y)² + (p₁ p₂ - c²) y² / p₁
    -- but we avoid sqrt by case-splitting on whether p₁ = 0 or not.
    -- Simpler: use nlinarith with the hint that (p₁ x + c y)² ≥ 0.
    -- Key identity: p₁ · (p₁ x² + 2c x y + p₂ y²) = (p₁ x + c y)² + (p₁ p₂ - c²) y²
    by_cases hp1_zero : ρ.p₁ = 0
    · -- p₁ = 0 forces c² ≤ 0 hence c = 0; quadratic reduces to p₂ y².
      have hc_sq_zero : ρ.coh_re ^ 2 ≤ 0 := by
        rw [hp1_zero] at hcoh_sq_le
        linarith
      have hc_zero : ρ.coh_re = 0 := by
        have h_nn : 0 ≤ ρ.coh_re ^ 2 := sq_nonneg _
        have hc2 : ρ.coh_re ^ 2 = 0 := le_antisymm hc_sq_zero h_nn
        exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp hc2
      rw [hp1_zero, hc_zero]
      have : (0 : ℝ) * v 0 ^ 2 + 2 * 0 * v 0 * v 1 + ρ.p₂ * v 1 ^ 2
          = ρ.p₂ * v 1 ^ 2 := by ring
      rw [this]
      exact mul_nonneg hp2 (sq_nonneg _)
    · have hp1_pos : 0 < ρ.p₁ := lt_of_le_of_ne hp1 (Ne.symm hp1_zero)
      -- Multiply-by-p₁ trick: p₁ · (quadratic) = (p₁ x + c y)² + (p₁ p₂ - c²) y².
      have key : ρ.p₁ *
          (ρ.p₁ * v 0 ^ 2 + 2 * ρ.coh_re * v 0 * v 1 + ρ.p₂ * v 1 ^ 2)
        = (ρ.p₁ * v 0 + ρ.coh_re * v 1) ^ 2
          + (ρ.p₁ * ρ.p₂ - ρ.coh_re ^ 2) * v 1 ^ 2 := by ring
      have hRHS_nn : (0 : ℝ) ≤
          (ρ.p₁ * v 0 + ρ.coh_re * v 1) ^ 2
          + (ρ.p₁ * ρ.p₂ - ρ.coh_re ^ 2) * v 1 ^ 2 := by
        have h1 : (0 : ℝ) ≤ (ρ.p₁ * v 0 + ρ.coh_re * v 1) ^ 2 := sq_nonneg _
        have h2 : (0 : ℝ) ≤ (ρ.p₁ * ρ.p₂ - ρ.coh_re ^ 2) * v 1 ^ 2 :=
          mul_nonneg (by linarith) (sq_nonneg _)
        linarith
      have hLHS_nn : (0 : ℝ) ≤ ρ.p₁ *
          (ρ.p₁ * v 0 ^ 2 + 2 * ρ.coh_re * v 0 * v 1 + ρ.p₂ * v 1 ^ 2) := by
        rw [key]; exact hRHS_nn
      -- Divide by p₁ > 0.
      have := (mul_nonneg_iff_of_pos_left hp1_pos).mp hLHS_nn
      exact this

/-- **Bridge map (n=2):** an honest 2-state density matrix with zero
    imaginary coherence lifts to an honest n-dimensional density matrix
    at n=2. -/
noncomputable def toN2 (ρ : DensityMatrix2Honest) (hcim : ρ.coh_im = 0) :
    DensityMatrixN 2 where
  M := matrixOf2 ρ
  hSymm := matrixOf2_isSymm ρ
  hTrace := matrixOf2_trace ρ
  hPSD := matrixOf2_posSemidef ρ hcim

/-- **Inverse direction (real slice):** a `DensityMatrixN 2` produces a
    `DensityMatrix2Honest` with `coh_im = 0`. The PSD condition
    `coh_re² ≤ p₁ · p₂` follows from `M.PosSemidef` applied to the test
    vector `(p₂, -coh_re)` (the standard 2×2 PSD argument). -/
noncomputable def fromN2 (ρ : DensityMatrixN 2) : DensityMatrix2Honest where
  p₁ := ρ.M 0 0
  p₂ := ρ.M 1 1
  coh_re := ρ.M 0 1
  coh_im := 0
  hp₁_nn := ρ.diag_nonneg 0
  hp₂_nn := ρ.diag_nonneg 1
  htrace := by
    have := ρ.hTrace
    rw [Matrix.trace_fin_two] at this
    exact this
  hPSD := by
    -- Need: ρ.M 0 1 ^ 2 + 0 ^ 2 ≤ ρ.M 0 0 * ρ.M 1 1.
    -- Use the PSD test vector (ρ.M 1 1, -ρ.M 0 1).
    -- Quadratic-form value:
    --   p₂² · M00 - 2 · p₂ · c · M01 + c² · M11
    -- with c = ρ.M 0 1, M00 = ρ.M 0 0, M11 = ρ.M 1 1, p₂ = ρ.M 1 1.
    -- = M11² · M00 - 2 · M11 · M01² + M01² · M11
    -- = M11 · (M00 · M11 - M01²)
    -- ≥ 0, and since M11 ≥ 0 we want M00 · M11 ≥ M01².
    -- Two cases on M11.
    have hsym := ρ.hSymm
    have hM10 : ρ.M 1 0 = ρ.M 0 1 := by
      have := hsym.apply 0 1
      simpa using this
    set v : Fin 2 → ℝ := ![ρ.M 1 1, -(ρ.M 0 1)]
    have hQ : v ⬝ᵥ (ρ.M *ᵥ v) =
        ρ.M 1 1 * (ρ.M 0 0 * ρ.M 1 1 - ρ.M 0 1 ^ 2) := by
      simp [dotProduct, Matrix.mulVec, Fin.sum_univ_two, v, hM10]
      ring
    have hQ_nn : 0 ≤ v ⬝ᵥ (ρ.M *ᵥ v) := ρ.quadForm_nonneg v
    rw [hQ] at hQ_nn
    have hM11_nn : 0 ≤ ρ.M 1 1 := ρ.diag_nonneg 1
    -- Two cases: M11 = 0 or M11 > 0.
    by_cases hM11_zero : ρ.M 1 1 = 0
    · -- If diagonal entry is 0 in a PSD matrix, the off-diagonal
      -- on that row/column must also be 0. We use the test vector
      -- (1, -t · M01) for varying t and take the limit; cleaner: use
      -- the explicit fact via a different test vector.
      -- Use v' = (-c, ε) and take ε → 0... avoid limits: use the
      -- result `v' = (1, t)` quadratic and pick t = -M01 / λ approach.
      -- Cleaner: the discriminant of the quadratic
      --   M00 · x² + 2 · M01 · x · y + M11 · y²    (in y, viewing x
      -- as parameter) ≥ 0 for ALL x,y. Picking x = M01, y = -M00:
      -- gives M00² · M11 ≥ M01² · M00 (similar). The fastest is to
      -- pick v' = (M01, -M00) directly:
      set v' : Fin 2 → ℝ := ![ρ.M 0 1, -(ρ.M 0 0)]
      have hQ' : v' ⬝ᵥ (ρ.M *ᵥ v') =
          ρ.M 0 0 * (ρ.M 0 0 * ρ.M 1 1 - ρ.M 0 1 ^ 2) := by
        simp [dotProduct, Matrix.mulVec, Fin.sum_univ_two, v', hM10]
        ring
      have hQ'_nn : 0 ≤ v' ⬝ᵥ (ρ.M *ᵥ v') := ρ.quadForm_nonneg v'
      rw [hQ'] at hQ'_nn
      -- hQ'_nn: 0 ≤ M00 · (M00 · M11 - M01²)
      -- With M11 = 0: 0 ≤ M00 · (-M01²) = -M00 · M01²
      rw [hM11_zero] at hQ'_nn
      have hM00_nn : 0 ≤ ρ.M 0 0 := ρ.diag_nonneg 0
      -- 0 ≤ M00 · (M00 · 0 - M01²) = -M00 · M01²
      -- so M00 · M01² ≤ 0, combined with M00 ≥ 0 and M01² ≥ 0 gives
      -- M00 · M01² = 0.
      have hM01_sq_nn : 0 ≤ ρ.M 0 1 ^ 2 := sq_nonneg _
      have hprod_nn : 0 ≤ ρ.M 0 0 * ρ.M 0 1 ^ 2 :=
        mul_nonneg hM00_nn hM01_sq_nn
      have hprod_le : ρ.M 0 0 * ρ.M 0 1 ^ 2 ≤ 0 := by nlinarith
      have hprod_zero : ρ.M 0 0 * ρ.M 0 1 ^ 2 = 0 :=
        le_antisymm hprod_le hprod_nn
      -- We want: M01² + 0² ≤ M00 · M11 = M00 · 0 = 0
      -- Equivalently: M01² ≤ 0, hence M01² = 0.
      -- Case split on M00.
      by_cases hM00_zero : ρ.M 0 0 = 0
      · -- Both diagonals zero. Need: M01² ≤ 0.
        -- Use yet another test vector: v'' = (1, 0).
        -- v'' ⬝ᵥ (M *ᵥ v'') = M00 = 0. Doesn't help.
        -- Use v'' = (1, t): M00 + 2·M01·t + M11·t² = 0 + 2·M01·t + 0 = 2·M01·t
        -- ≥ 0 for ALL t, hence M01 = 0.
        -- Use test vector v3 = (-M01, 1):
        set v3 : Fin 2 → ℝ := ![-(ρ.M 0 1), 1]
        have hQ3 : v3 ⬝ᵥ (ρ.M *ᵥ v3) =
            ρ.M 0 0 * (ρ.M 0 1) ^ 2 - 2 * (ρ.M 0 1) ^ 2 + ρ.M 1 1 := by
          simp [dotProduct, Matrix.mulVec, Fin.sum_univ_two, v3, hM10]
          ring
        have hQ3_nn : 0 ≤ v3 ⬝ᵥ (ρ.M *ᵥ v3) := ρ.quadForm_nonneg v3
        rw [hQ3, hM00_zero, hM11_zero] at hQ3_nn
        -- 0 ≤ 0 · M01² - 2 · M01² + 0 = -2·M01²
        have hM01_sq_le : ρ.M 0 1 ^ 2 ≤ 0 := by nlinarith
        have hM01_sq_zero : ρ.M 0 1 ^ 2 = 0 :=
          le_antisymm hM01_sq_le (sq_nonneg _)
        -- Goal: M.0,1² + 0² ≤ M.0,0 · M.1,1
        change ρ.M 0 1 ^ 2 + (0 : ℝ) ^ 2 ≤ ρ.M 0 0 * ρ.M 1 1
        rw [hM00_zero, hM11_zero, hM01_sq_zero]
        norm_num
      · -- M00 > 0. From hprod_zero, M01² = 0.
        have hM00_pos : 0 < ρ.M 0 0 := lt_of_le_of_ne hM00_nn (Ne.symm hM00_zero)
        have hM01_sq_zero : ρ.M 0 1 ^ 2 = 0 := by
          rcases mul_eq_zero.mp hprod_zero with h | h
          · exact absurd h hM00_zero
          · exact h
        change ρ.M 0 1 ^ 2 + (0 : ℝ) ^ 2 ≤ ρ.M 0 0 * ρ.M 1 1
        rw [hM11_zero, hM01_sq_zero]
        simp
    · -- M11 > 0. Then 0 ≤ M11 · (M00·M11 - M01²) implies M00·M11 ≥ M01².
      have hM11_pos : 0 < ρ.M 1 1 := lt_of_le_of_ne hM11_nn (Ne.symm hM11_zero)
      have hbracket_nn : 0 ≤ ρ.M 0 0 * ρ.M 1 1 - ρ.M 0 1 ^ 2 :=
        (mul_nonneg_iff_of_pos_left hM11_pos).mp hQ_nn
      change ρ.M 0 1 ^ 2 + (0 : ℝ) ^ 2 ≤ ρ.M 0 0 * ρ.M 1 1
      have : (0 : ℝ) ^ 2 = 0 := by norm_num
      rw [this, add_zero]
      linarith

/-- **Round trip (one direction):** `fromN2 ∘ toN2 = id` on the real
    slice (where `coh_im = 0`). -/
theorem fromN2_toN2 (ρ : DensityMatrix2Honest) (hcim : ρ.coh_im = 0) :
    let ρ' := fromN2 (toN2 ρ hcim)
    ρ'.p₁ = ρ.p₁ ∧ ρ'.p₂ = ρ.p₂ ∧
    ρ'.coh_re = ρ.coh_re ∧ ρ'.coh_im = ρ.coh_im := by
  refine ⟨rfl, rfl, rfl, ?_⟩
  exact hcim.symm

/-- **Round trip (other direction):** `toN2 ∘ fromN2` reproduces the
    same matrix entries as the original. -/
theorem toN2_fromN2_M (ρ : DensityMatrixN 2) :
    (toN2 (fromN2 ρ) rfl).M = ρ.M := by
  ext i j
  fin_cases i <;> fin_cases j
  · rfl
  · rfl
  · -- (1,0) entry: matrix is symm so M 1 0 = M 0 1
    have := ρ.hSymm.apply 0 1
    simpa [toN2, fromN2, matrixOf2] using this.symm
  · rfl

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 7: MASTER THEOREM
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- **MASTER THEOREM (HONEST n-DIMENSIONAL DENSITY MATRIX).**

    Bundling the structural properties of `DensityMatrixN`:

    (1) The zero matrix is REJECTED at every positive dimension
        (`pathological_zero_rejected`): trace 0 ≠ 1.
    (2) Matrices with negative diagonal entries are REJECTED
        (`pathological_neg_diag_rejected`): PSD forces `M i i ≥ 0`.
    (3) Pure states (rank-1 projectors from unit vectors) are valid
        density matrices (`pure`).
    (4) Convex combinations preserve the density-matrix property
        (`convexCombination`).
    (5) The real slice (coh_im = 0) of the n=2 honest type embeds into
        and out of `DensityMatrixN 2` (`toN2`, `fromN2`, `fromN2_toN2`,
        `toN2_fromN2_M`).
-/
theorem honest_density_matrix_n_master (n : ℕ) :
    -- (1) Zero rejected
    (¬ ∃ ρ : DensityMatrixN n, ρ.M = 0)
    -- (2) Negative diagonals rejected
    ∧ (¬ ∃ ρ : DensityMatrixN n, ∃ i : Fin n, ρ.M i i < 0)
    -- (3) Pure-state existence
    ∧ (∀ v : Fin n → ℝ, v ⬝ᵥ v = 1 →
        ∃ ρ : DensityMatrixN n, Matrix.trace ρ.M = 1)
    -- (4) Convex closure
    ∧ (∀ ρ₁ ρ₂ : DensityMatrixN n, ∀ t : ℝ, 0 ≤ t → t ≤ 1 →
        ∃ ρ : DensityMatrixN n,
          ρ.M = t • ρ₁.M + (1 - t) • ρ₂.M) := by
  refine ⟨pathological_zero_rejected, pathological_neg_diag_rejected,
          ?_, ?_⟩
  · intro v hnorm
    exact ⟨pure v hnorm, pure_trace v hnorm⟩
  · intro ρ₁ ρ₂ t ht_nn ht_le
    exact ⟨convexCombination ρ₁ ρ₂ t ht_nn ht_le, rfl⟩

end UnifiedTheory.LayerB.DensityMatrixHonestN
