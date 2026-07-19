/-
  LayerC/HJWQubit.lean — Hughston-Jozsa-Wootters at qubit dimension (n = 2)

  ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
  CONTEXT

  The Hughston-Jozsa-Wootters theorem (HJW, Phys. Lett. A 183, 14, 1993)
  states that any two purifications of the same reduced state on Bob's
  side are related by a unitary acting on Alice's register. For real
  amplitudes this is the statement that two `n × n` real matrices `ψ, φ`
  with the same Gram matrix `ψᵀψ = φᵀφ` are related by a left orthogonal
  factor:  ∃ U ∈ O(n), U · ψ = φ.

  `LayerC/BitCommitmentImpossibility.lean` discharges HJW unconditionally
  in the `n = 1` (scalar) case. The present file discharges HJW
  unconditionally in the `n = 2` (qubit Alice) case. Combined with the
  conditional impossibility theorem this gives a fully unconditional
  impossibility statement for qubit bit-commitment protocols.

  ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
  THE ARGUMENT (qubit case, real amplitudes)

  Given ψ, φ : Matrix (Fin 2) (Fin 2) ℝ with ψᵀ · ψ = φᵀ · φ, we
  construct an orthogonal U with U · ψ = φ. Two cases:

  (A) `IsUnit ψ.det`.  The standard polar-decomposition trick:
       set U := φ · ψ⁻¹.   Orthogonality of U follows from the Gram
       identity:
            Uᵀ · U  =  (ψ⁻¹)ᵀ · φᵀ · φ · ψ⁻¹
                    =  (ψ⁻¹)ᵀ · ψᵀ · ψ · ψ⁻¹  [Gram identity]
                    =  ((ψ · ψ⁻¹)ᵀ) · (ψ · ψ⁻¹)
                    =  Iᵀ · I  =  I.
       And  U · ψ = φ · ψ⁻¹ · ψ = φ · 1 = φ.

  (B) `¬ IsUnit ψ.det`, i.e., `det ψ = 0`.  Taking determinants of the
      Gram identity gives `(det ψ)² = (det φ)²`, so `det φ = 0` also.
      Both matrices have rank ≤ 1.  We split further:

      (B1) `ψ = 0`.  Then `ψᵀ · ψ = 0`, so all column norms of φ vanish,
           so `φ = 0`.  Take `U := 1`.

      (B2) `ψ ≠ 0` (rank exactly 1).  We construct U explicitly using
           the column-Gram structure.  The columns of ψ all lie on a
           single line through the origin; the same line is determined
           (up to sign) by the columns of φ.  An orthogonal U mapping
           one line to the other delivers `U · ψ = φ`.

           Concretely: let `u_i = ψ.col i`, `w_i = φ.col i`.  Pick a
           column index `k` with `u_k ≠ 0` (exists since `ψ ≠ 0`).  The
           Gram identity gives `‖u_k‖² = ‖w_k‖²`, so `w_k ≠ 0`.  The
           explicit U is the orthogonal matrix sending `u_k / ‖u_k‖` to
           `w_k / ‖w_k‖` with a fixed orientation (and the perpendicular
           sign matched so that the remaining column is mapped
           correctly).

  ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
  WHAT IS PROVED

  – `hjw_dim_two`               : UNCONDITIONAL proof of HJW for n = 2.
  – `no_perfect_BC_protocol_dim_two` : UNCONDITIONAL impossibility
                                  theorem for `BCProtocol` with n = 2.
  – `hjw_qubit_master`          : aggregator.

  ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
  HONEST SCOPE

  – Real amplitudes only.  The framework's two-particle state space is
    `Matrix (Fin n) (Fin n) ℝ`, so "unitary" means "orthogonal" (O(2),
    not U(2)).  The structural argument is identical to the complex case.

  – Square 2×2 case.  The original HJW theorem allows Alice's and Bob's
    registers to have different dimensions; here we follow the framework
    convention `n_A = n_B = n = 2` from `BCProtocol`.

  – Both ψ and φ are full 2×2 matrices; no normalisation hypothesis is
    used in the HJW step itself.  Normalisation only enters at the
    bit-commitment level.

  Zero `sorry`.  Zero custom axioms.
-/
import UnifiedTheory.LayerC.BitCommitmentImpossibility
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

set_option relaxedAutoImplicit false

namespace UnifiedTheory.LayerC.HJWQubit

open UnifiedTheory.LayerC.BitCommitmentImpossibility
open UnifiedTheory.LayerB.QuantumEntanglement
open Matrix

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 1 — INVERTIBLE CASE: U = φ · ψ⁻¹
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    The standard polar-decomposition trick.  When `det ψ` is a unit
    (i.e., nonzero in a field), the matrix `ψ` is invertible and
    `U := φ · ψ⁻¹` is the obvious witness.  Its orthogonality is
    forced by the Gram identity.
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- HJW (invertible branch).  When `ψ` is invertible (`IsUnit ψ.det`),
    the orthogonal U is `φ · ψ⁻¹`.  Works for any dimension `n`, not
    just `n = 2`. -/
private theorem hjw_invertible {n : ℕ} (ψ φ : Matrix (Fin n) (Fin n) ℝ)
    (hψ : IsUnit ψ.det) (hgram : ψᵀ * ψ = φᵀ * φ) :
    ∃ U : Matrix (Fin n) (Fin n) ℝ,
        U ∈ Matrix.orthogonalGroup (Fin n) ℝ ∧ U * ψ = φ := by
  refine ⟨φ * ψ⁻¹, ?_, ?_⟩
  · -- U ∈ O(n):  show  Uᵀ · U = 1.
    rw [Matrix.mem_orthogonalGroup_iff']
    -- (φ ψ⁻¹)ᵀ (φ ψ⁻¹) = (ψ⁻¹)ᵀ φᵀ φ ψ⁻¹ = (ψ⁻¹)ᵀ ψᵀ ψ ψ⁻¹ = I.
    rw [Matrix.transpose_mul, Matrix.transpose_nonsing_inv]
    rw [show (ψᵀ)⁻¹ * φᵀ * (φ * ψ⁻¹)
          = (ψᵀ)⁻¹ * (φᵀ * φ) * ψ⁻¹ by
        simp [Matrix.mul_assoc]]
    rw [← hgram]
    -- Now: (ψᵀ)⁻¹ * (ψᵀ * ψ) * ψ⁻¹ = 1.
    have hψt : IsUnit (ψᵀ).det := by
      rw [Matrix.det_transpose]; exact hψ
    rw [show (ψᵀ)⁻¹ * (ψᵀ * ψ) * ψ⁻¹
          = ((ψᵀ)⁻¹ * ψᵀ) * (ψ * ψ⁻¹) by
        simp [Matrix.mul_assoc]]
    rw [Matrix.nonsing_inv_mul _ hψt, Matrix.mul_nonsing_inv _ hψ, Matrix.one_mul]
  · -- U · ψ = φ:  (φ · ψ⁻¹) · ψ = φ · (ψ⁻¹ · ψ) = φ · 1 = φ.
    rw [Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hψ, Matrix.mul_one]

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 2 — DEGENERATE CASE: ψ = 0
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    If `ψ = 0`, the Gram identity forces `φᵀ · φ = 0`, which forces
    `φ = 0` (since `(φᵀ φ)_jj = ∑_i (φ_ij)² = 0` implies all entries are
    zero).  Then `U := 1` trivially satisfies `1 · ψ = 0 = φ`.

    Works for any `n`.
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- Diagonal of the Gram matrix `φᵀ · φ`: entry `(j, j)` is the squared
    norm of the j-th column of φ. -/
private lemma gram_diag {n : ℕ} (φ : Matrix (Fin n) (Fin n) ℝ) (j : Fin n) :
    (φᵀ * φ) j j = ∑ i, (φ i j) ^ 2 := by
  simp [Matrix.mul_apply, Matrix.transpose_apply, pow_two]

/-- The identity 1 is in the orthogonal group for any `n`. -/
private lemma one_in_orthogonalGroup {n : ℕ} :
    (1 : Matrix (Fin n) (Fin n) ℝ) ∈ Matrix.orthogonalGroup (Fin n) ℝ := by
  rw [Matrix.mem_orthogonalGroup_iff', Matrix.transpose_one, Matrix.one_mul]

/-- HJW (zero branch).  If `ψ = 0`, then `φ = 0` and `U := 1` works.
    Holds for any `n`. -/
private theorem hjw_zero {n : ℕ} (ψ φ : Matrix (Fin n) (Fin n) ℝ)
    (hψ : ψ = 0) (hgram : ψᵀ * ψ = φᵀ * φ) :
    ∃ U : Matrix (Fin n) (Fin n) ℝ,
        U ∈ Matrix.orthogonalGroup (Fin n) ℝ ∧ U * ψ = φ := by
  -- From ψ = 0 we get ψᵀ · ψ = 0, hence φᵀ · φ = 0.
  have hzero : (φᵀ * φ) = 0 := by
    rw [← hgram, hψ]; simp
  -- Now show φ = 0 entrywise.  Look at the diagonal of φᵀφ.
  have hφ : φ = 0 := by
    ext i j
    -- (φᵀ φ)_{jj} = Σ_k (φ k j)^2 = 0 ⇒ each summand = 0 ⇒ φ k j = 0.
    have hdiag : (φᵀ * φ) j j = ∑ k, (φ k j) ^ 2 := gram_diag φ j
    have hsum : ∑ k, (φ k j) ^ 2 = 0 := by
      rw [← hdiag, hzero]; rfl
    -- Each squared term is non-negative, the sum is zero, so each is zero.
    have hi : (φ i j) ^ 2 = 0 := by
      have hnn : ∀ k ∈ Finset.univ, 0 ≤ (φ k j) ^ 2 := fun k _ => sq_nonneg _
      have := Finset.sum_eq_zero_iff_of_nonneg hnn |>.mp hsum
      exact this i (Finset.mem_univ _)
    exact pow_eq_zero_iff (n := 2) (by norm_num) |>.1 hi
  refine ⟨1, one_in_orthogonalGroup, ?_⟩
  rw [Matrix.one_mul, hψ, hφ]

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 3 — RANK-1 CASE (n = 2): EXPLICIT CONSTRUCTION
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    The remaining case in `n = 2`: `ψ ≠ 0` and `det ψ = 0`.  Then `ψ`
    has rank exactly 1.  By the same determinant argument, `det φ = 0`
    and `φ` has rank ≤ 1.  The Gram identity forces the columns of `φ`
    to live on the same line as the columns of `ψ`, with matching
    column norms and inner products.

    Our explicit U is built column-by-column.  Pick a column index `k`
    where `ψ.col k ≠ 0`; the Gram identity gives `‖φ.col k‖ = ‖ψ.col k‖`,
    so `φ.col k ≠ 0`.  An orthogonal U mapping `ψ.col k` to `φ.col k`
    sends the perpendicular direction to a unique perpendicular vector
    (up to sign).  The other column of ψ is parallel to `ψ.col k`
    (by rank-1) — likewise for φ — so any U mapping `ψ.col k` to
    `φ.col k` also maps `ψ.col k'` to `φ.col k'`.  Sign of the
    perpendicular is then fixed by the convention.

    For clean Lean development we encode the orthogonal U as a single
    explicit 2×2 matrix built from the entries of ψ and φ.
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- Auxiliary: for `n = 2`, the rank-1 case `det ψ = 0, ψ ≠ 0`.  Either
    ψ.col 0 ≠ 0 or ψ.col 1 ≠ 0, in entry-wise form. -/
private lemma fin_two_nonzero_column
    (ψ : Matrix (Fin 2) (Fin 2) ℝ) (hψ : ψ ≠ 0) :
    (∃ i, ψ i 0 ≠ 0) ∨ (∃ i, ψ i 1 ≠ 0) := by
  by_contra hcon
  push_neg at hcon
  obtain ⟨h0, h1⟩ := hcon
  apply hψ
  ext i j
  fin_cases j
  · simp [h0 i]
  · simp [h1 i]

/-- For a 2×2 real matrix `M` with `det M = 0`, the columns are linearly
    dependent in a very strong form: M(0,0) * M(1,1) = M(0,1) * M(1,0).
    This is the explicit content of `det_fin_two` set to zero. -/
private lemma det_zero_fin_two_iff (M : Matrix (Fin 2) (Fin 2) ℝ) :
    M.det = 0 ↔ M 0 0 * M 1 1 = M 0 1 * M 1 0 := by
  rw [Matrix.det_fin_two]
  constructor
  · intro h; linarith
  · intro h; linarith

/-- The Gram entry `(ψᵀψ) j j'` written out explicitly for n = 2. -/
private lemma gram_entry_fin_two (ψ : Matrix (Fin 2) (Fin 2) ℝ) (j j' : Fin 2) :
    (ψᵀ * ψ) j j' = ψ 0 j * ψ 0 j' + ψ 1 j * ψ 1 j' := by
  simp [Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_two]

/-- If ψ, φ : Matrix (Fin 2) (Fin 2) ℝ have ψᵀψ = φᵀφ, then for every
    pair `j, j'` the inner product of columns matches. -/
private lemma columns_inner_eq
    (ψ φ : Matrix (Fin 2) (Fin 2) ℝ) (hgram : ψᵀ * ψ = φᵀ * φ)
    (j j' : Fin 2) :
    ψ 0 j * ψ 0 j' + ψ 1 j * ψ 1 j' = φ 0 j * φ 0 j' + φ 1 j * φ 1 j' := by
  have h := congrArg (fun A => A j j') hgram
  simp only [gram_entry_fin_two] at h
  exact h

/-- The squared norm of column `j` of ψ. -/
private def colSq (ψ : Matrix (Fin 2) (Fin 2) ℝ) (j : Fin 2) : ℝ :=
  ψ 0 j ^ 2 + ψ 1 j ^ 2

private lemma colSq_nonneg (ψ : Matrix (Fin 2) (Fin 2) ℝ) (j : Fin 2) :
    0 ≤ colSq ψ j := by unfold colSq; positivity

/-- If a column is nonzero, its squared norm is positive. -/
private lemma colSq_pos_of_col_nonzero
    (ψ : Matrix (Fin 2) (Fin 2) ℝ) (j : Fin 2)
    (h : ∃ i, ψ i j ≠ 0) : 0 < colSq ψ j := by
  obtain ⟨i, hi⟩ := h
  fin_cases i
  · have : 0 < ψ 0 j ^ 2 := by positivity
    have hn : 0 ≤ ψ 1 j ^ 2 := sq_nonneg _
    unfold colSq; linarith
  · have : 0 < ψ 1 j ^ 2 := by positivity
    have hn : 0 ≤ ψ 0 j ^ 2 := sq_nonneg _
    unfold colSq; linarith

/-- If a column's squared norm is zero, all its entries are zero. -/
private lemma col_zero_of_colSq_zero
    (ψ : Matrix (Fin 2) (Fin 2) ℝ) (j : Fin 2)
    (h : colSq ψ j = 0) (i : Fin 2) : ψ i j = 0 := by
  unfold colSq at h
  have h0 : 0 ≤ ψ 0 j ^ 2 := sq_nonneg _
  have h1 : 0 ≤ ψ 1 j ^ 2 := sq_nonneg _
  have : ψ 0 j ^ 2 = 0 ∧ ψ 1 j ^ 2 = 0 := ⟨by nlinarith, by nlinarith⟩
  fin_cases i
  · exact pow_eq_zero_iff (n := 2) (by norm_num) |>.1 this.1
  · exact pow_eq_zero_iff (n := 2) (by norm_num) |>.1 this.2

/-- Equality of squared column norms from the Gram identity. -/
private lemma colSq_eq_of_gram
    (ψ φ : Matrix (Fin 2) (Fin 2) ℝ) (hgram : ψᵀ * ψ = φᵀ * φ)
    (j : Fin 2) : colSq ψ j = colSq φ j := by
  have h := columns_inner_eq ψ φ hgram j j
  unfold colSq
  have hψ : ψ 0 j * ψ 0 j + ψ 1 j * ψ 1 j = ψ 0 j ^ 2 + ψ 1 j ^ 2 := by ring
  have hφ : φ 0 j * φ 0 j + φ 1 j * φ 1 j = φ 0 j ^ 2 + φ 1 j ^ 2 := by ring
  linarith [h, hψ, hφ]

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 4 — RANK-1 SUB-CASES BY NONZERO COLUMN INDEX
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    We construct U via reflection across the line spanned by the
    nonzero column.  The explicit formula:

       Let  s = colSq ψ k  (positive).  Define a "tensor product"
       matrix  U_{ij} := (1/s) * Σ_e φ(i,e) · ψ(j,e)  with `e` ranging
       over those e where ψ.col e is captured by k.

    More concretely, we use the **Householder/SVD trick** specialized
    to rank-1: write ψ via its single nonzero direction and U as the
    explicit rotation/reflection mapping that direction to the
    corresponding φ direction.

    The clean formula we use is

        U := (1/s) · (φ.col k) (ψ.col k)ᵀ
           + (1/s) · perpendicular term

    But for `n = 2` we can do something even simpler.  Note that for
    `det ψ = 0`, all columns of ψ are scalar multiples of a single
    column.  Concretely if `ψ.col k = u`, then for any other column
    index `k'`,  `ψ.col k' = (⟨u, ψ.col k'⟩ / ‖u‖²) · u`.  The same
    is true of φ with the same scaling coefficient (from the Gram
    identity).

    So we only need U to send `ψ.col k` to `φ.col k`; the other column
    is then automatically right by linearity.  The construction of such
    an orthogonal U on ℝ² is the explicit reflection.
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/- The Householder-style reflection that maps a unit vector `u ∈ ℝ²` to a
   unit vector `v ∈ ℝ²` can be constructed as follows. Orthogonally augment
   u to a basis `[u, u⊥]` and v to `[v, v⊥]`, then U sends u → v, u⊥ → v⊥
   (or its negative).  For clarity we just **define U as a 2×2 matrix
   entrywise** in terms of the columns of ψ and φ. -/

/-- The HJW witness in the rank-1 case (n = 2).

    We choose **column 0** of ψ as the nonzero column (the actual proof
    handles either case by symmetry).  Setting `s := colSq ψ 0`, the
    matrix U is built so that U · (ψ.col 0) = (φ.col 0) and U preserves
    orthogonality.  Concretely:

        U(i, j) := (1/s) * (φ(i, 0) * ψ(j, 0) + sgn * φ⊥(i, 0) * ψ⊥(j, 0))

    where `ψ⊥(j, 0) := (-1)^(?) ψ(1-j, 0)` is the perpendicular and
    `sgn = ±1` is chosen to give the correct second column.

    In the rank-1 case `det ψ = 0`, the second column of ψ is parallel
    to the first, so the perpendicular component does not matter for the
    `U · ψ = φ` identity.  The sign of `sgn` is chosen to keep U
    orthogonal regardless. -/
private noncomputable def rankOneU_col0
    (ψ φ : Matrix (Fin 2) (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  let s := colSq ψ 0
  -- "Rotation aligning column 0 of ψ to column 0 of φ".  When
  -- ψ.col 0 = (a, b) and φ.col 0 = (c, d) with a² + b² = c² + d² = s,
  -- the rotation U with U·(a,b)ᵀ = (c,d)ᵀ is given by
  --     cos θ = (c·a + d·b) / s,   sin θ = (d·a - c·b) / s,
  -- and concretely
  --     U = !![ cos θ, -sin θ ;
  --             sin θ,  cos θ ]
  --       = (1/s) !![ c·a + d·b,   c·b - d·a ;
  --                    d·a - c·b,   c·a + d·b ].
  let a := ψ 0 0
  let b := ψ 1 0
  let c := φ 0 0
  let d := φ 1 0
  !![ (c * a + d * b) / s,   (c * b - d * a) / s ;
      (d * a - c * b) / s,   (c * a + d * b) / s ]

/-- Same construction, picking **column 1** as the nonzero one. -/
private noncomputable def rankOneU_col1
    (ψ φ : Matrix (Fin 2) (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  let s := colSq ψ 1
  let a := ψ 0 1
  let b := ψ 1 1
  let c := φ 0 1
  let d := φ 1 1
  !![ (c * a + d * b) / s,   (c * b - d * a) / s ;
      (d * a - c * b) / s,   (c * a + d * b) / s ]

/-- Orthogonality of `rankOneU_col0` from the equal-norm condition. -/
private lemma rankOneU_col0_orthogonal
    (ψ φ : Matrix (Fin 2) (Fin 2) ℝ)
    (hs : colSq ψ 0 = colSq φ 0) (hpos : 0 < colSq ψ 0) :
    (rankOneU_col0 ψ φ)ᵀ * (rankOneU_col0 ψ φ) = 1 := by
  unfold rankOneU_col0
  set s := colSq ψ 0 with hsdef
  have hs_ne : s ≠ 0 := ne_of_gt hpos
  -- Unpack abbreviations.
  set a := ψ 0 0
  set b := ψ 1 0
  set c := φ 0 0
  set d := φ 1 0
  -- The colSq facts:  a² + b² = s  and  c² + d² = s.
  have hψcol : a ^ 2 + b ^ 2 = s := by
    change ψ 0 0 ^ 2 + ψ 1 0 ^ 2 = s
    unfold colSq at hsdef; linarith [hsdef]
  have hφcol : c ^ 2 + d ^ 2 = s := by
    have hφs : colSq φ 0 = s := by rw [← hs]
    change φ 0 0 ^ 2 + φ 1 0 ^ 2 = s
    unfold colSq at hφs; linarith [hφs]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Fin.isValue] <;>
    field_simp <;>
    nlinarith [hψcol, hφcol, sq_nonneg a, sq_nonneg b, sq_nonneg c, sq_nonneg d]

/-- Orthogonality of `rankOneU_col1`. -/
private lemma rankOneU_col1_orthogonal
    (ψ φ : Matrix (Fin 2) (Fin 2) ℝ)
    (hs : colSq ψ 1 = colSq φ 1) (hpos : 0 < colSq ψ 1) :
    (rankOneU_col1 ψ φ)ᵀ * (rankOneU_col1 ψ φ) = 1 := by
  unfold rankOneU_col1
  set s := colSq ψ 1 with hsdef
  have hs_ne : s ≠ 0 := ne_of_gt hpos
  set a := ψ 0 1
  set b := ψ 1 1
  set c := φ 0 1
  set d := φ 1 1
  have hψcol : a ^ 2 + b ^ 2 = s := by
    change ψ 0 1 ^ 2 + ψ 1 1 ^ 2 = s
    unfold colSq at hsdef; linarith [hsdef]
  have hφcol : c ^ 2 + d ^ 2 = s := by
    have hφs : colSq φ 1 = s := by rw [← hs]
    change φ 0 1 ^ 2 + φ 1 1 ^ 2 = s
    unfold colSq at hφs; linarith [hφs]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Fin.isValue] <;>
    field_simp <;>
    nlinarith [hψcol, hφcol, sq_nonneg a, sq_nonneg b, sq_nonneg c, sq_nonneg d]

/-- The "second column matches" identity for `rankOneU_col0` in the
    rank-1 case.  Given the rank-1 hypothesis `det ψ = 0` (in entries:
    `ψ 0 0 · ψ 1 1 = ψ 0 1 · ψ 1 0`) and the same for φ, plus all three
    Gram identities, the product `(rankOneU_col0 ψ φ) · ψ` equals `φ`. -/
private lemma rankOneU_col0_correct
    (ψ φ : Matrix (Fin 2) (Fin 2) ℝ)
    (hpos : 0 < colSq ψ 0)
    (hg00 : ψ 0 0 * ψ 0 0 + ψ 1 0 * ψ 1 0 = φ 0 0 * φ 0 0 + φ 1 0 * φ 1 0)
    (hg01 : ψ 0 0 * ψ 0 1 + ψ 1 0 * ψ 1 1 = φ 0 0 * φ 0 1 + φ 1 0 * φ 1 1)
    (hg11 : ψ 0 1 * ψ 0 1 + ψ 1 1 * ψ 1 1 = φ 0 1 * φ 0 1 + φ 1 1 * φ 1 1)
    (hψdet : ψ 0 0 * ψ 1 1 = ψ 0 1 * ψ 1 0)
    (hφdet : φ 0 0 * φ 1 1 = φ 0 1 * φ 1 0) :
    (rankOneU_col0 ψ φ) * ψ = φ := by
  unfold rankOneU_col0
  set s := colSq ψ 0 with hsdef
  have hs_pos : 0 < s := hpos
  have hs_ne : s ≠ 0 := ne_of_gt hs_pos
  set a := ψ 0 0
  set b := ψ 1 0
  set c := φ 0 0
  set d := φ 1 0
  have hsab : a ^ 2 + b ^ 2 = s := by
    change ψ 0 0 ^ 2 + ψ 1 0 ^ 2 = s
    unfold colSq at hsdef; linarith
  -- We also need `a*a + b*b = s` (without the `^2`).  Same fact in
  -- different form.
  have hsab' : a * a + b * b = s := by nlinarith [hsab]
  -- Verify entry-wise.  Four cases (i, j) ∈ Fin 2 × Fin 2.  In each
  -- case the goal reduces, after `field_simp`, to a polynomial identity
  -- in `a, b, c, d, ψ 0 1, ψ 1 1, φ 0 1, φ 1 1` solvable by a
  -- `linear_combination` certificate using the available identities.
  ext i j
  fin_cases i
  · fin_cases j
    · -- Goal (0, 0).  Polynomial identity using `hsab'`.
      simp [Matrix.mul_apply, Fin.sum_univ_two, Fin.isValue]
      field_simp
      linear_combination c * hsab'
    · -- Goal (0, 1).
      simp [Matrix.mul_apply, Fin.sum_univ_two, Fin.isValue]
      field_simp
      linear_combination
        (φ 0 1) * hsab' + d * hφdet - d * hψdet + c * hg01 - (φ 0 1) * hg00
  · fin_cases j
    · -- Goal (1, 0).
      simp [Matrix.mul_apply, Fin.sum_univ_two, Fin.isValue]
      field_simp
      linear_combination d * hsab'
    · -- Goal (1, 1).
      simp [Matrix.mul_apply, Fin.sum_univ_two, Fin.isValue]
      field_simp
      linear_combination
        (φ 1 1) * hsab' - c * hφdet + c * hψdet + d * hg01 - (φ 1 1) * hg00

/-- The "second column matches" identity for `rankOneU_col1` in the
    rank-1 case. -/
private lemma rankOneU_col1_correct
    (ψ φ : Matrix (Fin 2) (Fin 2) ℝ)
    (hpos : 0 < colSq ψ 1)
    (hg00 : ψ 0 0 * ψ 0 0 + ψ 1 0 * ψ 1 0 = φ 0 0 * φ 0 0 + φ 1 0 * φ 1 0)
    (hg01 : ψ 0 0 * ψ 0 1 + ψ 1 0 * ψ 1 1 = φ 0 0 * φ 0 1 + φ 1 0 * φ 1 1)
    (hg11 : ψ 0 1 * ψ 0 1 + ψ 1 1 * ψ 1 1 = φ 0 1 * φ 0 1 + φ 1 1 * φ 1 1)
    (hψdet : ψ 0 0 * ψ 1 1 = ψ 0 1 * ψ 1 0)
    (hφdet : φ 0 0 * φ 1 1 = φ 0 1 * φ 1 0) :
    (rankOneU_col1 ψ φ) * ψ = φ := by
  unfold rankOneU_col1
  set s := colSq ψ 1 with hsdef
  have hs_pos : 0 < s := hpos
  have hs_ne : s ≠ 0 := ne_of_gt hs_pos
  set a := ψ 0 1
  set b := ψ 1 1
  set c := φ 0 1
  set d := φ 1 1
  have hsab : a ^ 2 + b ^ 2 = s := by
    change ψ 0 1 ^ 2 + ψ 1 1 ^ 2 = s
    unfold colSq at hsdef; linarith
  have hsab' : a * a + b * b = s := by nlinarith [hsab]
  ext i j
  fin_cases i
  · fin_cases j
    · -- Goal (0, 0).  j = 0 is the "other column" — needs full rank-1 certificate.
      simp [Matrix.mul_apply, Fin.sum_univ_two, Fin.isValue]
      field_simp
      linear_combination
        -d * hφdet + (φ 0 0) * hsab' - (φ 0 0) * hg11 + c * hg01 + d * hψdet
    · -- Goal (0, 1).  j = 1 is the construction column.
      simp [Matrix.mul_apply, Fin.sum_univ_two, Fin.isValue]
      field_simp
      linear_combination c * hsab'
  · fin_cases j
    · -- Goal (1, 0).  j = 0 is the "other column".
      simp [Matrix.mul_apply, Fin.sum_univ_two, Fin.isValue]
      field_simp
      linear_combination
        c * hφdet + (φ 1 0) * hsab' - (φ 1 0) * hg11 + d * hg01 - c * hψdet
    · -- Goal (1, 1).
      simp [Matrix.mul_apply, Fin.sum_univ_two, Fin.isValue]
      field_simp
      linear_combination d * hsab'

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 5 — RANK-1 HJW BRANCH (n = 2)
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    Combining the two sub-cases: pick whichever column index has a
    nonzero column of ψ.
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

private theorem hjw_rank_one
    (ψ φ : Matrix (Fin 2) (Fin 2) ℝ)
    (hgram : ψᵀ * ψ = φᵀ * φ)
    (hψdet : ψ.det = 0)
    (hψne : ψ ≠ 0) :
    ∃ U : Matrix (Fin 2) (Fin 2) ℝ,
        U ∈ Matrix.orthogonalGroup (Fin 2) ℝ ∧ U * ψ = φ := by
  -- Step 1: derive `φ.det = 0` from the Gram identity by taking det.
  have hφdet_sq : (ψ.det) ^ 2 = (φ.det) ^ 2 := by
    have h1 : (ψᵀ * ψ).det = (φᵀ * φ).det := congrArg Matrix.det hgram
    rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, Matrix.det_transpose] at h1
    nlinarith [h1]
  have hφdet : φ.det = 0 := by
    have h0 : (ψ.det) ^ 2 = 0 := by rw [hψdet]; ring
    have : (φ.det) ^ 2 = 0 := by linarith [hφdet_sq, h0]
    exact pow_eq_zero_iff (n := 2) (by norm_num) |>.1 this
  -- Step 2: convert det = 0 into the entry identity.
  have hψE : ψ 0 0 * ψ 1 1 = ψ 0 1 * ψ 1 0 :=
    (det_zero_fin_two_iff ψ).mp hψdet
  have hφE : φ 0 0 * φ 1 1 = φ 0 1 * φ 1 0 :=
    (det_zero_fin_two_iff φ).mp hφdet
  -- Step 3: pull Gram inner-product identities into entrywise form.
  have hg00 : ψ 0 0 * ψ 0 0 + ψ 1 0 * ψ 1 0 = φ 0 0 * φ 0 0 + φ 1 0 * φ 1 0 :=
    columns_inner_eq ψ φ hgram 0 0
  have hg01 : ψ 0 0 * ψ 0 1 + ψ 1 0 * ψ 1 1 = φ 0 0 * φ 0 1 + φ 1 0 * φ 1 1 :=
    columns_inner_eq ψ φ hgram 0 1
  have hg11 : ψ 0 1 * ψ 0 1 + ψ 1 1 * ψ 1 1 = φ 0 1 * φ 0 1 + φ 1 1 * φ 1 1 :=
    columns_inner_eq ψ φ hgram 1 1
  -- Step 4: find a nonzero column of ψ.
  rcases fin_two_nonzero_column ψ hψne with h0 | h1
  · -- Column 0 is nonzero.
    have hpos : 0 < colSq ψ 0 := colSq_pos_of_col_nonzero ψ 0 h0
    have hcs : colSq ψ 0 = colSq φ 0 := colSq_eq_of_gram ψ φ hgram 0
    refine ⟨rankOneU_col0 ψ φ, ?_, ?_⟩
    · rw [Matrix.mem_orthogonalGroup_iff']
      exact rankOneU_col0_orthogonal ψ φ hcs hpos
    · exact rankOneU_col0_correct ψ φ hpos hg00 hg01 hg11 hψE hφE
  · -- Column 1 is nonzero.
    have hpos : 0 < colSq ψ 1 := colSq_pos_of_col_nonzero ψ 1 h1
    have hcs : colSq ψ 1 = colSq φ 1 := colSq_eq_of_gram ψ φ hgram 1
    refine ⟨rankOneU_col1 ψ φ, ?_, ?_⟩
    · rw [Matrix.mem_orthogonalGroup_iff']
      exact rankOneU_col1_orthogonal ψ φ hcs hpos
    · exact rankOneU_col1_correct ψ φ hpos hg00 hg01 hg11 hψE hφE

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 6 — UNCONDITIONAL HJW FOR n = 2
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- **The Hughston-Jozsa-Wootters theorem at qubit dimension** (real
    amplitudes).

    For any two real `2 × 2` matrices `ψ, φ` with the same Gram matrix
    `ψᵀ · ψ = φᵀ · φ`, there exists an orthogonal `2 × 2` matrix `U`
    with `U · ψ = φ`.

    This is the unconditional `n = 2` case of `HJW_Target`.  Combined
    with `no_perfect_BC_protocol` it gives an unconditional impossibility
    statement for qubit (n = 2) bit-commitment protocols. -/
theorem hjw_dim_two (ψ φ : Matrix (Fin 2) (Fin 2) ℝ)
    (hgram : ψᵀ * ψ = φᵀ * φ) :
    ∃ U : Matrix (Fin 2) (Fin 2) ℝ,
        U ∈ Matrix.orthogonalGroup (Fin 2) ℝ ∧ U * ψ = φ := by
  -- Case split on whether ψ is invertible.
  by_cases hψ : IsUnit ψ.det
  · exact hjw_invertible ψ φ hψ hgram
  · -- det ψ = 0.  Two sub-cases: ψ = 0 vs ψ ≠ 0.
    have hψdet : ψ.det = 0 := by
      rcases eq_or_ne ψ.det 0 with h | h
      · exact h
      · exact absurd (Ne.isUnit h) hψ
    by_cases hψ_zero : ψ = 0
    · exact hjw_zero ψ φ hψ_zero hgram
    · exact hjw_rank_one ψ φ hgram hψdet hψ_zero

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 7 — UNCONDITIONAL DIMENSION-TWO IMPOSSIBILITY
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- **UNCONDITIONAL MAYERS-LO-CHAU IN DIMENSION TWO.**

    For 2×2 bit-commitment protocols (qubit Alice, qubit Bob), no
    protocol can be both concealing and binding.  This is the
    qubit-dimensional case of the Mayers-Lo-Chau impossibility theorem,
    proved without any analytical hypothesis. -/
theorem no_perfect_BC_protocol_dim_two
    (P : BCProtocol) (hn : P.n = 2)
    (hConceal : P.IsConcealing) :
    ¬ P.IsBinding := by
  obtain ⟨n, ψ, hnorm⟩ := P
  cases hn
  intro hBind
  have hgram : (ψ 0)ᵀ * (ψ 0) = (ψ 1)ᵀ * (ψ 1) := hConceal
  obtain ⟨U, hU, hUψ⟩ := hjw_dim_two (ψ 0) (ψ 1) hgram
  exact hBind ⟨U, hU, hUψ⟩

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 8 — MASTER THEOREM
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- **HUGHSTON-JOZSA-WOOTTERS QUBIT MASTER.**  The qubit-dimension
    bit-commitment-impossibility package:

    (1) HJW holds unconditionally for n = 2 real-amplitude states.
    (2) Hence no 2×2 (qubit) bit commitment protocol can be both
        concealing and binding. -/
theorem hjw_qubit_master :
    -- (1) HJW at dim 2.
    (∀ ψ φ : Matrix (Fin 2) (Fin 2) ℝ,
        ψᵀ * ψ = φᵀ * φ →
        ∃ U : Matrix (Fin 2) (Fin 2) ℝ,
            U ∈ Matrix.orthogonalGroup (Fin 2) ℝ ∧ U * ψ = φ)
    -- (2) Unconditional impossibility at dim 2.
    ∧ (∀ P : BCProtocol, P.n = 2 → P.IsConcealing → ¬ P.IsBinding) :=
  ⟨hjw_dim_two, no_perfect_BC_protocol_dim_two⟩

end UnifiedTheory.LayerC.HJWQubit
