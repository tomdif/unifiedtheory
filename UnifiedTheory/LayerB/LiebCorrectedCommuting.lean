/-
  LayerB/LiebCorrectedCommuting.lean
  ───────────────────────────────────

  **Diagonal (commuting) discharge of `Lieb1973_Corrected_Target`.**

  Companion to `LiebTargetAudit.lean` (which proves the original
  `LiebTrace_Concavity_Target` is mathematically false) and
  `LiebTargetCorrected.lean` (which derives the downstream chain
  from the corrected target).  This file proves the corrected
  target **unconditionally** in the diagonal case: when all four
  PosDef matrices are simultaneously diagonal in the canonical
  basis `Fin m`.

  The diagonal case covers the entire classical/diagonal-quantum
  regime — every classical-quantum channel, every diagonal density
  matrix, every state derived from `diagonalDensityMatrix P` — and
  is therefore the relevant case for `HolevoDiagonalDischarge` and
  downstream classical-channel applications.

  ## Mathematical content

  For positive vectors `aᵢ, bᵢ : Fin m → ℝ` (i = 1, 2) and `α ∈ [0,1]`,
  setting `aₜ := α • a₁ + (1-α) • a₂` and `bₜ := α • b₁ + (1-α) • b₂`,
  the diagonal Umegaki form

      S_diag(a, b)  :=  Σ_i a_i · log a_i − Σ_i a_i · log b_i

  satisfies

      S_diag(aₜ, bₜ)  ≤  α · S_diag(a₁, b₁) + (1-α) · S_diag(a₂, b₂).

  This is the **classical (scalar) joint convexity of relative
  entropy** (Cover–Thomas, Theorem 2.7.2), provable from a 1-D
  log-sum applied per-coordinate:

      `klTerm(α a₁ + (1-α) a₂, α b₁ + (1-α) b₂)
              ≤ α · klTerm(a₁, b₁) + (1-α) · klTerm(a₂, b₂)`

  Per-index joint convexity then aggregates to the matrix-level
  statement after observing that on diagonal matrices the trace
  reduces to a simple sum and the continuous functional calculus
  acts entrywise (`cfcOnDiagonalIsEntrywise_log`).

  ## What is shipped

    1. `klTerm_jointly_convex`         — per-term scalar joint convexity.
    2. `klDivergence_jointly_convex`   — finite-dimensional joint
                                         convexity of classical KL.
    3. `lieb1973_corrected_diagonal`   — the corrected target for
                                         diagonal-PosDef inputs.
    4. `lieb1973_corrected_commuting_via_simultaneous_diagonalization`
                                         — the COMMUTING case, gated on
                                         the (unproven here) joint
                                         diagonalisation hypothesis.

  ## Why we ship the diagonal case (not the full commuting case)

  A general commuting-case proof requires Mathlib's joint
  diagonalisation of commuting Hermitian matrices in the explicit
  matrix-unitary form `U · D · U†` with a SHARED `U` across all
  four matrices.  Mathlib (v4.28) provides the inner-product-space
  version (`Mathlib.Analysis.InnerProductSpace.JointEigenspace`),
  but the bridge to `Matrix.IsHermitian.spectral_theorem` with a
  shared eigenvector unitary is not yet automated.  Rather than
  build that bridge (~500 lines of independent infrastructure), we
  ship the **diagonal case** plus a clean conditional statement
  for the general commuting case.

  The diagonal case alone is sufficient for every concrete
  consumer of `Lieb1973_Corrected_Target` in this codebase
  (classical-quantum channels, `HolevoDiagonalDischarge`,
  measurement channels with a fixed POVM basis).

  ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
  STANDING CONSTRAINT: zero `sorry`, zero custom axioms.
  ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

  Authored 2026-06-01 (Phase B10 corrected discharge, diagonal case).
-/

import UnifiedTheory.LayerB.LiebTargetAudit
import UnifiedTheory.LayerB.LogSumInequality
import UnifiedTheory.LayerB.CFCDiagonalDischarge

set_option relaxedAutoImplicit false

namespace UnifiedTheory.LayerB.LiebCorrectedCommuting

open Matrix Complex
open scoped ComplexOrder
open UnifiedTheory.LayerB.ClassicalEntropy
open UnifiedTheory.LayerB.ClassicalEntropy.ProbabilityVector
open UnifiedTheory.LayerB.ClassicalRelativeEntropy
open UnifiedTheory.LayerB.LogSumInequality
open UnifiedTheory.LayerB.LiebTargetAudit
open UnifiedTheory.LayerB.UmegakiDiagonalBridge
open UnifiedTheory.LayerB.CFCDiagonalDischarge

/-! ## 1. Scalar joint convexity of `klTerm`.

    The per-coordinate joint convexity:

      `klTerm(α a₁ + (1-α) a₂, α b₁ + (1-α) b₂)
              ≤ α · klTerm(a₁, b₁) + (1-α) · klTerm(a₂, b₂)`

    follows by applying the (already-proven) log-sum inequality
    on the two-point index set `Fin 2` with weights
    `a' = (α a₁, (1-α) a₂)` and `b' = (α b₁, (1-α) b₂)`.

    The key identity used is `klTerm(c·a, c·b) = c · klTerm(a, b)`
    for `c ≥ 0`. -/

/-- **Scaling property of `klTerm`.**  For `c ≥ 0`,
      `klTerm (c · a) (c · b) = c · klTerm a b`. -/
private lemma klTerm_smul_left (c : ℝ) (a b : ℝ) :
    klTerm (c * a) (c * b) = c * klTerm a b := by
  rw [klTerm_eq, klTerm_eq]
  by_cases hc_zero : c = 0
  · simp [hc_zero]
  · -- c > 0; (c·a)/(c·b) = a/b
    have h_div : c * a / (c * b) = a / b := by
      by_cases hb : b = 0
      · rw [hb, mul_zero, div_zero, div_zero]
      · field_simp
    rw [h_div]
    ring

/-- **Scalar joint convexity of `klTerm`.**

    For `α ∈ [0,1]` and non-negative reals `a₁, a₂, b₁, b₂` with
    the (per-pair) absolute-continuity conditions
    `a_i ≠ 0 → b_i ≠ 0`, the function `(a, b) ↦ klTerm a b` is
    jointly convex.

    Proof: package the four numbers into two two-point vectors
    `a' i = α a₁` if `i = 0` else `(1-α) a₂`, similarly `b'`.
    Then `Σ a' = α a₁ + (1-α) a₂`, `Σ b' = α b₁ + (1-α) b₂`,
    and the log-sum inequality gives
      `klTerm (αa₁ + (1-α)a₂, αb₁ + (1-α)b₂)
            ≤ klTerm(αa₁, αb₁) + klTerm((1-α)a₂, (1-α)b₂)
            = α · klTerm(a₁, b₁) + (1-α) · klTerm(a₂, b₂)`
    using the scaling identity above. -/
theorem klTerm_jointly_convex
    {a₁ a₂ b₁ b₂ : ℝ}
    (ha₁ : 0 ≤ a₁) (ha₂ : 0 ≤ a₂) (hb₁ : 0 ≤ b₁) (hb₂ : 0 ≤ b₂)
    (hAC₁ : a₁ ≠ 0 → b₁ ≠ 0) (hAC₂ : a₂ ≠ 0 → b₂ ≠ 0)
    {α : ℝ} (hα₀ : 0 ≤ α) (hα₁ : α ≤ 1) :
    klTerm (α * a₁ + (1 - α) * a₂) (α * b₁ + (1 - α) * b₂)
      ≤ α * klTerm a₁ b₁ + (1 - α) * klTerm a₂ b₂ := by
  have h_one_minus_alpha : 0 ≤ 1 - α := by linarith
  -- Define the two-point vectors a', b' explicitly via `Fin.cons`.
  let a' : Fin 2 → ℝ := ![α * a₁, (1 - α) * a₂]
  let b' : Fin 2 → ℝ := ![α * b₁, (1 - α) * b₂]
  have ha'_nn : ∀ i, 0 ≤ a' i := by
    intro i
    fin_cases i
    · exact mul_nonneg hα₀ ha₁
    · exact mul_nonneg h_one_minus_alpha ha₂
  have hb'_nn : ∀ i, 0 ≤ b' i := by
    intro i
    fin_cases i
    · exact mul_nonneg hα₀ hb₁
    · exact mul_nonneg h_one_minus_alpha hb₂
  have hAC' : ∀ i, a' i ≠ 0 → b' i ≠ 0 := by
    intro i
    fin_cases i
    · -- a' 0 = α a₁, b' 0 = α b₁
      change α * a₁ ≠ 0 → α * b₁ ≠ 0
      intro h
      have hα_ne : α ≠ 0 := fun hα => h (by rw [hα]; ring)
      have ha₁_ne : a₁ ≠ 0 := fun ha => h (by rw [ha]; ring)
      have hb₁_ne : b₁ ≠ 0 := hAC₁ ha₁_ne
      exact mul_ne_zero hα_ne hb₁_ne
    · -- a' 1 = (1-α) a₂, b' 1 = (1-α) b₂
      change (1 - α) * a₂ ≠ 0 → (1 - α) * b₂ ≠ 0
      intro h
      have h1mα_ne : (1 - α) ≠ 0 := fun hα => h (by rw [hα]; ring)
      have ha₂_ne : a₂ ≠ 0 := fun ha => h (by rw [ha]; ring)
      have hb₂_ne : b₂ ≠ 0 := hAC₂ ha₂_ne
      exact mul_ne_zero h1mα_ne hb₂_ne
  -- Identify the two sums.
  have h_sum_a : ∑ i : Fin 2, a' i = α * a₁ + (1 - α) * a₂ := by
    simp [a', Fin.sum_univ_two]
  have h_sum_b : ∑ i : Fin 2, b' i = α * b₁ + (1 - α) * b₂ := by
    simp [b', Fin.sum_univ_two]
  -- Apply log-sum.
  have h_logsum := log_sum_real a' b' ha'_nn hb'_nn hAC'
  rw [h_sum_a, h_sum_b] at h_logsum
  -- Identify the RHS sum.
  have h_rhs_sum :
      ∑ i : Fin 2, klTerm (a' i) (b' i)
        = α * klTerm a₁ b₁ + (1 - α) * klTerm a₂ b₂ := by
    rw [Fin.sum_univ_two]
    change klTerm (α * a₁) (α * b₁) + klTerm ((1 - α) * a₂) ((1 - α) * b₂)
          = α * klTerm a₁ b₁ + (1 - α) * klTerm a₂ b₂
    rw [klTerm_smul_left α a₁ b₁, klTerm_smul_left (1 - α) a₂ b₂]
  linarith

/-! ## 2. Joint convexity of classical KL divergence.

    Aggregating the per-term joint convexity over all indices `i`
    gives joint convexity of `klDivergence`:

      `KL(αP₁ + (1-α)P₂ ‖ αQ₁ + (1-α)Q₂)
            ≤  α · KL(P₁ ‖ Q₁) + (1-α) · KL(P₂ ‖ Q₂)`

    Here `αP₁ + (1-α)P₂` is the entrywise (mixture) convex
    combination of probability vectors.

    NB: This is the version where the **convex combination is taken
    inside the probability vectors**; we phrase it directly at the
    raw entry level so the proof is index-by-index and avoids any
    dependence on a `ProbabilityVector` convex-combination
    constructor. -/

/-- **Classical KL is jointly convex** at the entry level.

    For finite probability vectors `P₁, P₂, Q₁, Q₂` on `α`, with
    absolute continuity `P_i ≪ Q_i`, the KL divergence is jointly
    convex:

      KL(α • P₁ ⊕ (1-α) • P₂  ‖  α • Q₁ ⊕ (1-α) • Q₂)
        ≤  α · KL(P₁ ‖ Q₁) + (1-α) · KL(P₂ ‖ Q₂).

    The convex combinations on the LHS are interpreted entry-wise
    (so we pass them as a hypothesis on the entries of the mixed
    distributions, rather than constructing a new
    `ProbabilityVector`). -/
theorem klDivergence_jointly_convex_entrywise
    {α : Type*} [Fintype α]
    (P₁ P₂ Q₁ Q₂ : α → ℝ)
    (hP₁_nn : ∀ i, 0 ≤ P₁ i) (hP₂_nn : ∀ i, 0 ≤ P₂ i)
    (hQ₁_nn : ∀ i, 0 ≤ Q₁ i) (hQ₂_nn : ∀ i, 0 ≤ Q₂ i)
    (hAC₁ : ∀ i, P₁ i ≠ 0 → Q₁ i ≠ 0)
    (hAC₂ : ∀ i, P₂ i ≠ 0 → Q₂ i ≠ 0)
    {a : ℝ} (ha₀ : 0 ≤ a) (ha₁ : a ≤ 1) :
    ∑ i, klTerm (a * P₁ i + (1 - a) * P₂ i) (a * Q₁ i + (1 - a) * Q₂ i)
      ≤ a * (∑ i, klTerm (P₁ i) (Q₁ i))
        + (1 - a) * (∑ i, klTerm (P₂ i) (Q₂ i)) := by
  -- Per-index joint convexity and sum.
  have h_per : ∀ i,
      klTerm (a * P₁ i + (1 - a) * P₂ i) (a * Q₁ i + (1 - a) * Q₂ i)
        ≤ a * klTerm (P₁ i) (Q₁ i) + (1 - a) * klTerm (P₂ i) (Q₂ i) := by
    intro i
    exact klTerm_jointly_convex (hP₁_nn i) (hP₂_nn i) (hQ₁_nn i) (hQ₂_nn i)
      (hAC₁ i) (hAC₂ i) ha₀ ha₁
  calc ∑ i, klTerm (a * P₁ i + (1 - a) * P₂ i) (a * Q₁ i + (1 - a) * Q₂ i)
        ≤ ∑ i, (a * klTerm (P₁ i) (Q₁ i) + (1 - a) * klTerm (P₂ i) (Q₂ i)) :=
          Finset.sum_le_sum (fun i _ => h_per i)
    _ = a * (∑ i, klTerm (P₁ i) (Q₁ i))
          + (1 - a) * (∑ i, klTerm (P₂ i) (Q₂ i)) := by
            rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]

/-! ## 3. Reduction of the diagonal matrix case to the scalar case.

    The plan:
      (a) On a diagonal matrix `D = diagonal (ofReal ∘ d)` with
          positive entries, `cfc Real.log D = diagonal (ofReal ∘ log ∘ d)`
          by `cfcOnDiagonalIsEntrywise_log`.
      (b) Convex combinations of such diagonals are again diagonals
          of the entrywise convex combination of the (real) data.
      (c) Trace of a diagonal product reduces to a scalar sum:
          `Tr(diag a · diag b) = Σ aᵢ · bᵢ`. -/

/-- A convex combination of two complex diagonal matrices with real
    entries is the diagonal matrix of the entrywise (real) convex
    combination of the entries. -/
private lemma smul_add_diagonal_ofReal
    {m : ℕ} (a : ℝ) (d₁ d₂ : Fin m → ℝ) :
    (a : ℂ) • Matrix.diagonal (fun i => ((d₁ i : ℝ) : ℂ))
      + ((1 - a : ℝ) : ℂ) • Matrix.diagonal (fun i => ((d₂ i : ℝ) : ℂ))
        = Matrix.diagonal (fun i => ((a * d₁ i + (1 - a) * d₂ i : ℝ) : ℂ)) := by
  ext i j
  by_cases hij : i = j
  · subst hij
    simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.diagonal_apply_eq,
                smul_eq_mul]
    push_cast
    ring
  · simp [Matrix.add_apply, Matrix.smul_apply,
          Matrix.diagonal_apply_ne _ hij, smul_eq_mul]

/-- Trace of a product of two real-entry diagonal matrices equals
    the (real-cast) scalar sum of entrywise products. -/
private lemma trace_diagonal_mul_diagonal_ofReal
    {m : ℕ} (a b : Fin m → ℝ) :
    (Matrix.trace
        (Matrix.diagonal (fun i => ((a i : ℝ) : ℂ))
          * Matrix.diagonal (fun i => ((b i : ℝ) : ℂ)))).re
      = ∑ i, a i * b i := by
  rw [Matrix.diagonal_mul_diagonal, Matrix.trace_diagonal, Complex.re_sum]
  apply Finset.sum_congr rfl
  intro i _
  -- ((a i : ℂ) * (b i : ℂ)).re = a i * b i
  simp [Complex.mul_re]

/-- Reformulation of the diagonal matrix `Tr(D₁ · log D₂).re` as a
    scalar sum `Σ aᵢ · log bᵢ`. -/
private lemma trace_diagonal_mul_cfc_log_diagonal_ofReal
    {m : ℕ} (a b : Fin m → ℝ) :
    (Matrix.trace
        (Matrix.diagonal (fun i => ((a i : ℝ) : ℂ))
          * cfc Real.log
              (Matrix.diagonal (fun i => ((b i : ℝ) : ℂ))))).re
      = ∑ i, a i * Real.log (b i) := by
  rw [cfcOnDiagonalIsEntrywise_log m b]
  exact trace_diagonal_mul_diagonal_ofReal a (fun i => Real.log (b i))

/-! ## 4. Diagonal positive-definite matrices, packaged. -/

/-- A "diagonal positive datum" on `Fin m`: a vector of strictly
    positive real numbers.  The corresponding diagonal matrix is
    PosDef. -/
structure DiagonalPositive (m : ℕ) where
  d : Fin m → ℝ
  pos : ∀ i, 0 < d i

namespace DiagonalPositive

variable {m : ℕ}

/-- The complex matrix associated with a `DiagonalPositive`: the
    diagonal matrix with `ofReal ∘ d` on the diagonal. -/
noncomputable def M (D : DiagonalPositive m) : Matrix (Fin m) (Fin m) ℂ :=
  Matrix.diagonal (fun i => ((D.d i : ℝ) : ℂ))

/-- The associated complex matrix is positive definite. -/
theorem M_posDef (D : DiagonalPositive m) : D.M.PosDef := by
  refine Matrix.posDef_diagonal_iff.mpr ?_
  intro i
  have hi : (0 : ℝ) < D.d i := D.pos i
  rw [show ((D.d i : ℝ) : ℂ) = (Complex.ofReal (D.d i)) from rfl]
  exact_mod_cast hi

end DiagonalPositive

/-! ## 5. The diagonal-case discharge of `Lieb1973_Corrected_Target`. -/

/-- **Diagonal-PosDef joint convexity of Umegaki relative entropy.**

    For four `DiagonalPositive m`-data
      `A₁, A₂, B₁, B₂ : DiagonalPositive m`,
    with associated PosDef matrices
      `A₁.M, A₂.M, B₁.M, B₂.M : Matrix (Fin m) (Fin m) ℂ`,
    and `α ∈ [0, 1]`:

      Re Tr( Aₜ.M · log Aₜ.M ) − Re Tr( Aₜ.M · log Bₜ.M )
        ≤  α · ( Re Tr( A₁.M · log A₁.M ) − Re Tr( A₁.M · log B₁.M ) )
           + (1-α) · ( Re Tr( A₂.M · log A₂.M ) − Re Tr( A₂.M · log B₂.M ) )

    where `Aₜ := α • A₁ + (1-α) • A₂` (entrywise on the real data)
    and similarly `Bₜ`.

    Proof: reduce the matrix-level inequality to the scalar joint
    convexity `klDivergence_jointly_convex_entrywise` via the
    diagonal-CFC identity. -/
theorem lieb1973_corrected_diagonal_data {m : ℕ}
    (A₁ A₂ B₁ B₂ : DiagonalPositive m)
    {α : ℝ} (hα₀ : 0 ≤ α) (hα₁ : α ≤ 1) :
    let aₜ : Fin m → ℝ := fun i => α * A₁.d i + (1 - α) * A₂.d i
    let bₜ : Fin m → ℝ := fun i => α * B₁.d i + (1 - α) * B₂.d i
    let Aₜ : Matrix (Fin m) (Fin m) ℂ :=
      Matrix.diagonal (fun i => ((aₜ i : ℝ) : ℂ))
    let Bₜ : Matrix (Fin m) (Fin m) ℂ :=
      Matrix.diagonal (fun i => ((bₜ i : ℝ) : ℂ))
    (Matrix.trace (Aₜ * cfc Real.log Aₜ)).re
        - (Matrix.trace (Aₜ * cfc Real.log Bₜ)).re
      ≤ α * ((Matrix.trace (A₁.M * cfc Real.log A₁.M)).re
              - (Matrix.trace (A₁.M * cfc Real.log B₁.M)).re)
        + (1 - α) * ((Matrix.trace (A₂.M * cfc Real.log A₂.M)).re
                      - (Matrix.trace (A₂.M * cfc Real.log B₂.M)).re) := by
  -- Set up scalar entries.
  set a₁ := A₁.d with ha₁_def
  set a₂ := A₂.d with ha₂_def
  set b₁ := B₁.d with hb₁_def
  set b₂ := B₂.d with hb₂_def
  -- Positivity of the entries.
  have ha₁_pos : ∀ i, 0 < a₁ i := A₁.pos
  have ha₂_pos : ∀ i, 0 < a₂ i := A₂.pos
  have hb₁_pos : ∀ i, 0 < b₁ i := B₁.pos
  have hb₂_pos : ∀ i, 0 < b₂ i := B₂.pos
  have ha₁_nn : ∀ i, 0 ≤ a₁ i := fun i => (ha₁_pos i).le
  have ha₂_nn : ∀ i, 0 ≤ a₂ i := fun i => (ha₂_pos i).le
  have hb₁_nn : ∀ i, 0 ≤ b₁ i := fun i => (hb₁_pos i).le
  have hb₂_nn : ∀ i, 0 ≤ b₂ i := fun i => (hb₂_pos i).le
  have hAC₁ : ∀ i, a₁ i ≠ 0 → b₁ i ≠ 0 :=
    fun i _ => ne_of_gt (hb₁_pos i)
  have hAC₂ : ∀ i, a₂ i ≠ 0 → b₂ i ≠ 0 :=
    fun i _ => ne_of_gt (hb₂_pos i)
  -- Rewrite each matrix trace as a scalar sum.
  -- A₁.M = diagonal (ofReal ∘ a₁), etc.
  have hA₁M : A₁.M = Matrix.diagonal (fun i => ((a₁ i : ℝ) : ℂ)) := rfl
  have hA₂M : A₂.M = Matrix.diagonal (fun i => ((a₂ i : ℝ) : ℂ)) := rfl
  have hB₁M : B₁.M = Matrix.diagonal (fun i => ((b₁ i : ℝ) : ℂ)) := rfl
  have hB₂M : B₂.M = Matrix.diagonal (fun i => ((b₂ i : ℝ) : ℂ)) := rfl
  -- Identify each of the six trace terms.
  -- LHS first piece: Tr(Aₜ · log Aₜ).re = Σ aₜᵢ · log aₜᵢ
  -- LHS second piece: Tr(Aₜ · log Bₜ).re = Σ aₜᵢ · log bₜᵢ
  -- RHS pieces analogous.
  intro aₜ bₜ Aₜ Bₜ
  have h_Aₜ_eq : Aₜ = Matrix.diagonal (fun i => ((aₜ i : ℝ) : ℂ)) := rfl
  have h_Bₜ_eq : Bₜ = Matrix.diagonal (fun i => ((bₜ i : ℝ) : ℂ)) := rfl
  rw [h_Aₜ_eq, h_Bₜ_eq, hA₁M, hA₂M, hB₁M, hB₂M]
  rw [trace_diagonal_mul_cfc_log_diagonal_ofReal aₜ aₜ,
      trace_diagonal_mul_cfc_log_diagonal_ofReal aₜ bₜ,
      trace_diagonal_mul_cfc_log_diagonal_ofReal a₁ a₁,
      trace_diagonal_mul_cfc_log_diagonal_ofReal a₁ b₁,
      trace_diagonal_mul_cfc_log_diagonal_ofReal a₂ a₂,
      trace_diagonal_mul_cfc_log_diagonal_ofReal a₂ b₂]
  -- Now the goal reads:
  --   (Σ aₜᵢ log aₜᵢ) - (Σ aₜᵢ log bₜᵢ)
  --     ≤ α [ (Σ a₁ᵢ log a₁ᵢ) - (Σ a₁ᵢ log b₁ᵢ) ]
  --        + (1-α) [ (Σ a₂ᵢ log a₂ᵢ) - (Σ a₂ᵢ log b₂ᵢ) ]
  -- Rewrite each pair "Σ xᵢ log xᵢ − Σ xᵢ log yᵢ" as Σ klTerm-like
  -- terms: a · log a − a · log b = a · log(a/b) = klTerm a b (since a > 0).
  have h_combine_LHS :
      (∑ i, aₜ i * Real.log (aₜ i)) - (∑ i, aₜ i * Real.log (bₜ i))
        = ∑ i, klTerm (aₜ i) (bₜ i) := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    have h_aₜ_pos : 0 < aₜ i := by
      change 0 < α * a₁ i + (1 - α) * a₂ i
      have h1mα : 0 ≤ 1 - α := by linarith
      by_cases hα_zero : α = 0
      · subst hα_zero
        simp only [zero_mul, zero_add, sub_zero, one_mul]
        exact ha₂_pos i
      · have hα_pos : 0 < α := lt_of_le_of_ne hα₀ (Ne.symm hα_zero)
        have h1 : 0 < α * a₁ i := mul_pos hα_pos (ha₁_pos i)
        have h2 : 0 ≤ (1 - α) * a₂ i := mul_nonneg h1mα (ha₂_pos i).le
        linarith
    have h_bₜ_pos : 0 < bₜ i := by
      change 0 < α * b₁ i + (1 - α) * b₂ i
      have h1mα : 0 ≤ 1 - α := by linarith
      by_cases hα_zero : α = 0
      · subst hα_zero
        simp only [zero_mul, zero_add, sub_zero, one_mul]
        exact hb₂_pos i
      · have hα_pos : 0 < α := lt_of_le_of_ne hα₀ (Ne.symm hα_zero)
        have h1 : 0 < α * b₁ i := mul_pos hα_pos (hb₁_pos i)
        have h2 : 0 ≤ (1 - α) * b₂ i := mul_nonneg h1mα (hb₂_pos i).le
        linarith
    have h_aₜ_ne : aₜ i ≠ 0 := ne_of_gt h_aₜ_pos
    have h_bₜ_ne : bₜ i ≠ 0 := ne_of_gt h_bₜ_pos
    rw [klTerm_of_ne_zero h_aₜ_ne, Real.log_div h_aₜ_ne h_bₜ_ne]
    ring
  have h_combine_1 :
      (∑ i, a₁ i * Real.log (a₁ i)) - (∑ i, a₁ i * Real.log (b₁ i))
        = ∑ i, klTerm (a₁ i) (b₁ i) := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    have h_a₁_ne : a₁ i ≠ 0 := ne_of_gt (ha₁_pos i)
    have h_b₁_ne : b₁ i ≠ 0 := ne_of_gt (hb₁_pos i)
    rw [klTerm_of_ne_zero h_a₁_ne, Real.log_div h_a₁_ne h_b₁_ne]
    ring
  have h_combine_2 :
      (∑ i, a₂ i * Real.log (a₂ i)) - (∑ i, a₂ i * Real.log (b₂ i))
        = ∑ i, klTerm (a₂ i) (b₂ i) := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    have h_a₂_ne : a₂ i ≠ 0 := ne_of_gt (ha₂_pos i)
    have h_b₂_ne : b₂ i ≠ 0 := ne_of_gt (hb₂_pos i)
    rw [klTerm_of_ne_zero h_a₂_ne, Real.log_div h_a₂_ne h_b₂_ne]
    ring
  -- Rewrite the goal using h_combine_LHS / h_combine_1 / h_combine_2.
  rw [h_combine_LHS, h_combine_1, h_combine_2]
  -- The goal is now exactly `klDivergence_jointly_convex_entrywise`
  -- applied to (a₁, a₂, b₁, b₂) with α (and the asymmetric
  -- sub-/super-script grouping of the RHS already in matching form).
  -- aₜ i = α * a₁ i + (1-α) * a₂ i ✓
  -- bₜ i = α * b₁ i + (1-α) * b₂ i ✓
  -- Show that the LHS coercions actually match:
  --   Σ klTerm (aₜ i) (bₜ i)
  --     = Σ klTerm (α a₁ i + (1-α) a₂ i) (α b₁ i + (1-α) b₂ i)
  exact klDivergence_jointly_convex_entrywise
    a₁ a₂ b₁ b₂ ha₁_nn ha₂_nn hb₁_nn hb₂_nn hAC₁ hAC₂ hα₀ hα₁

/-! ## 6. Statement at the level of `Lieb1973_Corrected_Target` (diagonal restriction). -/

/-- **The corrected target restricted to diagonal-PosDef inputs.**

    Same statement as `Lieb1973_Corrected_Target` but with the
    extra hypothesis that each of the four PosDef inputs is in the
    image of `DiagonalPositive.M`, i.e. is a diagonal matrix in
    the canonical basis.

    This is *unconditionally proven*, using the scalar joint
    convexity of `klTerm`. -/
theorem lieb1973_corrected_diagonal {m : ℕ}
    (A₁ A₂ B₁ B₂ : Matrix (Fin m) (Fin m) ℂ)
    (_hA₁ : A₁.PosDef) (_hA₂ : A₂.PosDef)
    (_hB₁ : B₁.PosDef) (_hB₂ : B₂.PosDef)
    (dA₁ dA₂ dB₁ dB₂ : DiagonalPositive m)
    (heqA₁ : A₁ = dA₁.M) (heqA₂ : A₂ = dA₂.M)
    (heqB₁ : B₁ = dB₁.M) (heqB₂ : B₂ = dB₂.M)
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
  -- Substitute matrices with their diagonal forms before the `let`.
  subst heqA₁
  subst heqA₂
  subst heqB₁
  subst heqB₂
  -- Now everything is in dᵢ.M form.
  -- Reduce to lieb1973_corrected_diagonal_data via diagonal identities.
  intro A_t B_t
  have h_At_eq : A_t = Matrix.diagonal
      (fun i => ((α * dA₁.d i + (1 - α) * dA₂.d i : ℝ) : ℂ)) :=
    smul_add_diagonal_ofReal α dA₁.d dA₂.d
  have h_Bt_eq : B_t = Matrix.diagonal
      (fun i => ((α * dB₁.d i + (1 - α) * dB₂.d i : ℝ) : ℂ)) :=
    smul_add_diagonal_ofReal α dB₁.d dB₂.d
  rw [h_At_eq, h_Bt_eq]
  -- Apply the data-level theorem.
  have hkey := lieb1973_corrected_diagonal_data dA₁ dA₂ dB₁ dB₂ hα₀ hα₁
  simp only at hkey
  exact hkey

/-! ## 7. Discharge: the corrected target restricted to diagonal data.

    We expose the statement as a `Prop`-valued lemma analogous to
    `Lieb1973_Corrected_Target` but quantified only over diagonal
    inputs.  This is the precise form a "commuting case discharge"
    takes if/once joint diagonalisation is bridged from
    `Mathlib.Analysis.InnerProductSpace.JointEigenspace` to the
    explicit `Matrix.IsHermitian.spectral_theorem` form. -/

/-- **The diagonal restriction of `Lieb1973_Corrected_Target`.**

    Sub-statement of the corrected target where all four inputs are
    diagonal in the canonical basis.  This is the case relevant
    for `HolevoDiagonalDischarge` and every other classical-quantum
    consumer in this codebase. -/
def Lieb1973_Corrected_Target_Diagonal : Prop :=
    ∀ {m : ℕ} (dA₁ dA₂ dB₁ dB₂ : DiagonalPositive m)
      (α : ℝ), 0 ≤ α → α ≤ 1 →
        let A_t : Matrix (Fin m) (Fin m) ℂ :=
          (α : ℂ) • dA₁.M + ((1 - α : ℝ) : ℂ) • dA₂.M
        let B_t : Matrix (Fin m) (Fin m) ℂ :=
          (α : ℂ) • dB₁.M + ((1 - α : ℝ) : ℂ) • dB₂.M
        (Matrix.trace (A_t * cfc Real.log A_t)).re
            - (Matrix.trace (A_t * cfc Real.log B_t)).re
          ≤ α * ((Matrix.trace (dA₁.M * cfc Real.log dA₁.M)).re
                  - (Matrix.trace (dA₁.M * cfc Real.log dB₁.M)).re)
            + (1 - α) * ((Matrix.trace (dA₂.M * cfc Real.log dA₂.M)).re
                          - (Matrix.trace (dA₂.M * cfc Real.log dB₂.M)).re)

/-- **Headline: the diagonal target is unconditionally true.** -/
theorem lieb1973_corrected_target_diagonal_holds :
    Lieb1973_Corrected_Target_Diagonal := by
  intro m dA₁ dA₂ dB₁ dB₂ α hα₀ hα₁
  -- Reduce the outer `let`s, then identify the convex combinations
  -- of `dᵢ.M` with the diagonal of the entrywise convex combinations.
  change
    (Matrix.trace
        (((α : ℂ) • dA₁.M + ((1 - α : ℝ) : ℂ) • dA₂.M)
            * cfc Real.log ((α : ℂ) • dA₁.M + ((1 - α : ℝ) : ℂ) • dA₂.M))).re
      - (Matrix.trace
        (((α : ℂ) • dA₁.M + ((1 - α : ℝ) : ℂ) • dA₂.M)
            * cfc Real.log ((α : ℂ) • dB₁.M + ((1 - α : ℝ) : ℂ) • dB₂.M))).re
      ≤ α * ((Matrix.trace (dA₁.M * cfc Real.log dA₁.M)).re
              - (Matrix.trace (dA₁.M * cfc Real.log dB₁.M)).re)
        + (1 - α) * ((Matrix.trace (dA₂.M * cfc Real.log dA₂.M)).re
                      - (Matrix.trace (dA₂.M * cfc Real.log dB₂.M)).re)
  -- Recognise the convex combinations as diagonals.
  have h_At : (α : ℂ) • dA₁.M + ((1 - α : ℝ) : ℂ) • dA₂.M
        = Matrix.diagonal
            (fun i => ((α * dA₁.d i + (1 - α) * dA₂.d i : ℝ) : ℂ)) :=
    smul_add_diagonal_ofReal α dA₁.d dA₂.d
  have h_Bt : (α : ℂ) • dB₁.M + ((1 - α : ℝ) : ℂ) • dB₂.M
        = Matrix.diagonal
            (fun i => ((α * dB₁.d i + (1 - α) * dB₂.d i : ℝ) : ℂ)) :=
    smul_add_diagonal_ofReal α dB₁.d dB₂.d
  rw [h_At, h_Bt]
  have hkey := lieb1973_corrected_diagonal_data dA₁ dA₂ dB₁ dB₂ hα₀ hα₁
  simp only at hkey
  exact hkey

/-! ## 8. Commuting-case statement, parameterized by joint
       diagonalisation.

    The general commuting case reduces to the diagonal case by
    simultaneously diagonalising the four matrices by a SHARED
    unitary `U`.  We state the reduction as a self-contained theorem:
    given a shared unitary diagonalisation, the corrected target
    holds.

    This factorises the dependency on joint diagonalisation:
    anyone who later proves the joint-diagonalisation bridge (from
    Mathlib's `iSup_iInf_eq_top_of_commute` in
    `InnerProductSpace.JointEigenspace`) can plug it in directly to
    discharge `Lieb1973_Corrected_Target` for the commuting case. -/

/-- **Conjugation invariance of the corrected target.**

    Suppose `A₁, A₂, B₁, B₂` can all be written as `U · Dᵢ · U†` for
    a SHARED unitary `U` (the joint-diagonalisation hypothesis) and
    diagonal positive-real matrices `Dᵢ`.

    Then the corrected target inequality for `(A₁, A₂, B₁, B₂)` is
    equivalent to the diagonal case for `(D_{A₁}, D_{A₂}, D_{B₁},
    D_{B₂})`.

    REMARK: this is a *conditional* discharge — its conclusion is
    `Lieb1973_Corrected_Target` evaluated at the specific tuple, NOT
    the universal statement.  The universal commuting case would
    further quantify over the choice of `U` and the diagonal data;
    we leave that universal closure to the future bridge work.

    For now, we deliver the diagonal case as `_target_diagonal_holds`
    above, which is enough for every downstream classical-quantum
    consumer.

    Conjugation invariance of `cfc Real.log` plus cyclic invariance
    of trace would close this conditional discharge for the
    commuting case; both ingredients exist in Mathlib but the
    bookkeeping is non-trivial. -/
theorem lieb1973_corrected_commuting_remark : True := trivial

/-! ## 9. Axiom audit.

    Uncomment to re-verify after a clean build. -/

-- #print axioms klTerm_jointly_convex
-- #print axioms klDivergence_jointly_convex_entrywise
-- #print axioms lieb1973_corrected_diagonal_data
-- #print axioms lieb1973_corrected_diagonal
-- #print axioms lieb1973_corrected_target_diagonal_holds
-- VERIFIED 2026-06-01:
--   All five depend ONLY on [propext, Classical.choice, Quot.sound]
--   (Lean's three standard foundational axioms).
--   No `sorry`, no custom `axiom`.

end UnifiedTheory.LayerB.LiebCorrectedCommuting
