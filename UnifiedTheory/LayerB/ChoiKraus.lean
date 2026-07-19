/-
  LayerB/ChoiKraus.lean
  ─────────────────────

  The **Choi matrix bridge for Kraus channels** — Phase B5 keystone.

  For a Kraus family `{K_α : Matrix m m ℂ}_{α ∈ A}` defining the channel
  `Φ(ρ) = Σ_α K_α ρ K_α†`, the Choi matrix is

      Choi(K) ∈ Matrix (m × m) (m × m) ℂ
      Choi(K)_{(i,j), (i',j')} := Σ_α (K_α)_{j,i} · conj((K_α)_{j',i'}).

  The **keystone property** is `Choi(K) ≥ 0` (PSD), proved here by
  exhibiting the quadratic form as a sum of squared norms:

      x* · Choi(K) · x  =  Σ_α |Σ_{ij} conj(x_{ij}) · (K_α)_{j,i}|² ≥ 0.

  WHAT IS PROVEN (no sorry, no custom axioms):
    1. `choi K`  — the entry-level definition.
    2. `choi_isHermitian`  — Hermiticity from `star`-symmetry.
    3. `choi_posSemidef`  — **the keystone**: sum of rank-1 PSDs.
    4. `krausChannel K ρ := Σ_α K_α · ρ · K_α†`  — the Kraus channel.
    5. `krausChannel_eq_choi_apply`  — the channel acts via the Choi
       matrix:  `Φ(ρ)_{j j'} = Σ_{i,i'} ρ_{i,i'} · Choi(K)_{(i,j),(i',j')}`.

  WHAT IS DEFERRED:
    • The trace-preservation identity `Tr_2 (Choi(K)) = Σ_α K_α† K_α`,
      which gives a one-line proof that a Kraus channel is TP iff
      its Choi matrix has unit reduced state on the input system.
    • The "PSD Choi ⟹ Kraus" direction (extraction via spectral
      decomposition) is handled separately in `KrausExistence.lean`.

  NAMING:
    A separate namespace `UnifiedTheory.LayerB.ChoiKraus` is used to
    avoid clashing with the existing `UnifiedTheory.LayerB.Kraus.choi`
    (the linear-map formulation in `ChoiMatrix.lean`).
-/

import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Complex.Basic
import Mathlib.Analysis.Complex.Order
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import UnifiedTheory.LayerB.PartialTrace

set_option relaxedAutoImplicit false
-- `[Fintype m]` is needed only by `choi_quadForm_eq_sum_self_mul_star` and
-- `choi_posSemidef` (which sum over `m × m`); `choi`, `choi_apply`, and
-- `choi_isHermitian` are entry-level and don't iterate.  We keep the
-- assumption in scope uniformly via the `variable` declaration below and
-- silence the linter for the few statements that don't depend on it.
set_option linter.unusedFintypeInType false
set_option linter.unusedSectionVars false

namespace UnifiedTheory.LayerB.ChoiKraus

open Matrix Complex
open scoped BigOperators ComplexOrder

/-- Local `AddLeftMono ℂ` instance — needed for `Finset.sum_nonneg`
    over ℂ.  Mathlib provides `IsOrderedAddMonoid ℂ` via ComplexOrder
    but does not register the corresponding `AddLeftMono` covariant
    class instance globally.  Copied from
    `UnifiedTheory.LayerB.KrausRepresentation`. -/
local instance : AddLeftMono ℂ where
  elim c a b (h : a ≤ b) := by
    change c + a ≤ c + b
    obtain ⟨hr, hi⟩ := h
    exact ⟨by simp only [Complex.add_re]; linarith,
           by simp only [Complex.add_im]; linarith⟩

variable {m : Type*} [Fintype m]
variable {A : Type*} [Fintype A]

/-! ## 1. The Choi matrix of a Kraus family -/

/-- The Choi matrix of a Kraus family `K : A → Matrix m m ℂ`:

    `Choi(K)_{(i,j), (i',j')} := Σ_α (K_α)_{j,i} · conj((K_α)_{j',i'})`.

    Indexing convention: outer pair `(i, j)` puts the *input* (column)
    index `i` first and the *output* (row) index `j` second.  With this
    choice, the quadratic form of `Choi(K)` is
    `x* · Choi(K) · x = Σ_α |Σ_{ij} conj(x_{ij}) · (K_α)_{j,i}|²`. -/
noncomputable def choi (K : A → Matrix m m ℂ) :
    Matrix (m × m) (m × m) ℂ :=
  fun ij ij' => ∑ α, K α ij.2 ij.1 * star (K α ij'.2 ij'.1)

/-- Direct evaluation formula for the Choi matrix. -/
@[simp]
theorem choi_apply (K : A → Matrix m m ℂ) (i j i' j' : m) :
    choi K (i, j) (i', j') = ∑ α, K α j i * star (K α j' i') := rfl

/-! ## 2. Hermiticity -/

/-- The Choi matrix is Hermitian:  `Choi(K)† = Choi(K)`. -/
theorem choi_isHermitian (K : A → Matrix m m ℂ) :
    (choi K).IsHermitian := by
  ext ij ij'
  obtain ⟨i, j⟩ := ij
  obtain ⟨i', j'⟩ := ij'
  -- Goal: (choi K)ᴴ (i,j) (i',j') = choi K (i,j) (i',j')
  -- i.e.  star (choi K (i',j') (i,j)) = choi K (i,j) (i',j')
  change star (choi K (i', j') (i, j)) = choi K (i, j) (i', j')
  simp only [choi_apply]
  rw [star_sum]
  apply Finset.sum_congr rfl
  intro α _
  -- star (K α j' i' * star (K α j i)) = K α j i * star (K α j' i')
  rw [StarMul.star_mul, star_star]

/-! ## 3. The PSD keystone

The quadratic form of `Choi(K)` on `x : m × m → ℂ`:

  `star x ⬝ᵥ Choi(K) *ᵥ x`
    `= Σ_α (Σ_{ij} star(x_{ij}) · K_α j i) · star(Σ_{i'j'} star(x_{i'j'}) · K_α j' i')`
    `= Σ_α |c_α|² ≥ 0`

where `c_α := Σ_{ij} star(x_{ij}) · K_α j i`. -/

/-- The quadratic form of `Choi(K)` factors as a sum of `c_α * star c_α`,
    one per Kraus operator.  Each term is `≥ 0` (it equals `‖c_α‖²`),
    so the sum is `≥ 0`. -/
private lemma choi_quadForm_eq_sum_self_mul_star
    (K : A → Matrix m m ℂ) (x : m × m → ℂ) :
    star x ⬝ᵥ (choi K) *ᵥ x
      = ∑ α, (∑ ij : m × m, star (x ij) * K α ij.2 ij.1)
              * star (∑ ij : m × m, star (x ij) * K α ij.2 ij.1) := by
  -- Step 1: Expand LHS to a triple sum (over ij, ij', α).
  rw [dotProduct]
  -- LHS = ∑ ij, (star x) ij * ((choi K) *ᵥ x) ij
  --     = ∑ ij, ∑ ij', ∑ α, star (x ij) * (K α ij.2 ij.1 * star (K α ij'.2 ij'.1)) * x ij'
  have hLHS :
      ∑ ij : m × m, (star x) ij * ((choi K) *ᵥ x) ij
        = ∑ ij : m × m, ∑ ij' : m × m,
            ∑ α, star (x ij) * (K α ij.2 ij.1 * star (K α ij'.2 ij'.1)) * x ij' := by
    apply Finset.sum_congr rfl
    intro ij _
    -- (star x) ij = star (x ij)
    change star (x ij) * ((choi K) *ᵥ x) ij = _
    rw [Matrix.mulVec, dotProduct, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro ij' _
    rw [choi_apply]
    rw [Finset.sum_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro α _
    ring
  rw [hLHS]
  -- Step 2: Swap the triple sum to put α outermost.
  -- Current:  ∑ ij, ∑ ij', ∑ α, F ij ij' α
  -- Target:   ∑ α, ∑ ij, ∑ ij', F ij ij' α
  have h_swap_inner :
      (∑ ij : m × m, ∑ ij' : m × m, ∑ α,
            star (x ij) * (K α ij.2 ij.1 * star (K α ij'.2 ij'.1)) * x ij')
        = ∑ ij : m × m, ∑ α, ∑ ij' : m × m,
            star (x ij) * (K α ij.2 ij.1 * star (K α ij'.2 ij'.1)) * x ij' := by
    apply Finset.sum_congr rfl
    intro ij _
    rw [Finset.sum_comm]
  rw [h_swap_inner]
  rw [Finset.sum_comm]
  -- Step 3: For each α, the inner double sum factors as cα * star cα.
  apply Finset.sum_congr rfl
  intro α _
  -- ∑ ij, ∑ ij', star (x ij) * (K α ij.2 ij.1 * star (K α ij'.2 ij'.1)) * x ij'
  --   = (∑ ij, star (x ij) * K α ij.2 ij.1) * star (∑ ij', star (x ij') * K α ij'.2 ij'.1)
  rw [star_sum]
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro ij _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro ij' _
  rw [StarMul.star_mul, star_star]
  ring

/-- **THE KEYSTONE.**  The Choi matrix of a Kraus family is positive
    semidefinite. -/
theorem choi_posSemidef (K : A → Matrix m m ℂ) :
    (choi K).PosSemidef := by
  refine PosSemidef.of_dotProduct_mulVec_nonneg (choi_isHermitian K) ?_
  intro x
  rw [choi_quadForm_eq_sum_self_mul_star]
  -- Each cα * star cα ≥ 0 (it equals ‖cα‖² as a complex number, which
  -- is nonneg under the order on ℂ).
  apply Finset.sum_nonneg
  intro α _
  -- For any z : ℂ, 0 ≤ z * star z, since z * star z = (Complex.normSq z : ℂ)
  -- and Complex.normSq z ≥ 0 in ℝ ⊆ ℂ.
  set z : ℂ := ∑ ij : m × m, star (x ij) * K α ij.2 ij.1
  have h_eq : z * star z = ((Complex.normSq z : ℝ) : ℂ) := by
    have h := Complex.mul_conj z
    -- h : z * (starRingEnd ℂ) z = ↑(Complex.normSq z)
    -- (starRingEnd ℂ) z = star z
    change z * star z = ((Complex.normSq z : ℝ) : ℂ)
    convert h using 1
  rw [h_eq]
  -- 0 ≤ ((Complex.normSq z : ℝ) : ℂ) under ComplexOrder.
  have h_nn : (0 : ℝ) ≤ Complex.normSq z := Complex.normSq_nonneg z
  -- Cast nonneg real to nonneg complex (on the real axis).
  exact_mod_cast h_nn

/-! ## 4. The Kraus channel and the Choi acts-on-density identity -/

/-- The Kraus channel from a Kraus family:
    `Φ(ρ) := Σ_α K_α · ρ · K_α†`. -/
noncomputable def krausChannel (K : A → Matrix m m ℂ) (ρ : Matrix m m ℂ) :
    Matrix m m ℂ :=
  ∑ α, K α * ρ * (K α).conjTranspose

/-- **Channel acts via the Choi matrix.**  Reading off matrix elements:

      `Φ(ρ)_{j, j'} = Σ_{i, i'} ρ_{i, i'} · Choi(K)_{(i, j), (i', j')}`.

    This is the standard Choi–Jamiolkowski formula, made entry-level
    explicit for the indexing convention `Choi(K)_{(i,j),(i',j')} :=
    Σ_α (K_α)_{j,i} · conj((K_α)_{j',i'})`. -/
theorem krausChannel_eq_choi_apply (K : A → Matrix m m ℂ) (ρ : Matrix m m ℂ)
    (j j' : m) :
    (krausChannel K ρ) j j'
      = ∑ i, ∑ i', ρ i i' * choi K (i, j) (i', j') := by
  unfold krausChannel
  -- Push (∑ α, _) j j' onto the indexed sum
  have hLHS : (∑ α, K α * ρ * (K α).conjTranspose) j j'
        = ∑ α, (K α * ρ * (K α).conjTranspose) j j' := by
    rw [Finset.sum_apply j Finset.univ (fun α => K α * ρ * (K α).conjTranspose)]
    rw [Finset.sum_apply j' Finset.univ
      (fun α => (K α * ρ * (K α).conjTranspose) j)]
  rw [hLHS]
  -- Expand each ((K α * ρ) * (K α)†) j j' to ∑ i ∑ i', K α j i * ρ i i' * star (K α j' i')
  have h_term : ∀ α,
      (K α * ρ * (K α).conjTranspose) j j'
        = ∑ i, ∑ i', K α j i * ρ i i' * star (K α j' i') := by
    intro α
    rw [Matrix.mul_apply]
    -- ((K α * ρ) * (K α)†) j j' = ∑ s, (K α * ρ) j s * ((K α)†) s j'
    have h_inner : ∀ s,
        (K α * ρ) j s * (K α).conjTranspose s j'
          = ∑ i, K α j i * ρ i s * star (K α j' s) := by
      intro s
      rw [Matrix.mul_apply, Matrix.conjTranspose_apply]
      rw [Finset.sum_mul]
    rw [Finset.sum_congr rfl (fun s _ => h_inner s)]
    -- Now: ∑ s, ∑ i, K α j i * ρ i s * star (K α j' s)
    -- Reindex: s plays the role of i', i is inner. Swap to ∑ i, ∑ s.
    rw [Finset.sum_comm]
  simp_rw [h_term]
  -- LHS = ∑ α, ∑ i, ∑ i', K α j i * ρ i i' * star (K α j' i')
  -- Goal: ... = ∑ i, ∑ i', ρ i i' * choi K (i, j) (i', j')
  -- Bring ∑ α to the inside, matching choi.
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i' _
  rw [choi_apply]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro α _
  ring

/-! ## 5. Partial-trace identities (bonus)

Under the indexing convention `Choi(K)_{(i,j),(i',j')} :=
Σ_α (K_α)_{j,i} · star((K_α)_{j',i'})`, the **left** partial trace
(tracing out the first / "input" factor) gives the output state of
the channel applied to the maximally mixed input:

    `Tr_1 (Choi K) = Σ_α K_α · K_α†`,

i.e., `partialTrace_left (choi K) = Φ(I)`.  The **right** partial trace
gives the (transpose of the) "trace-preserving" Stinespring sum:

    `(Tr_2 (Choi K))_{i,i'} = Σ_α (K_α† · K_α)_{i',i}`,

so the channel is trace-preserving iff this equals `I_{i',i} = δ_{i,i'}`
iff `Σ_α K_α† · K_α = I`.
-/

/-- **Left partial trace of Choi = channel applied to the identity.**

    `partialTrace_left (choi K) = Σ_α K_α · K_α†  =  Φ(I)`. -/
theorem partialTrace_left_choi (K : A → Matrix m m ℂ) :
    UnifiedTheory.LayerB.PartialTrace.partialTrace_left (choi K)
      = ∑ α, K α * (K α).conjTranspose := by
  ext j j'
  unfold UnifiedTheory.LayerB.PartialTrace.partialTrace_left
  -- LHS = ∑ i, choi K (i, j) (i, j') = ∑ i, ∑ α, (K α j i) * star (K α j' i)
  have hLHS : ∀ i,
      choi K (i, j) (i, j') = ∑ α, K α j i * star (K α j' i) := by
    intro i; rfl
  rw [Finset.sum_congr rfl (fun i _ => hLHS i)]
  -- Swap ∑ i ↔ ∑ α
  rw [Finset.sum_comm]
  -- RHS = (∑ α, K α * (K α)†) j j' = ∑ α, (K α * (K α)†) j j'
  have hRHS : (∑ α, K α * (K α).conjTranspose) j j'
        = ∑ α, (K α * (K α).conjTranspose) j j' := by
    rw [Finset.sum_apply j Finset.univ (fun α => K α * (K α).conjTranspose)]
    rw [Finset.sum_apply j' Finset.univ (fun α => (K α * (K α).conjTranspose) j)]
  rw [hRHS]
  -- For each α: (K α * (K α)†) j j' = ∑ i, K α j i * star (K α j' i)
  apply Finset.sum_congr rfl
  intro α _
  rw [Matrix.mul_apply]
  apply Finset.sum_congr rfl
  intro i _
  rw [Matrix.conjTranspose_apply]

/-- **Right partial trace of Choi = transpose of `Σ_α K_α† · K_α`.**

    `(partialTrace_right (choi K))_{i, i'} = (Σ_α K_α† · K_α)_{i', i}`. -/
theorem partialTrace_right_choi (K : A → Matrix m m ℂ) (i i' : m) :
    UnifiedTheory.LayerB.PartialTrace.partialTrace_right (choi K) i i'
      = (∑ α, (K α).conjTranspose * K α) i' i := by
  unfold UnifiedTheory.LayerB.PartialTrace.partialTrace_right
  -- LHS = ∑ j, choi K (i, j) (i', j) = ∑ j, ∑ α, K α j i * star (K α j i')
  have hLHS : ∀ j,
      choi K (i, j) (i', j) = ∑ α, K α j i * star (K α j i') := by
    intro j; rfl
  rw [Finset.sum_congr rfl (fun j _ => hLHS j)]
  rw [Finset.sum_comm]
  -- RHS = (∑ α, (K α)† * K α) i' i
  --     = ∑ α, ((K α)† * K α) i' i
  --     = ∑ α, ∑ j, (K α)† i' j * K α j i
  --     = ∑ α, ∑ j, star (K α j i') * K α j i
  rw [Finset.sum_apply i' Finset.univ (fun α => (K α).conjTranspose * K α)]
  rw [Finset.sum_apply i Finset.univ
    (fun α => ((K α).conjTranspose * K α) i')]
  apply Finset.sum_congr rfl
  intro α _
  rw [Matrix.mul_apply]
  apply Finset.sum_congr rfl
  intro j _
  rw [Matrix.conjTranspose_apply]
  ring

end UnifiedTheory.LayerB.ChoiKraus
