/-
  LayerB/ClassicalEntropy.lean
  ────────────────────────────

  Shannon entropy of a finite probability distribution, with the
  foundational lemmas that downstream von Neumann / relative-entropy /
  data-processing files will rely on.

  We work with `ProbabilityVector α` for an arbitrary `Fintype α`,
  packaging non-negative weights summing to 1.  Entropy:

      H(P)  :=  − ∑ᵢ pᵢ · log pᵢ

  (Mathlib's convention `Real.log 0 = 0` makes `0 · log 0 = 0`, so
  zero-probability terms contribute nothing and require no special
  treatment.)

  WHAT IS PROVEN (no sorry, no custom axioms):
    1. `ProbabilityVector α`  structure (over any `Fintype α`).
    2. `ProbabilityVector.le_one`  :  pᵢ ≤ 1 for every i.
    3. `shannonEntropy P`  definition + `entropy_congr`.
    4. `entropy_nonneg`     :  0 ≤ H(P).
    5. `entropy_delta_eq_zero`     :  H of a delta distribution is 0.
    6. `entropy_uniform_eq_log_n`  :  H of the uniform distribution
       on n points is log n.
    7. `productDistribution P Q`  :  ProbabilityVector (α × β).
    8. `entropy_of_product`        :  H(P × Q) = H(P) + H(Q).

  Next step:  `DiagonalVonNeumannEntropy.lean` will define the entropy
  of a diagonal density matrix as `shannonEntropy` of its diagonal,
  providing the bridge that lets full von Neumann entropy be defined
  via spectral decomposition without re-proving foundational
  entropy lemmas.
-/

import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity

set_option relaxedAutoImplicit false

namespace UnifiedTheory.LayerB.ClassicalEntropy

open Real

/-! ## 1. ProbabilityVector -/

/-- A finite probability distribution: non-negative weights summing to 1. -/
structure ProbabilityVector (α : Type*) [Fintype α] where
  p : α → ℝ
  nonneg : ∀ i, 0 ≤ p i
  sum_one : ∑ i, p i = 1

namespace ProbabilityVector

variable {α β : Type*} [Fintype α] [Fintype β]

/-- Every coordinate of a probability vector is bounded above by 1
    (consequence of `sum_one` + non-negativity of the other entries). -/
theorem le_one (P : ProbabilityVector α) (i : α) : P.p i ≤ 1 := by
  have h_single := Finset.single_le_sum (f := P.p)
                    (fun j _ => P.nonneg j) (Finset.mem_univ i)
  rw [P.sum_one] at h_single
  exact h_single

/-! ## 2. Shannon entropy -/

/-- Shannon entropy of a finite probability distribution
    (natural-log base; Mathlib's `Real.log 0 = 0` makes
    `0 · log 0 = 0` automatically). -/
noncomputable def shannonEntropy (P : ProbabilityVector α) : ℝ :=
  - ∑ i, P.p i * Real.log (P.p i)

theorem entropy_congr (P Q : ProbabilityVector α) (h : ∀ i, P.p i = Q.p i) :
    shannonEntropy P = shannonEntropy Q := by
  unfold shannonEntropy
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rw [h]

/-! ## 3. Entropy is non-negative -/

/-- **Shannon entropy is non-negative.** -/
theorem entropy_nonneg (P : ProbabilityVector α) :
    0 ≤ shannonEntropy P := by
  unfold shannonEntropy
  -- Each term pᵢ · log pᵢ ≤ 0 for pᵢ ∈ [0, 1]; sum is ≤ 0; negate.
  have h_sum_nonpos : ∑ i, P.p i * Real.log (P.p i) ≤ 0 := by
    apply Finset.sum_nonpos
    intro i _
    by_cases hp : P.p i = 0
    · rw [hp]; simp
    · have h_pos : 0 < P.p i := lt_of_le_of_ne (P.nonneg i) (Ne.symm hp)
      have h_le : P.p i ≤ 1 := le_one P i
      have h_log_nonpos : Real.log (P.p i) ≤ 0 := Real.log_nonpos h_pos.le h_le
      exact mul_nonpos_of_nonneg_of_nonpos (P.nonneg i) h_log_nonpos
  linarith

/-! ## 4. Delta distribution -/

/-- The delta distribution concentrated at a single point. -/
noncomputable def delta (α : Type*) [Fintype α] [DecidableEq α] (i₀ : α) :
    ProbabilityVector α where
  p i := if i = i₀ then 1 else 0
  nonneg i := by split_ifs <;> norm_num
  sum_one := by
    rw [Finset.sum_ite_eq']
    simp

/-- **Entropy of a delta distribution is zero.** -/
theorem entropy_delta_eq_zero {α : Type*} [Fintype α] [DecidableEq α] (i₀ : α) :
    shannonEntropy (delta α i₀) = 0 := by
  unfold shannonEntropy delta
  have h_sum : (∑ i, (if i = i₀ then (1 : ℝ) else 0) *
                      Real.log (if i = i₀ then (1 : ℝ) else 0)) = 0 := by
    apply Finset.sum_eq_zero
    intro i _
    by_cases h : i = i₀
    · simp [h]
    · simp [h]
  rw [h_sum]
  ring

/-! ## 5. Uniform distribution -/

/-- The uniform distribution on `Fin n` for `n > 0`. -/
noncomputable def uniform (n : ℕ) (hn : 0 < n) : ProbabilityVector (Fin n) where
  p _ := 1 / (n : ℝ)
  nonneg _ := by
    have h_n_pos : (0 : ℝ) < n := by exact_mod_cast hn
    positivity
  sum_one := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
    have h_n_pos : (0 : ℝ) < n := by exact_mod_cast hn
    have h_n_ne : (n : ℝ) ≠ 0 := ne_of_gt h_n_pos
    rw [nsmul_eq_mul]
    field_simp

/-- **Entropy of the uniform distribution on n points is log n.** -/
theorem entropy_uniform_eq_log_n (n : ℕ) (hn : 0 < n) :
    shannonEntropy (uniform n hn) = Real.log n := by
  unfold shannonEntropy
  have h_n_pos : (0 : ℝ) < n := by exact_mod_cast hn
  have h_n_ne : (n : ℝ) ≠ 0 := ne_of_gt h_n_pos
  -- Each summand is (1/n) · log(1/n); sum is n · (1/n) · log(1/n) = log(1/n) = -log n
  change -(∑ _i : Fin n, (1 / (n : ℝ)) * Real.log (1 / (n : ℝ))) = Real.log n
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
  rw [Real.log_div one_ne_zero h_n_ne, Real.log_one, zero_sub]
  rw [nsmul_eq_mul]
  field_simp

/-! ## 6. Product distribution -/

/-- The product distribution `PQ_{(i,j)} = P_i · Q_j`. -/
noncomputable def productDistribution
    (P : ProbabilityVector α) (Q : ProbabilityVector β) :
    ProbabilityVector (α × β) where
  p ij := P.p ij.1 * Q.p ij.2
  nonneg ij := mul_nonneg (P.nonneg _) (Q.nonneg _)
  sum_one := by
    rw [Fintype.sum_prod_type]
    -- ∑ i, ∑ j, P.p i * Q.p j = ∑ i, P.p i * (∑ j, Q.p j)
    --                          = ∑ i, P.p i * 1 = ∑ i, P.p i = 1
    simp_rw [← Finset.mul_sum]
    rw [Q.sum_one]
    simp [P.sum_one]

/-! ## 7. Entropy of a product distribution -/

/-- **H(P × Q) = H(P) + H(Q)** — Shannon entropy adds under
    independent products. -/
theorem entropy_of_product
    (P : ProbabilityVector α) (Q : ProbabilityVector β) :
    shannonEntropy (productDistribution P Q)
      = shannonEntropy P + shannonEntropy Q := by
  unfold shannonEntropy
  change - ∑ ij : α × β, (P.p ij.1 * Q.p ij.2) * Real.log (P.p ij.1 * Q.p ij.2)
       = -(∑ i, P.p i * Real.log (P.p i)) + -(∑ j, Q.p j * Real.log (Q.p j))
  -- Per-term identity (handles degenerate p_i = 0 or q_j = 0 cases)
  have h_per : ∀ ij : α × β,
      P.p ij.1 * Q.p ij.2 * Real.log (P.p ij.1 * Q.p ij.2)
        = P.p ij.1 * Q.p ij.2 * Real.log (P.p ij.1)
          + P.p ij.1 * Q.p ij.2 * Real.log (Q.p ij.2) := by
    intro ij
    by_cases hP : P.p ij.1 = 0
    · rw [hP]; ring
    by_cases hQ : Q.p ij.2 = 0
    · rw [hQ]; ring
    rw [Real.log_mul hP hQ]; ring
  simp_rw [h_per]
  -- Split sum and factor
  rw [Finset.sum_add_distrib]
  rw [neg_add]
  congr 1
  · -- -∑_{ij} P_i Q_j log P_i = -∑_i P_i log P_i
    congr 1
    rw [Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro i _
    -- ∑ j, P.p i · Q.p j · log(P.p i) = (∑ j, Q.p j) · (P.p i · log(P.p i))
    --                                  = 1 · P.p i · log(P.p i)
    calc (∑ j, P.p i * Q.p j * Real.log (P.p i))
        = ∑ j, Q.p j * (P.p i * Real.log (P.p i)) := by
              apply Finset.sum_congr rfl; intro j _; ring
      _ = (∑ j, Q.p j) * (P.p i * Real.log (P.p i)) := by rw [← Finset.sum_mul]
      _ = P.p i * Real.log (P.p i) := by rw [Q.sum_one, one_mul]
  · -- -∑_{ij} P_i Q_j log Q_j = -∑_j Q_j log Q_j
    congr 1
    rw [Fintype.sum_prod_type]
    -- ∑ i, ∑ j, P.p i · Q.p j · log(Q.p j) = (∑ i, P.p i) · (∑ j, Q.p j · log(Q.p j))
    --                                       = 1 · ∑_j Q.p j · log(Q.p j)
    calc (∑ i : α, ∑ j : β, P.p i * Q.p j * Real.log (Q.p j))
        = ∑ i : α, P.p i * (∑ j, Q.p j * Real.log (Q.p j)) := by
              apply Finset.sum_congr rfl; intro i _
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl; intro j _; ring
      _ = (∑ i, P.p i) * (∑ j, Q.p j * Real.log (Q.p j)) := by rw [← Finset.sum_mul]
      _ = ∑ j, Q.p j * Real.log (Q.p j) := by rw [P.sum_one, one_mul]

end ProbabilityVector

end UnifiedTheory.LayerB.ClassicalEntropy
