/-
  LayerA/SparseSum.lean — Sparse vector double sum reduction (2-support)
-/
import Mathlib.Analysis.Normed.Field.Basic

namespace UnifiedTheory.LayerA.SparseSum

/-- Two-element sum: if f vanishes outside {a, b}, Σf = f(a) + f(b). -/
lemma sum_pair {n : ℕ} (f : Fin n → ℝ) (a b : Fin n) (hab : a ≠ b)
    (hf : ∀ i, i ≠ a → i ≠ b → f i = 0) :
    ∑ i : Fin n, f i = f a + f b := by
  classical
  have : (∑ i : Fin n, f i) = (∑ i ∈ ({a, b} : Finset (Fin n)), f i) := by
    symm; apply Finset.sum_subset (Finset.subset_univ _)
    intro i _ hi
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi
    push_neg at hi; exact hf i hi.1 hi.2
  rw [this, Finset.sum_pair hab]

/-- **Two-support double sum (symmetric M).** -/
theorem double_sum_two_support_sym {n : ℕ}
    (M : Fin n → Fin n → ℝ) (hSym : ∀ i j, M i j = M j i)
    (w : Fin n → ℝ) (a b : Fin n) (hab : a ≠ b)
    (hw : ∀ i, i ≠ a → i ≠ b → w i = 0) :
    ∑ i : Fin n, ∑ j : Fin n, M i j * w i * w j =
    M a a * w a * w a + 2 * M a b * w a * w b + M b b * w b * w b := by
  have houter : ∀ i, i ≠ a → i ≠ b → (∑ j, M i j * w i * w j) = 0 := by
    intro i ha hb; apply Finset.sum_eq_zero; intro j _; simp [hw i ha hb]
  rw [sum_pair _ a b hab houter]
  have ha_inner : ∀ j, j ≠ a → j ≠ b → M a j * w a * w j = 0 := by
    intro j hja hjb; simp [hw j hja hjb]
  rw [sum_pair _ a b hab ha_inner]
  have hb_inner : ∀ j, j ≠ a → j ≠ b → M b j * w b * w j = 0 := by
    intro j hja hjb; simp [hw j hja hjb]
  rw [sum_pair _ a b hab hb_inner]
  rw [hSym b a]; ring

end UnifiedTheory.LayerA.SparseSum
