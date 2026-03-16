/-
  LayerA/SparseSum.lean — Sparse vector double sum reduction

  One utility: if w is zero outside {a, b}, the double sum collapses.
-/
import Mathlib.Analysis.Normed.Field.Basic

namespace UnifiedTheory.LayerA.SparseSum

/-- Two-element sum extraction: if f vanishes outside {a, b}, Σf = f(a) + f(b). -/
lemma sum_pair {n : ℕ} (f : Fin n → ℝ) (a b : Fin n) (hab : a ≠ b)
    (hf : ∀ i, i ≠ a → i ≠ b → f i = 0) :
    ∑ i : Fin n, f i = f a + f b := by
  classical
  have key : ∀ i, i ≠ a → i ≠ b → f i = 0 := hf
  have ha_mem : a ∈ Finset.univ (α := Fin n) := Finset.mem_univ a
  have hb_mem : b ∈ Finset.univ (α := Fin n) := Finset.mem_univ b
  have : (∑ i : Fin n, f i) = (∑ i ∈ ({a, b} : Finset (Fin n)), f i) := by
    symm; apply Finset.sum_subset (Finset.subset_univ _)
    intro i _ hi; simp at hi; exact hf i hi.1 hi.2
  rw [this, Finset.sum_pair hab]

/-- **Two-support double sum (symmetric M).**
    If w is zero outside {a, b} and M is symmetric:
    ∑ᵢ ∑ⱼ M(i,j)w(i)w(j) = M(a,a)w(a)² + 2M(a,b)w(a)w(b) + M(b,b)w(b)² -/
theorem double_sum_two_support_sym {n : ℕ}
    (M : Fin n → Fin n → ℝ) (hSym : ∀ i j, M i j = M j i)
    (w : Fin n → ℝ) (a b : Fin n) (hab : a ≠ b)
    (hw : ∀ i, i ≠ a → i ≠ b → w i = 0) :
    ∑ i : Fin n, ∑ j : Fin n, M i j * w i * w j =
    M a a * w a * w a + 2 * M a b * w a * w b + M b b * w b * w b := by
  -- Outer: kill i ∉ {a, b}
  have houter : ∀ i, i ≠ a → i ≠ b → (∑ j, M i j * w i * w j) = 0 := by
    intro i ha hb; apply Finset.sum_eq_zero; intro j _
    simp [hw i ha hb]
  rw [sum_pair _ a b hab houter]
  -- Inner at a: kill j ∉ {a, b}
  have hinner_a : ∀ j, j ≠ a → j ≠ b → M a j * w a * w j = 0 := by
    intro j hja hjb; simp [hw j hja hjb]
  rw [sum_pair _ a b hab hinner_a]
  -- Inner at b: kill j ∉ {a, b}
  have hinner_b : ∀ j, j ≠ a → j ≠ b → M b j * w b * w j = 0 := by
    intro j hja hjb; simp [hw j hja hjb]
  rw [sum_pair _ a b hab hinner_b]
  -- Now: M a a * w a * w a + M a b * w a * w b +
  --     (M b a * w b * w a + M b b * w b * w b)
  -- Use symmetry M b a = M a b, then ring
  rw [hSym b a]; ring

/-- **Three-support sum extraction.**
    If f vanishes outside {a, b, c} (all distinct), Σf = f(a)+f(b)+f(c). -/
lemma sum_triple {n : ℕ} (f : Fin n → ℝ) (a b c : Fin n)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hf : ∀ i, i ≠ a → i ≠ b → i ≠ c → f i = 0) :
    ∑ i : Fin n, f i = f a + f b + f c := by
  classical
  have : (∑ i : Fin n, f i) = (∑ i ∈ ({a, b, c} : Finset (Fin n)), f i) := by
    symm; apply Finset.sum_subset (Finset.subset_univ _)
    intro i _ hi
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hi
    exact hf i hi.1 hi.2.1 hi.2.2
  rw [this]
  rw [show ({a, b, c} : Finset (Fin n)) = {a, b, c} from rfl]
  have ha_not : a ∉ ({b, c} : Finset (Fin n)) := by
    intro h; simp only [Finset.mem_insert, Finset.mem_singleton] at h
    rcases h with rfl | rfl <;> contradiction
  rw [Finset.sum_insert ha_not]
  rw [Finset.sum_pair hbc]

/-- **Three-support double sum (symmetric M).** -/
theorem double_sum_three_support_sym {n : ℕ}
    (M : Fin n → Fin n → ℝ) (hSym : ∀ i j, M i j = M j i)
    (w : Fin n → ℝ) (a b c : Fin n)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hw : ∀ i, i ≠ a → i ≠ b → i ≠ c → w i = 0) :
    ∑ i : Fin n, ∑ j : Fin n, M i j * w i * w j =
    M a a * w a * w a + 2 * M a b * w a * w b + 2 * M a c * w a * w c +
    M b b * w b * w b + 2 * M b c * w b * w c +
    M c c * w c * w c := by
  -- Outer: kill i ∉ {a, b, c}
  have houter : ∀ i, i ≠ a → i ≠ b → i ≠ c →
      (∑ j, M i j * w i * w j) = 0 := by
    intro i ha hb hc; apply Finset.sum_eq_zero; intro j _; simp [hw i ha hb hc]
  rw [sum_triple _ a b c hab hac hbc houter]
  -- Inner at a:
  have ha_inner : ∀ j, j ≠ a → j ≠ b → j ≠ c → M a j * w a * w j = 0 := by
    intro j hja hjb hjc; simp [hw j hja hjb hjc]
  rw [sum_triple _ a b c hab hac hbc ha_inner]
  -- Inner at b:
  have hb_inner : ∀ j, j ≠ a → j ≠ b → j ≠ c → M b j * w b * w j = 0 := by
    intro j hja hjb hjc; simp [hw j hja hjb hjc]
  rw [sum_triple _ a b c hab hac hbc hb_inner]
  -- Inner at c:
  have hc_inner : ∀ j, j ≠ a → j ≠ b → j ≠ c → M c j * w c * w j = 0 := by
    intro j hja hjb hjc; simp [hw j hja hjb hjc]
  rw [sum_triple _ a b c hab hac hbc hc_inner]
  -- Use symmetry and ring
  rw [hSym b a, hSym c a, hSym c b]; ring

end UnifiedTheory.LayerA.SparseSum
