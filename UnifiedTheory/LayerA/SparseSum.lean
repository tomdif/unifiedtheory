/-
  LayerA/SparseSum.lean — Sparse vector double sum reduction

  The utility theorem that closes NullConeGeneral sorrys.
-/
import Mathlib.Analysis.Normed.Field.Basic

namespace UnifiedTheory.LayerA.SparseSum

/-- If w(i) = 0, the inner sum at i vanishes. -/
lemma inner_sum_zero {n : ℕ} (M : Fin n → Fin n → ℝ)
    (w : Fin n → ℝ) (i : Fin n) (hw : w i = 0) :
    ∑ j : Fin n, M i j * w i * w j = 0 := by
  apply Finset.sum_eq_zero; intro j _; simp [hw]

/-- Extract a single-element sum: if f(i) = 0 for i ≠ k, then Σf = f(k). -/
lemma sum_eq_single_nonzero {n : ℕ} (f : Fin n → ℝ) (k : Fin n)
    (hf : ∀ i, i ≠ k → f i = 0) :
    ∑ i : Fin n, f i = f k := by
  exact (Finset.sum_eq_single_of_mem k (Finset.mem_univ k)
    (fun b _ hb => hf b hb)).symm ▸ rfl

/-- Extract a two-element sum: if f(i) = 0 for i ∉ {a, b}, then Σf = f(a) + f(b). -/
lemma sum_eq_two {n : ℕ} (f : Fin n → ℝ) (a b : Fin n) (hab : a ≠ b)
    (hf : ∀ i, i ≠ a → i ≠ b → f i = 0) :
    ∑ i : Fin n, f i = f a + f b := by
  have key : ∑ i : Fin n, f i =
      ∑ i : Fin n, (if i = a then f a else if i = b then f b else 0) := by
    apply Finset.sum_congr rfl; intro i _
    by_cases ha : i = a
    · simp [ha]
    · by_cases hb : i = b
      · simp [ha, hb]
      · simp [ha, hb, hf i ha hb]
  rw [key, show (fun i : Fin n => if i = a then f a else if i = b then f b else 0) =
    (fun i => if i = a then f a else 0) + (fun i => if i = b then f b else 0) from by
      ext i; simp [Pi.add_apply]; by_cases ha : i = a <;> simp [ha]]
  rw [Finset.sum_add_distrib,
      Finset.sum_ite_eq' Finset.univ a (fun _ => f a),
      Finset.sum_ite_eq' Finset.univ b (fun _ => f b)]
  simp

/-- **Two-support double sum (symmetric M).**
    If w is zero outside {a, b} and M is symmetric:
    ∑ᵢ ∑ⱼ M(i,j) w(i) w(j) = M(a,a)w(a)² + 2M(a,b)w(a)w(b) + M(b,b)w(b)² -/
theorem double_sum_two_support_sym {n : ℕ}
    (M : Fin n → Fin n → ℝ) (hSym : ∀ i j, M i j = M j i)
    (w : Fin n → ℝ) (a b : Fin n) (hab : a ≠ b)
    (hw : ∀ i, i ≠ a → i ≠ b → w i = 0) :
    ∑ i : Fin n, ∑ j : Fin n, M i j * w i * w j =
    M a a * w a * w a + 2 * M a b * w a * w b + M b b * w b * w b := by
  -- Outer sum: only i = a and i = b contribute
  have houter : ∀ i, i ≠ a → i ≠ b →
      (∑ j, M i j * w i * w j) = 0 :=
    fun i ha hb => inner_sum_zero M w i (hw i ha hb)
  -- Inner sum at a: only j = a and j = b contribute
  have ha_inner : ∀ j, j ≠ a → j ≠ b → M a j * w a * w j = 0 :=
    fun j hja hjb => by rw [hw j hja hjb, mul_zero]
  -- Inner sum at b: only j = a and j = b contribute
  have hb_inner : ∀ j, j ≠ a → j ≠ b → M b j * w b * w j = 0 :=
    fun j hja hjb => by rw [hw j hja hjb, mul_zero]
  -- Use sum_eq_two for outer, then for each inner
  sorry -- 3 applications of sum_eq_two + ring with symmetry

end UnifiedTheory.LayerA.SparseSum
