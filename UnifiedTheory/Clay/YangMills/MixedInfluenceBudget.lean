/- Exact algebra for the mixed-interaction budget after one-site elimination.
Retained couplings acquire a two-step term; the deleted column pays its row
cost when the original nonnegative influence rows are at most one. -/
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace UnifiedTheory.Clay.YangMills.MixedInfluenceBudget
noncomputable section

variable {I : Type*} [DecidableEq I]

/-- Delete the integrated coordinate and retain the new two-step coupling. -/
def step (c : I → I → ℝ) (e i j : I) : ℝ :=
  if i = e ∨ j = e ∨ i = j then 0 else c i j + c i e * c e j

theorem step_nonneg (c : I → I → ℝ) (hc : ∀ i j, 0 ≤ c i j) (e i j : I) :
    0 ≤ step c e i j := by
  unfold step
  split
  · exact le_rfl
  · exact add_nonneg (hc i j) (mul_nonneg (hc i e) (hc e j))

theorem step_diagonal (c : I → I → ℝ) (e i : I) : step c e i i = 0 := by
  simp [step]

theorem step_eliminated (c : I → I → ℝ) (e i : I) :
    step c e e i = 0 ∧ step c e i e = 0 := by simp [step]

theorem step_symmetric (c : I → I → ℝ) (hc : ∀ i j, c i j = c j i) (e i j : I) :
    step c e i j = step c e j i := by
  by_cases hi : i = e
  · subst i
    simp [step]
  by_cases hj : j = e
  · subst j
    simp [step]
  by_cases hij : i = j
  · subst j
    rfl
  simp only [step, hi, hj, hij, Ne.symm hij, or_self, ↓reduceIte]
  rw [hc i j, hc i e, hc e j, mul_comm]

/-- Elimination can increase individual retained interaction bounds. -/
theorem retained_le_step (c : I → I → ℝ) (hc : ∀ i j, 0 ≤ c i j)
    (e i j : I) (hi : i ≠ e) (hj : j ≠ e) (hij : i ≠ j) :
    c i j ≤ step c e i j := by
  simp only [step, hi, hj, hij, or_self, ↓reduceIte]
  exact le_add_of_nonneg_right (mul_nonneg (hc i e) (hc e j))

variable [Fintype I]

/-- A row pays for newly generated couplings using the removed column. -/
theorem row_step_bound (c : I → I → ℝ) (hc : ∀ i j, 0 ≤ c i j)
    (hdiag : ∀ i, c i i = 0) (e i : I) (hi : i ≠ e) :
    ∑ j, step c e i j ≤ (∑ j, c i j) - c i e + c i e * (∑ j, c e j) := by
  have hp (j : I) : step c e i j ≤
      c i j + c i e * c e j - if j = e then c i e else 0 := by
    by_cases hj : j = e
    · subst j
      simp [step, hdiag]
    · by_cases hij : i = j
      · subst j
        simp only [step_diagonal, if_neg hi, sub_zero, hdiag, zero_add]
        exact mul_nonneg (hc i e) (hc e i)
      · simp only [step, hi, hj, hij, or_self, ↓reduceIte, sub_zero, le_refl]
  calc
    _ ≤ ∑ j, (c i j + c i e * c e j - if j = e then c i e else 0) :=
      Finset.sum_le_sum (fun j _ => hp j)
    _ = _ := by
      rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum]
      simp
      ring

/-- The same row budget survives elimination whenever it is at most one. -/
theorem row_step_le (c : I → I → ℝ) (hc : ∀ i j, 0 ≤ c i j)
    (hdiag : ∀ i, c i i = 0) (α : ℝ) (hα0 : 0 ≤ α) (hα1 : α ≤ 1)
    (hrow : ∀ i, ∑ j, c i j ≤ α) (e i : I) : ∑ j, step c e i j ≤ α := by
  by_cases hi : i = e
  · subst i
    simpa [step] using hα0
  · have hs := row_step_bound c hc hdiag e i hi
    have hm := mul_le_mul_of_nonneg_left (hrow e) (hc i e)
    have hn := mul_nonneg (sub_nonneg.mpr hα1) (hc i e)
    linarith [hrow i]

/-- Every stage includes the couplings actually created in the preceding step. -/
def iterate (c : I → I → ℝ) (E : ℕ → I) : ℕ → I → I → ℝ
  | 0 => c
  | k + 1 => step (iterate c E k) (E k)

/-- No repeated smallness premise is needed after the initial budget has been established. -/
theorem iterate_properties (c : I → I → ℝ) (hc : ∀ i j, 0 ≤ c i j)
    (hsym : ∀ i j, c i j = c j i) (hdiag : ∀ i, c i i = 0)
    (α : ℝ) (hα0 : 0 ≤ α) (hα1 : α ≤ 1) (hrow : ∀ i, ∑ j, c i j ≤ α)
    (E : ℕ → I) : ∀ k,
      (∀ i j, 0 ≤ iterate c E k i j) ∧
      (∀ i j, iterate c E k i j = iterate c E k j i) ∧
      (∀ i, iterate c E k i i = 0) ∧
      (∀ i, ∑ j, iterate c E k i j ≤ α) := by
  intro k
  induction k with
  | zero => exact ⟨hc, hsym, hdiag, hrow⟩
  | succ k ih =>
      exact ⟨step_nonneg _ ih.1 _, step_symmetric _ ih.2.1 _, step_diagonal _ _,
        row_step_le _ ih.1 ih.2.2.1 α hα0 hα1 ih.2.2.2 _⟩

end
end UnifiedTheory.Clay.YangMills.MixedInfluenceBudget
