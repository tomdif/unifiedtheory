/- Submultiplicative spatial weights survive the exact mixed-interaction
elimination majorant. No finite-range or coloring property is required of
the generated interactions. -/
import UnifiedTheory.Clay.YangMills.MixedInfluenceBudget

set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace UnifiedTheory.Clay.YangMills.WeightedMixedInfluence
noncomputable section
open MixedInfluenceBudget

variable {I : Type*} [Fintype I] [DecidableEq I]

omit [Fintype I] in
/-- Weighting commutes with elimination up to a favorable inequality. -/
theorem weighted_step (c w : I → I → ℝ) (hc : ∀ i j, 0 ≤ c i j)
    (htriangle : ∀ i e j, w i j ≤ w i e * w e j) (e i j : I) :
    w i j * step c e i j ≤ step (fun i j => w i j * c i j) e i j := by
  unfold step
  split
  · simp
  · have h := mul_le_mul_of_nonneg_right (htriangle i e j)
      (mul_nonneg (hc i e) (hc e j))
    nlinarith only [h]

/-- An initially small weighted row budget remains small after one integration. -/
theorem row_step (c w : I → I → ℝ) (hc : ∀ i j, 0 ≤ c i j)
    (hw : ∀ i j, 0 ≤ w i j) (hdiag : ∀ i, c i i = 0)
    (htriangle : ∀ i e j, w i j ≤ w i e * w e j)
    (α : ℝ) (hα0 : 0 ≤ α) (hα1 : α ≤ 1)
    (hrow : ∀ i, ∑ j, w i j * c i j ≤ α) (e i : I) :
    ∑ j, w i j * step c e i j ≤ α := by
  exact (Finset.sum_le_sum (fun j _ => weighted_step c w hc htriangle e i j)).trans
    (row_step_le (fun i j => w i j * c i j)
      (fun i j => mul_nonneg (hw i j) (hc i j)) (by simp [hdiag])
      α hα0 hα1 hrow e i)

/-- The weighted estimate holds at every finite depth, with no stagewise smallness premise. -/
theorem iterate_rows (c w : I → I → ℝ) (hc : ∀ i j, 0 ≤ c i j)
    (hw : ∀ i j, 0 ≤ w i j) (hdiag : ∀ i, c i i = 0)
    (htriangle : ∀ i e j, w i j ≤ w i e * w e j)
    (α : ℝ) (hα0 : 0 ≤ α) (hα1 : α ≤ 1)
    (hrow : ∀ i, ∑ j, w i j * c i j ≤ α) (E : ℕ → I) :
    ∀ k, (∀ i j, 0 ≤ iterate c E k i j) ∧
      (∀ i, iterate c E k i i = 0) ∧
      (∀ i, ∑ j, w i j * iterate c E k i j ≤ α) := by
  intro k
  induction k with
  | zero => exact ⟨hc, hdiag, hrow⟩
  | succ k ih =>
      exact ⟨step_nonneg _ ih.1 _, step_diagonal _ _,
        row_step _ w ih.1 hw ih.2.1 htriangle α hα0 hα1 ih.2.2 _⟩

omit [Fintype I] [DecidableEq I] in
/-- Exponential metric weights are submultiplicative. -/
theorem exp_triangle (d : I → I → ℝ) (hd : ∀ i e j, d i j ≤ d i e + d e j)
    (m : ℝ) (hm : 0 ≤ m) (i e j : I) :
    Real.exp (m * d i j) ≤ Real.exp (m * d i e) * Real.exp (m * d e j) := by
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  nlinarith [hd i e j]

omit [DecidableEq I] in
/-- An exponential row bound gives a pointwise decay estimate for each generated coefficient. -/
theorem entry_decay (c : I → I → ℝ) (hc : ∀ i j, 0 ≤ c i j)
    (d : I → I → ℝ) (m α : ℝ)
    (hrow : ∀ i, ∑ j, Real.exp (m * d i j) * c i j ≤ α) (i j : I) :
    c i j ≤ α * Real.exp (-m * d i j) := by
  have h : Real.exp (m * d i j) * c i j ≤ α :=
    (Finset.single_le_sum (fun k _ => mul_nonneg (Real.exp_pos (m * d i k)).le (hc i k))
      (Finset.mem_univ j)).trans (hrow i)
  have h' := mul_le_mul_of_nonneg_left h (Real.exp_pos (-m * d i j)).le
  have he : Real.exp (-m * d i j) * Real.exp (m * d i j) = 1 := by
    rw [← Real.exp_add]
    have hz : -m * d i j + m * d i j = 0 := by ring
    rw [hz, Real.exp_zero]
  rw [← mul_assoc, he, one_mul] at h'
  simpa only [mul_comm] using h'

omit [DecidableEq I] in
/-- Ordinary rows are bounded by weighted rows when every weight is at least one. -/
theorem unweighted_row (c w : I → I → ℝ) (hc : ∀ i j, 0 ≤ c i j)
    (hw : ∀ i j, 1 ≤ w i j) (α : ℝ)
    (hrow : ∀ i, ∑ j, w i j * c i j ≤ α) (i : I) : ∑ j, c i j ≤ α := by
  apply le_trans (Finset.sum_le_sum (fun j _ => ?_)) (hrow i)
  simpa only [one_mul] using mul_le_mul_of_nonneg_right (hw i j) (hc i j)

end
end UnifiedTheory.Clay.YangMills.WeightedMixedInfluence
