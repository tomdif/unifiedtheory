/- Weighted coordinate sensitivities for the actual random-site iteration.
The one-site factor will cancel in the covariance resolvent estimate. -/
import UnifiedTheory.Clay.YangMills.ParallelOscillation

set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace UnifiedTheory.Clay.YangMills.WeightedOscillation
noncomputable section
open ParallelOscillation

variable {I : Type*} [Fintype I] [Nonempty I]

theorem weighted_budget (C : I → I → ℝ) (u d : I → ℝ) (α : ℝ)
    (hd : ∀ i, 0 ≤ d i) (hrow : ∀ i, ∑ j, C i j * u j ≤ α * u i) :
    (∑ j, u j * colorBound (Color := I) C d j) ≤
      colorRate (Color := I) α * ∑ i, u i * d i := by
  have hs : (∑ j, u j * ∑ i, C i j * d i) ≤ α * ∑ i, u i * d i := by
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    calc
      _ = ∑ i, (∑ j, C i j * u j) * d i := by
        simp only [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro j _
        ring
      _ ≤ ∑ i, (α * u i) * d i :=
        Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_right (hrow i) (hd i))
      _ = _ := by simp only [mul_assoc]
  have hm := mul_le_mul_of_nonneg_left hs
    (by positivity : 0 ≤ (Fintype.card I : ℝ)⁻¹)
  calc
    _ = (1 - (Fintype.card I : ℝ)⁻¹) * (∑ j, u j * d j) +
        (Fintype.card I : ℝ)⁻¹ * ∑ j, u j * ∑ i, C i j * d i := by
      have he (j : I) : u j * colorBound (Color := I) C d j =
          (1 - (Fintype.card I : ℝ)⁻¹) * (u j * d j) +
          (Fintype.card I : ℝ)⁻¹ * (u j * ∑ i, C i j * d i) := by
        unfold colorBound
        ring
      simp only [he, Finset.sum_add_distrib, ← Finset.mul_sum]
    _ ≤ (1 - (Fintype.card I : ℝ)⁻¹) * (∑ j, u j * d j) +
        (Fintype.card I : ℝ)⁻¹ * (α * ∑ i, u i * d i) := add_le_add le_rfl hm
    _ = _ := by unfold colorRate; ring

theorem weighted_iterate (C : I → I → ℝ) (hC : ∀ i j, 0 ≤ C i j)
    (u d : I → ℝ) (hd : ∀ i, 0 ≤ d i) (α : ℝ) (hα : 0 ≤ α)
    (hrow : ∀ i, ∑ j, C i j * u j ≤ α * u i) (k : ℕ) :
    (∑ j, u j * budgetIterate (Color := I) C k d j) ≤
      colorRate (Color := I) α ^ k * ∑ j, u j * d j := by
  induction k with
  | zero => simp [budgetIterate]
  | succ k ih =>
      calc
        _ ≤ colorRate (Color := I) α *
            ∑ j, u j * budgetIterate (Color := I) C k d j :=
          weighted_budget C u _ α (budgetIterate_nonneg C hC d hd k) hrow
        _ ≤ colorRate (Color := I) α *
            (colorRate (Color := I) α ^ k * ∑ j, u j * d j) :=
          mul_le_mul_of_nonneg_left ih (colorRate_nonneg α hα)
        _ = _ := by rw [pow_succ]; ring

omit [Nonempty I] in
/-- A distance-to-support potential converts pair weights into a site-weight contraction. -/
theorem exp_site_row (C : I → I → ℝ) (hC : ∀ i j, 0 ≤ C i j)
    (d : I → I → ℝ) (r : I → ℝ) (hr : ∀ i j, r i ≤ d i j + r j)
    (m α : ℝ) (hm : 0 ≤ m)
    (hrow : ∀ i, ∑ j, Real.exp (m * d i j) * C i j ≤ α) (i : I) :
    ∑ j, C i j * Real.exp (-m * r j) ≤ α * Real.exp (-m * r i) := by
  calc
    _ ≤ ∑ j, (Real.exp (m * d i j) * C i j) * Real.exp (-m * r i) := by
      apply Finset.sum_le_sum
      intro j _
      have he : Real.exp (-m * r j) ≤
          Real.exp (m * d i j) * Real.exp (-m * r i) := by
        rw [← Real.exp_add]
        apply Real.exp_le_exp.mpr
        nlinarith [hr i j]
      nlinarith only [mul_le_mul_of_nonneg_left he (hC i j)]
    _ = (∑ j, Real.exp (m * d i j) * C i j) * Real.exp (-m * r i) :=
      (Finset.sum_mul _ _ _).symm
    _ ≤ _ := mul_le_mul_of_nonneg_right (hrow i) (Real.exp_pos _).le

end
end UnifiedTheory.Clay.YangMills.WeightedOscillation
