/-
Weighted scale costs for the conditional flux recurrence.

The required margin is a bound on normalized partial sums, not merely a
pointwise assertion that the costs grow slower than 4 ^ k. A telescoping envelope
allows costs of order 4 ^ k/k ^ 2, beyond the geometric envelopes q ^ k with q < 4.
No physical transfer-operator estimate or Yang--Mills continuum construction
is asserted here.
-/
import UnifiedTheory.Clay.YangMills.Twisted.TwistedSubArea
import Mathlib.Analysis.PSeries

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Clay.YangMills.Twisted.TwistedWeightedBudget
noncomputable section
open UnifiedTheory.Clay.YangMills.Twisted.TwistedSubArea
open scoped Topology

def cost (m : ℕ → ℝ) (k : ℕ) : ℝ :=
  ∑ j ∈ Finset.range k, m j / 4 ^ (j + 1)

theorem area_bound_of_budget (u m : ℕ → ℝ) (B : ℝ)
    (hstep : ∀ k, 4 * u k - m k ≤ u (k + 1))
    (hbudget : ∀ k, cost m k ≤ B) (k : ℕ) :
    (4 : ℝ) ^ k * (u 0 - B) ≤ u k := by
  have hi := log_iterate u m hstep k
  have hb := hbudget k
  dsimp [cost] at hb
  nlinarith [mul_le_mul_of_nonneg_left hb (show (0 : ℝ) ≤ 4 ^ k by positivity)]

theorem positive_margin (u m : ℕ → ℝ) (B : ℝ)
    (hstep : ∀ k, 4 * u k - m k ≤ u (k + 1))
    (hbudget : ∀ k, cost m k ≤ B) (hseed : B < u 0) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ k, (4 : ℝ) ^ k * δ ≤ u k := by
  exact ⟨u 0 - B, sub_pos.mpr hseed, area_bound_of_budget u m B hstep hbudget⟩

def saturated (initial : ℝ) (m : ℕ → ℝ) (k : ℕ) : ℝ :=
  (4 : ℝ) ^ k * (initial - cost m k)

theorem saturated_step (initial : ℝ) (m : ℕ → ℝ) (k : ℕ) :
    saturated initial m (k + 1) = 4 * saturated initial m k - m k := by
  simp only [saturated, cost, Finset.sum_range_succ]
  have h4 : (4 : ℝ) ^ (k + 1) ≠ 0 := by positivity
  field_simp
  ring

theorem saturated_margin_iff (initial δ : ℝ) (m : ℕ → ℝ) :
    (∀ k, (4 : ℝ) ^ k * δ ≤ saturated initial m k) ↔
      ∀ k, cost m k ≤ initial - δ := by
  simp only [saturated]
  constructor <;> intro h k
  · have hp : (0 : ℝ) < 4 ^ k := by positivity
    nlinarith [h k]
  · exact mul_le_mul_of_nonneg_left (by linarith [h k]) (by positivity)

theorem reciprocal_pair_sum (k : ℕ) :
    (∑ j ∈ Finset.range k, (1 : ℝ) / (((j : ℝ) + 1) * ((j : ℝ) + 2))) =
      1 - 1 / ((k : ℝ) + 1) := by
  induction k with
  | zero => norm_num
  | succ k ih =>
    rw [Finset.sum_range_succ, ih]
    push_cast
    have h1 : (k : ℝ) + 1 ≠ 0 := by positivity
    have h2 : (k : ℝ) + 2 ≠ 0 := by positivity
    field_simp
    ring

theorem near_area_budget (m : ℕ → ℝ) (B : ℝ) (hB : 0 ≤ B)
    (hm : ∀ j, m j ≤ (4 : ℝ) ^ (j + 1) * B / (((j : ℝ) + 1) * ((j : ℝ) + 2)))
    (k : ℕ) : cost m k ≤ B := by
  have hterm : ∀ j, m j / (4 : ℝ) ^ (j + 1) ≤ B * (1 / (((j : ℝ) + 1) * ((j : ℝ) + 2))) := by
    intro j
    apply (div_le_iff₀ (show (0 : ℝ) < 4 ^ (j + 1) by positivity)).mpr
    calc
      m j ≤ 4 ^ (j + 1) * B / (((j : ℝ) + 1) * ((j : ℝ) + 2)) := hm j
      _ = B * (1 / (((j : ℝ) + 1) * ((j : ℝ) + 2))) * 4 ^ (j + 1) := by ring
  calc
    cost m k ≤ ∑ j ∈ Finset.range k, B * (1 / (((j : ℝ) + 1) * ((j : ℝ) + 2))) :=
      Finset.sum_le_sum fun j _ => hterm j
    _ = B * (1 - 1 / ((k : ℝ) + 1)) := by rw [← Finset.mul_sum, reciprocal_pair_sum]
    _ ≤ B := by
      have : 0 ≤ B * (1 / ((k : ℝ) + 1)) := by positivity
      nlinarith

theorem near_area_positive_margin (u m : ℕ → ℝ) (B : ℝ) (hB : 0 ≤ B)
    (hm : ∀ j, m j ≤ (4 : ℝ) ^ (j + 1) * B / (((j : ℝ) + 1) * ((j : ℝ) + 2)))
    (hstep : ∀ k, 4 * u k - m k ≤ u (k + 1)) (hseed : B < u 0) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ k, (4 : ℝ) ^ k * δ ≤ u k := by
  exact positive_margin u m B hstep (near_area_budget m B hB hm) hseed

/-- Costs proportional to 4 ^ (j + 1)/(j + 1) have a divergent normalized budget. -/
theorem harmonic_normalized_cost_not_summable :
    ¬ Summable (fun j : ℕ =>
      (((4 : ℝ) ^ (j + 1) / ((j : ℝ) + 1)) / 4 ^ (j + 1))) := by
  have heq : (fun j : ℕ => (((4 : ℝ) ^ (j + 1) / ((j : ℝ) + 1)) / 4 ^ (j + 1))) =
      (fun j : ℕ => 1 / ((j : ℝ) + 1)) := by
    funext j
    field_simp
  rw [heq]
  simpa only [Nat.cast_add, Nat.cast_one] using
    mt (summable_nat_add_iff (f := fun j : ℕ => 1 / (j : ℝ)) 1).mp
      Real.not_summable_one_div_natCast

/-- The same divergent-budget example is nevertheless pointwise subarea. -/
theorem harmonic_cost_is_subarea :
    Filter.Tendsto (fun j : ℕ =>
      (((4 : ℝ) ^ (j + 1) / ((j : ℝ) + 1)) / 4 ^ j)) Filter.atTop (𝓝 0) := by
  have heq : (fun j : ℕ => (((4 : ℝ) ^ (j + 1) / ((j : ℝ) + 1)) / 4 ^ j)) =
      (fun j : ℕ => (4 : ℝ) * (1 / ((j : ℝ) + 1))) := by
    funext j
    rw [pow_succ]
    field_simp
  rw [heq]
  simpa only [mul_zero] using
    (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul 4

theorem harmonic_budget_diverges :
    Filter.Tendsto (cost (fun j : ℕ => (4 : ℝ) ^ (j + 1) / ((j : ℝ) + 1)))
      Filter.atTop Filter.atTop := by
  convert Real.tendsto_sum_range_one_div_nat_succ_atTop using 1
  funext k
  apply Finset.sum_congr rfl
  intro j _
  dsimp
  field_simp

end
end UnifiedTheory.Clay.YangMills.Twisted.TwistedWeightedBudget
