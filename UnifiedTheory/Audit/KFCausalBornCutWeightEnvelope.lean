/-
  Optimal finite selection under bounded cut-weight contrast.

  These certificates optimize over all weights in [1,A]. The analytic
  uniform-cut limit and causal-history concentration argument are given in
  CAUSAL_CUT_CONTRAST_BOUND.md, not asserted as formal trajectory theorems.
-/

import UnifiedTheory.Audit.KFCausalBornMicroscopicSelection

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Audit.KFCausalBornCutWeightEnvelope
noncomputable section
open scoped BigOperators

variable {ι : Type*} [Fintype ι] [Nonempty ι]

def weightMean (x w : ι → ℝ) : ℝ := (∑ i, w i * x i) / ∑ i, w i

def thresholdWeight (x : ι → ℝ) (A a : ℝ) (i : ι) : ℝ :=
  if x i < a then A else 1

theorem positive_weight_sum (w : ι → ℝ) (hw : ∀ i, 1 ≤ w i) :
    0 < ∑ i, w i := by
  exact Finset.sum_pos (fun i _ => lt_of_lt_of_le (by norm_num) (hw i))
    Finset.univ_nonempty

theorem weightMean_centered (x w : ι → ℝ) (hw : ∀ i, 1 ≤ w i) :
    ∑ i, w i * (x i - weightMean x w) = 0 := by
  have hz := ne_of_gt (positive_weight_sum w hw)
  simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, weightMean]
  field_simp
  ring

omit [Nonempty ι] in
/-- Endpoint weights minimize the centered linear objective pointwise. -/
theorem threshold_centered_le (x w : ι → ℝ) (A a : ℝ)
    (hlo : ∀ i, 1 ≤ w i) (hhi : ∀ i, w i ≤ A) :
    ∑ i, thresholdWeight x A a i * (x i - a) ≤ ∑ i, w i * (x i - a) := by
  apply Finset.sum_le_sum
  intro i _
  unfold thresholdWeight
  split_ifs with hi
  · exact mul_le_mul_of_nonpos_right (hhi i) (sub_nonpos.mpr hi.le)
  · simpa using mul_le_mul_of_nonneg_right (hlo i) (sub_nonneg.mpr (le_of_not_gt hi))

/-- A finite dual certificate for every admissible weight vector. -/
theorem threshold_lower_certificate (x w : ι → ℝ) (A a : ℝ)
    (hlo : ∀ i, 1 ≤ w i) (hhi : ∀ i, w i ≤ A)
    (hcert : 0 ≤ ∑ i, thresholdWeight x A a i * (x i - a)) :
    a ≤ weightMean x w := by
  have h := hcert.trans (threshold_centered_le x w A a hlo hhi)
  simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul] at h
  unfold weightMean
  apply (le_div_iff₀ (positive_weight_sum w hlo)).mpr
  nlinarith

/-- Every law can be matched or improved by one threshold law. This
reduces the global finite optimization to finitely many cut thresholds. -/
theorem threshold_at_mean_improves (x w : ι → ℝ) (A : ℝ) (hA : 1 ≤ A)
    (hlo : ∀ i, 1 ≤ w i) (hhi : ∀ i, w i ≤ A) :
    weightMean x (thresholdWeight x A (weightMean x w)) ≤ weightMean x w := by
  have ht : ∀ i, 1 ≤ thresholdWeight x A (weightMean x w) i := by
    intro i
    unfold thresholdWeight
    split_ifs <;> linarith
  have h := threshold_centered_le x w A (weightMean x w) hlo hhi
  rw [weightMean_centered x w hlo] at h
  simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul] at h
  unfold weightMean at ⊢
  apply (div_le_iff₀ (positive_weight_sum _ ht)).mpr
  change (∑ i, thresholdWeight x A (weightMean x w) i * x i) ≤
    weightMean x w * ∑ i, thresholdWeight x A (weightMean x w) i
  nlinarith

theorem self_consistent_threshold_is_optimal (x w : ι → ℝ) (A a : ℝ)
    (hlo : ∀ i, 1 ≤ w i) (hhi : ∀ i, w i ≤ A)
    (hself : ∑ i, thresholdWeight x A a i * (x i - a) = 0) :
    a ≤ weightMean x w :=
  threshold_lower_certificate x w A a hlo hhi (le_of_eq hself.symm)

def selectionSlack (x w : ι → ℝ) (A a : ℝ) (i : ι) : ℝ :=
  if x i < a then (A - w i) * (a - x i) else (w i - 1) * (x i - a)

omit [Fintype ι] [Nonempty ι] in
theorem selectionSlack_nonneg (x w : ι → ℝ) (A a : ℝ)
    (hlo : ∀ i, 1 ≤ w i) (hhi : ∀ i, w i ≤ A) (i : ι) :
    0 ≤ selectionSlack x w A a i := by
  unfold selectionSlack
  split_ifs with hi
  · exact mul_nonneg (sub_nonneg.mpr (hhi i)) (sub_nonneg.mpr hi.le)
  · exact mul_nonneg (sub_nonneg.mpr (hlo i)) (sub_nonneg.mpr (le_of_not_gt hi))

/-- Exact regret identity: distance above a certified optimal mean is
the sum of the unused endpoint biases, weighted by distance from the cut. -/
theorem weightMean_regret_identity (x w : ι → ℝ) (A a : ℝ)
    (hlo : ∀ i, 1 ≤ w i)
    (hself : ∑ i, thresholdWeight x A a i * (x i - a) = 0) :
    (∑ i, w i) * (weightMean x w - a) = ∑ i, selectionSlack x w A a i := by
  have hpoint : ∀ i, selectionSlack x w A a i =
      w i * (x i - a) - thresholdWeight x A a i * (x i - a) := by
    intro i
    unfold selectionSlack thresholdWeight
    split_ifs <;> ring
  simp_rw [hpoint]
  rw [Finset.sum_sub_distrib, hself, sub_zero]
  have hz := ne_of_gt (positive_weight_sum w hlo)
  simp only [weightMean, mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul]
  field_simp

/-- At an optimal mean, every alternative strictly away from the cutoff
must saturate its allowed weight endpoint. -/
theorem optimal_weight_endpoint_rigidity (x w : ι → ℝ) (A a : ℝ)
    (hlo : ∀ i, 1 ≤ w i) (hhi : ∀ i, w i ≤ A)
    (hself : ∑ i, thresholdWeight x A a i * (x i - a) = 0)
    (hmean : weightMean x w = a) (i : ι) :
    (x i < a → w i = A) ∧ (a < x i → w i = 1) := by
  have hsum : ∑ j, selectionSlack x w A a j = 0 := by
    rw [← weightMean_regret_identity x w A a hlo hself, hmean, sub_self, mul_zero]
  have hzero : selectionSlack x w A a i = 0 := by
    have hle := Finset.single_le_sum
      (fun j (_ : j ∈ (Finset.univ : Finset ι)) => selectionSlack_nonneg x w A a hlo hhi j)
      (Finset.mem_univ i)
    rw [hsum] at hle
    exact le_antisymm hle (selectionSlack_nonneg x w A a hlo hhi i)
  constructor
  · intro hi
    rw [selectionSlack, if_pos hi] at hzero
    have h := (mul_eq_zero.mp hzero).resolve_right (ne_of_gt (sub_pos.mpr hi))
    linarith
  · intro hi
    rw [selectionSlack, if_neg (not_lt.mpr hi.le)] at hzero
    have h := (mul_eq_zero.mp hzero).resolve_right (ne_of_gt (sub_pos.mpr hi))
    linarith

def cutThresholdWeight (N : ℕ) (A : ℝ) (m : ℕ) (j : Fin N) : ℝ :=
  if j.val < m then A else 1

private theorem sum_prefix (N m : ℕ) (hm : m ≤ N) (f : ℕ → ℝ) :
    (∑ j : Fin N, if j.val < m then f j.val else 0) = ∑ j ∈ Finset.range m, f j := by
  rw [Fin.sum_univ_eq_sum_range (fun j => if j < m then f j else 0), ← Finset.sum_filter]
  congr 1
  ext j
  simp only [Finset.mem_filter, Finset.mem_range]
  omega

private theorem sum_range_real (N : ℕ) :
    (∑ j ∈ Finset.range N, (j : ℝ)) = (N : ℝ) * (N - 1) / 2 := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ, ih]
    push_cast
    ring

theorem cutThresholdMean_formula (N m : ℕ) (A : ℝ) (hm : m ≤ N) :
    weightMean (fun j : Fin N => (j.val : ℝ)) (cutThresholdWeight N A m) =
      ((N : ℝ) * (N - 1) + (A - 1) * m * (m - 1)) /
        (2 * (N + (A - 1) * m)) := by
  have hn : ∀ j : Fin N, cutThresholdWeight N A m j * (j.val : ℝ) =
      j.val + (A - 1) * (if j.val < m then (j.val : ℝ) else 0) := by
    intro j
    unfold cutThresholdWeight
    split_ifs <;> ring
  have hd : ∀ j : Fin N, cutThresholdWeight N A m j =
      1 + (A - 1) * (if j.val < m then (1 : ℝ) else 0) := by
    intro j
    unfold cutThresholdWeight
    split_ifs <;> ring
  unfold weightMean
  simp_rw [hn, hd, Finset.sum_add_distrib, ← Finset.mul_sum]
  rw [sum_prefix N m hm (fun j => (j : ℝ)), sum_prefix N m hm (fun _ => 1)]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, Finset.card_range,
    nsmul_eq_mul, mul_one, Fin.sum_univ_eq_sum_range, sum_range_real]
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

/-- Completing the square gives the sharp uniform-cut envelope, including
the finite grid correction. The remainder is nonnegative for s >= 1. -/
theorem thresholdMean_square_identity (L m s : ℝ) (hL : 0 < L)
    (hm : 0 ≤ m) (hs : 1 ≤ s) :
    (L * (L - 1) + (s ^ 2 - 1) * m * (m - 1)) / (2 * (L + (s ^ 2 - 1) * m)) =
      L / (1 + s) - 1 / 2 +
        (s - 1) * (L - (1 + s) * m) ^ 2 / (2 * (1 + s) * (L + (s ^ 2 - 1) * m)) := by
  have hs0 : 0 < 1 + s := by linarith
  have hsm : 0 ≤ (s ^ 2 - 1) * m := mul_nonneg (by nlinarith) hm
  have hden : L + (s ^ 2 - 1) * m ≠ 0 := by linarith
  field_simp
  ring

theorem thresholdMean_lower_bound (L m s : ℝ) (hL : 0 < L)
    (hm : 0 ≤ m) (hs : 1 ≤ s) :
    L / (1 + s) - 1 / 2 ≤
      (L * (L - 1) + (s ^ 2 - 1) * m * (m - 1)) / (2 * (L + (s ^ 2 - 1) * m)) := by
  rw [thresholdMean_square_identity L m s hL hm hs]
  have hsm : 0 ≤ (s ^ 2 - 1) * m := mul_nonneg (by nlinarith) hm
  have hnum : 0 ≤ (s - 1) * (L - (1 + s) * m) ^ 2 := mul_nonneg (by linarith) (sq_nonneg _)
  have hden : 0 < 2 * (1 + s) * (L + (s ^ 2 - 1) * m) := by positivity
  exact le_add_of_nonneg_right (div_nonneg hnum hden.le)

/-- Every cut law with weight contrast at most s^2 obeys the sharp
all-rank lower bound. No monotonicity of the original weights is assumed. -/
theorem bounded_cut_mean_lower (n : ℕ) (w : Fin (n + 1) → ℝ) (s : ℝ)
    (hs : 1 ≤ s) (hlo : ∀ j, 1 ≤ w j) (hhi : ∀ j, w j ≤ s ^ 2) :
    ((n : ℝ) + 1) / (1 + s) - 1 / 2 ≤ weightMean (fun j => (j.val : ℝ)) w := by
  let x : Fin (n + 1) → ℝ := fun j => j.val
  let a := weightMean x w
  have ha : a ≤ (n : ℝ) := by
    apply (div_le_iff₀ (positive_weight_sum w hlo)).mpr
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro j _
    have hj : (j.val : ℝ) ≤ n := by exact_mod_cast (Nat.le_of_lt_succ j.isLt)
    change w j * (j.val : ℝ) ≤ (n : ℝ) * w j
    nlinarith [hlo j]
  let m := Nat.ceil a
  have hm : m ≤ n + 1 := by
    apply Nat.ceil_le.mpr
    push_cast
    linarith
  have ht : thresholdWeight x (s ^ 2) a = cutThresholdWeight (n + 1) (s ^ 2) m := by
    funext j
    simp only [thresholdWeight, cutThresholdWeight, x, m, Nat.lt_ceil]
  have himprove := threshold_at_mean_improves x w (s ^ 2) (by nlinarith) hlo hhi
  change weightMean x (thresholdWeight x (s ^ 2) a) ≤ a at himprove
  rw [ht] at himprove
  change weightMean (fun j : Fin (n + 1) => (j.val : ℝ))
    (cutThresholdWeight (n + 1) (s ^ 2) m) ≤ a at himprove
  rw [cutThresholdMean_formula (n + 1) m (s ^ 2) hm] at himprove
  have hbound := thresholdMean_lower_bound ((n : ℝ) + 1) m s (by positivity) (by positivity) hs
  push_cast at himprove
  exact hbound.trans himprove

/-- The 81:1 weight-contrast specialization gives (n-4)/10 ancestors.
The asymptotic 1/10 interpretation alone is not a four-dimensional geometry. -/
theorem contrast_eightyOne_cut_mean (n : ℕ) (w : Fin (n + 1) → ℝ)
    (hlo : ∀ j, 1 ≤ w j) (hhi : ∀ j, w j ≤ 81) :
    ((n : ℝ) - 4) / 10 ≤ weightMean (fun j => (j.val : ℝ)) w := by
  have h := bounded_cut_mean_lower n w 9 (by norm_num) hlo (by norm_num; exact hhi)
  norm_num at h
  linarith

#print axioms threshold_lower_certificate
#print axioms threshold_at_mean_improves
#print axioms self_consistent_threshold_is_optimal
#print axioms weightMean_regret_identity
#print axioms optimal_weight_endpoint_rigidity
#print axioms thresholdMean_square_identity
#print axioms bounded_cut_mean_lower
#print axioms contrast_eightyOne_cut_mean

end
end UnifiedTheory.Audit.KFCausalBornCutWeightEnvelope
