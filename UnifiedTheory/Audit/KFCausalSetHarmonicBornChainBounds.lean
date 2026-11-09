/-
  Analytic ingredients for the harmonic Born chain-atom audit.

  These theorems prove the harmonic suppression bound, stability of positive
  radial projection near a deterministic vertex, a geometric tail estimate,
  and positivity of a product with summable escape probabilities.

  The chain-precursor reduction and assembly into the repository's infinite
  trajectory measure are given in HARMONIC_BORN_CHAIN_ATOM.md. They are not
  asserted here as a machine-checked identification theorem.
-/

import UnifiedTheory.Audit.KFCausalSetHarmonicBornAllRankSupport
import Mathlib.Analysis.SpecialFunctions.Log.Summable
import Mathlib.Analysis.PSeries

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Audit.KFCausalSetHarmonicBornChainBounds

noncomputable section

open scoped BigOperators
open Filter Topology
open UnifiedTheory.Audit.KFCausalSetMultiplicityCorrectedRunning

theorem harmonic_le_rank (n : ℕ) : (harmonic n : ℝ) ≤ n := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [harmonic_succ, Rat.cast_add, Rat.cast_inv, Rat.cast_natCast]
      have hInv : ((n + 1 : ℕ) : ℝ)⁻¹ ≤ 1 := by
        apply inv_le_one_of_one_le₀
        exact_mod_cast (show 1 ≤ n + 1 by omega)
      push_cast at *
      linarith

theorem harmonic_sq_le_twice_rank_sub_one {n : ℕ} (hn : 3 ≤ n) :
    (harmonic n : ℝ)^2 ≤ 2 * (n - 1) := by
  induction n, hn using Nat.le_induction with
  | base => norm_num [harmonic_succ, harmonic_zero]
  | succ n hn ih =>
      rw [harmonic_succ, Rat.cast_add, Rat.cast_inv, Rat.cast_natCast]
      have hH := harmonic_le_rank n
      have hd : (0 : ℝ) < (n + 1 : ℕ) := by positivity
      have hInv : (0 : ℝ) ≤ ((n + 1 : ℕ) : ℝ)⁻¹ := by positivity
      have hProduct := mul_le_mul_of_nonneg_right hH hInv
      have hCancel : (((n + 1 : ℕ) : ℝ)⁻¹) * ((n + 1 : ℕ) : ℝ) = 1 :=
        inv_mul_cancel₀ (ne_of_gt hd)
      have hInvLe : (((n + 1 : ℕ) : ℝ)⁻¹)^2 ≤
          2 * (((n + 1 : ℕ) : ℝ)⁻¹) := by
        have hSmall : ((n + 1 : ℕ) : ℝ)⁻¹ ≤ 1 := by
          apply inv_le_one_of_one_le₀
          exact_mod_cast (show 1 ≤ n + 1 by omega)
        nlinarith
      push_cast at *
      nlinarith

/-- The nearest competing chain precursor has relative amplitude at most
`2/n`. This is an all-rank inequality, not an asymptotic fit. -/
theorem harmonic_chain_nearest_ratio_bound {n : ℕ} (hn : 3 ≤ n) :
    (n : ℝ) ≤ 2 * harmonicCriticalPairCoupling n ^ (2 * (n - 1)) := by
  let h : ℝ := harmonic n
  let m : ℝ := 2 * (n - 1)
  have hm : 0 < m := by
    dsimp [m]
    have hnR : (3 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  have hh : 0 ≤ h := le_of_lt (by
    dsimp [h]
    exact_mod_cast harmonic_pos (by omega : n ≠ 0))
  have hsq : h^2 ≤ m := harmonic_sq_le_twice_rank_sub_one hn
  have hFormula : harmonicCriticalPairCoupling n = 1 + h/m := by
    simp [harmonicCriticalPairCoupling, harmonicCriticalPairCouplingQ,
      show ¬ n ≤ 1 by omega, h, m]
  have hlam : 0 < harmonicCriticalPairCoupling n :=
    lt_trans zero_lt_one (harmonicCriticalPairCoupling_gt_one n)
  have hLog := Real.one_sub_inv_le_log_of_pos hlam
  have hMul := mul_le_mul_of_nonneg_left hLog hm.le
  have hLower : h - 1 ≤ m * (1 - (harmonicCriticalPairCoupling n)⁻¹) := by
    rw [hFormula]
    have hsum : 0 < m + h := by linarith
    have hId : m * (1 - (1 + h/m)⁻¹) = h - h^2/(m+h) := by
      field_simp
      ring
    rw [hId]
    have : h^2 / (m+h) ≤ 1 := (div_le_one hsum).2 (by linarith)
    linarith
  have hHalf : Real.log n + 1/2 < h := by
    have hc := Real.eulerMascheroniConstant_lt_eulerMascheroniSeq' n
    rw [Real.eulerMascheroniSeq', if_neg (by omega : n ≠ 0)] at hc
    have hg := Real.one_half_lt_eulerMascheroniConstant
    dsimp [h]
    linarith
  have hLogTwo : (1/2 : ℝ) ≤ Real.log 2 := by
    have hTwo := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at hTwo
    linarith
  have hLogFinal : Real.log n ≤
      Real.log (2 * harmonicCriticalPairCoupling n ^ (2 * (n-1))) := by
    rw [Real.log_mul (by norm_num) (pow_ne_zero _ (ne_of_gt hlam)), Real.log_pow]
    have hCast : ((2 * (n-1) : ℕ) : ℝ) = m := by
      dsimp [m]
      rw [Nat.cast_mul, Nat.cast_sub (by omega : 1 ≤ n)]
      norm_num
    rw [hCast]
    linarith
  exact (Real.log_le_log_iff (by positivity) (by positivity)).mp hLogFinal

/-- A duplicated last term accounts for the empty and singleton precursors
of a chain having the same raw magnitude. -/
theorem geometric_tail_with_duplicate_le_two (q : ℝ)
    (hq : 0 ≤ q) (hhalf : q ≤ 1/2) (m : ℕ) :
    (∑ k ∈ Finset.range m, q^k) + 2*q^m ≤ 2 := by
  induction m with
  | zero => simp
  | succ m ih =>
      rw [Finset.sum_range_succ, pow_succ]
      have h := mul_nonneg (pow_nonneg hq m) (by linarith : 0 ≤ 1-2*q)
      nlinarith

/-- Projection onto a sphere is within twice the original distance to any
point on that sphere. Applied to the Born sphere, this gives a quadratic
escape bound near a deterministic transition. -/
theorem positive_radial_projection_distance_le_twice
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (u a e : E) (r : ℝ) (ha : a ≠ u)
    (he : ‖e-u‖ = r) :
    ‖(u + (r/‖a-u‖) • (a-u)) - e‖ ≤ 2*‖a-e‖ := by
  have hd : ‖a-u‖ ≠ 0 := norm_ne_zero_iff.mpr (sub_ne_zero.mpr ha)
  have hDiff : (u + (r/‖a-u‖) • (a-u)) - a =
      (r/‖a-u‖ - 1) • (a-u) := by module
  have hNorm : ‖(u + (r/‖a-u‖) • (a-u)) - a‖ = |r-‖a-u‖| := by
    rw [hDiff, norm_smul, Real.norm_eq_abs]
    calc
      |r/‖a-u‖ - 1| * ‖a-u‖ = |(r/‖a-u‖ - 1)*‖a-u‖| := by
        rw [abs_mul, abs_of_nonneg (norm_nonneg _)]
      _ = |r-‖a-u‖| := by congr 1; field_simp
  have hBound : |r-‖a-u‖| ≤ ‖a-e‖ := by
    rw [← he]
    have h := abs_norm_sub_norm_le (e-u) (a-u)
    simpa [sub_sub_sub_cancel_right, norm_sub_rev] using h
  calc
    _ ≤ ‖(u + (r/‖a-u‖) • (a-u)) - a‖ + ‖a-e‖ := by
      have hTriangle := norm_add_le
        ((u + (r/‖a-u‖) • (a-u)) - a) (a-e)
      simpa only [sub_add_sub_cancel] using hTriangle
    _ ≤ 2*‖a-e‖ := by rw [hNorm]; linarith

/-- Positive transition probabilities with summable losses have a strictly
positive infinite survival product. -/
theorem positive_survival_product_of_summable_escape
    (p : ℕ → ℝ) (hp : ∀ n, 0 < p n)
    (hsum : Summable (fun n => 1-p n)) : 0 < ∏' n, p n := by
  have hneg : Summable (fun n => -(1-p n)) := hsum.neg
  have hlog : Summable (fun n => Real.log (p n)) := by
    simpa using Real.summable_log_one_add_of_summable hneg
  rw [← Real.rexp_tsum_eq_tprod hp hlog]
  exact Real.exp_pos _

/-- Exact sum of competing raw magnitudes relative to the timid magnitude
on an n-chain: n-1 nonempty precursors and the empty precursor. -/
def chainRelativeTail (n : ℕ) : ℝ :=
  (∑ k ∈ Finset.range (n-1),
    (harmonicCriticalPairCoupling n)⁻¹ ^ ((k+1)*(2*n-(k+1)-1))) +
      (harmonicCriticalPairCoupling n)⁻¹ ^ (n*(n-1))

theorem chainRelativeTail_le_four_div_rank {n : ℕ} (hn : 8 ≤ n) :
    chainRelativeTail n ≤ 4/(n : ℝ) := by
  let z := (harmonicCriticalPairCoupling n)⁻¹
  let q := z^(n-1)
  have hlam : 0 < harmonicCriticalPairCoupling n :=
    lt_trans zero_lt_one (harmonicCriticalPairCoupling_gt_one n)
  have hz : 0 ≤ z := inv_nonneg.mpr hlam.le
  have hzOne : z ≤ 1 := inv_le_one_of_one_le₀
    (harmonicCriticalPairCoupling_gt_one n).le
  have hq : 0 ≤ q := pow_nonneg hz _
  have ht : q^2 ≤ 2/(n : ℝ) := by
    have hNearest := harmonic_chain_nearest_ratio_bound (by omega : 3 ≤ n)
    have hqId : q^2 = (harmonicCriticalPairCoupling n ^ (2*(n-1)))⁻¹ := by
      simp [q, z, ← pow_mul, mul_comm]
    rw [hqId, inv_eq_one_div]
    exact (div_le_div_iff₀ (by positivity) (by positivity)).2 (by simpa using hNearest)
  have hnR : (8 : ℝ) ≤ n := by exact_mod_cast hn
  have hQuarter : 2/(n : ℝ) ≤ 1/4 := (div_le_iff₀ (by positivity)).2 (by linarith)
  have hHalf : q ≤ 1/2 := by nlinarith
  have hTerms : ∀ k ∈ Finset.range (n-1),
      z^((k+1)*(2*n-(k+1)-1)) ≤ q^(k+2) := by
    intro k hk
    have hkN : k+2 ≤ n := by simp only [Finset.mem_range] at hk; omega
    have h1 : n-1+1=n := by omega
    have h2 : 2*n-(k+1)-1+(k+1)+1=2*n := by omega
    have h3 : n-k-2+k+2=n := by omega
    have hExp : (k+2)*(n-1) ≤ (k+1)*(2*n-(k+1)-1) := by
      nlinarith [Nat.zero_le (k*(n-k-2))]
    have hBound := pow_le_pow_of_le_one hz hzOne hExp
    simpa [q, ← pow_mul, mul_comm] using hBound
  have hEmpty : z^(n*(n-1)) = q^n := by simp [q, ← pow_mul, mul_comm]
  have hSum : (∑ k ∈ Finset.range (n-1), q^(k+2)) + q^n =
      q^2*((∑ k ∈ Finset.range (n-2), q^k) + 2*q^(n-2)) := by
    have hN1 : n-1 = (n-2)+1 := by omega
    have hN2 : n = (n-2)+2 := by omega
    rw [hN1, Finset.sum_range_succ]
    conv_lhs => arg 2; rw [hN2]
    simp_rw [pow_add]
    rw [← Finset.sum_mul]
    ring
  calc
    chainRelativeTail n ≤ (∑ k ∈ Finset.range (n-1), q^(k+2)) + q^n := by
      unfold chainRelativeTail
      change (∑ k ∈ Finset.range (n-1), z^_) + z^_ ≤ _
      rw [hEmpty]
      have h := Finset.sum_le_sum hTerms
      linarith
    _ = q^2*((∑ k ∈ Finset.range (n-2), q^k) + 2*q^(n-2)) := hSum
    _ ≤ q^2*2 := mul_le_mul_of_nonneg_left
      (geometric_tail_with_duplicate_le_two q hq hHalf _) (sq_nonneg q)
    _ ≤ (2/(n : ℝ))*2 := mul_le_mul_of_nonneg_right ht (by norm_num)
    _ = 4/(n : ℝ) := by ring

theorem positive_survival_product_of_inverse_square_escape
    (p : ℕ → ℝ) (hp : ∀ n, 0 < p n) (hpOne : ∀ n, p n ≤ 1)
    (hBound : ∀ n, 8 ≤ n → 1-p n ≤ 128/(n : ℝ)^2) :
    0 < ∏' n, p n := by
  apply positive_survival_product_of_summable_escape p hp
  have hMajor : Summable (fun n : ℕ => 128/(n : ℝ)^2) := by
    simpa [div_eq_mul_inv] using
      (Real.summable_nat_pow_inv.mpr (by norm_num : 1 < (2 : ℕ))).mul_left (128 : ℝ)
  rw [← summable_nat_add_iff 8]
  apply ((summable_nat_add_iff 8).2 hMajor).of_nonneg_of_le
  · intro n
    exact sub_nonneg.mpr (hpOne (n+8))
  · intro n
    exact hBound (n+8) (by omega)

#print axioms harmonic_chain_nearest_ratio_bound
#print axioms positive_radial_projection_distance_le_twice
#print axioms positive_survival_product_of_summable_escape
#print axioms chainRelativeTail_le_four_div_rank
#print axioms positive_survival_product_of_inverse_square_escape

end
end UnifiedTheory.Audit.KFCausalSetHarmonicBornChainBounds
