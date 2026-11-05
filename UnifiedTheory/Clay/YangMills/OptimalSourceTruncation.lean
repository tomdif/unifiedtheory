/- Elementary factorial bounds and uniform optimal truncation. These
estimates convert a supplied factorial remainder to exponential decay;
they do not identify the Wilson source or prove its Haar expansion. -/
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Tactic
set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace UnifiedTheory.Clay.YangMills.OptimalSourceTruncation
open Real

/-- The logarithmic factorial upper bound, proved by induction from
`1 - x⁻¹ ≤ log x`; no Stirling asymptotic is used. -/
theorem log_factorial_le (n : ℕ) (hn : 1 ≤ n) :
    log (n.factorial : ℝ) ≤ ((n : ℝ)+1)*log n - n + 1 := by
  induction n, hn using Nat.le_induction with
  | base => norm_num
  | succ n hn ih =>
    have hnp : (0 : ℝ) < n := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn)
    have hnp1 : (0 : ℝ) < (n : ℝ)+1 := by positivity
    have hrat := Real.one_sub_inv_le_log_of_pos (div_pos hnp1 hnp)
    rw [Real.log_div hnp1.ne' hnp.ne'] at hrat
    have hstep : 1 ≤ ((n : ℝ)+1) * (log ((n : ℝ)+1)-log n) := by
      have ht := mul_le_mul_of_nonneg_left hrat hnp1.le
      field_simp at ht
      nlinarith
    rw [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one,
      Real.log_mul hnp1.ne' (by positivity : (n.factorial : ℝ) ≠ 0)]
    nlinarith

/-- An elementary upper bound with an explicit exponential constant. -/
theorem factorial_le (n : ℕ) (hn : 1 ≤ n) :
    (n.factorial : ℝ) ≤ exp 1 * n * ((n : ℝ)/exp 1)^n := by
  have hnp : (0 : ℝ) < n := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn)
  have hp : (0 : ℝ) < n.factorial := by positivity
  apply (Real.log_le_log_iff hp (by positivity)).1
  rw [Real.log_mul (by positivity : exp 1 * (n : ℝ) ≠ 0) (by positivity),
    Real.log_mul (exp_pos 1).ne' hnp.ne', Real.log_pow,
    Real.log_div hnp.ne' (exp_pos 1).ne', Real.log_exp]
  nlinarith [log_factorial_le n hn]

/-- Before the least-term index, the denominator controls the power
occurring in the factorial upper bound. -/
theorem factorial_succ_div_pow_le (N : ℕ) (hN : 1 ≤ N) (κ : ℝ)
    (hκ : 0 < κ) (hupper : (N : ℝ) ≤ 2 * κ) :
    ((N+1).factorial : ℝ)/(2 * κ)^N ≤
      exp 1 * N * ((N : ℝ)+1) * exp (-(N : ℝ)) := by
  have hpow : ((N : ℝ)/exp 1)^N/(2 * κ)^N ≤ exp (-(N : ℝ)) := by
    calc
      _ = ((N : ℝ)/(2 * κ)/exp 1)^N := by rw [← div_pow]; congr 1; ring
      _ ≤ (1/exp 1)^N := by
        apply pow_le_pow_left₀ (by positivity)
        apply (div_le_div_iff_of_pos_right (exp_pos 1)).2
        exact (div_le_one (by positivity)).2 hupper
      _ = exp (-(N : ℝ)) := by
        rw [one_div, inv_pow, ← Real.exp_nat_mul, ← Real.exp_neg]
        congr 1
        simp
  calc
    _ = ((N : ℝ)+1) * (N.factorial : ℝ)/(2 * κ)^N := by
      rw [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
    _ ≤ ((N : ℝ)+1) * (exp 1 * N * ((N : ℝ)/exp 1)^N)/(2 * κ)^N := by
      gcongr
      exact factorial_le N hN
    _ = (exp 1 * N * ((N : ℝ)+1)) * (((N : ℝ)/exp 1)^N/(2 * κ)^N) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hpow (by positivity)

/-- An index within one of `2κ₀` gives a bound uniform for all `κ ≥ κ₀`. -/
theorem optimal_factorial_bound (N : ℕ) (hN : 1 ≤ N) (κ₀ κ : ℝ)
    (hκ₀ : 0 < κ₀) (hκ : κ₀ ≤ κ)
    (hupper : (N : ℝ) ≤ 2 * κ₀) (hlower : 2 * κ₀ - 1 ≤ (N : ℝ)) :
    ((N+1).factorial : ℝ)/(2 * κ)^N ≤
      exp 2 * N * ((N : ℝ)+1) * exp (-2 * κ₀) := by
  calc
    _ ≤ exp 1 * N * ((N : ℝ)+1) * exp (-(N : ℝ)) :=
      factorial_succ_div_pow_le N hN κ (lt_of_lt_of_le hκ₀ hκ) (by linarith)
    _ ≤ exp 1 * N * ((N : ℝ)+1) * exp (1-2 * κ₀) := by
      gcongr
      linarith
    _ = _ := by
      rw [Real.exp_sub, show -2 * κ₀ = -(2 * κ₀) by ring, Real.exp_neg,
        show (2 : ℝ) = 1+1 by norm_num, Real.exp_add]
      ring

/-- The floor choice satisfies the required index inequalities. -/
theorem optimal_floor_factorial_bound (κ₀ κ : ℝ) (hκ₀ : 3 / 2 ≤ κ₀)
    (hκ : κ₀ ≤ κ) :
    ((⌊2 * κ₀⌋₊+1).factorial : ℝ)/(2 * κ)^⌊2 * κ₀⌋₊ ≤
      exp 2 * ⌊2 * κ₀⌋₊ * ((⌊2 * κ₀⌋₊ : ℝ)+1) * exp (-2 * κ₀) := by
  apply optimal_factorial_bound
  · apply Nat.le_floor
    norm_num
    linarith
  · linarith
  · exact hκ
  · exact Nat.floor_le (by linarith)
  · have h := Nat.lt_floor_add_one (2 * κ₀)
    linarith

/-- Explicit conversion of the factorial remainder prefactor used in
the optimally truncated normalized source expansion. -/
theorem optimal_remainder_bound (κ₀ κ : ℝ) (hκ₀ : 3 / 2 ≤ κ₀)
    (hκ : κ₀ ≤ κ) :
    6*((⌊2 * κ₀⌋₊ : ℝ)+9/2)*((⌊2 * κ₀⌋₊+1).factorial : ℝ)/(2 * κ)^⌊2 * κ₀⌋₊ ≤
      6*exp 2*(2 * κ₀)*(2 * κ₀+1)*(2 * κ₀+9/2)*exp (-2 * κ₀) := by
  have hfloor := Nat.floor_le (show 0 ≤ 2 * κ₀ by linarith)
  calc
    _ = (6*((⌊2 * κ₀⌋₊ : ℝ)+9/2)) *
        (((⌊2 * κ₀⌋₊+1).factorial : ℝ)/(2 * κ)^⌊2 * κ₀⌋₊) := by ring
    _ ≤ (6*((⌊2 * κ₀⌋₊ : ℝ)+9/2)) *
        (exp 2 * ⌊2 * κ₀⌋₊ * ((⌊2 * κ₀⌋₊ : ℝ)+1) * exp (-2 * κ₀)) :=
      mul_le_mul_of_nonneg_left (optimal_floor_factorial_bound κ₀ κ hκ₀ hκ) (by positivity)
    _ ≤ (6*(2 * κ₀+9/2)) * (exp 2 * (2 * κ₀) * (2 * κ₀+1) * exp (-2 * κ₀)) := by
      gcongr
    _ = _ := by ring

end UnifiedTheory.Clay.YangMills.OptimalSourceTruncation
