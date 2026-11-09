/- Finite shifted-truncation algebra for normalized source expansions.
Every sum is finite; no convergence of a formal asymptotic series is used. -/
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Clay.YangMills.FiniteSourceConvolution
open Finset

theorem triangular_sum (F : ℕ → ℕ → ℝ) (N : ℕ) :
    (∑ i ∈ range N, ∑ j ∈ range (N - i), F i j) =
      ∑ k ∈ range N, ∑ i ∈ range (k + 1), F i (k - i) := by
  induction N with
  | zero => simp
  | succ N ih =>
    have hs : (∑ i ∈ range N, ∑ j ∈ range (N + 1 - i), F i j) =
        (∑ i ∈ range N, ∑ j ∈ range (N - i), F i j) +
          ∑ i ∈ range N, F i (N - i) := by
      rw [← sum_add_distrib]
      apply sum_congr rfl
      intro i hi
      have he : N + 1 - i = (N - i) + 1 := by
        have := mem_range.mp hi
        omega
      rw [he, sum_range_succ]
    rw [sum_range_succ, sum_range_succ, hs, ih]
    simp only [Nat.add_sub_cancel_left, sum_range_one]
    rw [sum_range_succ]
    simp only [Nat.sub_self]
    ring

/-- The quotient-coefficient convolution gives exact cancellation below
degree `N` using a shorter denominator polynomial for each coefficient. -/
theorem shifted_polynomial_identity (b d e : ℕ → ℝ)
    (hconv : ∀ n, (∑ i ∈ range (n + 1), b i * d (n - i)) = e n)
    (N : ℕ) (x : ℝ) :
    (∑ i ∈ range N, (b i * x ^ i) *
      (∑ j ∈ range (N - i), d j * x ^ j)) =
      ∑ k ∈ range N, e k * x ^ k := by
  simp_rw [mul_sum]
  rw [triangular_sum]
  apply sum_congr rfl
  intro k _
  calc
    _ = ∑ i ∈ range (k + 1), (b i * d (k - i)) * x ^ k := by
      apply sum_congr rfl
      intro i hi
      have he : i + (k - i) = k := by
        have := mem_range.mp hi
        omega
      rw [show (b i * x ^ i) * (d (k - i) * x ^ (k - i)) =
        (b i * d (k - i)) * (x ^ i * x ^ (k - i)) by ring, ← pow_add, he]
    _ = (∑ i ∈ range (k + 1), b i * d (k - i)) * x ^ k := (sum_mul ..).symm
    _ = _ := by rw [hconv]

theorem shifted_remainder_identity (b d e : ℕ → ℝ)
    (hconv : ∀ n, (∑ i ∈ range (n + 1), b i * d (n - i)) = e n)
    (N : ℕ) (x D M : ℝ) :
    D * (∑ i ∈ range N, b i * x ^ i) - M =
      (∑ i ∈ range N, (b i * x ^ i) *
        (D - ∑ j ∈ range (N - i), d j * x ^ j)) +
      ((∑ k ∈ range N, e k * x ^ k) - M) := by
  simp_rw [mul_sub]
  rw [sum_sub_distrib, ← sum_mul, shifted_polynomial_identity b d e hconv N x]
  ring

end UnifiedTheory.Clay.YangMills.FiniteSourceConvolution
