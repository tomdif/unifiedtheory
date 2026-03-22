/-
  LayerA/ContinuumLimit.lean — Equidistribution of {n·√2} via Weyl criterion

  FULLY PROVED: zero axioms, zero sorry.

  What is proven:
  1. EquidistributedWeyl — 1D Weyl equidistribution criterion
  2. int_mul_irrational — k·α irrational for irrational α, k ≠ 0
  3. irrational_mul_not_int — k·α ∉ ℤ for irrational α, k ≠ 0
  4. cexp_irrational_ne_one — e^{2πi·k·α} ≠ 1 for irrational α, k ≠ 0
  5. cexp_sum_bound — |Σ e^{inθ}| ≤ 2/|e^{iθ}-1| (geometric sum)
  6. exp_sum_of_irrational_tendsto_zero — (1/N) Σ e^{2πiknα} → 0
  7. sqrt2_equidistributed — {n·√2} is equidistributed (Weyl)
  8. continuum_limit_exists — existence of equidistributed sequence
-/
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Algebra.Field.GeomSum
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Order.Filter.AtTopBot.Tendsto
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

set_option relaxedAutoImplicit false

namespace UnifiedTheory.LayerA.ContinuumLimit

open Complex Real Filter Topology
open scoped BigOperators

noncomputable section

/-! ## Definition: Weyl equidistribution criterion (1D) -/

/-- **Weyl equidistribution criterion (1D).**
    A sequence x : ℕ → ℝ is equidistributed mod 1 if for every nonzero
    integer k, the exponential average (1/N) Σ e^{2πi k x(n)} → 0. -/
def EquidistributedWeyl (x : ℕ → ℝ) : Prop :=
  ∀ (k : ℤ), k ≠ 0 →
    Tendsto (fun (N : ℕ) => (1 / (N : ℂ)) *
      ∑ n ∈ Finset.range N,
        cexp (2 * ↑Real.pi * I * ↑(↑k * x n)))
      atTop (𝓝 0)

/-! ## Helper lemmas -/

/-- If α is irrational and k ≠ 0 is an integer, then k·α is irrational. -/
theorem int_mul_irrational (α : ℝ) (hα : Irrational α) (k : ℤ) (hk : k ≠ 0) :
    Irrational ((k : ℝ) * α) := by
  rw [Irrational] at *
  intro ⟨q, hq⟩
  apply hα
  exact ⟨q / k, by push_cast; field_simp [Int.cast_ne_zero.mpr hk] at hq ⊢; linarith⟩

/-- If α is irrational and k ≠ 0, then k·α is not an integer. -/
theorem irrational_mul_not_int (α : ℝ) (hα : Irrational α) (k : ℤ) (hk : k ≠ 0)
    (m : ℤ) : (k : ℝ) * α ≠ (m : ℝ) := by
  intro hm
  have hk_ne : (k : ℝ) ≠ 0 := Int.cast_ne_zero.mpr hk
  have hα_eq : α = (m : ℝ) / (k : ℝ) := by
    field_simp [hk_ne] at hm ⊢; linarith
  have : (↑((m : ℚ) / (k : ℚ)) : ℝ) = α := by
    push_cast; exact hα_eq.symm
  exact hα ⟨(m : ℚ) / (k : ℚ), this⟩

/-- For irrational α and k ≠ 0, the exponential e^{2πi·k·α} ≠ 1.
    Proof: e^z = 1 iff z = 2πin, which would force k·α ∈ ℤ. -/
theorem cexp_irrational_ne_one (α : ℝ) (hα : Irrational α) (k : ℤ) (hk : k ≠ 0) :
    cexp (↑(2 * π * ↑k * α) * I) ≠ 1 := by
  intro h_eq
  rw [Complex.exp_eq_one_iff] at h_eq
  obtain ⟨n, hn⟩ := h_eq
  have h_lhs_im : (↑(2 * π * ↑k * α) * I).im = 2 * π * ↑k * α := by
    simp [Complex.mul_im]
  have h_rhs_im : (↑n * (2 * ↑π * I)).im = 2 * π * ↑n := by
    simp [Complex.mul_im]; ring
  have h_im := congr_arg Complex.im hn
  rw [h_lhs_im, h_rhs_im] at h_im
  have hpi : (0 : ℝ) < 2 * π := by positivity
  have hkα_eq_n : (k : ℝ) * α = (n : ℝ) := by nlinarith
  exact irrational_mul_not_int α hα k hk n hkα_eq_n

/-! ## Geometric sum bound -/

/-- **Exponential sum bound**: ‖Σ_{n=0}^{N-1} e^{inθ}‖ ≤ 2/‖e^{iθ} - 1‖.
    Uses the geometric series formula and |e^{iθ}| = 1. -/
theorem cexp_sum_bound (θ : ℝ) (hθ : cexp (↑θ * I) ≠ 1) (N : ℕ) :
    ‖∑ n ∈ Finset.range N, cexp (↑(↑n * θ) * I)‖ ≤ 2 / ‖cexp (↑θ * I) - 1‖ := by
  have h_terms : ∀ n : ℕ, cexp (↑(↑n * θ) * I) = (cexp (↑θ * I)) ^ n := by
    intro n
    rw [show (↑(↑n * θ) : ℂ) * I = ↑n * (↑θ * I) by push_cast; ring]
    rw [Complex.exp_nat_mul]
  simp_rw [h_terms]
  rw [geom_sum_eq hθ N, norm_div]
  have h_num : ‖(cexp (↑θ * I)) ^ N - 1‖ ≤ 2 := by
    have h_norm : ‖(cexp (↑θ * I)) ^ N‖ = 1 := by
      rw [norm_pow, norm_exp_ofReal_mul_I, one_pow]
    calc ‖(cexp (↑θ * I)) ^ N - 1‖
        ≤ ‖(cexp (↑θ * I)) ^ N‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
      _ = 1 + 1 := by simp [h_norm]
      _ = 2 := by ring
  have h_denom_pos : 0 < ‖cexp (↑θ * I) - 1‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hθ)
  exact div_le_div_of_nonneg_right h_num (le_of_lt h_denom_pos)

/-! ## Main: exponential sum tends to zero -/

/-- **Character averages tend to zero for irrational α.**
    For k ≠ 0 and α irrational, (1/N) Σ_{n<N} e^{2πi·k·n·α} → 0.
    Proof: the geometric series gives |Σ z^n| ≤ 2/|z-1| where z = e^{2πikα},
    so dividing by N gives a bound of O(1/N) → 0. -/
theorem exp_sum_of_irrational_tendsto_zero (α : ℝ) (hα : Irrational α)
    (k : ℤ) (hk : k ≠ 0) :
    Tendsto (fun (N : ℕ) => (1 / (N : ℂ)) *
      ∑ n ∈ Finset.range N, cexp (↑(↑n * (2 * π * ↑k * α)) * I))
      atTop (𝓝 0) := by
  set θ := 2 * π * (k : ℝ) * α with hθ_def
  have hθ : cexp (↑θ * I) ≠ 1 := cexp_irrational_ne_one α hα k hk
  have h_denom : ‖cexp (↑θ * I) - 1‖ > 0 :=
    norm_pos_iff.mpr (sub_ne_zero.mpr hθ)
  set C := 2 / ‖cexp (↑θ * I) - 1‖ with hC_def
  have hC : C > 0 := div_pos (by norm_num : (2 : ℝ) > 0) h_denom
  have h_bound : ∀ N : ℕ, ‖∑ n ∈ Finset.range N, cexp (↑(↑n * θ) * I)‖ ≤ C :=
    fun N => cexp_sum_bound θ hθ N
  rw [Metric.tendsto_atTop]
  intro ε hε
  use Nat.ceil (C / ε) + 1
  intro N hN
  simp only [dist_zero_right]
  have hN_pos : (0 : ℝ) < N := by
    have h1 : (0 : ℕ) < Nat.ceil (C / ε) + 1 := Nat.zero_lt_succ _
    exact Nat.cast_pos.mpr (Nat.lt_of_lt_of_le h1 hN)
  calc ‖(1 / (N : ℂ)) * ∑ n ∈ Finset.range N, cexp (↑(↑n * θ) * I)‖
      = ‖(1 / (N : ℂ))‖ * ‖∑ n ∈ Finset.range N, cexp (↑(↑n * θ) * I)‖ :=
        norm_mul _ _
    _ ≤ (1 / N) * C := by
        apply mul_le_mul
        · simp only [norm_div, norm_one, Complex.norm_natCast]; rfl
        · exact h_bound N
        · exact norm_nonneg _
        · simp only [one_div, inv_nonneg, Nat.cast_nonneg]
    _ = C / N := by ring
    _ < ε := by
        rw [div_lt_iff₀ hN_pos]
        have hN_gt : C / ε < (N : ℝ) := by
          have h1 : C / ε ≤ Nat.ceil (C / ε) := Nat.le_ceil _
          have h3 : (Nat.ceil (C / ε) + 1 : ℕ) ≤ N := hN
          have h4 : ((Nat.ceil (C / ε) + 1 : ℕ) : ℝ) ≤ (N : ℝ) := Nat.cast_le.mpr h3
          simp only [Nat.cast_add, Nat.cast_one] at h4
          linarith
        have := mul_lt_mul_of_pos_right hN_gt hε
        rw [div_mul_cancel₀ _ (ne_of_gt hε)] at this
        linarith

/-! ## Equidistribution of n·√2 -/

/-- **The sequence n ↦ n·√2 is equidistributed mod 1.**
    This is the simplest non-trivial case of the Weyl equidistribution theorem.
    Proof: √2 is irrational (Mathlib), so for each nonzero k, the exponential
    sum (1/N) Σ e^{2πiknα} → 0 by exp_sum_of_irrational_tendsto_zero. -/
theorem sqrt2_equidistributed :
    EquidistributedWeyl (fun n => (n : ℝ) * Real.sqrt 2) := by
  intro k hk
  have key := exp_sum_of_irrational_tendsto_zero (Real.sqrt 2) irrational_sqrt_two k hk
  -- Rewrite the exponential argument to match
  suffices h : (fun (N : ℕ) => (1 / (N : ℂ)) *
      ∑ n ∈ Finset.range N,
        cexp (2 * ↑Real.pi * I * ↑(↑k * ((n : ℝ) * Real.sqrt 2)))) =
    (fun (N : ℕ) => (1 / (N : ℂ)) *
      ∑ n ∈ Finset.range N,
        cexp (↑(↑n * (2 * π * ↑k * Real.sqrt 2)) * I)) by
    rw [h]; exact key
  funext N
  congr 1
  apply Finset.sum_congr rfl
  intro n _
  congr 1
  push_cast
  ring

/-! ## Existence of equidistributed sequence -/

/-- There exists an equidistributed sequence (namely n ↦ n·√2). -/
theorem continuum_limit_exists :
    ∃ (x : ℕ → ℝ), EquidistributedWeyl x :=
  ⟨_, sqrt2_equidistributed⟩

end

end UnifiedTheory.LayerA.ContinuumLimit
