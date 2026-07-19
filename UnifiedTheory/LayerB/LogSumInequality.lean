/-
  LayerB/LogSumInequality.lean
  ─────────────────────────────

  **Discharges the `LogSumInequality` hypothesis used by the
  classical / diagonal-quantum / measurement-channel DPI files.**

  The log-sum inequality, in the form used throughout this stack:

      klTerm (∑ a_i) (∑ b_i)   ≤   ∑ klTerm (a_i) (b_i)

  for non-negative reals `a_i, b_i` satisfying the absolute-
  continuity condition `a_i ≠ 0 → b_i ≠ 0`.  This is the standard
  finite-dimensional log-sum / Gibbs inequality; AC is required
  because under the Mathlib convention `Real.log 0 = 0` the
  inequality fails on counter-examples like `a = (1,1), b = (0,1)`.

  Proof strategy: reduce to Jensen's inequality applied to the
  convex function `x ↦ x · log x` on `[0, ∞)` (i.e.
  `Real.convexOn_mul_log`), with weights `w_i := b_i / B` and
  points `z_i := a_i / b_i`.

  WHAT IS PROVEN (no sorry, no custom axioms):
    1. `log_sum_real`            — the scalar log-sum inequality.
    2. `logSumInequality_holds`  — discharges the abstract
                                    `LogSumInequality ι` predicate.

  Corollary modules can now unconditionally instantiate every DPI
  theorem in `ClassicalChannelDPI`, `DiagonalQuantumDPI`,
  `MeasurementChannel`, etc.
-/

import UnifiedTheory.LayerB.ClassicalChannelDPI
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.Analysis.Convex.Jensen

set_option relaxedAutoImplicit false

namespace UnifiedTheory.LayerB.LogSumInequality

open UnifiedTheory.LayerB.ClassicalEntropy
open UnifiedTheory.LayerB.ClassicalEntropy.ProbabilityVector
open UnifiedTheory.LayerB.ClassicalRelativeEntropy
open UnifiedTheory.LayerB.ClassicalChannelDPI

variable {ι : Type*} [Fintype ι]

/-! ## 1. The scalar log-sum inequality -/

/-- **The finite-dimensional log-sum inequality.**  For non-negative
    reals `a_i, b_i` with absolute continuity (`a_i ≠ 0 → b_i ≠ 0`),

      klTerm (∑ a_i) (∑ b_i)   ≤   ∑ klTerm (a_i) (b_i). -/
theorem log_sum_real (a b : ι → ℝ)
    (ha : ∀ i, 0 ≤ a i) (hb : ∀ i, 0 ≤ b i)
    (hAC : ∀ i, a i ≠ 0 → b i ≠ 0) :
    klTerm (∑ i, a i) (∑ i, b i) ≤ ∑ i, klTerm (a i) (b i) := by
  set A := ∑ i, a i with hA_def
  set B := ∑ i, b i with hB_def
  ----------------------------------------------------------------
  -- Edge case 1: B = 0 — by AC, A = 0 too, both sides vanish.
  ----------------------------------------------------------------
  by_cases hB_zero : B = 0
  · have h_all_b : ∀ i, b i = 0 := by
      intro i
      exact (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => hb j)).mp hB_zero i
        (Finset.mem_univ i)
    have h_all_a : ∀ i, a i = 0 := by
      intro i
      by_contra h_ne
      exact hAC i h_ne (h_all_b i)
    have hA_zero : A = 0 := Finset.sum_eq_zero (fun i _ => h_all_a i)
    have h_lhs_zero : klTerm A B = 0 := by rw [hA_zero, klTerm_zero_left]
    have h_rhs_zero : ∑ i, klTerm (a i) (b i) = 0 := by
      apply Finset.sum_eq_zero
      intro i _
      rw [h_all_a i, klTerm_zero_left]
    linarith
  ----------------------------------------------------------------
  -- B > 0 hereafter.
  ----------------------------------------------------------------
  have hB_pos : 0 < B :=
    lt_of_le_of_ne (Finset.sum_nonneg (fun i _ => hb i)) (Ne.symm hB_zero)
  have hB_ne : B ≠ 0 := hB_zero
  ----------------------------------------------------------------
  -- Edge case 2: A = 0 — LHS = 0, RHS ≥ 0 termwise.
  ----------------------------------------------------------------
  by_cases hA_zero : A = 0
  · have h_lhs_zero : klTerm A B = 0 := by rw [hA_zero, klTerm_zero_left]
    rw [h_lhs_zero]
    apply Finset.sum_nonneg
    intro i _
    have h_ai_zero : a i = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => ha j)).mp hA_zero i
        (Finset.mem_univ i)
    rw [h_ai_zero, klTerm_zero_left]
  ----------------------------------------------------------------
  -- Main case: A > 0 and B > 0 — Jensen on x · log x.
  ----------------------------------------------------------------
  have hA_pos : 0 < A :=
    lt_of_le_of_ne (Finset.sum_nonneg (fun i _ => ha i)) (Ne.symm hA_zero)
  have hA_ne : A ≠ 0 := hA_zero
  -- Convexity of f(x) = x · log x on [0, ∞)
  have hf : ConvexOn ℝ (Set.Ici (0 : ℝ)) (fun x => x * Real.log x) :=
    Real.convexOn_mul_log
  -- Weights w i := b i / B
  have h_weights_nn : ∀ i ∈ Finset.univ, 0 ≤ b i / B :=
    fun i _ => div_nonneg (hb i) (le_of_lt hB_pos)
  have h_weights_sum : ∑ i, b i / B = 1 := by
    have h_eq : ∑ i, b i / B = (∑ i, b i) * B⁻¹ := by
      simp_rw [div_eq_mul_inv]
      rw [← Finset.sum_mul]
    rw [h_eq, ← hB_def, ← div_eq_mul_inv, div_self hB_ne]
  -- Points z i := a i / b i, all in [0, ∞)
  have h_pts_mem : ∀ i ∈ Finset.univ, a i / b i ∈ Set.Ici (0 : ℝ) := by
    intro i _
    simp only [Set.mem_Ici]
    by_cases h_bi : b i = 0
    · rw [h_bi, div_zero]
    · exact div_nonneg (ha i) (hb i)
  -- Jensen's inequality (the `Finset.sum` form).
  have hJensen := hf.map_sum_le h_weights_nn h_weights_sum h_pts_mem
  simp only [smul_eq_mul] at hJensen
  -- hJensen :
  --   (∑ i, b i / B * (a i / b i)) * Real.log (∑ i, b i / B * (a i / b i))
  --     ≤ ∑ i, b i / B * (a i / b i * Real.log (a i / b i))
  -- Step A: identify the LHS argument as A / B.
  have h_zsum_eq : (∑ i, b i / B * (a i / b i)) = A / B := by
    have h_per : ∀ i, (b i / B) * (a i / b i) = a i / B := by
      intro i
      by_cases h_bi : b i = 0
      · have h_ai : a i = 0 := by
          by_contra h_ne
          exact hAC i h_ne h_bi
        rw [h_bi, h_ai]; simp
      · field_simp
    simp_rw [h_per]
    have h_eq : ∑ i, a i / B = (∑ i, a i) * B⁻¹ := by
      simp_rw [div_eq_mul_inv]
      rw [← Finset.sum_mul]
    rw [h_eq, ← hA_def, ← div_eq_mul_inv]
  rw [h_zsum_eq] at hJensen
  -- Step B: relate the RHS sum to (1/B) · ∑ a_i · log(a_i / b_i).
  have h_rhs_eq :
      ∑ i, b i / B * (a i / b i * Real.log (a i / b i))
        = (1 / B) * ∑ i, a i * Real.log (a i / b i) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    by_cases h_bi : b i = 0
    · have h_ai : a i = 0 := by
        by_contra h_ne
        exact hAC i h_ne h_bi
      rw [h_bi, h_ai]; simp
    · field_simp
  rw [h_rhs_eq] at hJensen
  -- hJensen : (A/B) * log(A/B) ≤ (1/B) * ∑ i, a i * log(a i / b i)
  -- Multiply by B (positive) to clear denominators.
  have h_scaled :
      A * Real.log (A / B) ≤ ∑ i, a i * Real.log (a i / b i) := by
    have h_mul := mul_le_mul_of_nonneg_left hJensen (le_of_lt hB_pos)
    -- h_mul : B * ((A/B) * log(A/B)) ≤ B * ((1/B) * ∑ ...)
    have h_lhs_simp : B * (A / B * Real.log (A / B))
                    = A * Real.log (A / B) := by field_simp
    have h_rhs_simp : B * (1 / B * ∑ i, a i * Real.log (a i / b i))
                    = ∑ i, a i * Real.log (a i / b i) := by field_simp
    linarith [h_mul, h_lhs_simp, h_rhs_simp]
  -- Convert to klTerm form.
  rw [klTerm_of_ne_zero hA_ne]
  -- Goal: A * log(A/B) ≤ ∑ i, klTerm (a i) (b i)
  have h_rhs_klTerm :
      ∑ i, a i * Real.log (a i / b i) = ∑ i, klTerm (a i) (b i) := by
    apply Finset.sum_congr rfl
    intro i _
    rw [klTerm_eq]
  linarith [h_scaled, h_rhs_klTerm]

/-! ## 2. Discharging the abstract `LogSumInequality` predicate -/

/-- **`LogSumInequality ι` is a theorem.**  Discharges the
    Margolus–Levitin-style hypothesis carried by every DPI
    theorem in this file's downstream. -/
theorem logSumInequality_holds : LogSumInequality ι :=
  fun a b ha hb hAC => log_sum_real a b ha hb hAC

end UnifiedTheory.LayerB.LogSumInequality
