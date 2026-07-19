/-
  LayerB/Pinsker.lean
  ────────────────────

  **Pinsker's inequality** for finite probability vectors, in the
  same Margolus–Levitin / LogSum conditional pattern used elsewhere
  in this stack: the binary-case analytic core is carried as a
  Prop hypothesis `BinaryPinsker`, and the structural reduction
  (total-variation = positive-part = sum-over-separator,
   KL ≥ binary KL at separator via log-sum) is proved here
  unconditionally.

  The binary-case discharge is intentionally deferred to a separate
  file.

  WHAT IS PROVEN (no sorry, no custom axioms):
    1. `tvDistance P Q`             — `(1/2) · ∑ |P_i − Q_i|`.
    2. `tvDistance_nonneg`.
    3. `separator P Q`              — the index set where `P ≥ Q`.
    4. `tvDistance_eq_separator_diff`
                                     — `TV = P(A) − Q(A)` for the
                                       separator A.
    5. `binaryKL p q`               — the two-point KL using `klTerm`.
    6. `log_sum_finset`             — finset-indexed log-sum from
                                       the fintype version.
    7. `klDivergence_ge_binaryKL_at_separator`
                                     — the structural reduction:
                                       `KL(P‖Q) ≥ binaryKL(P_A, Q_A)`.
    8. `BinaryPinsker` (predicate)  — the binary-case analytic
                                       hypothesis to be discharged
                                       separately.
    9. `pinsker_of_binaryPinsker`   — conditional Pinsker:
                                       `2·TV(P,Q)² ≤ KL(P‖Q)`.
-/

import UnifiedTheory.LayerB.LogSumInequality
import UnifiedTheory.LayerB.GibbsInequality

set_option relaxedAutoImplicit false

namespace UnifiedTheory.LayerB.Pinsker

open UnifiedTheory.LayerB.ClassicalEntropy
open UnifiedTheory.LayerB.ClassicalEntropy.ProbabilityVector
open UnifiedTheory.LayerB.ClassicalRelativeEntropy
open UnifiedTheory.LayerB.ClassicalChannelDPI
open UnifiedTheory.LayerB.LogSumInequality

variable {α ι : Type*} [Fintype α] [Fintype ι]

/-! ## 1. Total variation distance -/

/-- The total variation distance:
      `TV(P, Q) = ½ · ∑ |P_i − Q_i|`. -/
noncomputable def tvDistance (P Q : ProbabilityVector α) : ℝ :=
  (1/2 : ℝ) * ∑ i, |P.p i - Q.p i|

theorem tvDistance_nonneg (P Q : ProbabilityVector α) :
    0 ≤ tvDistance P Q := by
  apply mul_nonneg
  · norm_num
  · exact Finset.sum_nonneg fun i _ => abs_nonneg _

/-! ## 2. Separator and TV = P(A) - Q(A) -/

/-- The *separator*: the set of indices where `P` dominates `Q`. -/
noncomputable def separator (P Q : ProbabilityVector α) : Finset α := by
  classical exact Finset.univ.filter (fun i => Q.p i ≤ P.p i)

/-- TV equals the dominance-set probability gap:
      `TV(P, Q) = P(A) − Q(A)`  where  `A := { i : P_i ≥ Q_i }`. -/
theorem tvDistance_eq_separator_diff (P Q : ProbabilityVector α) :
    tvDistance P Q
      = (∑ i ∈ separator P Q, P.p i) - (∑ i ∈ separator P Q, Q.p i) := by
  classical
  unfold tvDistance separator
  set A : Finset α := Finset.univ.filter (fun i => Q.p i ≤ P.p i) with hA_def
  -- Split the absolute-value sum by membership in A.
  have h_split :
      ∑ i, |P.p i - Q.p i|
        = (∑ i ∈ A, |P.p i - Q.p i|)
          + (∑ i ∈ Finset.univ.filter (fun i => ¬ Q.p i ≤ P.p i),
              |P.p i - Q.p i|) := by
    exact (Finset.sum_filter_add_sum_filter_not Finset.univ
            (fun i => Q.p i ≤ P.p i) _).symm
  -- On A: |P - Q| = P - Q.
  have h_A : ∑ i ∈ A, |P.p i - Q.p i| = ∑ i ∈ A, (P.p i - Q.p i) := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [hA_def] at hi
    rw [Finset.mem_filter] at hi
    exact abs_of_nonneg (sub_nonneg.mpr hi.2)
  -- On Aᶜ: |P - Q| = Q - P.
  have h_B : ∑ i ∈ Finset.univ.filter (fun i => ¬ Q.p i ≤ P.p i),
              |P.p i - Q.p i|
           = ∑ i ∈ Finset.univ.filter (fun i => ¬ Q.p i ≤ P.p i),
              (Q.p i - P.p i) := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.mem_filter] at hi
    have h_lt : P.p i < Q.p i := lt_of_not_ge hi.2
    rw [abs_of_neg (sub_neg.mpr h_lt), neg_sub]
  -- Marginal sums for P and Q split A / Aᶜ.
  have h_P_split : ∑ i ∈ A, P.p i
                 + ∑ i ∈ Finset.univ.filter (fun i => ¬ Q.p i ≤ P.p i), P.p i
                 = 1 := by
    rw [Finset.sum_filter_add_sum_filter_not Finset.univ _ P.p]
    exact P.sum_one
  have h_Q_split : ∑ i ∈ A, Q.p i
                 + ∑ i ∈ Finset.univ.filter (fun i => ¬ Q.p i ≤ P.p i), Q.p i
                 = 1 := by
    rw [Finset.sum_filter_add_sum_filter_not Finset.univ _ Q.p]
    exact Q.sum_one
  -- Combine.
  rw [h_split, h_A, h_B]
  -- ∑_A (P-Q) = P_A - Q_A; ∑_B (Q-P) = Q_B - P_B = (1-Q_A) - (1-P_A) = P_A - Q_A.
  have h_sumA : ∑ i ∈ A, (P.p i - Q.p i) = (∑ i ∈ A, P.p i) - ∑ i ∈ A, Q.p i := by
    rw [Finset.sum_sub_distrib]
  have h_sumB :
      ∑ i ∈ Finset.univ.filter (fun i => ¬ Q.p i ≤ P.p i), (Q.p i - P.p i)
        = (∑ i ∈ A, P.p i) - ∑ i ∈ A, Q.p i := by
    rw [Finset.sum_sub_distrib]
    linarith [h_P_split, h_Q_split]
  rw [h_sumA, h_sumB]
  ring

/-! ## 3. Binary KL -/

/-- The binary KL divergence `binKL(p, q) = klTerm p q + klTerm (1−p) (1−q)`,
    written via the safe `klTerm` so zero cases drop out cleanly. -/
noncomputable def binaryKL (p q : ℝ) : ℝ :=
  klTerm p q + klTerm (1 - p) (1 - q)

/-! ## 4. Finset version of log-sum (subtype reduction) -/

/-- `log_sum_real` re-indexed over a `Finset`. -/
theorem log_sum_finset (s : Finset ι) (a b : ι → ℝ)
    (ha : ∀ i ∈ s, 0 ≤ a i) (hb : ∀ i ∈ s, 0 ≤ b i)
    (hAC : ∀ i ∈ s, a i ≠ 0 → b i ≠ 0) :
    klTerm (∑ i ∈ s, a i) (∑ i ∈ s, b i) ≤ ∑ i ∈ s, klTerm (a i) (b i) := by
  -- Reduce to `Fintype` of the subtype `{x // x ∈ s}` via `Finset.sum_attach`.
  rw [← Finset.sum_attach s a, ← Finset.sum_attach s b,
      ← Finset.sum_attach s (fun i => klTerm (a i) (b i))]
  exact log_sum_real (fun i : {x // x ∈ s} => a i.1)
                     (fun i : {x // x ∈ s} => b i.1)
                     (fun i => ha i.1 i.2) (fun i => hb i.1 i.2)
                     (fun i => hAC i.1 i.2)

/-! ## 5. Reduction to binary KL at the separator -/

/-- **The log-sum reduction.**  Splitting the index set by the
    separator and applying `log_sum_finset` to each half yields:

      `binaryKL (P(A), Q(A))  ≤  KL(P ‖ Q)`. -/
theorem klDivergence_ge_binaryKL_at_separator
    (P Q : ProbabilityVector α) (hAC : IsAbsolutelyContinuous P Q) :
    binaryKL (∑ i ∈ separator P Q, P.p i) (∑ i ∈ separator P Q, Q.p i)
      ≤ klDivergence P Q := by
  classical
  unfold klDivergence binaryKL separator
  set A : Finset α := Finset.univ.filter (fun i => Q.p i ≤ P.p i) with hA_def
  set B : Finset α := Finset.univ.filter (fun i => ¬ Q.p i ≤ P.p i) with hB_def
  -- KL = sum over A + sum over B.
  have h_split : ∑ i, klTerm (P.p i) (Q.p i)
                = ∑ i ∈ A, klTerm (P.p i) (Q.p i)
                  + ∑ i ∈ B, klTerm (P.p i) (Q.p i) :=
    (Finset.sum_filter_add_sum_filter_not Finset.univ _ _).symm
  -- log-sum on A: klTerm (P_A) (Q_A) ≤ ∑_A klTerm.
  have h_logA := log_sum_finset A P.p Q.p
    (fun i _ => P.nonneg i) (fun i _ => Q.nonneg i)
    (fun i _ => hAC i)
  -- log-sum on B: klTerm (P_B) (Q_B) ≤ ∑_B klTerm.
  have h_logB := log_sum_finset B P.p Q.p
    (fun i _ => P.nonneg i) (fun i _ => Q.nonneg i)
    (fun i _ => hAC i)
  -- P_B = 1 - P_A and Q_B = 1 - Q_A.
  have h_PB : ∑ i ∈ B, P.p i = 1 - ∑ i ∈ A, P.p i := by
    have h_total : (∑ i ∈ A, P.p i) + ∑ i ∈ B, P.p i = 1 := by
      rw [Finset.sum_filter_add_sum_filter_not Finset.univ _ P.p]
      exact P.sum_one
    linarith
  have h_QB : ∑ i ∈ B, Q.p i = 1 - ∑ i ∈ A, Q.p i := by
    have h_total : (∑ i ∈ A, Q.p i) + ∑ i ∈ B, Q.p i = 1 := by
      rw [Finset.sum_filter_add_sum_filter_not Finset.univ _ Q.p]
      exact Q.sum_one
    linarith
  rw [h_PB, h_QB] at h_logB
  rw [h_split]
  linarith [h_logA, h_logB]

/-! ## 6. The binary Pinsker hypothesis -/

/-- **`BinaryPinsker`**: the analytic core of Pinsker's inequality,
    isolated as a `Prop` hypothesis.  For real numbers `p, q` in
    `[0, 1]` with absolute continuity on both `p, q` and `1−p, 1−q`,

      `2 · (p − q)²  ≤  binaryKL p q`.

    Standard proof: the negative binary entropy `h(x) = x log x +
    (1−x) log(1−x)` has second derivative `1 / (x(1−x)) ≥ 4` on
    `(0, 1)`, and `binaryKL` is the Bregman divergence of `h`,
    so a Taylor expansion gives the quadratic lower bound.

    Discharged in a separate analytic file. -/
def BinaryPinsker : Prop :=
  ∀ p q : ℝ, 0 ≤ p → p ≤ 1 → 0 ≤ q → q ≤ 1 →
    (p ≠ 0 → q ≠ 0) → (1 - p ≠ 0 → 1 - q ≠ 0) →
    2 * (p - q) ^ 2 ≤ binaryKL p q

/-! ## 7. Conditional Pinsker -/

/-- Witness lemma: if a non-negative finite sum is non-zero, some
    summand is strictly positive. -/
private lemma sum_ne_zero_implies_witness_pos (s : Finset ι) (f : ι → ℝ)
    (hf : ∀ i ∈ s, 0 ≤ f i) (h : ∑ i ∈ s, f i ≠ 0) :
    ∃ i ∈ s, 0 < f i := by
  by_contra h_neg
  push_neg at h_neg
  apply h
  apply Finset.sum_eq_zero
  intro i hi
  exact le_antisymm (h_neg i hi) (hf i hi)

/-- **Conditional Pinsker's inequality.**  Under absolute continuity
    and the binary-case hypothesis,

      `2 · TV(P, Q)²  ≤  KL(P ‖ Q)`. -/
theorem pinsker_of_binaryPinsker
    (h_binary : BinaryPinsker)
    (P Q : ProbabilityVector α)
    (hAC : IsAbsolutelyContinuous P Q) :
    2 * tvDistance P Q ^ 2 ≤ klDivergence P Q := by
  classical
  set A := separator P Q with hA
  set p := ∑ i ∈ A, P.p i with hp
  set q := ∑ i ∈ A, Q.p i with hq
  -- TV = p - q.
  have h_TV : tvDistance P Q = p - q := tvDistance_eq_separator_diff P Q
  -- p, q ∈ [0, 1].
  have h_p_nn : 0 ≤ p := Finset.sum_nonneg (fun i _ => P.nonneg i)
  have h_q_nn : 0 ≤ q := Finset.sum_nonneg (fun i _ => Q.nonneg i)
  have h_p_le : p ≤ 1 := by
    have h_total : ∑ i, P.p i = 1 := P.sum_one
    have h_sub : p ≤ ∑ i, P.p i := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · exact Finset.subset_univ _
      · intros i _ _; exact P.nonneg i
    linarith
  have h_q_le : q ≤ 1 := by
    have h_total : ∑ i, Q.p i = 1 := Q.sum_one
    have h_sub : q ≤ ∑ i, Q.p i := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · exact Finset.subset_univ _
      · intros i _ _; exact Q.nonneg i
    linarith
  -- AC of p w.r.t. q: if some P_i > 0 in A, by AC some Q_i > 0 in A, so q > 0.
  have h_ac_pq : p ≠ 0 → q ≠ 0 := by
    intro hp_ne
    obtain ⟨i, hi_A, hi_pos⟩ :=
      sum_ne_zero_implies_witness_pos A P.p (fun i _ => P.nonneg i) hp_ne
    have h_Qi : Q.p i ≠ 0 := hAC i (ne_of_gt hi_pos)
    have h_Qi_pos : 0 < Q.p i := lt_of_le_of_ne (Q.nonneg i) (Ne.symm h_Qi)
    have h_q_pos : 0 < q := by
      apply lt_of_lt_of_le h_Qi_pos
      exact Finset.single_le_sum (f := Q.p) (fun j _ => Q.nonneg j) hi_A
    exact ne_of_gt h_q_pos
  -- AC of (1-p) w.r.t. (1-q): similar argument on the complement.
  have h_total_P : (∑ i ∈ A, P.p i) + ∑ i ∈ Finset.univ \ A, P.p i = 1 := by
    rw [← Finset.sum_union (Finset.disjoint_sdiff)]
    rw [Finset.union_sdiff_of_subset (Finset.subset_univ _)]
    exact P.sum_one
  have h_total_Q : (∑ i ∈ A, Q.p i) + ∑ i ∈ Finset.univ \ A, Q.p i = 1 := by
    rw [← Finset.sum_union (Finset.disjoint_sdiff)]
    rw [Finset.union_sdiff_of_subset (Finset.subset_univ _)]
    exact Q.sum_one
  have h_one_sub_p : 1 - p = ∑ i ∈ Finset.univ \ A, P.p i := by linarith
  have h_one_sub_q : 1 - q = ∑ i ∈ Finset.univ \ A, Q.p i := by linarith
  have h_ac_1pq : 1 - p ≠ 0 → 1 - q ≠ 0 := by
    intro hp1_ne
    rw [h_one_sub_p] at hp1_ne
    obtain ⟨i, hi_Ac, hi_pos⟩ :=
      sum_ne_zero_implies_witness_pos _ P.p (fun i _ => P.nonneg i) hp1_ne
    have h_Qi : Q.p i ≠ 0 := hAC i (ne_of_gt hi_pos)
    have h_Qi_pos : 0 < Q.p i := lt_of_le_of_ne (Q.nonneg i) (Ne.symm h_Qi)
    have h_1q_pos : 0 < 1 - q := by
      rw [h_one_sub_q]
      apply lt_of_lt_of_le h_Qi_pos
      exact Finset.single_le_sum (f := Q.p) (fun j _ => Q.nonneg j) hi_Ac
    exact ne_of_gt h_1q_pos
  -- Apply the binary hypothesis.
  have h_bp : 2 * (p - q) ^ 2 ≤ binaryKL p q :=
    h_binary p q h_p_nn h_p_le h_q_nn h_q_le h_ac_pq h_ac_1pq
  -- Apply the log-sum reduction.
  have h_red : binaryKL p q ≤ klDivergence P Q :=
    klDivergence_ge_binaryKL_at_separator P Q hAC
  -- Conclude.
  rw [h_TV]
  linarith

end UnifiedTheory.LayerB.Pinsker
