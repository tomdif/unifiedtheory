/-
  LayerB/ClassicalChannelDPI.lean
  ────────────────────────────────

  **Classical (stochastic-matrix) Data-Processing Inequality**,
  proved *conditional on the log-sum inequality* passed as a
  hypothesis.

  This mirrors the Margolus–Levitin pattern (cf.
  `LayerB/MargolusLevitin.lean`): isolate the hard analytic
  monster as a hypothesis, prove the structural / channel part
  unconditionally.  The log-sum inequality itself (the convex-
  analysis content) is left to a follow-up file.

  Specifically we prove

      KL(T ∘ P ‖ T ∘ Q)   ≤   KL(P ‖ Q)

  whenever `T` is a column-stochastic matrix and the log-sum
  inequality holds in the form

      klTerm (∑ a_i) (∑ b_i)   ≤   ∑ klTerm (a_i) (b_i).

  WHAT IS PROVEN (no sorry, no custom axioms):
    1. `StochasticMatrix α β`     — column-stochastic finite matrix.
    2. `StochasticMatrix.push`    — pushforward of a probability vector.
    3. `klTerm_smul_left`         — `klTerm (c·p) (c·q) = c · klTerm p q`
                                     for `0 ≤ c`.
    4. `LogSumInequality`         — abstract hypothesis carrying the
                                     analytic content.
    5. `klDivergence_contracts_under_stochastic_of_logsum`
                                   — the conditional classical DPI.
    6. `StochasticMatrix.id`      — identity channel, and
       `id_push`                   — its pushforward is the identity.

  Full quantum DPI is intentionally deferred; this is the scalar
  analogue and will serve as the engine for the diagonal-channel
  quantum DPI.
-/

import UnifiedTheory.LayerB.ClassicalRelativeEntropy

set_option relaxedAutoImplicit false

namespace UnifiedTheory.LayerB.ClassicalChannelDPI

open UnifiedTheory.LayerB.ClassicalEntropy
open UnifiedTheory.LayerB.ClassicalEntropy.ProbabilityVector
open UnifiedTheory.LayerB.ClassicalRelativeEntropy

variable {α β : Type*} [Fintype α] [Fintype β]

/-! ## 1. Column-stochastic finite matrices -/

/-- A column-stochastic matrix `T : β × α → ℝ` with non-negative
    entries whose columns sum to `1`.  Maps input states in `α`
    to output states in `β`. -/
structure StochasticMatrix (α β : Type*) [Fintype α] [Fintype β] where
  /-- The matrix entry `T(b, a)` — probability of mapping `a ↦ b`. -/
  M : β → α → ℝ
  /-- Entries are non-negative. -/
  nonneg : ∀ b a, 0 ≤ M b a
  /-- Each column sums to one. -/
  col_sum_one : ∀ a, ∑ b, M b a = 1

namespace StochasticMatrix

/-- The pushforward of a probability vector through a stochastic
    matrix: `(T · P)_b = ∑_a T(b,a) · P(a)`. -/
noncomputable def push (T : StochasticMatrix α β)
    (P : ProbabilityVector α) : ProbabilityVector β where
  p b := ∑ a, T.M b a * P.p a
  nonneg b := Finset.sum_nonneg fun a _ =>
    mul_nonneg (T.nonneg b a) (P.nonneg a)
  sum_one := by
    -- ∑ b, ∑ a, T b a · P a = ∑ a, ∑ b, T b a · P a
    --                       = ∑ a, (∑ b, T b a) · P a
    --                       = ∑ a, 1 · P a
    --                       = ∑ a, P a = 1
    rw [Finset.sum_comm]
    have h_inner : ∀ a, ∑ b, T.M b a * P.p a = P.p a := by
      intro a
      rw [← Finset.sum_mul, T.col_sum_one a, one_mul]
    simp_rw [h_inner]
    exact P.sum_one

/-- The identity stochastic channel on `α`. -/
noncomputable def id (α : Type*) [Fintype α] [DecidableEq α] :
    StochasticMatrix α α where
  M b a := if b = a then 1 else 0
  nonneg b a := by split_ifs <;> norm_num
  col_sum_one a := by
    rw [Finset.sum_ite_eq']
    simp

/-- The identity channel acts as the identity on probability vectors. -/
theorem id_push [DecidableEq α] (P : ProbabilityVector α) (a : α) :
    (StochasticMatrix.id α |>.push P).p a = P.p a := by
  change ∑ a', (if a = a' then (1 : ℝ) else 0) * P.p a' = P.p a
  rw [Finset.sum_eq_single a]
  · simp
  · intro a' _ ha'
    rw [if_neg (Ne.symm ha'), zero_mul]
  · intro h
    exact absurd (Finset.mem_univ _) h

end StochasticMatrix

/-! ## 2. Linear behaviour of `klTerm` under non-negative scaling -/

/-- **Scaling identity**: for any `0 ≤ c`,
      `klTerm (c·p) (c·q) = c · klTerm p q`.
    The non-negativity `_hc` is kept in the API for downstream
    callers (which arise in inequality contexts), but it is not
    load-bearing in the identity itself. -/
lemma klTerm_smul_left (c p q : ℝ) (_hc : 0 ≤ c) :
    klTerm (c * p) (c * q) = c * klTerm p q := by
  by_cases hcz : c = 0
  · rw [hcz, zero_mul, zero_mul, klTerm_zero_left, zero_mul]
  by_cases hp : p = 0
  · rw [hp, mul_zero, klTerm_zero_left, klTerm_zero_left, mul_zero]
  · have hcp : c * p ≠ 0 := mul_ne_zero hcz hp
    rw [klTerm_of_ne_zero hcp, klTerm_of_ne_zero hp]
    -- (c·p)/(c·q) = p/q (since c ≠ 0)
    have h_div : c * p / (c * q) = p / q :=
      mul_div_mul_left p q hcz
    rw [h_div]
    ring

/-! ## 3. The log-sum inequality (abstract hypothesis) -/

/-- **The log-sum inequality** for a fixed finite index set `ι`:
    for non-negative weights `a_i, b_i` satisfying the absolute-
    continuity condition `a_i ≠ 0 → b_i ≠ 0`,
      `klTerm (∑ a_i) (∑ b_i)  ≤  ∑ klTerm (a_i) (b_i)`.

    The AC hypothesis is essential under the Mathlib convention
    `Real.log 0 = 0`.  Without it the inequality fails in
    e.g. `a = (1,1), b = (0,1)`: the right-hand side collapses to
    `0` (via the `log 0 = 0` convention on the `a₁/b₁ = 1/0` term),
    while the left-hand side equals `2 · log 2 > 0`.

    This is the analytic monster.  We pass it in as a Prop so the
    structural DPI argument can be checked independently of the
    convex-analysis proof.  A subsequent file discharges this
    hypothesis using Jensen's inequality applied to `x ↦ x · log x`.

    Parameterising by `ι` (rather than universally over all finite
    types) avoids a universe-mismatch when the hypothesis is plugged
    into a theorem whose `α` lives at a specific universe level. -/
def LogSumInequality (ι : Type*) [Fintype ι] : Prop :=
  ∀ (a b : ι → ℝ),
    (∀ i, 0 ≤ a i) → (∀ i, 0 ≤ b i) →
    (∀ i, a i ≠ 0 → b i ≠ 0) →
    klTerm (∑ i, a i) (∑ i, b i) ≤ ∑ i, klTerm (a i) (b i)

/-! ## 4. The conditional DPI -/

/-- **Conditional classical Data-Processing Inequality.**  Under
    the log-sum inequality and absolute continuity `P ≪ Q`, the KL
    divergence cannot increase under pushforward by a column-
    stochastic channel:

      KL(T ∘ P ‖ T ∘ Q)   ≤   KL(P ‖ Q).

    Absolute continuity is essential — without it, the Mathlib
    `Real.log 0 = 0` convention makes both `KL` values finite but
    the contraction can fail.  Specifically, the per-row log-sum
    requires absolute continuity of `T(b,·)·P` w.r.t. `T(b,·)·Q`,
    which follows from `hAC` (multiplying by the same `T(b,a)` on
    both sides preserves the implication `≠ 0 → ≠ 0`).

    Proof:
      KL(TP‖TQ) = ∑_b klTerm (∑_a T(b,a)·P_a) (∑_a T(b,a)·Q_a)
                ≤ ∑_b ∑_a klTerm (T(b,a)·P_a) (T(b,a)·Q_a)   [log-sum per b]
                = ∑_b ∑_a T(b,a) · klTerm (P_a) (Q_a)          [scaling]
                = ∑_a (∑_b T(b,a)) · klTerm (P_a) (Q_a)        [sum_mul]
                = ∑_a 1 · klTerm (P_a) (Q_a)                   [col_sum_one]
                = KL(P‖Q). -/
theorem klDivergence_contracts_under_stochastic_of_logsum
    (T : StochasticMatrix α β)
    (P Q : ProbabilityVector α)
    (hAC : IsAbsolutelyContinuous P Q)
    (hLogSum : LogSumInequality α) :
    klDivergence (T.push P) (T.push Q) ≤ klDivergence P Q := by
  unfold klDivergence
  calc ∑ b, klTerm ((T.push P).p b) ((T.push Q).p b)
      = ∑ b, klTerm (∑ a, T.M b a * P.p a) (∑ a, T.M b a * Q.p a) := by
            apply Finset.sum_congr rfl
            intro b _
            rfl
    _ ≤ ∑ b, ∑ a, klTerm (T.M b a * P.p a) (T.M b a * Q.p a) := by
            apply Finset.sum_le_sum
            intro b _
            have hP_nn : ∀ i : α, 0 ≤ T.M b i * P.p i :=
              fun i => mul_nonneg (T.nonneg b i) (P.nonneg i)
            have hQ_nn : ∀ i : α, 0 ≤ T.M b i * Q.p i :=
              fun i => mul_nonneg (T.nonneg b i) (Q.nonneg i)
            -- Per-row AC: T(b,a)·P_a ≠ 0 ⟹ T(b,a) ≠ 0 ∧ P_a ≠ 0
            --                             ⟹ T(b,a) ≠ 0 ∧ Q_a ≠ 0  (hAC)
            --                             ⟹ T(b,a)·Q_a ≠ 0.
            have hAC_row : ∀ i : α,
                T.M b i * P.p i ≠ 0 → T.M b i * Q.p i ≠ 0 := by
              intro i hi
              obtain ⟨hT, hP⟩ := mul_ne_zero_iff.mp hi
              exact mul_ne_zero hT (hAC i hP)
            exact hLogSum (fun i => T.M b i * P.p i)
                          (fun i => T.M b i * Q.p i) hP_nn hQ_nn hAC_row
    _ = ∑ b, ∑ a, T.M b a * klTerm (P.p a) (Q.p a) := by
            apply Finset.sum_congr rfl; intro b _
            apply Finset.sum_congr rfl; intro a _
            exact klTerm_smul_left _ _ _ (T.nonneg b a)
    _ = ∑ a, ∑ b, T.M b a * klTerm (P.p a) (Q.p a) :=
            Finset.sum_comm
    _ = ∑ a, (∑ b, T.M b a) * klTerm (P.p a) (Q.p a) := by
            apply Finset.sum_congr rfl; intro a _
            rw [← Finset.sum_mul]
    _ = ∑ a, klTerm (P.p a) (Q.p a) := by
            apply Finset.sum_congr rfl; intro a _
            rw [T.col_sum_one a, one_mul]

end UnifiedTheory.LayerB.ClassicalChannelDPI
