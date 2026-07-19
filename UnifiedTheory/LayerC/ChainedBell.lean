/-
  LayerC/ChainedBell.lean — The chained Bell inequality (Braunstein-Caves 1990).

  ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
  CONTEXT

  `LayerB/SeparableCHSH.lean` proves the classical CHSH bound |S| ≤ 2
  for ANY factorizable correlation. `LayerB/TsirelsonBound.lean`
  proves the quantum Tsirelson bound |S| ≤ 2√2 for the singlet
  correlation E(θ_a, θ_b) = -cos(θ_a - θ_b).

  This file formalises the **N-setting chained Bell inequality** of
  Braunstein-Caves (1990), the natural generalisation of CHSH (the
  N = 1 case in our convention, corresponding to a 2-setting CHSH).

  Setup: Alice has N+1 binary measurement settings (indexed 0..N),
  Bob has N+1 binary measurement settings (indexed 0..N). Outcomes
  are ±1. The "chained" Bell quantity is

      I_N := Σ_{k≤N} E(A_k, B_k)             (N+1 "diagonal" terms)
           + Σ_{k<N} E(A_{k+1}, B_k)         (N "shifted" terms)
           - E(A_0, B_N)                     (one wrap-around term)

  This has 2N+1 correlators and a classical bound of 2N. N = 1
  recovers CHSH (with bound 2).

  ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
  WHAT IS PROVED

  – `ChainedLHVModel N`: a local hidden variable model with N+1 binary
    settings per party. Λ is a finite "hidden variable" space with a
    probability distribution μ; responses are ±1-valued functions of
    setting and hidden variable.
  – `ChainedLHVModel.correlation`: the µ-averaged correlator.
  – `ChainedLHVModel.I_N`: the chained Bell expression I_N for an LHV.
  – `chained_pointwise_bound`: **the pointwise telescoping bound.**
    For ANY ±1-valued functions a, b : Fin (N+1) → ℝ,
        |T(a, b)| ≤ 2N.
  – `ChainedLHVModel.abs_I_N_le`: **THE CLASSICAL CHAINED BELL BOUND.**
    For any chained LHV model with N+1 settings, |I_N| ≤ 2N.
  – `quantumChainedBell N`: the quantum prediction at uniformly-spaced
    angles, |I_N^Q| = 2(N+1)·cos(π/(2(N+1))).
  – `quantum_violates_chained`: **THE QUANTUM VIOLATION.**
    For N ≥ 1, 2(N+1)·cos(π/(2(N+1))) > 2N.
  – `no_LHV_realizes_quantumChainedBell`: **THE CHAINED BELL NO-GO.**

  ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
  HONEST SCOPE

  – Classical bound: PROVED unconditionally for arbitrary N ≥ 0.
  – Quantum value: stated as the Braunstein-Caves prediction
    `quantumChainedBell N = 2(N+1)·cos(π/(2(N+1)))`. The violation
    `> 2N` is proved using Mathlib's `1 - x²/2 ≤ cos x` plus
    `3 < π < 4`.
  – Asymptotic ratio I_N^Q / I_N^C → π/2 is NOT proved here.

  Zero sorry. Zero custom axioms.
-/

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

set_option relaxedAutoImplicit false

namespace UnifiedTheory.LayerC.ChainedBell

open Real Finset

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 1: ALGEBRAIC LEMMAS ON ±1 VALUES
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- For x, y ∈ {-1, +1}, |x + y| + |x - y| = 2 EXACTLY.
    Exactly one of x+y, x-y is zero; the other has absolute value 2. -/
lemma abs_add_plus_abs_sub_pm_one (x y : ℝ)
    (hx : x = 1 ∨ x = -1) (hy : y = 1 ∨ y = -1) :
    |x + y| + |x - y| = 2 := by
  rcases hx with rfl | rfl <;> rcases hy with rfl | rfl <;> norm_num

/-- A ±1 real has absolute value 1. -/
lemma abs_pm_one (x : ℝ) (hx : x = 1 ∨ x = -1) : |x| = 1 := by
  rcases hx with rfl | rfl <;> norm_num

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 2: TELESCOPING TRIANGLE INEQUALITY ON Fin (N+1)
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- The telescoping identity: a_N - a_0 = Σ_{k<N}(a_{k+1} - a_k),
    where a : Fin (N+1) → ℝ, indices via `Fin.castSucc` and
    `Fin.succ` for `k : Fin N`. -/
lemma telescoping_identity {N : ℕ} (a : Fin (N + 1) → ℝ) :
    a (Fin.last N) - a 0 =
    ∑ k : Fin N, (a k.succ - a k.castSucc) := by
  induction N with
  | zero => simp
  | succ M ih =>
    -- Split off the last term via Fin.sum_univ_castSucc.
    rw [Fin.sum_univ_castSucc]
    -- Define a' k = a (k.castSucc), which restricts a from Fin (M+2) to Fin (M+1).
    let a' : Fin (M + 1) → ℝ := fun k => a k.castSucc
    have ih' := ih a'
    -- Key identifications:
    --   a (Fin.last (M+1)) = a (Fin.last M).succ
    --   a (Fin.last M).castSucc = a' (Fin.last M)
    --   a 0 = a (Fin.castSucc 0) = a' 0
    have hlast_succ : (Fin.last (M + 1) : Fin (M + 2)) = (Fin.last M).succ := rfl
    have ha'_last : a' (Fin.last M) = a (Fin.last M).castSucc := rfl
    have ha'_zero : a' 0 = a (0 : Fin (M + 2)) := rfl
    -- Rewrite LHS using hlast_succ:
    rw [hlast_succ]
    -- Now goal: a (Fin.last M).succ - a 0
    --         = (∑ k:Fin M, a (k.castSucc).succ - a (k.castSucc).castSucc)
    --           + (a (Fin.last M).succ - a (Fin.last M).castSucc).
    -- Identify each summand at k : Fin M:
    --   a' k.succ - a' k.castSucc
    --     = a (k.succ.castSucc) - a (k.castSucc.castSucc)
    --     = a (k.castSucc.succ) - a (k.castSucc.castSucc)  [by Fin.castSucc_succ direction]
    -- Both directions of the (succ, castSucc) commute hold; we need:
    --     (k.succ).castSucc = (k.castSucc).succ   for k : Fin M, both in Fin (M+2).
    have h_comm : ∀ k : Fin M,
        (k.succ.castSucc : Fin (M + 2)) = k.castSucc.succ := by
      intro k; rfl
    have h_sum_eq :
        (∑ k : Fin M, (a' k.succ - a' k.castSucc))
        = ∑ k : Fin M, (a (Fin.castSucc k).succ - a (Fin.castSucc k).castSucc) := by
      apply Finset.sum_congr rfl
      intro k _
      -- Goal: a' k.succ - a' k.castSucc
      --     = a (Fin.castSucc k).succ - a (Fin.castSucc k).castSucc
      -- via (k.succ).castSucc = (k.castSucc).succ.
      change a (k.succ.castSucc) - a (k.castSucc.castSucc)
           = a (k.castSucc.succ) - a (k.castSucc.castSucc)
      rw [h_comm k]
    -- Rewrite ih' to express a'(last M) - a'(0) via this sum:
    rw [ha'_last, ha'_zero] at ih'
    rw [← h_sum_eq, ← ih']
    -- Now goal:
    --   a (Fin.last M).succ - a 0
    -- = (a (Fin.last M).castSucc - a 0)
    --   + (a (Fin.last M).succ - a (Fin.last M).castSucc)
    ring

/-- **Telescoping triangle inequality**: |a_N - a_0| ≤ Σ |a_{k+1} - a_k|. -/
lemma telescoping_abs_le {N : ℕ} (a : Fin (N + 1) → ℝ) :
    |a (Fin.last N) - a 0| ≤
      ∑ k : Fin N, |a k.succ - a k.castSucc| := by
  rw [telescoping_identity]
  exact Finset.abs_sum_le_sum_abs _ _

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 3: THE POINTWISE CHAINED BELL EXPRESSION + BOUND
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    For sequences a, b : Fin (N+1) → ℝ, the chained Bell integrand is

        T(a, b) := Σ_{k≤N} a_k · b_k
                 + Σ_{k<N} a_{k.succ} · b_{k.castSucc}
                 − a_0 · b_N.

    Regrouping (algebra):

        T = Σ_{k<N} b_{k.castSucc} · (a_{k.castSucc} + a_{k.succ})
            + b_N · (a_N − a_0).

    The classical bound |T| ≤ 2N follows from:
      • |b_k| = 1 for ±1 sequences, so the inner sum is bounded by
        Σ_{k<N} |a_{k.castSucc} + a_{k.succ}|.
      • The wrap-around |a_N − a_0| ≤ Σ_{k<N} |a_{k.succ} − a_{k.castSucc}|
        by telescoping.
      • The EXACT identity |x+y| + |x−y| = 2 for x, y ∈ {±1} kills the
        combined sum into Σ_{k<N} 2 = 2N.
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- The pointwise chained Bell integrand for sequences a, b : Fin (N+1) → ℝ. -/
def chainedPointwise {N : ℕ} (a b : Fin (N + 1) → ℝ) : ℝ :=
    (∑ k : Fin (N + 1), a k * b k)
  + (∑ k : Fin N, a k.succ * b k.castSucc)
  - a 0 * b (Fin.last N)

/-- **Algebraic regrouping** of T:
        T = Σ_{k<N} b_{k.castSucc}·(a_{k.castSucc} + a_{k.succ}) + b_N·(a_N − a_0). -/
lemma chainedPointwise_regroup {N : ℕ} (a b : Fin (N + 1) → ℝ) :
    chainedPointwise a b =
      (∑ k : Fin N, b k.castSucc * (a k.castSucc + a k.succ))
      + b (Fin.last N) * (a (Fin.last N) - a 0) := by
  unfold chainedPointwise
  -- Split the Σ_{k≤N} a_k b_k via Fin.sum_univ_castSucc.
  rw [Fin.sum_univ_castSucc (f := fun k => a k * b k)]
  -- Distribute the regrouped sum.
  have h_distrib :
      (∑ k : Fin N, b k.castSucc * (a k.castSucc + a k.succ))
      = (∑ k : Fin N, b k.castSucc * a k.castSucc)
        + (∑ k : Fin N, b k.castSucc * a k.succ) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl; intros; ring
  -- Commute multiplication inside the sums.
  have h_comm1 :
      (∑ k : Fin N, b k.castSucc * a k.castSucc)
      = (∑ k : Fin N, a k.castSucc * b k.castSucc) := by
    apply Finset.sum_congr rfl; intros; ring
  have h_comm2 :
      (∑ k : Fin N, b k.castSucc * a k.succ)
      = (∑ k : Fin N, a k.succ * b k.castSucc) := by
    apply Finset.sum_congr rfl; intros; ring
  rw [h_distrib, h_comm1, h_comm2]
  ring

/-- The triangle inequality applied to the regrouped chained Bell expression. -/
lemma chainedPointwise_abs_le_regrouped {N : ℕ} (a b : Fin (N + 1) → ℝ) :
    |chainedPointwise a b| ≤
      (∑ k : Fin N, |b k.castSucc| * |a k.castSucc + a k.succ|)
      + |b (Fin.last N)| * |a (Fin.last N) - a 0| := by
  rw [chainedPointwise_regroup]
  -- |X + Y| ≤ |X| + |Y|
  refine le_trans (abs_add_le _ _) ?_
  -- |Σ b · (a+a)| ≤ Σ |b · (a+a)| = Σ |b| · |a+a|
  have h_sum_abs :
      |∑ k : Fin N, b k.castSucc * (a k.castSucc + a k.succ)|
      ≤ ∑ k : Fin N, |b k.castSucc * (a k.castSucc + a k.succ)| :=
    Finset.abs_sum_le_sum_abs _ _
  have h_sum_eq :
      (∑ k : Fin N, |b k.castSucc * (a k.castSucc + a k.succ)|)
      = ∑ k : Fin N, |b k.castSucc| * |a k.castSucc + a k.succ| := by
    apply Finset.sum_congr rfl
    intros k _; exact abs_mul _ _
  -- |b_N · (a_N - a_0)| = |b_N| · |a_N - a_0|
  have h_last_eq :
      |b (Fin.last N) * (a (Fin.last N) - a 0)|
      = |b (Fin.last N)| * |a (Fin.last N) - a 0| := abs_mul _ _
  linarith [h_sum_abs.trans h_sum_eq.le, h_last_eq.le, h_last_eq.symm.le]

/-- **THE POINTWISE CHAINED BELL BOUND.**

    For any ±1-valued sequences a, b : Fin (N+1) → ℝ, the chained Bell
    integrand satisfies |T(a, b)| ≤ 2N. -/
theorem chained_pointwise_bound {N : ℕ} (a b : Fin (N + 1) → ℝ)
    (ha : ∀ k, a k = 1 ∨ a k = -1) (hb : ∀ k, b k = 1 ∨ b k = -1) :
    |chainedPointwise a b| ≤ 2 * (N : ℝ) := by
  -- Step 1: triangle-and-regroup bound.
  have h1 := chainedPointwise_abs_le_regrouped a b
  -- Step 2: |b_k| = 1 for all k.
  have h_bk_one : ∀ k : Fin N, |b k.castSucc| = 1 := fun k => abs_pm_one _ (hb _)
  have h_bN_one : |b (Fin.last N)| = 1 := abs_pm_one _ (hb _)
  -- Simplify the bound: each |b|·|...| = |...|.
  have h2 :
      (∑ k : Fin N, |b k.castSucc| * |a k.castSucc + a k.succ|)
      + |b (Fin.last N)| * |a (Fin.last N) - a 0|
      = (∑ k : Fin N, |a k.castSucc + a k.succ|)
        + |a (Fin.last N) - a 0| := by
    rw [h_bN_one, one_mul]
    congr 1
    apply Finset.sum_congr rfl
    intros k _
    rw [h_bk_one, one_mul]
  -- Step 3: telescoping triangle for |a_N - a_0|.
  have h_tele := telescoping_abs_le a
  -- Step 4: combine into Σ (|a+a| + |a-a|).
  have h_combine :
      (∑ k : Fin N, |a k.castSucc + a k.succ|) + |a (Fin.last N) - a 0|
      ≤ ∑ k : Fin N, (|a k.castSucc + a k.succ| + |a k.succ - a k.castSucc|) := by
    rw [Finset.sum_add_distrib]
    linarith
  -- Step 5: each summand equals 2 by abs_add_plus_abs_sub_pm_one.
  have h_each : ∀ k : Fin N,
      |a k.castSucc + a k.succ| + |a k.succ - a k.castSucc| = 2 := by
    intro k
    have h := abs_add_plus_abs_sub_pm_one (a k.castSucc) (a k.succ) (ha _) (ha _)
    have hsym : |a k.succ - a k.castSucc| = |a k.castSucc - a k.succ| :=
      abs_sub_comm _ _
    linarith
  -- Step 6: sum of 2's is 2N.
  have h_sum_2N :
      ∑ k : Fin N, (|a k.castSucc + a k.succ| + |a k.succ - a k.castSucc|) = 2 * (N : ℝ) := by
    have h_rewrite :
        ∑ k : Fin N, (|a k.castSucc + a k.succ| + |a k.succ - a k.castSucc|)
        = ∑ _k : Fin N, (2 : ℝ) := by
      apply Finset.sum_congr rfl
      intros k _; exact h_each k
    rw [h_rewrite]
    simp [Finset.sum_const, Finset.card_univ, Fintype.card_fin, mul_comm]
  -- Chain everything.
  calc |chainedPointwise a b|
      ≤ (∑ k : Fin N, |b k.castSucc| * |a k.castSucc + a k.succ|)
        + |b (Fin.last N)| * |a (Fin.last N) - a 0| := h1
    _ = (∑ k : Fin N, |a k.castSucc + a k.succ|)
        + |a (Fin.last N) - a 0| := h2
    _ ≤ ∑ k : Fin N, (|a k.castSucc + a k.succ| + |a k.succ - a k.castSucc|) := h_combine
    _ = 2 * (N : ℝ) := h_sum_2N

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 4: LHV MODEL AND CLASSICAL CHAINED BELL BOUND
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- A local hidden variable model for the chained Bell scenario with
    N+1 binary measurement settings per party. -/
structure ChainedLHVModel (N : ℕ) where
  /-- The hidden variable space (finite). -/
  Λ : Type
  /-- Λ is finite. -/
  [fintype : Fintype Λ]
  /-- Probability distribution over hidden variables. -/
  μ : Λ → ℝ
  /-- Probabilities are non-negative. -/
  μ_nonneg : ∀ l, 0 ≤ μ l
  /-- Probabilities sum to 1. -/
  μ_sum : (∑ l, μ l) = 1
  /-- Alice's response function: setting × hidden variable → ±1. -/
  responseA : Fin (N + 1) → Λ → ℝ
  /-- Bob's response function: setting × hidden variable → ±1. -/
  responseB : Fin (N + 1) → Λ → ℝ
  /-- Alice's responses are ±1. -/
  rA_pm : ∀ k l, responseA k l = 1 ∨ responseA k l = -1
  /-- Bob's responses are ±1. -/
  rB_pm : ∀ k l, responseB k l = 1 ∨ responseB k l = -1

attribute [instance] ChainedLHVModel.fintype

namespace ChainedLHVModel

variable {N : ℕ}

/-- The LHV-averaged correlator. -/
def correlation (m : ChainedLHVModel N) (x y : Fin (N + 1)) : ℝ :=
  ∑ l, m.μ l * m.responseA x l * m.responseB y l

/-- The chained Bell expression I_N for an LHV model. -/
def I_N (m : ChainedLHVModel N) : ℝ :=
    (∑ k : Fin (N + 1), m.correlation k k)
  + (∑ k : Fin N, m.correlation k.succ k.castSucc)
  - m.correlation 0 (Fin.last N)

/-- Pull out μ: I_N = Σ_λ μ(λ) · T(A(·,λ), B(·,λ)). -/
lemma I_N_eq_sum_mu_chainedPointwise (m : ChainedLHVModel N) :
    m.I_N = ∑ l, m.μ l * chainedPointwise (fun k => m.responseA k l)
                                          (fun k => m.responseB k l) := by
  unfold I_N correlation chainedPointwise
  -- Strategy: convert each Σ_k Σ_l μ·A·B into Σ_l μ · Σ_k A·B by `Finset.sum_comm`,
  -- then factor μ(l) and combine into a single Σ_l of the bracketed expression.
  -- Step 1: rewrite each piece into a Σ_l shape.
  have h1 :
      (∑ k : Fin (N+1), ∑ l, m.μ l * m.responseA k l * m.responseB k l)
      = ∑ l, m.μ l * ∑ k : Fin (N+1),
                       (fun k => m.responseA k l) k * (fun k => m.responseB k l) k := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intros l _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intros k _; ring
  have h2 :
      (∑ k : Fin N, ∑ l, m.μ l * m.responseA k.succ l * m.responseB k.castSucc l)
      = ∑ l, m.μ l * ∑ k : Fin N,
            (fun k => m.responseA k l) k.succ * (fun k => m.responseB k l) k.castSucc := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intros l _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intros k _; ring
  have h3 :
      (∑ l, m.μ l * m.responseA 0 l * m.responseB (Fin.last N) l)
      = ∑ l, m.μ l * ((fun k => m.responseA k l) 0
                      * (fun k => m.responseB k l) (Fin.last N)) := by
    apply Finset.sum_congr rfl
    intros l _; ring
  -- Now rewrite LHS using h1, h2, h3.
  rw [h1, h2, h3]
  -- Now LHS = (Σ_l μ·X) + (Σ_l μ·Y) - (Σ_l μ·Z) where X,Y,Z are the per-l
  -- chained pointwise pieces. Combine into single Σ_l μ·(X+Y-Z).
  rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intros l _; ring

/-- **THE CLASSICAL CHAINED BELL BOUND.**

    For any chained LHV model with N+1 binary settings per party,
        |I_N| ≤ 2N.

    This is the standard Braunstein-Caves bound (1990), generalising
    CHSH (the N=1 case, bound 2). -/
theorem abs_I_N_le (m : ChainedLHVModel N) :
    |m.I_N| ≤ 2 * (N : ℝ) := by
  rw [I_N_eq_sum_mu_chainedPointwise]
  -- |Σ_l μ_l · T_l| ≤ Σ_l |μ_l · T_l| = Σ_l μ_l · |T_l| (μ_l ≥ 0)
  -- ≤ Σ_l μ_l · 2N = 2N (μ sums to 1).
  have h_tri :
      |∑ l, m.μ l * chainedPointwise (fun k => m.responseA k l)
                                     (fun k => m.responseB k l)|
      ≤ ∑ l, |m.μ l * chainedPointwise (fun k => m.responseA k l)
                                       (fun k => m.responseB k l)| :=
    Finset.abs_sum_le_sum_abs _ _
  have h_each : ∀ l : m.Λ,
      |m.μ l * chainedPointwise (fun k => m.responseA k l)
                                (fun k => m.responseB k l)|
      ≤ m.μ l * (2 * (N : ℝ)) := by
    intro l
    rw [abs_mul, abs_of_nonneg (m.μ_nonneg l)]
    have hT := chained_pointwise_bound
      (fun k => m.responseA k l) (fun k => m.responseB k l)
      (fun k => m.rA_pm k l) (fun k => m.rB_pm k l)
    exact mul_le_mul_of_nonneg_left hT (m.μ_nonneg l)
  have h_sum_each :
      ∑ l, |m.μ l * chainedPointwise (fun k => m.responseA k l)
                                     (fun k => m.responseB k l)|
      ≤ ∑ l, m.μ l * (2 * (N : ℝ)) := by
    apply Finset.sum_le_sum
    intros l _; exact h_each l
  have h_sum_eq :
      (∑ l, m.μ l * (2 * (N : ℝ))) = 2 * (N : ℝ) := by
    rw [← Finset.sum_mul, m.μ_sum, one_mul]
  linarith

end ChainedLHVModel

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 5: THE QUANTUM PREDICTION AND VIOLATION
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    For the singlet at uniformly-spaced angles
        α_k = k · π/(N+1) for k = 0..N
        β_k = (k + 1/2) · π/(N+1) for k = 0..N
    with E(θ_a, θ_b) = -cos(θ_a - θ_b), all "matched" correlators
    equal -cos(π/(2(N+1))), and the wrap-around term gives the
    "anti-matched" +cos(π/(2(N+1))). Summing:
        I_N^Q = -(2N+1) cos(π/(2(N+1))) - cos(π/(2(N+1)))
              = -2(N+1) cos(π/(2(N+1))).
    So |I_N^Q| = 2(N+1) cos(π/(2(N+1))).
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- The quantum chained Bell value: |I_N^Q| = 2(N+1)·cos(π/(2(N+1)))
    at Braunstein-Caves uniformly-spaced singlet angles. -/
noncomputable def quantumChainedBell (N : ℕ) : ℝ :=
  2 * ((N : ℝ) + 1) * Real.cos (Real.pi / (2 * ((N : ℝ) + 1)))

/-- **TRIG VIOLATION INEQUALITY**: for N ≥ 1,
        2(N+1)·cos(π/(2(N+1))) > 2N.

    Proof: by Mathlib's `1 - x²/2 ≤ cos x`,
        cos(π/(2(N+1))) ≥ 1 - π²/(8(N+1)²).
    So 2(N+1)·cos(...) ≥ 2(N+1) - π²/(4(N+1)).
    We need: 2(N+1) - π²/(4(N+1)) > 2N, i.e. π²/(4(N+1)) < 2, i.e.
    π² < 8(N+1). For N ≥ 1, 8(N+1) ≥ 16 > π² (since π < 4 gives π² < 16).
    For the borderline N = 1, π² < 9.87 < 16. -/
theorem quantum_violates_chained (N : ℕ) (hN : 1 ≤ N) :
    2 * (N : ℝ) < quantumChainedBell N := by
  unfold quantumChainedBell
  -- Set x = π/(2(N+1)). Then x > 0 (since N+1 > 0).
  set x : ℝ := Real.pi / (2 * ((N : ℝ) + 1)) with hx_def
  -- Apply `one_sub_sq_div_two_le_cos`: 1 - x²/2 ≤ cos x.
  have h_cos_lb : 1 - x ^ 2 / 2 ≤ Real.cos x :=
    Real.one_sub_sq_div_two_le_cos
  -- Step: 2(N+1)·cos(x) ≥ 2(N+1) - (N+1)·x².
  have hNp1_pos : (0 : ℝ) < (N : ℝ) + 1 := by positivity
  have h_2Np1_pos : (0 : ℝ) ≤ 2 * ((N : ℝ) + 1) := by positivity
  have h_lhs_ge :
      2 * ((N : ℝ) + 1) * (1 - x^2 / 2)
      ≤ 2 * ((N : ℝ) + 1) * Real.cos x :=
    mul_le_mul_of_nonneg_left h_cos_lb h_2Np1_pos
  -- Compute: 2(N+1) · (1 - x²/2) = 2(N+1) - (N+1)·x².
  have h_expand : 2 * ((N : ℝ) + 1) * (1 - x^2 / 2)
                = 2 * ((N : ℝ) + 1) - ((N : ℝ) + 1) * x^2 := by ring
  -- Now we need 2N < 2(N+1) - (N+1)·x², i.e. (N+1)·x² < 2.
  -- x = π/(2(N+1)), so x² = π² / (4(N+1)²), and (N+1)·x² = π² / (4(N+1)).
  -- Need π² / (4(N+1)) < 2, i.e. π² < 8(N+1).
  -- For N ≥ 1, 8(N+1) ≥ 16, and π² < 16 since π < 4.
  have h_Np1_ne : ((N : ℝ) + 1) ≠ 0 := ne_of_gt hNp1_pos
  have h_x_sq : x ^ 2 = Real.pi ^ 2 / (4 * ((N : ℝ) + 1)^2) := by
    rw [hx_def]
    rw [div_pow]
    congr 1
    ring
  have h_term : ((N : ℝ) + 1) * x ^ 2 = Real.pi ^ 2 / (4 * ((N : ℝ) + 1)) := by
    rw [h_x_sq]
    field_simp
  have h_pi_lt_4 : Real.pi < 4 := Real.pi_lt_four
  have h_pi_pos : 0 < Real.pi := Real.pi_pos
  have h_pi_sq_lt_16 : Real.pi ^ 2 < 16 := by
    have h : Real.pi ^ 2 < 4 ^ 2 := by
      have := mul_self_lt_mul_self h_pi_pos.le h_pi_lt_4
      nlinarith [h_pi_pos]
    linarith
  have hN_R : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have h_8Np1_ge_16 : 16 ≤ 8 * ((N : ℝ) + 1) := by linarith
  have h_term_lt_2 : ((N : ℝ) + 1) * x ^ 2 < 2 := by
    rw [h_term]
    -- π² / (4(N+1)) < 2  ⟺  π² < 8(N+1)
    have h_denom_pos : (0 : ℝ) < 4 * ((N : ℝ) + 1) := by positivity
    rw [div_lt_iff₀ h_denom_pos]
    -- π² < 2 · 4(N+1) = 8(N+1)
    have : Real.pi ^ 2 < 16 := h_pi_sq_lt_16
    linarith
  -- Chain:  2N < 2(N+1) - (N+1)·x² ≤ 2(N+1)·(1 - x²/2) ≤ 2(N+1)·cos x.
  have h_step1 : 2 * (N : ℝ) < 2 * ((N : ℝ) + 1) - ((N : ℝ) + 1) * x ^ 2 := by
    linarith
  linarith [h_step1, h_expand ▸ h_lhs_ge]

/-- **THE CHAINED BELL NO-GO**: no LHV model can achieve the quantum
    chained Bell value for N ≥ 1 (i.e. 2 or more settings per party).

    The QM prediction `quantumChainedBell N` is strictly larger than
    the classical LHV bound `2N`, so no LHV can match it. -/
theorem no_LHV_realizes_quantumChainedBell (N : ℕ) (hN : 1 ≤ N) :
    ¬ ∃ m : ChainedLHVModel N, m.I_N = quantumChainedBell N := by
  intro ⟨m, hm⟩
  have hbound : |m.I_N| ≤ 2 * (N : ℝ) := ChainedLHVModel.abs_I_N_le m
  have hviol : 2 * (N : ℝ) < quantumChainedBell N := quantum_violates_chained N hN
  -- |I_N| ≤ 2N but I_N = quantumChainedBell N > 2N, so |quantumChainedBell N| ≤ 2N.
  rw [hm] at hbound
  -- But quantumChainedBell N > 2N > 0 (since N ≥ 1, the value is positive).
  have hQ_pos : 0 < quantumChainedBell N := by linarith
  have h_le_self : quantumChainedBell N = |quantumChainedBell N| :=
    (abs_of_pos hQ_pos).symm
  linarith [h_le_self ▸ hbound]

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 6: THE CHAINED BELL MASTER THEOREM
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- **THE CHAINED BELL MASTER THEOREM** (Braunstein-Caves 1990).

    Three statements bundled:
    (1) **Classical chained Bell bound**: |I_N| ≤ 2N for ANY local
        hidden variable model with N+1 binary settings per party.
    (2) **Quantum violation**: for N ≥ 1, the singlet at uniformly-spaced
        angles achieves the value 2(N+1)·cos(π/(2(N+1))), strictly
        exceeding the classical bound 2N.
    (3) **The no-go**: no LHV can match the quantum value for N ≥ 1.

    The CHSH case N = 1 gives bound 2 and quantum value 2·2·cos(π/4)
    = 4·(√2/2) = 2√2 = the standard Tsirelson value.

    HONEST SCOPE: the classical bound is fully proved; the quantum value
    is stated (not derived from operators here) as the Braunstein-Caves
    angle-spaced singlet prediction, with the violation against the
    classical bound rigorously proved using the Mathlib trig inequality
    1 - x²/2 ≤ cos x and the bound π < 4. -/
theorem chainedBell_master (N : ℕ) (hN : 1 ≤ N) :
    -- (1) Classical bound
    (∀ m : ChainedLHVModel N, |m.I_N| ≤ 2 * (N : ℝ))
    -- (2) Quantum violation
    ∧ (2 * (N : ℝ) < quantumChainedBell N)
    -- (3) No-go
    ∧ (¬ ∃ m : ChainedLHVModel N, m.I_N = quantumChainedBell N) :=
  ⟨ChainedLHVModel.abs_I_N_le,
   quantum_violates_chained N hN,
   no_LHV_realizes_quantumChainedBell N hN⟩

end UnifiedTheory.LayerC.ChainedBell
