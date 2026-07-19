/-
  LayerC/PRBox.lean — The Popescu–Rohrlich (PR) box and the strict
  three-tier hierarchy LHV < QM < NS.

  ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
  CONTEXT

  The framework's prior CHSH chain establishes
    `SeparableCHSH.chsh_factorizable_bound`:  |S| ≤ 2  (classical / LHV)
    `TsirelsonBound.tsirelson_bound`:         |S| ≤ 2√2 (quantum)
  and `BellTheorem.bell_violation` + `TsirelsonBound.singlet_saturates_tsirelson`
  show the singlet ATTAINS 2√2.

  This file COMPLETES the hierarchy by formalising the
  Popescu–Rohrlich (PR) box.  The PR box is a hypothetical
  joint-distribution table for two parties whose correlations
  satisfy the no-signalling (NS) marginal constraints but achieve
  the algebraic CHSH maximum |S| = 4 > 2√2.  Its existence shows
  that the Tsirelson bound is a NON-TRIVIAL feature of quantum
  mechanics, not a consequence of no-signalling alone.

  We prove:
    – `prBox_chsh_value`: the PR-box correlation table has S = 4
      (the algebraic maximum).
    – `tsirelson_lt_four`: 2·√2 < 4 (so the PR box's S strictly
      exceeds Tsirelson).
    – `two_lt_tsirelson`: 2 < 2·√2 (the standard Bell separation).
    – `prBox_not_factorizable`: no bounded factorizable
      correlation `f(x)·g(y)` (|f|, |g| ≤ 1) realises the PR-box
      CHSH value of 4 — the contrapositive of
      `chsh_factorizable_bound`.
    – `NoSignallingCorrelation`: a 4-axiom structure capturing
      the joint-probability table of a discrete no-signalling
      bipartite correlation.
    – `NoSignallingCorrelation.CHSH_le_four`: every NS correlation
      has |S| ≤ 4 (algebraic, pointwise).
    – `prBoxNoSignalling`: an explicit NS correlation realising
      the PR-box table; both marginals are uniform 1/2.
    – `prBoxNoSignalling_CHSH`: its CHSH value is exactly 4.
    – `lhv_qm_ns_strict_hierarchy`: the three-tier separation
      `2 < 2√2 < 4`, witnessed by `prBoxNoSignalling`.

  Zero `sorry`.  Zero custom `axiom`.
-/
import UnifiedTheory.LayerB.TsirelsonBound
import UnifiedTheory.LayerB.SeparableCHSH
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

set_option relaxedAutoImplicit false

namespace UnifiedTheory.LayerC.PRBox

open UnifiedTheory.LayerB.SeparableCHSH
open UnifiedTheory.LayerB.TsirelsonBound

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 1: THE PR-BOX CORRELATION TABLE
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- The PR-box correlation function.  For binary inputs `x, y ∈ {0,1}`,
    `E_PR(x, y) := (-1)^(x ∧ y)` with `∧` the Boolean AND.

    Equivalently:  `E_PR(0,0) = E_PR(0,1) = E_PR(1,0) = +1`,
                    `E_PR(1,1) = -1`. -/
def prBoxCorrelation : Bool → Bool → ℝ
  | false, false => 1
  | false, true  => 1
  | true,  false => 1
  | true,  true  => -1

/-- **The PR-box CHSH value is 4** — the algebraic maximum.

      S = E(0,0) + E(0,1) + E(1,0) − E(1,1)
        = 1 + 1 + 1 − (−1)
        = 4. -/
theorem prBox_chsh_value : chshExpr prBoxCorrelation = 4 := by
  unfold chshExpr prBoxCorrelation
  norm_num

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 2: STRICT INEQUALITIES 2 < 2√2 < 4
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- **`√2 < 2`** — basic numerical comparison.

    Proof: `2 = √4`, and `√` is strictly monotone on nonnegatives. -/
lemma sqrt_two_lt_two : Real.sqrt 2 < 2 := by
  have h₄ : Real.sqrt 4 = 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num,
        Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 2)]
  calc Real.sqrt 2 < Real.sqrt 4 :=
        Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
    _ = 2 := h₄

/-- **`1 < √2`** — basic numerical comparison.

    Proof: `1 = √1` and `√` is strictly monotone. -/
lemma one_lt_sqrt_two : 1 < Real.sqrt 2 := by
  calc (1 : ℝ) = Real.sqrt 1 := (Real.sqrt_one).symm
    _ < Real.sqrt 2 := Real.sqrt_lt_sqrt (by norm_num) (by norm_num)

/-- **`2 < 2√2`** — the Bell/Tsirelson separation in absolute terms.
    The classical CHSH bound 2 is strictly below the quantum bound 2√2. -/
theorem two_lt_tsirelson : (2 : ℝ) < 2 * Real.sqrt 2 := by
  have h := one_lt_sqrt_two
  linarith

/-- **`2√2 < 4`** — the Tsirelson/algebraic separation.
    The quantum bound 2√2 is strictly below the algebraic maximum 4
    achieved by the PR box. -/
theorem tsirelson_lt_four : 2 * Real.sqrt 2 < 4 := by
  have h := sqrt_two_lt_two
  linarith

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 3: PR-BOX EXCLUDES ALL FACTORIZABLE BOUNDED CORRELATIONS
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    In the framework's vocabulary, the "no LHV shadow" statement
    becomes:  no factorizable correlation `e(x,y) = f(x)·g(y)` with
    `|f|, |g| ≤ 1` can produce the PR-box CHSH value 4.

    This is the contrapositive of `chsh_factorizable_bound` applied
    to the PR-box CHSH value 4 > 2.  Together with the classical
    derivation that LHV models DO produce factorizable correlations
    (Bell 1964 / `SeparableCHSH.lean`), it rules out every local
    hidden-variable model with bounded measurement outcomes.
-/

/-- **THE PR BOX IS NOT REALISABLE BY ANY BOUNDED FACTORIZABLE
    CORRELATION** — the framework-vocabulary analogue of "no LHV
    model produces the PR box".

    Proof: any bounded factorizable correlation has |S| ≤ 2
    (`chsh_factorizable_bound`); but the PR box has S = 4 > 2. -/
theorem prBox_not_factorizable :
    ¬ ∃ f g : Bool → ℝ,
        (∀ x, |f x| ≤ 1) ∧ (∀ y, |g y| ≤ 1) ∧
        chshExpr (fun x y => f x * g y) = chshExpr prBoxCorrelation := by
  rintro ⟨f, g, hf, hg, heq⟩
  have hbound : |chshExpr (fun x y => f x * g y)| ≤ 2 :=
    chsh_factorizable_bound f g hf hg
  rw [heq, prBox_chsh_value] at hbound
  -- |4| = 4 ≤ 2 is false.
  have : |(4 : ℝ)| = 4 := by norm_num
  rw [this] at hbound
  linarith

/-- **PR-BOX EXCEEDS THE TSIRELSON BOUND IN ABSOLUTE VALUE.**
    The quantum upper bound 2√2 is strictly less than the PR-box
    CHSH value 4 — so the PR box is OUT OF REACH for any
    correlation arising from a quantum singlet measurement. -/
theorem prBox_exceeds_tsirelson :
    2 * Real.sqrt 2 < chshExpr prBoxCorrelation := by
  rw [prBox_chsh_value]
  exact tsirelson_lt_four

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 4: NO-SIGNALLING CORRELATIONS
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    A discrete bipartite no-signalling correlation is a joint
    probability table `P(a, b | x, y)` over outcomes `a, b ∈ {0,1}`
    and settings `x, y ∈ {0,1}` satisfying:
      (1) nonnegativity,
      (2) normalisation per (x, y),
      (3) Alice's marginal is independent of Bob's setting,
      (4) Bob's marginal is independent of Alice's setting.

    These are the strongest classical constraints compatible with
    relativistic causality — they forbid super-luminal signalling
    of `y` from Bob to Alice via the marginal `P(a | x, y)` (and
    symmetrically for `x` from Alice to Bob).

    The PR box satisfies all four constraints but produces |S| = 4.
-/

/-- A discrete bipartite no-signalling correlation on two binary
    inputs and two binary outputs.  The table `P a b x y` is the
    joint probability of outcomes `(a, b)` given settings `(x, y)`. -/
structure NoSignallingCorrelation where
  /-- The joint probability table `P(a, b | x, y)`. -/
  P : Fin 2 → Fin 2 → Fin 2 → Fin 2 → ℝ
  /-- Probabilities are nonnegative. -/
  P_nonneg : ∀ a b x y, 0 ≤ P a b x y
  /-- Each table normalises to 1 over the outcomes. -/
  P_sum_one : ∀ x y, (∑ a, ∑ b, P a b x y) = 1
  /-- Alice's marginal `P(a | x) := ∑_b P(a, b | x, y)` is
      independent of Bob's setting `y` (no signalling Bob → Alice). -/
  no_sig_A : ∀ a x y y', (∑ b, P a b x y) = (∑ b, P a b x y')
  /-- Bob's marginal `P(b | y) := ∑_a P(a, b | x, y)` is
      independent of Alice's setting `x` (no signalling Alice → Bob). -/
  no_sig_B : ∀ b x x' y, (∑ a, P a b x y) = (∑ a, P a b x' y)

namespace NoSignallingCorrelation

variable (c : NoSignallingCorrelation)

/-- The expected correlation `E(x, y) := P(same) − P(different)`
    for the binary-outcome NS table. -/
def correlation (x y : Fin 2) : ℝ :=
  c.P 0 0 x y + c.P 1 1 x y - c.P 0 1 x y - c.P 1 0 x y

/-- The CHSH expression of a no-signalling correlation:
        `S := E(0,0) + E(0,1) + E(1,0) − E(1,1)`. -/
def CHSH : ℝ :=
  c.correlation 0 0 + c.correlation 0 1 + c.correlation 1 0
    - c.correlation 1 1

/-- Every individual probability is at most 1 (since the four sum to 1
    and each is nonneg).  Useful as a pointwise upper bound. -/
lemma P_le_one (a b x y : Fin 2) : c.P a b x y ≤ 1 := by
  have hsum : (∑ a', ∑ b', c.P a' b' x y) = 1 := c.P_sum_one x y
  -- Expand the double sum over Fin 2 × Fin 2 explicitly.
  have hexp :
      (∑ a', ∑ b', c.P a' b' x y)
      = c.P 0 0 x y + c.P 0 1 x y + c.P 1 0 x y + c.P 1 1 x y := by
    simp [Fin.sum_univ_two]; ring
  rw [hexp] at hsum
  -- The other three probabilities are nonneg, so P a b x y ≤ 1.
  have h00 := c.P_nonneg 0 0 x y
  have h01 := c.P_nonneg 0 1 x y
  have h10 := c.P_nonneg 1 0 x y
  have h11 := c.P_nonneg 1 1 x y
  -- The four-cell sum equals 1; case-split on `a, b` to identify which
  -- cell is the target.
  fin_cases a <;> fin_cases b <;> (first | linarith | (simp; linarith))

/-- The correlation lies in `[-1, 1]`: a direct bound from
    `0 ≤ P(·) ≤ 1` and the four probabilities summing to 1 per setting. -/
lemma correlation_le_one (x y : Fin 2) : c.correlation x y ≤ 1 := by
  unfold correlation
  have hsum : (∑ a', ∑ b', c.P a' b' x y) = 1 := c.P_sum_one x y
  have hexp :
      (∑ a', ∑ b', c.P a' b' x y)
      = c.P 0 0 x y + c.P 0 1 x y + c.P 1 0 x y + c.P 1 1 x y := by
    simp [Fin.sum_univ_two]; ring
  rw [hexp] at hsum
  have h01 := c.P_nonneg 0 1 x y
  have h10 := c.P_nonneg 1 0 x y
  linarith

/-- The correlation is `≥ -1` by the same accounting. -/
lemma neg_one_le_correlation (x y : Fin 2) : -1 ≤ c.correlation x y := by
  unfold correlation
  have hsum : (∑ a', ∑ b', c.P a' b' x y) = 1 := c.P_sum_one x y
  have hexp :
      (∑ a', ∑ b', c.P a' b' x y)
      = c.P 0 0 x y + c.P 0 1 x y + c.P 1 0 x y + c.P 1 1 x y := by
    simp [Fin.sum_univ_two]; ring
  rw [hexp] at hsum
  have h00 := c.P_nonneg 0 0 x y
  have h11 := c.P_nonneg 1 1 x y
  linarith

/-- Combined: every NS correlation lies in `[-1, 1]`. -/
lemma abs_correlation_le_one (x y : Fin 2) : |c.correlation x y| ≤ 1 := by
  rw [abs_le]
  exact ⟨c.neg_one_le_correlation x y, c.correlation_le_one x y⟩

/-- **NO-SIGNALLING CHSH BOUND** — `|S| ≤ 4`, the algebraic maximum.

    Proof: each of the four correlations lies in `[-1, 1]`, so their
    signed sum is bounded in absolute value by 4.

    NOTE: this is the trivial pointwise bound; it does NOT use the
    no-signalling marginal constraints.  The PR box (next section)
    SATURATES this bound, so it cannot be improved without further
    structure — saturation by the PR box is what gives the bound
    its physical content as the boundary of the NS polytope. -/
theorem CHSH_le_four : |c.CHSH| ≤ 4 := by
  unfold CHSH
  have h00 := c.abs_correlation_le_one 0 0
  have h01 := c.abs_correlation_le_one 0 1
  have h10 := c.abs_correlation_le_one 1 0
  have h11 := c.abs_correlation_le_one 1 1
  -- Triangle inequality for the four-term sum, then |E_ij| ≤ 1 each.
  have h1 :
      |c.correlation 0 0 + c.correlation 0 1 + c.correlation 1 0
        - c.correlation 1 1|
      ≤ |c.correlation 0 0| + |c.correlation 0 1| + |c.correlation 1 0|
        + |c.correlation 1 1| := by
    have t1 := abs_add_le (c.correlation 0 0 + c.correlation 0 1
                          + c.correlation 1 0) (- c.correlation 1 1)
    have t2 := abs_add_le (c.correlation 0 0 + c.correlation 0 1)
                          (c.correlation 1 0)
    have t3 := abs_add_le (c.correlation 0 0) (c.correlation 0 1)
    have hneg : |-c.correlation 1 1| = |c.correlation 1 1| := abs_neg _
    have hsubeq :
        c.correlation 0 0 + c.correlation 0 1 + c.correlation 1 0
          - c.correlation 1 1
        = (c.correlation 0 0 + c.correlation 0 1 + c.correlation 1 0)
          + (- c.correlation 1 1) := by ring
    rw [hsubeq]
    calc |(c.correlation 0 0 + c.correlation 0 1 + c.correlation 1 0)
            + (- c.correlation 1 1)|
        ≤ |c.correlation 0 0 + c.correlation 0 1 + c.correlation 1 0|
          + |- c.correlation 1 1| := t1
      _ = |c.correlation 0 0 + c.correlation 0 1 + c.correlation 1 0|
          + |c.correlation 1 1| := by rw [hneg]
      _ ≤ (|c.correlation 0 0 + c.correlation 0 1| + |c.correlation 1 0|)
          + |c.correlation 1 1| := by linarith [t2]
      _ ≤ ((|c.correlation 0 0| + |c.correlation 0 1|)
            + |c.correlation 1 0|) + |c.correlation 1 1| := by linarith [t3]
      _ = |c.correlation 0 0| + |c.correlation 0 1| + |c.correlation 1 0|
          + |c.correlation 1 1| := by ring
  linarith

end NoSignallingCorrelation

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 5: THE PR BOX AS A NO-SIGNALLING CORRELATION
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    The explicit table is
        `P(a, b | x, y) = 1/2  if  a ⊕ b = x ∧ y`
                       `= 0    otherwise`.

    The four constraints check out by direct case analysis on
    `(x, y) ∈ Fin 2 × Fin 2`.  The marginals are uniform 1/2 for
    every setting, so both no-signalling axioms hold trivially.
-/

/-- The raw joint-probability table of the PR box.  Indexed by
    `(a, b, x, y) ∈ Fin 2⁴`; value `1/2` on the "winning" outcomes
    `a ⊕ b = x ∧ y`, value `0` otherwise. -/
noncomputable def prBoxP : Fin 2 → Fin 2 → Fin 2 → Fin 2 → ℝ :=
  fun a b x y =>
    if (a.val + b.val) % 2 = (x.val * y.val) % 2 then (1 : ℝ) / 2 else 0

/-- Nonnegativity of the PR-box table: every cell is either `1/2` or `0`. -/
lemma prBoxP_nonneg (a b x y : Fin 2) : 0 ≤ prBoxP a b x y := by
  unfold prBoxP
  split
  · norm_num
  · exact le_refl _

/-- Normalisation: for any `(x, y)`, the four outcomes' probabilities
    sum to 1.  Proved by exhaustive case analysis on `(x, y)`. -/
lemma prBoxP_sum_one (x y : Fin 2) :
    (∑ a, ∑ b, prBoxP a b x y) = 1 := by
  fin_cases x <;> fin_cases y <;>
    simp [Fin.sum_univ_two, prBoxP] <;> norm_num

/-- Alice's marginal `∑_b P(a, b | x, y)` is independent of Bob's
    setting `y`.  In fact, it equals `1/2` for every setting `(a, x, y)`. -/
lemma prBoxP_marginal_A (a x y : Fin 2) :
    (∑ b, prBoxP a b x y) = (1 : ℝ) / 2 := by
  fin_cases a <;> fin_cases x <;> fin_cases y <;>
    simp [Fin.sum_univ_two, prBoxP] <;> norm_num

/-- Bob's marginal `∑_a P(a, b | x, y)` is independent of Alice's
    setting `x`.  Again, equals `1/2` for every `(b, x, y)`. -/
lemma prBoxP_marginal_B (b x y : Fin 2) :
    (∑ a, prBoxP a b x y) = (1 : ℝ) / 2 := by
  fin_cases b <;> fin_cases x <;> fin_cases y <;>
    simp [Fin.sum_univ_two, prBoxP] <;> norm_num

/-- The no-signalling structure assembled from the PR-box table.

    Both marginals are constantly `1/2` (lemmas `prBoxP_marginal_A`,
    `prBoxP_marginal_B`), so the two no-signalling axioms reduce to
    `1/2 = 1/2`. -/
noncomputable def prBoxNoSignalling : NoSignallingCorrelation where
  P := prBoxP
  P_nonneg := prBoxP_nonneg
  P_sum_one := prBoxP_sum_one
  no_sig_A := by
    intro a x y y'
    rw [prBoxP_marginal_A a x y, prBoxP_marginal_A a x y']
  no_sig_B := by
    intro b x x' y
    rw [prBoxP_marginal_B b x y, prBoxP_marginal_B b x' y]

/-- Individual probability values of the PR box (used to compute the
    correlation explicitly). -/
-- Setting (x=0, y=0): x∧y=0, so P=1/2 iff a⊕b=0 i.e. a=b.
lemma prBoxP_00_00 : prBoxP 0 0 0 0 = 1 / 2 := by
  unfold prBoxP; rw [if_pos (by decide)]
lemma prBoxP_11_00 : prBoxP 1 1 0 0 = 1 / 2 := by
  unfold prBoxP; rw [if_pos (by decide)]
lemma prBoxP_01_00 : prBoxP 0 1 0 0 = 0 := by
  unfold prBoxP; rw [if_neg (by decide)]
lemma prBoxP_10_00 : prBoxP 1 0 0 0 = 0 := by
  unfold prBoxP; rw [if_neg (by decide)]
-- Setting (x=0, y=1): x∧y=0, same.
lemma prBoxP_00_01 : prBoxP 0 0 0 1 = 1 / 2 := by
  unfold prBoxP; rw [if_pos (by decide)]
lemma prBoxP_11_01 : prBoxP 1 1 0 1 = 1 / 2 := by
  unfold prBoxP; rw [if_pos (by decide)]
lemma prBoxP_01_01 : prBoxP 0 1 0 1 = 0 := by
  unfold prBoxP; rw [if_neg (by decide)]
lemma prBoxP_10_01 : prBoxP 1 0 0 1 = 0 := by
  unfold prBoxP; rw [if_neg (by decide)]
-- Setting (x=1, y=0): x∧y=0, same.
lemma prBoxP_00_10 : prBoxP 0 0 1 0 = 1 / 2 := by
  unfold prBoxP; rw [if_pos (by decide)]
lemma prBoxP_11_10 : prBoxP 1 1 1 0 = 1 / 2 := by
  unfold prBoxP; rw [if_pos (by decide)]
lemma prBoxP_01_10 : prBoxP 0 1 1 0 = 0 := by
  unfold prBoxP; rw [if_neg (by decide)]
lemma prBoxP_10_10 : prBoxP 1 0 1 0 = 0 := by
  unfold prBoxP; rw [if_neg (by decide)]
-- Setting (x=1, y=1): x∧y=1, so P=1/2 iff a⊕b=1 i.e. a≠b.
lemma prBoxP_00_11 : prBoxP 0 0 1 1 = 0 := by
  unfold prBoxP; rw [if_neg (by decide)]
lemma prBoxP_11_11 : prBoxP 1 1 1 1 = 0 := by
  unfold prBoxP; rw [if_neg (by decide)]
lemma prBoxP_01_11 : prBoxP 0 1 1 1 = 1 / 2 := by
  unfold prBoxP; rw [if_pos (by decide)]
lemma prBoxP_10_11 : prBoxP 1 0 1 1 = 1 / 2 := by
  unfold prBoxP; rw [if_pos (by decide)]

/-- The PR-box correlation `E(x, y) = (−1)^(x ∧ y)` computed from the
    joint probability table. -/
lemma prBoxNoSignalling_correlation_00 :
    prBoxNoSignalling.correlation 0 0 = 1 := by
  change prBoxNoSignalling.P 0 0 0 0 + prBoxNoSignalling.P 1 1 0 0
       - prBoxNoSignalling.P 0 1 0 0 - prBoxNoSignalling.P 1 0 0 0 = 1
  rw [show prBoxNoSignalling.P = prBoxP from rfl]
  rw [prBoxP_00_00, prBoxP_11_00, prBoxP_01_00, prBoxP_10_00]
  norm_num

lemma prBoxNoSignalling_correlation_01 :
    prBoxNoSignalling.correlation 0 1 = 1 := by
  change prBoxNoSignalling.P 0 0 0 1 + prBoxNoSignalling.P 1 1 0 1
       - prBoxNoSignalling.P 0 1 0 1 - prBoxNoSignalling.P 1 0 0 1 = 1
  rw [show prBoxNoSignalling.P = prBoxP from rfl]
  rw [prBoxP_00_01, prBoxP_11_01, prBoxP_01_01, prBoxP_10_01]
  norm_num

lemma prBoxNoSignalling_correlation_10 :
    prBoxNoSignalling.correlation 1 0 = 1 := by
  change prBoxNoSignalling.P 0 0 1 0 + prBoxNoSignalling.P 1 1 1 0
       - prBoxNoSignalling.P 0 1 1 0 - prBoxNoSignalling.P 1 0 1 0 = 1
  rw [show prBoxNoSignalling.P = prBoxP from rfl]
  rw [prBoxP_00_10, prBoxP_11_10, prBoxP_01_10, prBoxP_10_10]
  norm_num

lemma prBoxNoSignalling_correlation_11 :
    prBoxNoSignalling.correlation 1 1 = -1 := by
  change prBoxNoSignalling.P 0 0 1 1 + prBoxNoSignalling.P 1 1 1 1
       - prBoxNoSignalling.P 0 1 1 1 - prBoxNoSignalling.P 1 0 1 1 = -1
  rw [show prBoxNoSignalling.P = prBoxP from rfl]
  rw [prBoxP_00_11, prBoxP_11_11, prBoxP_01_11, prBoxP_10_11]
  norm_num

/-- **PR-BOX SATURATES THE NO-SIGNALLING ALGEBRAIC BOUND**: its CHSH
    value is exactly 4, the maximum allowed by `CHSH_le_four`. -/
theorem prBoxNoSignalling_CHSH : prBoxNoSignalling.CHSH = 4 := by
  change prBoxNoSignalling.correlation 0 0 + prBoxNoSignalling.correlation 0 1
        + prBoxNoSignalling.correlation 1 0
        - prBoxNoSignalling.correlation 1 1 = 4
  rw [prBoxNoSignalling_correlation_00, prBoxNoSignalling_correlation_01,
      prBoxNoSignalling_correlation_10, prBoxNoSignalling_correlation_11]
  norm_num

/-- **Sanity check**: the PR box passes `CHSH_le_four` with equality.
    A consistency statement linking the algebraic bound to its
    explicit witness. -/
theorem prBoxNoSignalling_attains_bound :
    |prBoxNoSignalling.CHSH| = 4 := by
  rw [prBoxNoSignalling_CHSH]; norm_num

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 6: THE LHV / QM / NS STRICT HIERARCHY
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- **THE STRICT THREE-TIER HIERARCHY** `LHV < QM < NS`.

      (1) Classical (LHV) bound: |S| ≤ 2  (`chsh_factorizable_bound`).
      (2) Quantum (Tsirelson) bound: |S| ≤ 2√2  (`tsirelson_bound`).
      (3) No-signalling (algebraic) bound: |S| ≤ 4
          (`NoSignallingCorrelation.CHSH_le_four`).

    Strict separations:
      `2 < 2√2`   — quantum strictly beats classical (Bell).
      `2√2 < 4`   — algebraic maximum strictly beats quantum
                     (Tsirelson is non-trivial).
      `prBoxNoSignalling.CHSH = 4`  — the PR box ATTAINS the
                                       algebraic maximum.

    The PR box is therefore a no-signalling correlation that is
    NOT realisable by any quantum singlet measurement nor by any
    bounded factorizable local-hidden-variable model.  This closes
    the three-tier hierarchy of correlation classes
    `LHV  ⊊  QM  ⊊  NS`. -/
theorem lhv_qm_ns_strict_hierarchy :
    -- Bell separation: classical < quantum
    (2 : ℝ) < 2 * Real.sqrt 2
    -- Tsirelson separation: quantum < algebraic
    ∧ 2 * Real.sqrt 2 < 4
    -- PR-box attains the algebraic maximum
    ∧ prBoxNoSignalling.CHSH = 4 :=
  ⟨two_lt_tsirelson, tsirelson_lt_four, prBoxNoSignalling_CHSH⟩

/-- **MASTER THEOREM** — the four-fold completion of the framework's
    Bell–Tsirelson–PR chain into a single citable statement:

      (1) Classical bound (`chsh_factorizable_bound`):
          factorizable correlations satisfy |S| ≤ 2.
      (2) Quantum bound (`tsirelson_bound`):
          the framework's singlet correlations satisfy |S| ≤ 2√2.
      (3) No-signalling bound (`CHSH_le_four`):
          every no-signalling correlation satisfies |S| ≤ 4.
      (4) PR-box witness (`prBoxNoSignalling_CHSH`):
          the PR box is a concrete NS correlation attaining 4.
      (5) Strict separations (`two_lt_tsirelson`, `tsirelson_lt_four`):
          `2 < 2√2 < 4`.

    The combination of (3) and (4) shows the algebraic bound 4 is
    SATURATED, hence sharp; combined with (1), (2), and (5) it
    establishes that the three correlation classes LHV ⊊ QM ⊊ NS
    are genuinely distinct and ordered. -/
theorem prBox_master_theorem :
    -- (1) Classical bound: factorizable ⇒ |S| ≤ 2.
    (∀ f g : Bool → ℝ, (∀ x, |f x| ≤ 1) → (∀ y, |g y| ≤ 1) →
        |chshExpr (fun x y => f x * g y)| ≤ 2)
    -- (2) Tsirelson bound: singlet correlations bounded by 2√2.
    ∧ (∀ θa θa' θb θb' : ℝ,
          |tsirelsonChshSinglet θa θa' θb θb'| ≤ 2 * Real.sqrt 2)
    -- (3) No-signalling bound: every NS correlation bounded by 4.
    ∧ (∀ c : NoSignallingCorrelation, |c.CHSH| ≤ 4)
    -- (4) PR-box witness: an explicit NS correlation with CHSH = 4.
    ∧ prBoxNoSignalling.CHSH = 4
    -- (5) Strict separations: 2 < 2√2 < 4.
    ∧ ((2 : ℝ) < 2 * Real.sqrt 2 ∧ 2 * Real.sqrt 2 < 4) :=
  ⟨chsh_factorizable_bound,
   tsirelson_bound,
   fun c => c.CHSH_le_four,
   prBoxNoSignalling_CHSH,
   ⟨two_lt_tsirelson, tsirelson_lt_four⟩⟩

end UnifiedTheory.LayerC.PRBox

-- Axiom audit: all main theorems use only standard Lean axioms.
#print axioms UnifiedTheory.LayerC.PRBox.prBox_chsh_value
#print axioms UnifiedTheory.LayerC.PRBox.prBox_not_factorizable
#print axioms UnifiedTheory.LayerC.PRBox.prBox_exceeds_tsirelson
#print axioms UnifiedTheory.LayerC.PRBox.NoSignallingCorrelation.CHSH_le_four
#print axioms UnifiedTheory.LayerC.PRBox.prBoxNoSignalling_CHSH
#print axioms UnifiedTheory.LayerC.PRBox.lhv_qm_ns_strict_hierarchy
#print axioms UnifiedTheory.LayerC.PRBox.prBox_master_theorem
