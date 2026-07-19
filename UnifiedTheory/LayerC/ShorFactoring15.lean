/-
  LayerC/ShorFactoring15.lean — Shor's algorithm: the classical reduction
  step formalised for the textbook concrete case N = 15, a = 2.

  ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
  WHAT IS PROVED

  Shor's quantum factoring algorithm (Shor 1994) reduces integer
  factorisation to the problem of finding the multiplicative order
  ("period") `r` of a chosen base `a` modulo `N`:

      r := min { x > 0 : a^x ≡ 1 (mod N) }.

  Given `r`, IF `r` is even AND `a^(r/2) ≢ ±1 (mod N)`, THEN
  `gcd(a^(r/2) ± 1, N)` produces non-trivial factors of `N`.
  This last step is purely number-theoretic — it does not require
  any quantum hardware; the quantum subroutine is the period-finder.

  We formalise the CLASSICAL REDUCTION step concretely for
  `(a, N) = (2, 15)`.

      f(x) := 2^x mod 15
      2^1 = 2,  2^2 = 4,  2^3 = 8,  2^4 = 16 ≡ 1   →   r = 4
      2^(r/2) = 2^2 = 4
      gcd(4 − 1, 15) = gcd(3, 15) = 3
      gcd(4 + 1, 15) = gcd(5, 15) = 5
      3 · 5 = 15.

  HEADLINE THEOREMS

    1.  `period_of_two_mod_15`         : f15 4 = 1
    2.  `period_is_minimal`            : ∀ x, 0 < x → f15 x = 1 → 4 ≤ x
    3.  `period_is_four`               : r = 4 is the multiplicative order
                                         of 2 mod 15 (combination of 1+2)
    4.  `shor_factor_minus`            : gcd(2^(r/2) − 1, 15) = 3
    5.  `shor_factor_plus`             : gcd(2^(r/2) + 1, 15) = 5
    6.  `shor_recovers_15`             : 3 · 5 = 15
    7.  `shor_nontrivial_factor_minus` : 1 < 3 < 15
    8.  `shor_nontrivial_factor_plus`  : 1 < 5 < 15
    9.  `shor_factor_minus_divides_15` : 3 ∣ 15
   10.  `shor_factor_plus_divides_15`  : 5 ∣ 15
   11.  `shor_factor_minus_divides`    : gcd(2^(r/2) − 1, 15) ∣ (2^(r/2) − 1)
   12.  `shor_factor_plus_divides`     : gcd(2^(r/2) + 1, 15) ∣ (2^(r/2) + 1)
   13.  `shor_factor_minus_coprime`    : gcd(2^(r/2) − 1, 2^(r/2) + 1) = 1
   14.  `shor_witness_nontrivial`      : the algorithm produces a factor
                                         that is neither 1 nor 15
   15.  `shor_factoring_15`            : bundled three-way conjunction
   16.  `shor_factoring_15_full`       : full bundle with non-triviality
   17.  `shor_factoring_15_from_quantum_period`
                                       : assuming the (out-of-scope)
                                         quantum period-finding subroutine
                                         `QuantumPeriodFinding_Target`,
                                         the classical reduction for
                                         N = 15 closes unconditionally.

  SCOPE.  This file proves only the classical (post period-finding) part
  of Shor for the concrete instance `N = 15`.  The full quantum
  period-finding subroutine for general `(a, N)` is recorded as a
  named hypothesis `QuantumPeriodFinding_Target : Prop` and is NOT
  discharged here.

  Zero `sorry`.  Zero custom `axiom`.
-/

import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.NormNum

set_option relaxedAutoImplicit false

namespace UnifiedTheory.LayerC.ShorFactoring15

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 1.  THE MODULAR EXPONENTIAL  f(x) = 2^x mod 15
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- Modular exponential `f(x) = 2^x mod 15`.  This is the classical
    function that the quantum subroutine of Shor's algorithm is queried
    on to find its period. -/
def f15 (x : ℕ) : ℕ := (2 ^ x) % 15

/-- Sanity: `f15 0 = 1` (the identity slot at the start of the period). -/
theorem f15_zero : f15 0 = 1 := by decide

/-- `f15 1 = 2`. -/
theorem f15_one : f15 1 = 2 := by decide

/-- `f15 2 = 4`. -/
theorem f15_two : f15 2 = 4 := by decide

/-- `f15 3 = 8`. -/
theorem f15_three : f15 3 = 8 := by decide

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 2.  PERIOD r = 4 OF f15
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- **Period r = 4 is genuine**: the function `f15` returns `1` at
    `x = r = 4`, i.e. `2^4 ≡ 1 (mod 15)`.  This is one of the two
    requirements for `4` to be the multiplicative order of `2` mod `15`. -/
theorem period_of_two_mod_15 : f15 4 = 1 := by decide

/-- **Period r = 4 is minimal**: no positive integer strictly smaller than
    `4` is a period.  Combined with `period_of_two_mod_15`, this certifies
    that `r = 4` is the multiplicative order of `2` modulo `15`. -/
theorem period_is_minimal : ∀ x, 0 < x → f15 x = 1 → 4 ≤ x := by
  intro x hx h
  -- The only positive values strictly below 4 are 1, 2, 3; none satisfies
  -- `f15 x = 1` because `f15 1 = 2`, `f15 2 = 4`, `f15 3 = 8`.
  by_contra hlt
  push_neg at hlt
  interval_cases x <;> simp_all [f15]

/-- **Period is exactly 4**: bundled version combining
    `period_of_two_mod_15` and `period_is_minimal`.  The multiplicative
    order of `2` modulo `15` is `4`. -/
theorem period_is_four :
    f15 4 = 1 ∧ (∀ x, 0 < x → f15 x = 1 → 4 ≤ x) :=
  ⟨period_of_two_mod_15, period_is_minimal⟩

/-- **r = 4 is even**, so the Shor reduction applies. -/
theorem period_is_even : ∃ k, (4 : ℕ) = 2 * k := ⟨2, by decide⟩

/-- `r / 2 = 2`. -/
theorem half_period : (4 : ℕ) / 2 = 2 := by decide

/-- `2^(r/2) = 4` in ℕ. -/
theorem two_pow_half_period : (2 : ℕ) ^ (4 / 2) = 4 := by decide

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 3.  NON-TRIVIALITY OF a^(r/2) MOD N
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    For Shor's classical reduction to succeed, we need
    `a^(r/2) ≢ ±1 (mod N)`.  Here `a^(r/2) = 4`, `N = 15`:
        4 mod 15 = 4 ≠ 1       (so 4 ≢ 1 mod 15)
        4 + 1 = 5 ≠ 0 mod 15   (so 4 ≢ −1 mod 15)
-/

/-- `a^(r/2) mod N = 4` (not 1). -/
theorem a_half_period_mod : (2 ^ (4 / 2)) % 15 = 4 := by decide

/-- `a^(r/2) ≢ 1 (mod 15)`. -/
theorem a_half_period_ne_one : (2 ^ (4 / 2)) % 15 ≠ 1 := by decide

/-- `(a^(r/2) + 1) mod N = 5`, which is non-zero, so `a^(r/2) ≢ −1 (mod 15)`. -/
theorem a_half_period_plus_one_mod : ((2 ^ (4 / 2)) + 1) % 15 = 5 := by decide

/-- `a^(r/2) ≢ −1 (mod 15)`. -/
theorem a_half_period_ne_neg_one : ((2 ^ (4 / 2)) + 1) % 15 ≠ 0 := by decide

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 4.  THE GCD STEP — RECOVERING THE FACTORS 3 AND 5
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- **gcd(a^(r/2) − 1, N) = 3**.  The first non-trivial factor of
    `15` is recovered as `gcd(4 − 1, 15) = gcd(3, 15) = 3`. -/
theorem shor_factor_minus : Nat.gcd (2 ^ (4 / 2) - 1) 15 = 3 := by decide

/-- **gcd(a^(r/2) + 1, N) = 5**.  The second non-trivial factor of
    `15` is recovered as `gcd(4 + 1, 15) = gcd(5, 15) = 5`. -/
theorem shor_factor_plus : Nat.gcd (2 ^ (4 / 2) + 1) 15 = 5 := by decide

/-- **Factorisation recovered**: 3 · 5 = 15. -/
theorem shor_recovers_15 : (3 : ℕ) * 5 = 15 := by decide

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 5.  NON-TRIVIALITY OF THE RECOVERED FACTORS
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- The recovered factor `3` lies strictly between `1` and `15`. -/
theorem shor_nontrivial_factor_minus : 1 < (3 : ℕ) ∧ (3 : ℕ) < 15 :=
  ⟨by decide, by decide⟩

/-- The recovered factor `5` lies strictly between `1` and `15`. -/
theorem shor_nontrivial_factor_plus : 1 < (5 : ℕ) ∧ (5 : ℕ) < 15 :=
  ⟨by decide, by decide⟩

/-- The recovered factor `3` divides `15`. -/
theorem shor_factor_minus_divides_15 : (3 : ℕ) ∣ 15 := by decide

/-- The recovered factor `5` divides `15`. -/
theorem shor_factor_plus_divides_15 : (5 : ℕ) ∣ 15 := by decide

/-- `gcd(a^(r/2) − 1, N)` divides `a^(r/2) − 1` (general gcd property,
    specialised here). -/
theorem shor_factor_minus_divides :
    Nat.gcd (2 ^ (4 / 2) - 1) 15 ∣ (2 ^ (4 / 2) - 1) := by
  decide

/-- `gcd(a^(r/2) + 1, N)` divides `a^(r/2) + 1`. -/
theorem shor_factor_plus_divides :
    Nat.gcd (2 ^ (4 / 2) + 1) 15 ∣ (2 ^ (4 / 2) + 1) := by
  decide

/-- `gcd(a^(r/2) − 1, N)` divides `N`. -/
theorem shor_factor_minus_divides_N :
    Nat.gcd (2 ^ (4 / 2) - 1) 15 ∣ 15 := by
  decide

/-- `gcd(a^(r/2) + 1, N)` divides `N`. -/
theorem shor_factor_plus_divides_N :
    Nat.gcd (2 ^ (4 / 2) + 1) 15 ∣ 15 := by
  decide

/-- The two recovered factors `3` and `5` are coprime to each other —
    structurally, because `gcd(a^(r/2) − 1, a^(r/2) + 1)` divides
    `(a^(r/2) + 1) − (a^(r/2) − 1) = 2`, and here both sides are odd. -/
theorem shor_factor_minus_coprime :
    Nat.gcd (2 ^ (4 / 2) - 1) (2 ^ (4 / 2) + 1) = 1 := by decide

/-- The product of the two recovered gcds equals `N = 15`. -/
theorem shor_factor_product :
    Nat.gcd (2 ^ (4 / 2) - 1) 15 * Nat.gcd (2 ^ (4 / 2) + 1) 15 = 15 := by
  decide

/-- A non-trivial factor of `15` was produced: it is neither `1` nor `15`. -/
theorem shor_witness_nontrivial :
    Nat.gcd (2 ^ (4 / 2) - 1) 15 ≠ 1 ∧
    Nat.gcd (2 ^ (4 / 2) - 1) 15 ≠ 15 := by
  refine ⟨?_, ?_⟩ <;> decide

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 6.  BUNDLED HEADLINE THEOREMS
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- **HEADLINE (compact bundle)**: Shor's classical reduction for `N = 15`.
    Given the period `r = 4` of `f(x) = 2^x mod 15`, the two
    `gcd(2^(r/2) ± 1, 15)` computations yield the factors `3` and `5`,
    and their product is `15`. -/
theorem shor_factoring_15 :
    Nat.gcd (2 ^ (4 / 2) - 1) 15 = 3 ∧
    Nat.gcd (2 ^ (4 / 2) + 1) 15 = 5 ∧
    (3 : ℕ) * 5 = 15 :=
  ⟨by decide, by decide, by decide⟩

/-- **HEADLINE (full bundle)**: same as `shor_factoring_15`, but also
    certifying non-triviality of each recovered factor and divisibility
    of `15`. -/
theorem shor_factoring_15_full :
    -- (i) gcd(2^(r/2) − 1, 15) = 3
    Nat.gcd (2 ^ (4 / 2) - 1) 15 = 3 ∧
    -- (ii) gcd(2^(r/2) + 1, 15) = 5
    Nat.gcd (2 ^ (4 / 2) + 1) 15 = 5 ∧
    -- (iii) 3 · 5 = 15
    (3 : ℕ) * 5 = 15 ∧
    -- (iv) 3 is a non-trivial factor of 15
    (1 < (3 : ℕ) ∧ (3 : ℕ) < 15 ∧ (3 : ℕ) ∣ 15) ∧
    -- (v) 5 is a non-trivial factor of 15
    (1 < (5 : ℕ) ∧ (5 : ℕ) < 15 ∧ (5 : ℕ) ∣ 15) ∧
    -- (vi) period 4 verified
    f15 4 = 1 ∧
    -- (vii) period 4 minimal
    (∀ x, 0 < x → f15 x = 1 → 4 ≤ x) :=
  ⟨ shor_factor_minus
  , shor_factor_plus
  , shor_recovers_15
  , ⟨shor_nontrivial_factor_minus.1, shor_nontrivial_factor_minus.2,
     shor_factor_minus_divides_15⟩
  , ⟨shor_nontrivial_factor_plus.1, shor_nontrivial_factor_plus.2,
     shor_factor_plus_divides_15⟩
  , period_of_two_mod_15
  , period_is_minimal ⟩

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 7.  THE QUANTUM SUBROUTINE AS A NAMED HYPOTHESIS
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    Shor's quantum advantage lies in efficiently finding the period
    `r` (the multiplicative order of `a` modulo `N`).  Classical
    period-finding is believed to require superpolynomial time; the
    quantum Fourier transform reduces it to polynomial time on a
    quantum computer.

    We do NOT discharge that quantum subroutine here.  We state it as
    a Prop hypothesis and show that, granted it, the classical
    reduction for `N = 15` closes unconditionally.
-/

/-- **Named target**: the quantum period-finding subroutine.  Promises
    that for any `1 < a < N` with `gcd(a, N) = 1` there exists a
    positive `r` with `a^r ≡ 1 (mod N)`.

    Notice: this is the *existence* of a period (a Mathlib fact when
    `N > 0` and `a` is coprime to `N`, via the multiplicative order
    of `a` in `(ZMod N)ˣ`).  The substantive content of "quantum
    period-finding" — efficient extraction in polylog time — is
    a *computational complexity* claim that lives outside the
    Prop universe and is documented only in the surrounding text. -/
def QuantumPeriodFinding_Target : Prop :=
  ∀ (a N : ℕ), 1 < a → a < N → Nat.Coprime a N →
    ∃ r, 0 < r ∧ a ^ r % N = 1

/-- For `(a, N) = (2, 15)`, the period-finding instance is concretely
    discharged by `r = 4` — no quantum subroutine needed in this
    finite-data case. -/
theorem period_witness_2_15 : ∃ r, 0 < r ∧ (2 : ℕ) ^ r % 15 = 1 :=
  ⟨4, by decide, by decide⟩

/-- `2` and `15` are coprime — necessary precondition for invoking
    `QuantumPeriodFinding_Target` on `(a, N) = (2, 15)`. -/
theorem two_coprime_15 : Nat.Coprime 2 15 := by decide

/-- **CLASSICAL-TO-QUANTUM HOOK**.  IF the quantum period-finding
    subroutine succeeds (named hypothesis `QuantumPeriodFinding_Target`),
    THEN Shor's algorithm factorises `15`.

    For `N = 15` the classical reduction does not actually consume the
    quantum hypothesis — the period `r = 4` is found by inspection in
    the finite range `x ∈ {1, 2, 3, 4}`.  So the conclusion of this
    theorem is `shor_factoring_15`, which holds unconditionally; the
    hypothesis `h` is documented but not exercised.  At larger `N`
    (e.g. `N = 21, 35, …`) `h` is genuinely needed to certify
    existence of `r` in polylog time. -/
theorem shor_factoring_15_from_quantum_period
    (_h : QuantumPeriodFinding_Target) :
    Nat.gcd (2 ^ (4 / 2) - 1) 15 = 3 ∧
    Nat.gcd (2 ^ (4 / 2) + 1) 15 = 5 ∧
    (3 : ℕ) * 5 = 15 :=
  shor_factoring_15

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 8.  AUXILIARY ARITHMETIC AUDIT
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    Audit certificates for the textbook claims surrounding the
    `(2, 15)` instance.  All `by decide`.
-/

/-- `2^4 = 16`. -/
theorem two_pow_four : (2 : ℕ) ^ 4 = 16 := by decide

/-- `16 mod 15 = 1`. -/
theorem sixteen_mod_15 : (16 : ℕ) % 15 = 1 := by decide

/-- `4 − 1 = 3`. -/
theorem four_minus_one : (4 : ℕ) - 1 = 3 := by decide

/-- `4 + 1 = 5`. -/
theorem four_plus_one : (4 : ℕ) + 1 = 5 := by decide

/-- `gcd(3, 15) = 3`. -/
theorem gcd_three_fifteen : Nat.gcd 3 15 = 3 := by decide

/-- `gcd(5, 15) = 5`. -/
theorem gcd_five_fifteen : Nat.gcd 5 15 = 5 := by decide

/-- Each step of the textbook derivation, end-to-end. -/
theorem shor_chain_2_15 :
    f15 4 = 1 ∧
    (2 : ℕ) ^ (4 / 2) = 4 ∧
    ((2 : ℕ) ^ (4 / 2)) - 1 = 3 ∧
    ((2 : ℕ) ^ (4 / 2)) + 1 = 5 ∧
    Nat.gcd 3 15 = 3 ∧
    Nat.gcd 5 15 = 5 ∧
    (3 : ℕ) * 5 = 15 :=
  ⟨by decide, by decide, by decide, by decide,
   by decide, by decide, by decide⟩

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 9.  PROBABILITY-OF-SUCCESS RECORD (TEXTBOOK CLAIM)
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    Textbook Shor: for random `a` coprime to a *generic* odd composite
    `N` not a prime power, the probability that the recovered period
    `r` is both even AND that `a^(r/2) ≢ −1 (mod N)` is at least
    `1 − 2^(−k+1)` where `k` is the number of distinct odd prime
    factors of `N`.

    For our concrete case `N = 15 = 3 · 5` we have `k = 2`, giving
    success probability at least `1 − 2^(−1) = 1/2`.  The chosen
    base `a = 2` lands in the favourable half: `r = 4` is even and
    `2^2 = 4 ≢ ±1 (mod 15)`.  We record both facts. -/

/-- The probability-of-success lower bound `1 − 2^(−(k−1))` for
    `k = 2` evaluates to `1/2`.  Stated rationally to avoid ℝ. -/
theorem shor_success_bound_k_two :
    (1 : ℚ) - (1 / 2 : ℚ) = (1 / 2 : ℚ) := by norm_num

/-- The chosen base `a = 2` is in the favourable half for `N = 15`:
    `r = 4` is even, `a^(r/2) ≢ ±1 (mod N)`, and the gcds are
    non-trivial. -/
theorem shor_base_two_succeeds :
    -- r even
    (∃ k, (4 : ℕ) = 2 * k) ∧
    -- a^(r/2) ≢ 1 (mod N)
    (2 ^ (4 / 2)) % 15 ≠ 1 ∧
    -- a^(r/2) ≢ −1 (mod N)
    ((2 ^ (4 / 2)) + 1) % 15 ≠ 0 ∧
    -- gcd(a^(r/2) − 1, N) is a non-trivial factor
    Nat.gcd (2 ^ (4 / 2) - 1) 15 ≠ 1 ∧
    Nat.gcd (2 ^ (4 / 2) - 1) 15 ≠ 15 ∧
    -- gcd(a^(r/2) + 1, N) is a non-trivial factor
    Nat.gcd (2 ^ (4 / 2) + 1) 15 ≠ 1 ∧
    Nat.gcd (2 ^ (4 / 2) + 1) 15 ≠ 15 :=
  ⟨ period_is_even
  , a_half_period_ne_one
  , a_half_period_ne_neg_one
  , by decide, by decide, by decide, by decide ⟩

end UnifiedTheory.LayerC.ShorFactoring15

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    AXIOM AUDIT.  All theorems are closed with `decide` or
    `norm_num`/`interval_cases`/`push_neg`; the only axioms invoked
    are the standard Mathlib set (`propext`, `Classical.choice`,
    `Quot.sound`).  Zero custom `axiom` declarations.
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

#print axioms UnifiedTheory.LayerC.ShorFactoring15.period_of_two_mod_15
#print axioms UnifiedTheory.LayerC.ShorFactoring15.period_is_minimal
#print axioms UnifiedTheory.LayerC.ShorFactoring15.shor_factor_minus
#print axioms UnifiedTheory.LayerC.ShorFactoring15.shor_factor_plus
#print axioms UnifiedTheory.LayerC.ShorFactoring15.shor_recovers_15
#print axioms UnifiedTheory.LayerC.ShorFactoring15.shor_factoring_15
#print axioms UnifiedTheory.LayerC.ShorFactoring15.shor_factoring_15_full
#print axioms UnifiedTheory.LayerC.ShorFactoring15.shor_factoring_15_from_quantum_period
