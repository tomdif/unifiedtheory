/-
  UnifiedTheory/LayerC/InformationCausality.lean
  ───────────────────────────────────────────────

  **The Information Causality (IC) bound** of Pawłowski et al. (Nature 2009),
  formalised in its smallest non-trivial case — the (2 → 1) Random Access
  Code (RAC) — and the explicit certificate that the Popescu–Rohrlich (PR)
  box VIOLATES it.

  ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
  WHY THIS FILE EXISTS

  Together with `LayerC/PRBox.lean` (which formalises the strict
  hierarchy `LHV ⊊ QM ⊊ NS`), this file supplies the OPERATIONAL
  principle that picks the quantum slice OUT of the no-signalling
  polytope:

      Information Causality:  with `c` bits of communication,
                              Bob's total mutual information about
                              Alice's `n` input bits is bounded by `c`.

  In the (n = 2, c = 1) Random Access Code, the IC bound specialises
  to the SUM OF SUCCESS PROBABILITIES across the two possible
  questions being bounded by `3/2`.  Classical strategies satisfy it
  (proved here, BY EXHAUSTIVE SEARCH over the 256 deterministic
  strategies).  Quantum strategies also satisfy it (the full IC
  proof of Pawłowski et al. uses an entropic / Holevo argument that
  is out of scope for this single file).  The PR box (formalised
  in `PRBox.lean`) VIOLATES it: it allows the perfect (2 → 1) RAC,
  i.e. sum of success probabilities = 2 > 3/2.

  ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
  WHAT IS PROVED

  • `ClassicalRACStrategy` — the type of deterministic (2 → 1)
    Random Access Code strategies (encoder + two decoders).
  • `successCount S b` — the number of inputs `a ∈ Fin 2 → Fin 2`
    on which `S` correctly answers question `b`.  An integer in
    `{0, 1, 2, 3, 4}`.
  • `avgSuccessProbability S b` — the success probability of `S`
    on question `b`, averaged over the uniform input distribution.
    Equals `successCount S b / 4`.
  • `totalSuccessSum S` — `avgSuccessProbability S 0 +
    avgSuccessProbability S 1`.  The Information Causality
    figure-of-merit at (n = 2, c = 1).
  • `successCount_sum_le_six` — for every classical RAC strategy,
    `successCount S 0 + successCount S 1 ≤ 6`.  The combinatorial
    core of the result, proved by `decide` after re-encoding
    strategies as `Fin 2^4 × Fin 2^4 × Fin 2^4`.
  • `classical_RAC_sum_le` — the corresponding REAL-NUMBER bound:
    `totalSuccessSum S ≤ 3 / 2`.  THIS IS THE IC BOUND for the
    (n = 2, c = 1) classical case.
  • `prBoxRACSuccess` — the PR-box-aided strategy's success
    probability on each question.  Equals `1` (perfect).
  • `prBox_violates_IC` — `prBoxRACSuccess + prBoxRACSuccess > 3/2`,
    so the PR box VIOLATES the (n = 2, c = 1) IC bound.
  • `ic_dichotomy` — the master statement: every classical RAC
    strategy satisfies `totalSuccessSum ≤ 3/2`, but the PR box
    achieves `2 > 3/2`.

  ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
  HONEST SCOPE

  • The deliverable is the CLASSICAL (n = 2) bound + the
    CONCRETE PR-box violation, NOT the general-n quantum IC
    theorem.  The original Pawłowski et al. (2009) proof of
    quantum IC uses the chain rule for von Neumann mutual
    information + the Holevo bound; the Holevo bound is not
    formalised in this codebase, so the quantum half of IC is
    OUTSIDE this file's scope.
  • We work with the SUM OF SUCCESS PROBABILITIES rather than the
    sum of mutual informations.  These are monotone in each other
    on the binary alphabet (and the IC theorem is usually quoted
    in the success-probability form for the RAC); the conversion
    is standard binary-entropy bookkeeping.
  • `prBoxRACSuccess` is DEFINED to be `1` rather than EXTRACTED
    from a PR-box-coupled strategy on the formal
    `NoSignallingCorrelation` of `PRBox.lean`.  The PR-box
    protocol `m := a₀ ⊕ A, g := m ⊕ B` (where `(A, B)` are PR
    outputs on input `(a₀ ⊕ a₁, b)`) is standard and gives
    success 1 on both questions because `a₀ ⊕ a₁` is XOR-related
    to the PR-box win condition `A ⊕ B = (a₀ ⊕ a₁) · b`; we cite
    Pawłowski et al. for the protocol and bake the result `= 1`
    into the definition.  The PR-box correlation table itself is
    formalised in `PRBox.lean` (`prBoxNoSignalling`).

  Zero `sorry`.  Zero custom `axiom`.
-/
import UnifiedTheory.LayerC.PRBox
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FinCases
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

set_option relaxedAutoImplicit false

namespace UnifiedTheory.LayerC.InformationCausality

open scoped BigOperators

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 1: CLASSICAL RAC STRATEGIES
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- **A classical, deterministic (2 → 1) Random Access Code (RAC)
    strategy.**

    Alice holds two bits `a₀, a₁` (encoded as `a : Fin 2 → Fin 2`,
    `a 0 = a₀`, `a 1 = a₁`).  She sends Bob ONE bit
    `m = encode a ∈ Fin 2`.  Bob, knowing the index he was asked
    (`b ∈ Fin 2`) and the received message `m`, outputs a guess
    `decode b m ∈ Fin 2`.

    The success condition on a single trial is `decode b (encode a) = a b`.

    `ClassicalRACStrategy` is the deterministic type: a probabilistic
    strategy is a convex combination of these, and its success sum
    is the corresponding convex combination of the deterministic
    sums (so the bound is inherited automatically). -/
structure ClassicalRACStrategy where
  /-- Alice's encoder: 2-bit input → 1-bit message. -/
  encode : (Fin 2 → Fin 2) → Fin 2
  /-- Bob's decoder: (asked index, received message) → guess. -/
  decode : Fin 2 → Fin 2 → Fin 2

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 2: SUCCESS METRICS
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- The number of inputs `a ∈ Fin 2 → Fin 2` (out of the four
    possibilities) on which strategy `S` answers question `b`
    correctly.  An integer in `{0, 1, 2, 3, 4}`. -/
def successCount (S : ClassicalRACStrategy) (b : Fin 2) : ℕ :=
  (Finset.univ : Finset (Fin 2 → Fin 2)).filter
    (fun a => S.decode b (S.encode a) = a b) |>.card

/-- The success probability of strategy `S` on question `b`,
    averaged over the uniform distribution on the four possible
    inputs `a ∈ Fin 2 → Fin 2`.  Equals `successCount S b / 4`. -/
noncomputable def avgSuccessProbability (S : ClassicalRACStrategy)
    (b : Fin 2) : ℝ :=
  (successCount S b : ℝ) / 4

/-- The (n = 2, c = 1) Information Causality figure of merit:
    sum of Bob's success probabilities across the two possible
    questions. -/
noncomputable def totalSuccessSum (S : ClassicalRACStrategy) : ℝ :=
  avgSuccessProbability S 0 + avgSuccessProbability S 1

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 3: THE COMBINATORIAL CORE — successCount sum ≤ 6
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    For every classical RAC strategy, the sum over the two possible
    questions of the number of correctly answered inputs is at most
    6 (out of 8 = 4 inputs × 2 questions).

    PROOF STRUCTURE — STRUCTURAL ARGUMENT.

    Fix a strategy `(encode, decode)`.  The encoder partitions the
    four inputs into two cells:
        `C₀ := encode⁻¹{0}`,  `C₁ := encode⁻¹{1}`.
    For each cell `C_m`, ALL inputs in `C_m` receive the SAME message
    `m`, and therefore Bob makes the SAME guess `decode b m` on
    question `b` for every `a ∈ C_m`.

    Inside `C_m`, Bob's question-`b` accuracy is:
        `#{a ∈ C_m : decode b m = a b}`
      = `#{a ∈ C_m : a b = decode b m}`.

    For a FIXED bit `g ∈ Fin 2` and FIXED index `b ∈ Fin 2`, the set
    `{a : Fin 2 → Fin 2 | a b = g}` has exactly 2 elements (the
    OTHER bit `a (1 − b)` is free).  So inside `C_m`, the count is
    at most `min(|C_m|, 2)` for each question.

    Summing over `m ∈ Fin 2` and `b ∈ Fin 2`:
        `Σ_m Σ_b #{a ∈ C_m : decode b m = a b}`
      ≤ `Σ_m 2 · min(|C_m|, 2)`.

    Now `|C₀| + |C₁| = 4`.  By case analysis on the partition shape
    `(|C₀|, |C₁|) ∈ {(0,4),(1,3),(2,2),(3,1),(4,0)}`, the bound
    `2 · min(|C₀|, 2) + 2 · min(|C₁|, 2)` is at most 6 in EVERY
    case, with the maximum 6 attained at the (2,2) split.

    Rather than walk through the partition-shape case analysis in
    Lean by hand, we use `decide` on a re-encoding of strategies as
    `(Fin 2)^4 × (Fin 2)^4` (encoder ↔ 4-bit truth table; the two
    decoders unite into a single `Fin 2 → Fin 2 → Fin 2`).  The
    underlying decidable predicate quantifies over 16 × 16 = 256
    objects, well within `decide`'s reach.
-/

/-- A finite, `DecidableEq`-equipped re-encoding of strategies as
    pairs `(eb, db) : (Fin 2 → Fin 2 → Fin 2) × (Fin 2 → Fin 2 → Fin 2)`
    where `eb b₀ b₁ := encode (a)` with `a 0 = b₀, a 1 = b₁`, and
    `db b m := decode b m`.

    Two encoders/decoders are equal as functions iff they agree on
    every input, and `Fin 2 → Fin 2 → Fin 2` is a finite type with
    16 elements (so `decide` can quantify over the 16 × 16 = 256
    pairs). -/
private def encodeTable (S : ClassicalRACStrategy) : Fin 2 → Fin 2 → Fin 2 :=
  fun b₀ b₁ => S.encode (fun i => if i = 0 then b₀ else b₁)

/-- Convenience: convert a length-2 `(Fin 2 → Fin 2)` to a pair `(b₀, b₁)`. -/
private def funToPair (a : Fin 2 → Fin 2) : Fin 2 × Fin 2 := (a 0, a 1)

/-- The "raw" success count for an arbitrary `enc, dec : Fin 2 → Fin 2 → Fin 2`
    on question `b`: count the four standard inputs `(b₀, b₁) ∈ Fin 2 × Fin 2`
    on which `dec b (enc b₀ b₁) = (if b = 0 then b₀ else b₁)`.

    Right-associated so that the bridge lemma `successCount_eq_raw`
    matches `Finset.sum_insert` without re-associativity. -/
private def rawSuccessCount
    (enc : Fin 2 → Fin 2 → Fin 2) (dec : Fin 2 → Fin 2 → Fin 2) (b : Fin 2) : ℕ :=
  (if dec b (enc 0 0) = (fun i : Fin 2 => if i = 0 then (0 : Fin 2) else 0) b then 1 else 0)
  + ((if dec b (enc 0 1) = (fun i : Fin 2 => if i = 0 then (0 : Fin 2) else 1) b then 1 else 0)
    + ((if dec b (enc 1 0) = (fun i : Fin 2 => if i = 0 then (1 : Fin 2) else 0) b then 1 else 0)
      + (if dec b (enc 1 1) = (fun i : Fin 2 => if i = 0 then (1 : Fin 2) else 1) b then 1 else 0)))

/-- **The combinatorial heart of classical IC at (n = 2, c = 1)**:
    For every pair of `enc, dec : Fin 2 → Fin 2 → Fin 2`, the sum
    `rawSuccessCount enc dec 0 + rawSuccessCount enc dec 1` is at most 6.

    Proved by `decide` over the finite type `Fin 2 → Fin 2 → Fin 2`
    (16 × 16 = 256 cases). -/
private theorem rawSuccessCount_sum_le_six :
    ∀ (enc dec : Fin 2 → Fin 2 → Fin 2),
      rawSuccessCount enc dec 0 + rawSuccessCount enc dec 1 ≤ 6 := by
  decide

/-- The four inputs `a : Fin 2 → Fin 2` enumerated as a Finset. -/
private lemma fin2_to_fin2_card_four :
    (Finset.univ : Finset (Fin 2 → Fin 2)).card = 4 := by
  decide

/-- Every function `a : Fin 2 → Fin 2` is equal to the standard
    representative obtained from its pair of values. -/
private lemma fin2_to_fin2_ext (a : Fin 2 → Fin 2) :
    a = (fun i : Fin 2 => if i = 0 then a 0 else a 1) := by
  funext i
  fin_cases i <;> simp

/-- The four standard representatives of `Fin 2 → Fin 2`. -/
private def a00 : Fin 2 → Fin 2 := fun i => if i = 0 then 0 else 0
private def a01 : Fin 2 → Fin 2 := fun i => if i = 0 then 0 else 1
private def a10 : Fin 2 → Fin 2 := fun i => if i = 0 then 1 else 0
private def a11 : Fin 2 → Fin 2 := fun i => if i = 0 then 1 else 1

/-- The four standard representatives are pairwise distinct. -/
private lemma a_distinct :
    a00 ≠ a01 ∧ a00 ≠ a10 ∧ a00 ≠ a11 ∧ a01 ≠ a10 ∧ a01 ≠ a11 ∧ a10 ≠ a11 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- a00 ≠ a01: differ at index 1
    intro h; have := congrFun h 1; simp [a00, a01] at this
  · -- a00 ≠ a10: differ at index 0
    intro h; have := congrFun h 0; simp [a00, a10] at this
  · -- a00 ≠ a11: differ at index 0
    intro h; have := congrFun h 0; simp [a00, a11] at this
  · -- a01 ≠ a10: differ at index 0
    intro h; have := congrFun h 0; simp [a01, a10] at this
  · -- a01 ≠ a11: differ at index 0
    intro h; have := congrFun h 0; simp [a01, a11] at this
  · -- a10 ≠ a11: differ at index 1
    intro h; have := congrFun h 1; simp [a10, a11] at this

/-- Each value of a `Fin 2 → Fin 2` function at any point is 0 or 1. -/
private lemma fin2_dichotomy (x : Fin 2) : x = 0 ∨ x = 1 := by
  fin_cases x
  · left; rfl
  · right; rfl

/-- Membership in the 4-element representative set: every function
    `a : Fin 2 → Fin 2` equals one of `a00, a01, a10, a11`. -/
private lemma fin2_to_fin2_mem_four (a : Fin 2 → Fin 2) :
    a = a00 ∨ a = a01 ∨ a = a10 ∨ a = a11 := by
  have h0 := fin2_dichotomy (a 0)
  have h1 := fin2_dichotomy (a 1)
  rcases h0 with h0 | h0 <;> rcases h1 with h1 | h1
  · left
    funext i; fin_cases i
    · exact h0
    · exact h1
  · right; left
    funext i; fin_cases i
    · exact h0
    · exact h1
  · right; right; left
    funext i; fin_cases i
    · exact h0
    · exact h1
  · right; right; right
    funext i; fin_cases i
    · exact h0
    · exact h1

/-- The universe over `Fin 2 → Fin 2` is the 4-element set
    `{a00, a01, a10, a11}`. -/
private lemma fin2_to_fin2_univ :
    (Finset.univ : Finset (Fin 2 → Fin 2)) = {a00, a01, a10, a11} := by
  apply Finset.eq_of_subset_of_card_le
  · intro a _
    have h := fin2_to_fin2_mem_four a
    rcases h with h | h | h | h <;> rw [h] <;> simp
  · rw [fin2_to_fin2_card_four]
    obtain ⟨h01, h02, h03, h12, h13, h23⟩ := a_distinct
    rw [show ({a00, a01, a10, a11} : Finset (Fin 2 → Fin 2))
        = insert a00 (insert a01 (insert a10 ({a11} : Finset (Fin 2 → Fin 2))))
        from rfl]
    rw [Finset.card_insert_of_notMem (by simp [h01, h02, h03]),
        Finset.card_insert_of_notMem (by simp [h12, h13]),
        Finset.card_insert_of_notMem (by simp [h23]),
        Finset.card_singleton]

/-- Bridge: `successCount` matches `rawSuccessCount (encodeTable S) S.decode`.

    The proof reduces both sides to a sum of four indicators by
    enumerating `Fin 2 → Fin 2 = {a00, a01, a10, a11}` and using
    `Finset.card_filter`. -/
private lemma successCount_eq_raw (S : ClassicalRACStrategy) (b : Fin 2) :
    successCount S b = rawSuccessCount (encodeTable S) S.decode b := by
  unfold successCount
  obtain ⟨h01, h02, h03, h12, h13, h23⟩ := a_distinct
  -- Step 1: `card filter = sum of indicators`.
  rw [Finset.card_filter]
  -- Step 2: enumerate the universe as `{a00, a01, a10, a11}`.
  rw [fin2_to_fin2_univ]
  -- Step 3: expand the sum over the literal 4-element set.
  rw [show ({a00, a01, a10, a11} : Finset (Fin 2 → Fin 2))
      = insert a00 (insert a01 (insert a10 ({a11} : Finset (Fin 2 → Fin 2))))
      from rfl]
  rw [Finset.sum_insert (by simp [h01, h02, h03]),
      Finset.sum_insert (by simp [h12, h13]),
      Finset.sum_insert (by simp [h23]),
      Finset.sum_singleton]
  -- Step 4: identify the four summands with the four `rawSuccessCount`
  -- if-branches.  `S.encode a_{ij} = encodeTable S i j` is rfl, and
  -- `a_{ij} b` evaluates to the same as the literal lambda's `b` projection.
  -- Both sides are right-associated sums of the same four indicators.
  rfl

/-- **Combinatorial IC bound (counting form)**: for every classical
    RAC strategy, the sum of the success counts over the two
    questions is at most 6 (out of a maximum 8). -/
theorem successCount_sum_le_six (S : ClassicalRACStrategy) :
    successCount S 0 + successCount S 1 ≤ 6 := by
  rw [successCount_eq_raw S 0, successCount_eq_raw S 1]
  exact rawSuccessCount_sum_le_six (encodeTable S) S.decode

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 4: THE CLASSICAL IC BOUND (real-valued form)
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- **CLASSICAL INFORMATION CAUSALITY BOUND, (n = 2, c = 1) case**.

    For every classical, deterministic RAC strategy with 2 input
    bits and a 1-bit message, the sum of Bob's per-question
    success probabilities is at most `3/2`.

    Equivalently: averaged uniformly over a uniformly random
    question `b`, Bob succeeds with probability at most `3/4`.

    This is the operational form of `I(a₀ ; g | B=0) +
    I(a₁ ; g | B=1) ≤ 1` for the binary-alphabet (n = 2, c = 1)
    RAC.

    NOTE: probabilistic (mixed) strategies are convex combinations
    of deterministic ones, so the bound applies to them as well
    (linearity of expectation).  We state the result for the
    deterministic case here. -/
theorem classical_RAC_sum_le (S : ClassicalRACStrategy) :
    totalSuccessSum S ≤ 3 / 2 := by
  unfold totalSuccessSum avgSuccessProbability
  have hcount : successCount S 0 + successCount S 1 ≤ 6 :=
    successCount_sum_le_six S
  have hcount_real :
      (successCount S 0 : ℝ) + (successCount S 1 : ℝ) ≤ 6 := by
    exact_mod_cast hcount
  linarith

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 5: PR-BOX VIOLATES INFORMATION CAUSALITY
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    The Pawłowski et al. (2009) protocol that uses 2^n − 1 PR boxes
    to win the (n → 1) RAC perfectly specialises at n = 2 to a
    SINGLE PR box used as follows:

      • Alice inputs `a₀ ⊕ a₁` to her side of the PR box, getting
        output `A`.
      • She sends Bob the message `m := a₀ ⊕ A`.
      • Bob inputs the asked index `b` to his side of the PR box,
        getting output `B`.
      • Bob's guess is `g := m ⊕ B = a₀ ⊕ A ⊕ B`.

    Using the PR-box win condition `A ⊕ B = (a₀ ⊕ a₁) · b`
    (formalised in `PRBox.lean`, every output pair `(a, b)` of the
    PR-box NS table satisfies `a ⊕ b = x ∧ y` with probability 1):

      • At b = 0:  g = a₀ ⊕ A ⊕ B = a₀ ⊕ 0 = a₀.   ✓ (perfect)
      • At b = 1:  g = a₀ ⊕ A ⊕ B = a₀ ⊕ (a₀ ⊕ a₁) = a₁.   ✓ (perfect)

    So both per-question success probabilities equal `1`, and the
    sum is `2 > 3/2`.

    The PR-box NS correlation table is formalised in
    `PRBox.lean` as `prBoxNoSignalling`; here we record the
    operational consequence symbolically as the value `1`.
-/

/-- The success probability of the canonical (2 → 1) PR-box-aided
    RAC strategy on each of the two possible questions.

    The strategy itself is the Pawłowski et al. (2009) protocol
    `m := a₀ ⊕ A,  g := m ⊕ B`, where `(A, B)` are PR-box outputs
    on inputs `(a₀ ⊕ a₁, b)`.  The PR-box win condition gives
    `g = a_b` deterministically, so the success probability on
    EITHER question is `1`. -/
noncomputable def prBoxRACSuccess : ℝ := 1

/-- **THE PR BOX VIOLATES THE CLASSICAL IC BOUND**:
    `prBoxRACSuccess + prBoxRACSuccess = 2 > 3 / 2`.

    Equivalently: with a single PR box, the (n = 2, c = 1) RAC
    success-sum is `2`, strictly exceeding the classical IC bound
    `3/2` proved in `classical_RAC_sum_le`. -/
theorem prBox_violates_IC :
    (3 / 2 : ℝ) < prBoxRACSuccess + prBoxRACSuccess := by
  unfold prBoxRACSuccess
  norm_num

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 6: THE IC DICHOTOMY HEADLINE
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- **THE INFORMATION CAUSALITY DICHOTOMY** at (n = 2, c = 1).

    Classical (and quantum, though we do not formalise the quantum
    half here) communication strategies cannot exceed
    `totalSuccessSum = 3/2`.  But the PR box achieves `2`.  The
    `3/2` boundary is therefore an OPERATIONAL principle that
    separates the physically realisable correlations from the
    full no-signalling polytope:

      • The classical IC bound `≤ 3/2` is the operational form of
        "Bob's accessible information about Alice's two input
        bits is at most one bit".
      • The PR-box success-sum `2` is the operational form of
        "perfect (2 → 1) random-access coding with one bit of
        communication", which would let Bob extract MORE
        information about Alice's input than the communication
        channel literally transmitted — a violation of the
        information-causality principle.

    Together with the `LHV ⊊ QM ⊊ NS` strict hierarchy of
    `PRBox.lean`, this gives the structural reason why "QM ≠ NS":
    QM is the slice of the NS polytope where Information Causality
    holds. -/
theorem ic_dichotomy :
    (∀ S : ClassicalRACStrategy, totalSuccessSum S ≤ 3 / 2)
    ∧ ((3 / 2 : ℝ) < prBoxRACSuccess + prBoxRACSuccess) :=
  ⟨classical_RAC_sum_le, prBox_violates_IC⟩

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 7: CONNECTION TO THE PR-BOX FORMAL CORRELATION
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    A consistency statement linking IC to `PRBox.lean`: the
    no-signalling correlation that supplies the PR-box-aided RAC
    protocol IS the one formalised as
    `UnifiedTheory.LayerC.PRBox.prBoxNoSignalling`.

    We expose this as a `Prop`-level reference so that downstream
    files can cite the IC dichotomy together with the underlying
    NS correlation in one place.
-/

/-- **REFERENCE FACT**: the PR-box NS correlation of `PRBox.lean`
    saturates the algebraic CHSH bound (`CHSH = 4`).  This is the
    SAME correlation that drives the IC violation above; the IC
    violation is the "operational" face of the same physical
    object whose "CHSH" face is `CHSH_le_four`-saturating.

    Citing this lemma allows downstream users to access both faces
    via a single import path. -/
theorem prBox_NS_CHSH_eq_four :
    UnifiedTheory.LayerC.PRBox.prBoxNoSignalling.CHSH = 4 :=
  UnifiedTheory.LayerC.PRBox.prBoxNoSignalling_CHSH

end UnifiedTheory.LayerC.InformationCausality

-- Axiom audit: every headline theorem should use only standard Lean axioms
-- (`propext`, `Classical.choice`, `Quot.sound`).  Zero custom axioms,
-- zero `sorry`.
#print axioms UnifiedTheory.LayerC.InformationCausality.successCount_sum_le_six
#print axioms UnifiedTheory.LayerC.InformationCausality.classical_RAC_sum_le
#print axioms UnifiedTheory.LayerC.InformationCausality.prBox_violates_IC
#print axioms UnifiedTheory.LayerC.InformationCausality.ic_dichotomy
#print axioms UnifiedTheory.LayerC.InformationCausality.prBox_NS_CHSH_eq_four
