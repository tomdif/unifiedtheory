/-
  UnifiedTheory/LayerC/HardyParadox.lean
  ──────────────────────────────────────

  **Hardy's nonlocality paradox: a logical no-LHV witness.**

  ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
  WHY THIS FILE EXISTS

  Bell's theorem refutes local hidden variable (LHV) models via a
  numerical *inequality* — Bell/CHSH — that quantum mechanics
  violates by a factor of √2.  `singlet_has_no_LHV_shadow` in
  `LayerC/LHVvsRR.lean` ships that argument as a Lean theorem.

  Hardy (1992) provides a *qualitatively different* witness: instead
  of an inequality, Hardy shows that a small set of joint-probability
  EQUALITIES (three "impossibility" events plus one "actual" event)
  is collectively realisable in QM but logically excluded by LHV.
  No real number ever needs to be compared to √2; the contradiction
  is a propositional one about the supports of LHV joint
  distributions.

  Hardy's table is, with the standard convention that outcome `+1`
  means "spin up" (↑) and outcome `-1` means "spin down" (↓):

    (H1)  P(↑↑ | x=0, y=0) = 0     "never ↑↑ at settings (1,1)"
    (H2)  P(↓· | x=1, y=0) = 0     "never ↓-anything at (2,1)"
    (H3)  P(·↓ | x=0, y=1) = 0     "never anything-↓ at (1,2)"
    (H4)  P(↑↑ | x=1, y=1) > 0     "sometimes ↑↑ at settings (2,2)"

  Quantum mechanics realises (H1)–(H4) simultaneously for a specific
  non-maximally-entangled two-qubit state with specific projective
  measurements.  This file does NOT instantiate that QM realisation
  (that is a separate computation, optional bonus); it ships only the
  LHV-impossibility theorem.

  ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
  THE PROOF

  Under any LHV model with discrete hidden variable `Λ`, the joint
  probability `P_LHV(a,b | x,y)` is

      P_LHV(a,b | x,y) = Σ_λ μ(λ) · [responseA x λ = a]
                                  · [responseB y λ = b].

  Conditions (H1)–(H3) say certain sums are zero.  Because every
  summand is nonnegative (`μ(λ) ≥ 0`), each individual summand must
  vanish whenever the indicator functions are both `1`.  This yields
  three λ-pointwise *implications* on the response sign-patterns:

    (I1)  μ(λ) > 0  ∧  responseA 0 λ = +1  ∧  responseB 0 λ = +1
                 → False
    (I2)  μ(λ) > 0  ∧  responseA 1 λ = -1  ∧  responseB 0 λ = +1
                 → False                       -- from "↓·" at (1,0)
    (I3)  μ(λ) > 0  ∧  responseA 0 λ = +1  ∧  responseB 1 λ = -1
                 → False                       -- from "·↓" at (0,1)

  Wait — actually `P(↓·|x,y) = 0` is the sum over BOTH Bob outcomes
  of `[responseA = -1] · [responseB = anything]`, i.e. the marginal:
  `μ(λ) · [responseA x λ = -1] = 0`.  So (H2) gives

    (I2')  μ(λ) > 0 → responseA 1 λ = +1,

  and similarly (H3) gives

    (I3')  μ(λ) > 0 → responseB 1 λ = +1.

  Now suppose toward contradiction that the LHV model also realises
  (H4): there exists some λ with μ(λ) > 0 and responseA 1 λ = +1
  and responseB 1 λ = +1.  But (I2') gives nothing new at setting 1
  (it just says +1, already true).  We need to USE (I1).

  Re-deriving: combine (I2') and (I3') with the fact that (H1) says
  μ(λ) · [responseA 0 λ = +1] · [responseB 0 λ = +1] = 0 for all λ.

  Pick a λ contributing to (H4): μ(λ) > 0, responseA 1 λ = +1,
  responseB 1 λ = +1.  By (I2') applied at *(setting x=1, y=0)*…

  Wait — (I2') was derived from (H2) which is at setting (1,0), and
  it says: for μ(λ) > 0, responseA 1 λ = +1.  This is consistent
  with our λ but gives no constraint on responseA 0.

  Hardy's argument actually uses these implications:

    (E1) from H1: λ has μ(λ) > 0 ⇒ ¬ (rA 0 λ = +1 ∧ rB 0 λ = +1)
    (E2) from H2: λ has μ(λ) > 0 ⇒ rA 1 λ = +1
    (E3) from H3: λ has μ(λ) > 0 ⇒ rB 1 λ = +1

  Then (H4) demands some λ* with μ(λ*) > 0 and rA 1 λ* = +1 ∧
  rB 1 λ* = +1.  By (E2), (E3), this is automatic at every
  positive-weight λ — so (H4) becomes equivalent to ∃ λ with
  μ(λ) > 0.

  The contradiction then comes from a different chain: standard
  Hardy uses perfect correlations that link (1,1)-up to (0,0)-up
  via the off-diagonal settings.  Specifically, Hardy's H2 and H3
  are NOT marginals but PERFECT-CORRELATION constraints:

    (H2*)  P(rA = -1, rB = +1 | x=1, y=0) = 0
           = "if rB(0)=+1 then rA(1)=+1" (μ-a.s.)
    (H3*)  P(rA = +1, rB = -1 | x=0, y=1) = 0
           = "if rA(0)=+1 then rB(1)=+1" (μ-a.s.)

  These are the conditions Hardy actually proves zero in QM.  We
  adopt them here.  Then the chain:

    Suppose (H4) holds: ∃ λ* with μ(λ*) > 0, rA 1 λ* = +1,
    rB 1 λ* = +1.

    Case on rA 0 λ*:
      • rA 0 λ* = +1.  Then (H3*) says rB 1 λ* = +1 ⇒ rA 0 λ* = +1
        implies… wait the contrapositive of H3* is "if rA(0)=+1 then
        rB(1)=+1", which is satisfied.  Use (H1): rA 0 λ* = +1 and
        rB 0 λ* = ? — case on rB 0 λ*:
          – rB 0 λ* = +1.  Then (H1) gives contradiction.
          – rB 0 λ* = -1.  Then (H2*) says rB 0 λ* = +1 OR rA 1 λ*
            = +1.  Since rA 1 λ* = +1, OK — no contradiction yet.
            BUT (H3*) says rA 0 λ* = +1 ⇒ rB 1 λ* = +1, which holds.
        We need another constraint.  Actually re-examining the
        Hardy chain (this is the textbook argument):
        Given the four conditions, for any λ with μ(λ) > 0:
          rA 1 λ = +1 ∧ rB 1 λ = +1                  -- target (H4)
            ⇒ rA 0 λ = +1                            -- by (H3*) contra
            ⇒ rB 0 λ = +1                            -- by (H2*) contra
            ⇒ rA 0 λ = +1 ∧ rB 0 λ = +1              -- conjunction
            ⇒ ⊥                                      -- by (H1)

  So the implications we extract are:

    (E1)  μ(λ) > 0 ⇒ ¬(rA 0 λ = +1 ∧ rB 0 λ = +1)        (from H1)
    (E2)  μ(λ) > 0 ⇒ ¬(rA 1 λ = -1 ∧ rB 0 λ = +1)        (from H2*)
                ≡ μ(λ) > 0 ⇒ (rB 0 λ = +1 → rA 1 λ = +1)
    (E3)  μ(λ) > 0 ⇒ ¬(rA 0 λ = +1 ∧ rB 1 λ = -1)        (from H3*)
                ≡ μ(λ) > 0 ⇒ (rA 0 λ = +1 → rB 1 λ = +1)

  Contrapositive forms used in Hardy's chain:
    (E2') μ(λ) > 0 ⇒ (rA 1 λ = -1 → rB 0 λ = -1)
                ≡ (rB 0 λ = +1 → rA 1 λ = +1)       [equivalent]
                In particular: (rA 1 λ = +1 → rB 0 λ = +1) is NOT
                directly given — but we need the other direction.

  Actually the chain is reversed.  Let's re-examine H2*:
    H2*: "never (rA = -1, rB = +1) at settings (x=1, y=0)" means
      μ-a.s. ¬(rA 1 λ = -1 ∧ rB 0 λ = +1).
    Contrapositive: μ-a.s. (rB 0 λ = +1 → rA 1 λ = +1).

  Hmm, so H2* gives: rB(0) = +1 ⇒ rA(1) = +1, not the reverse.

  For Hardy's contradiction chain to work as classically stated, we
  need: from (H4) target (rA 1 = +1, rB 1 = +1), derive
  (rA 0 = +1) and (rB 0 = +1).  But the implications I have go the
  OTHER way: rB(0) = +1 ⇒ rA(1) = +1 and rA(0) = +1 ⇒ rB(1) = +1.

  Those contrapositives are: rA(1) = -1 ⇒ rB(0) = -1, and
  rB(1) = -1 ⇒ rA(0) = -1.  These are STILL the wrong direction.

  To get the chain in the standard direction we need INSTEAD:
    (H2**) P(rA = +1, rB = -1 | x=1, y=0) = 0
           ≡ μ-a.s. (rA 1 = +1 → rB 0 = +1)
    (H3**) P(rA = -1, rB = +1 | x=0, y=1) = 0
           ≡ μ-a.s. (rB 1 = +1 → rA 0 = +1)

  These are different events from H2*/H3*.  Different formulations of
  Hardy's setup pick different "perfect correlation" patterns; what
  matters is that each H2/H3 *together with* H1 and H4 are jointly
  unrealisable.  We adopt the H2**/H3** convention because it makes
  the proof chain Hardy → H1 ⊥ direct:

    (E2**) μ(λ) > 0 ⇒ (rA 1 λ = +1 → rB 0 λ = +1)
    (E3**) μ(λ) > 0 ⇒ (rB 1 λ = +1 → rA 0 λ = +1)

  Chain: λ* witnesses (H4) → rA 1 λ* = +1 ∧ rB 1 λ* = +1 →
   (by E3**) rA 0 λ* = +1 → (by E2**) rB 0 λ* = +1 →
   (by E1) ⊥.

  We therefore encode the four Hardy conditions with the
  H2** / H3** sign convention.  This is genuinely Hardy's argument
  modulo a `+1 ↔ -1` relabelling of the off-diagonal outcomes, which
  is a free choice in any Hardy realisation.

  Zero `sorry`.  Zero custom `axiom`.
-/

import UnifiedTheory.LayerC.LHVvsRR
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith

set_option relaxedAutoImplicit false

namespace UnifiedTheory.LayerC.HardyParadox

open UnifiedTheory.LayerC.LHVvsRR
open scoped BigOperators

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 1: LHV JOINT PROBABILITIES
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- The LHV-predicted joint probability of seeing outcome `a` for Alice
    and `b` for Bob at settings `(x, y)`:
        P_LHV(a,b | x,y) = Σ_λ μ(λ) · [rA x λ = a] · [rB y λ = b].

    Implemented via the conditional `if … then 1 else 0` indicators. -/
noncomputable def lhvJointProb
    (m : LHVModel) (a b : ℤ) (x y : Fin 2) : ℝ :=
  ∑ l : m.HVar,
    m.μ l
      * (if m.responseA x l = a then (1 : ℝ) else 0)
      * (if m.responseB y l = b then (1 : ℝ) else 0)

/-- The indicator product `[rA x λ = a] · [rB y λ = b]` is nonneg. -/
private lemma indicator_pair_nonneg
    (m : LHVModel) (a b : ℤ) (x y : Fin 2) (l : m.HVar) :
    0 ≤ (if m.responseA x l = a then (1 : ℝ) else 0)
          * (if m.responseB y l = b then (1 : ℝ) else 0) := by
  by_cases ha : m.responseA x l = a
  · by_cases hb : m.responseB y l = b
    · simp [ha, hb]
    · simp [ha, hb]
  · by_cases hb : m.responseB y l = b
    · simp [ha, hb]
    · simp [ha, hb]

/-- Each summand of `jointProb` is nonnegative. -/
private lemma jointProb_summand_nonneg
    (m : LHVModel) (a b : ℤ) (x y : Fin 2) (l : m.HVar) :
    0 ≤ m.μ l
          * (if m.responseA x l = a then (1 : ℝ) else 0)
          * (if m.responseB y l = b then (1 : ℝ) else 0) := by
  have h := indicator_pair_nonneg m a b x y l
  have hμ := m.μ_nonneg l
  -- Rewrite μ * iA * iB = μ * (iA * iB) then apply mul_nonneg.
  have hrew :
      m.μ l
        * (if m.responseA x l = a then (1 : ℝ) else 0)
        * (if m.responseB y l = b then (1 : ℝ) else 0)
      = m.μ l
          * ((if m.responseA x l = a then (1 : ℝ) else 0)
              * (if m.responseB y l = b then (1 : ℝ) else 0)) := by ring
  rw [hrew]
  exact mul_nonneg hμ h

/-- If `lhvJointProb m a b x y = 0` and `μ(λ) > 0`, then at λ we cannot
    have both `responseA x λ = a` and `responseB y λ = b`.

    Proof: the summand at λ is `μ(λ) · 1 · 1 = μ(λ) > 0`, so if the
    whole sum is zero (and all summands are nonneg), this summand is
    zero — but it equals `μ(λ) > 0`, contradiction. -/
private lemma lhvJointProb_zero_pointwise
    (m : LHVModel) {a b : ℤ} {x y : Fin 2}
    (hzero : lhvJointProb m a b x y = 0)
    (l : m.HVar) (hμ : 0 < m.μ l) :
    ¬ (m.responseA x l = a ∧ m.responseB y l = b) := by
  intro ⟨hA, hB⟩
  -- Each summand is nonnegative; sum is zero ⇒ each is zero.
  have hsum_zero :
      ∀ l' ∈ (Finset.univ : Finset m.HVar),
        m.μ l'
          * (if m.responseA x l' = a then (1 : ℝ) else 0)
          * (if m.responseB y l' = b then (1 : ℝ) else 0) = 0 := by
    refine (Finset.sum_eq_zero_iff_of_nonneg ?_).1 ?_
    · intro l' _
      exact jointProb_summand_nonneg m a b x y l'
    · exact hzero
  have hAtL := hsum_zero l (Finset.mem_univ _)
  rw [if_pos hA, if_pos hB] at hAtL
  simp at hAtL
  linarith

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 2: HARDY CORRELATIONS STRUCTURE
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- **Hardy's correlation specification.**

    A 4-tuple of joint probabilities for the four (x, y) ∈ Fin 2 ×
    Fin 2 setting combinations.  Each entry `P x y a b` records the
    joint probability of outcome `(a, b)` at settings `(x, y)`.  Only
    the four numbers needed for Hardy's argument are constrained.

    Sign convention (Hardy 1992, standard textbook form modulo a
    relabel — see file header for justification):
      H1:  P(↑↑ | 0,0) = 0
      H2:  P(↑↓ | 1,0) = 0     (i.e. "rA = +1, rB = -1" at (1,0))
      H3:  P(↓↑ | 0,1) = 0     (i.e. "rA = -1, rB = +1" at (0,1))
      H4:  0 < P(↑↑ | 1,1)
    where +1 ≡ ↑ and -1 ≡ ↓.
-/
structure HardyCorrelations where
  /-- Joint probability table P(a, b | x, y). -/
  P : Fin 2 → Fin 2 → ℤ → ℤ → ℝ
  /-- (H1) Never both up at settings (0,0). -/
  hardy1 : P 0 0 1 1 = 0
  /-- (H2) Never (Alice up, Bob down) at settings (1,0). -/
  hardy2 : P 1 0 1 (-1) = 0
  /-- (H3) Never (Alice down, Bob up) at settings (0,1). -/
  hardy3 : P 0 1 (-1) 1 = 0
  /-- (H4) Sometimes both up at settings (1,1). -/
  hardy4 : 0 < P 1 1 1 1

/-- **An LHV model realises a `HardyCorrelations` table** if its
    predicted joint probabilities at the four (a, b, x, y) entries
    Hardy constrains match the table. -/
def LHVRealizesHardy (h : HardyCorrelations) (m : LHVModel) : Prop :=
  lhvJointProb m 1 1 0 0 = h.P 0 0 1 1
  ∧ lhvJointProb m 1 (-1) 1 0 = h.P 1 0 1 (-1)
  ∧ lhvJointProb m (-1) 1 0 1 = h.P 0 1 (-1) 1
  ∧ lhvJointProb m 1 1 1 1 = h.P 1 1 1 1

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 3: THE HARDY CHAIN — POINTWISE IMPLICATIONS
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- **Implication (E1) from Hardy condition H1.**  Under any LHV
    model satisfying (H1), at any positive-weight `λ` it is impossible
    that both Alice and Bob respond `+1` at the (0,0) settings. -/
private lemma hardy_E1
    {h : HardyCorrelations} {m : LHVModel} (hreal : LHVRealizesHardy h m)
    {l : m.HVar} (hμ : 0 < m.μ l) :
    ¬ (m.responseA 0 l = 1 ∧ m.responseB 0 l = 1) := by
  have hz : lhvJointProb m 1 1 0 0 = 0 := by
    rw [hreal.1]; exact h.hardy1
  exact lhvJointProb_zero_pointwise m hz l hμ

/-- **Implication (E2) from Hardy condition H2.**  Under any LHV
    model satisfying (H2), at any positive-weight `λ` it is impossible
    that `rA(1) = +1 ∧ rB(0) = -1`.  In contrapositive form:
    `rA(1) = +1 → rB(0) = +1` (since `rB` is `±1`-valued). -/
private lemma hardy_E2
    {h : HardyCorrelations} {m : LHVModel} (hreal : LHVRealizesHardy h m)
    {l : m.HVar} (hμ : 0 < m.μ l) (hA : m.responseA 1 l = 1) :
    m.responseB 0 l = 1 := by
  have hz : lhvJointProb m 1 (-1) 1 0 = 0 := by
    rw [hreal.2.1]; exact h.hardy2
  have hnot := lhvJointProb_zero_pointwise m hz l hμ
  rcases m.responseB_pm_one 0 l with hp | hm0
  · exact hp
  · exfalso; exact hnot ⟨hA, hm0⟩

/-- **Implication (E3) from Hardy condition H3.**  Under any LHV
    model satisfying (H3), at any positive-weight `λ`:
    `rB(1) = +1 → rA(0) = +1`. -/
private lemma hardy_E3
    {h : HardyCorrelations} {m : LHVModel} (hreal : LHVRealizesHardy h m)
    {l : m.HVar} (hμ : 0 < m.μ l) (hB : m.responseB 1 l = 1) :
    m.responseA 0 l = 1 := by
  have hz : lhvJointProb m (-1) 1 0 1 = 0 := by
    rw [hreal.2.2.1]; exact h.hardy3
  have hnot := lhvJointProb_zero_pointwise m hz l hμ
  rcases m.responseA_pm_one 0 l with hp | hm0
  · exact hp
  · exfalso; exact hnot ⟨hm0, hB⟩

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 4: WITNESS LEMMA — H4 FORCES A POSITIVE-WEIGHT WITNESS
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- If `lhvJointProb m 1 1 1 1 > 0`, then there exists a hidden value
    `λ` with `μ(λ) > 0`, `responseA 1 λ = +1`, and `responseB 1 λ = +1`.

    Proof: if every λ failed one of the three conditions, every
    summand would be zero and the sum would be zero, contradicting
    the strict positivity of the sum. -/
private lemma lhvJointProb_pos_witness
    (m : LHVModel) {a b : ℤ} {x y : Fin 2}
    (hpos : 0 < lhvJointProb m a b x y) :
    ∃ l : m.HVar,
      0 < m.μ l ∧ m.responseA x l = a ∧ m.responseB y l = b := by
  by_contra hno
  push_neg at hno
  have hall : ∀ l ∈ (Finset.univ : Finset m.HVar),
      m.μ l
        * (if m.responseA x l = a then (1 : ℝ) else 0)
        * (if m.responseB y l = b then (1 : ℝ) else 0) = 0 := by
    intro l _
    by_cases hA : m.responseA x l = a
    · by_cases hB : m.responseB y l = b
      · -- All three would have to hold; but hno forbids combination.
        have : m.μ l ≤ 0 := by
          have hcontra := hno l
          by_contra hposμ
          push_neg at hposμ
          exact (hcontra hposμ hA) hB
        have hμnn := m.μ_nonneg l
        have hμz : m.μ l = 0 := le_antisymm this hμnn
        rw [hμz]; ring
      · simp [hA, hB]
    · simp [hA]
  have hzero : lhvJointProb m a b x y = 0 := by
    unfold lhvJointProb
    exact Finset.sum_eq_zero hall
  linarith

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 5: HARDY'S NO-LHV THEOREM
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- **HARDY'S NO-LHV THEOREM.**

    No local hidden variable model can realise the Hardy joint
    probability table.  The Hardy conditions H1–H4 are jointly
    incompatible with `λ`-factorisability.

    Proof outline:
      1.  (H4): some `λ*` has `μ(λ*) > 0` and
          `rA(1) λ* = +1 ∧ rB(1) λ* = +1` (witness lemma).
      2.  (E3): `rB(1) λ* = +1 → rA(0) λ* = +1`.
      3.  (E2): `rA(1) λ* = +1 → rB(0) λ* = +1`.
      4.  Combined: `rA(0) λ* = +1 ∧ rB(0) λ* = +1`.
      5.  (E1) contradicts (4).
-/
theorem hardy_no_LHV (h : HardyCorrelations) :
    ¬ ∃ m : LHVModel, LHVRealizesHardy h m := by
  rintro ⟨m, hreal⟩
  -- Step 1: extract λ* witnessing (H4) at the LHV level.
  have hH4 : 0 < lhvJointProb m 1 1 1 1 := by
    rw [hreal.2.2.2]; exact h.hardy4
  obtain ⟨l, hμ, hA1, hB1⟩ := lhvJointProb_pos_witness m hH4
  -- Step 2: (E3) gives rA(0) λ = +1.
  have hA0 : m.responseA 0 l = 1 := hardy_E3 hreal hμ hB1
  -- Step 3: (E2) gives rB(0) λ = +1.
  have hB0 : m.responseB 0 l = 1 := hardy_E2 hreal hμ hA1
  -- Step 4 & 5: (E1) excludes (rA(0)=+1, rB(0)=+1) at any positive λ.
  exact hardy_E1 hreal hμ ⟨hA0, hB0⟩

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    AXIOM-CHECK DIAGNOSTICS
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

#print axioms hardy_no_LHV

end UnifiedTheory.LayerC.HardyParadox
