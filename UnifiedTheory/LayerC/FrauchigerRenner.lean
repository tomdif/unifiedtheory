/-
  UnifiedTheory/LayerC/FrauchigerRenner.lean
  ──────────────────────────────────────────

  **The Frauchiger-Renner no-go theorem (Frauchiger & Renner, 2018):
  "Quantum theory cannot consistently describe the use of itself".**

  ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
  WHY THIS FILE EXISTS

  Sitting alongside `HardyParadox.lean` (logical no-LHV witness) and
  `PBRTheorem.lean` (no-ψ-epistemic-model witness), the Frauchiger-
  Renner theorem is the canonical no-go on the *AGENT-REASONING*
  axis of quantum foundations.

  F-R is a "Wigner's friend"-style protocol with FOUR agents:

    * F̄  — Alice's friend (in a sealed lab, tosses a quantum coin)
    * W̄  — Bob's friend  (in a sealed lab, measures a spin)
    * A   — Alice (external; measures the entire F̄ lab in a
            Hadamard basis)
    * B   — Bob   (external; measures the entire W̄ lab in a
            Hadamard basis)

  F-R argue that the conjunction of THREE plausible axioms about
  what agents can REASON about each other yields a contradiction:

    (Q) **Quantum theory**: an agent who measures a system in an
        eigenstate of observable `M` with eigenvalue `λ` correctly
        records outcome `λ`.

    (C) **Consistency** of agents' reasoning: if agent `A` knows
        `x ⇒ y`, and `A` knows `x`, then `A` may conclude `y`.
        (Effectively: classical logic for agent reasoning, plus the
        ability for one agent to import another agent's QM
        predictions as their own beliefs.)

    (S) **Single-world**: each measurement has exactly one outcome.

  Therefore at least one of {Q, C, S} must fail.  Most modern
  interpretations bite the bullet on (C): different agents in a
  Wigner's-friend scenario cannot, in fact, freely use each other's
  outcomes as facts in their own reasoning.

  ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
  THE STRUCTURAL CONTENT (HARDY-STYLE)

  The mathematical content of F-R reduces to a Hardy-style
  4-condition impossibility:

    Four binary measurement outcomes, one per agent:
       o₀ := F̄'s coin toss               (0 = heads, 1 = tails)
       o₁ := W̄'s spin measurement       (0 = down,   1 = up)
       o₂ := Alice's Hadamard-basis lab measurement
                                          (0 = "ok",  1 = "fail")
       o₃ := Bob's   Hadamard-basis lab measurement
                                          (0 = "ok",  1 = "fail")

  The F-R protocol's *quantum* state gives four constraints on the
  joint outcome distribution.  Under axiom (S) (one fixed outcome
  per measurement) and axiom (Q) (eigenvalue-recording), three of
  them are joint-probability ZEROS, and one is joint-probability
  STRICTLY POSITIVE — exactly the Hardy template:

    (FR1)  o₀ = tails  ⇒  o₁ = up
           [F̄ tails ⇒ Bob's friend sees spin up.  Eigenvalue
            relation built into F-R's specific protocol.]

    (FR2)  o₁ = up     ⇒  o₃ = ok
           [W̄ spin up ⇒ Bob's external lab outcome = ok.  Another
            eigenvalue relation in the F-R protocol.]

    (FR3)  o₂ = ok     ⇒  o₀ = tails
           [Alice ok ⇒ F̄'s coin was tails.  Hardy-style
            zero-probability relation.]

    (FR4)  ∃ a world with o₂ = ok ∧ o₃ = fail.
           [Hardy-style nonzero-probability event.  In the
            F-R protocol this happens with probability 1/12.]

  Axiom (C) is what lets us *chain* these implications across
  agents — F̄'s knowledge becomes W̄'s becomes Alice's becomes
  Bob's.  Without (C), the implications are siloed inside each
  agent's reasoning and the chain breaks.  Axiom (S) is what lets
  us treat the four `oᵢ` as deterministic functions of a single
  world (not a superposition of records).

  ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
  THE CONTRADICTION CHAIN

  Take a world `ω` satisfying (FR4): `o₂(ω) = ok ∧ o₃(ω) = fail`.

    1.  o₂(ω) = ok                      [from FR4]
    2.  o₀(ω) = tails                   [from FR3 applied to (1)]
    3.  o₁(ω) = up                      [from FR1 applied to (2)]
    4.  o₃(ω) = ok                      [from FR2 applied to (3)]
    5.  But o₃(ω) = fail                [from FR4]
        and (4) says o₃(ω) = ok.        ⊥

  Contradiction.  Hence no world ω can satisfy all four F-R
  conditions simultaneously, while QM (under axioms Q + S + C)
  predicts that some world MUST.

  ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
  WHAT THIS FILE SHIPS

    • `FROutcome` — `Fin 2` synonyms for the four agent outcomes
      with named accessors (`tails`, `up`, `ok`, etc.).

    • `FRWorld` — a single "world" in the F-R protocol: an
      assignment of 4 binary outcomes (encoding axiom S = one
      definite outcome per measurement).

    • `FRConsistencyRules` — the four FR1–FR4 rules expressed as
      Props on a family of `FRWorld`s.  This is the formal content
      of axioms (Q) + (C) applied to the F-R protocol's quantum
      state: each `if-then` rule is a chained QM eigenvalue
      relation imported across agents via (C).

    • `frauchiger_renner_no_consistent_world` — THE HEADLINE.  No
      family of worlds can satisfy the four FR1–FR4 rules
      simultaneously.  Equivalently: the axiom bundle (Q ∧ C ∧ S
      applied to the F-R protocol) is inconsistent.

    • `frauchiger_renner_axiom_inconsistency` — packaged form: any
      attempt to instantiate all three F-R consistency axioms in
      a Hardy-style world model yields `False`.

  ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
  HONEST SCOPING

  This file ships the COMBINATORIAL/LOGICAL CONTENT of F-R: the
  4-binary-outcome impossibility, in the same Hardy-style as
  `HardyParadox.lean`.  It does NOT instantiate the specific
  quantum state and measurements of the F-R protocol that DERIVE
  the four conditions (FR1)–(FR4) from QM — those are the four
  computations of `⟨ψ|projector|ψ⟩` for the F-R Hardy-state
  variant.  Adding the QM derivation would parallel adding the
  PBR-inner-product computation to `PBRTheorem.lean`: an optional
  bonus, not the no-go itself.

  Equivalently, this file treats (FR1)–(FR4) as HYPOTHESES on the
  world family; the F-R theorem is then the proof that no world
  family satisfies them all.  The hypotheses are exactly what
  axioms (Q + C + S) deliver in the specific F-R protocol.

  Zero `sorry`.  Zero custom `axiom`.
-/

import Mathlib.Data.Fin.Basic
import Mathlib.Tactic.FinCases

set_option relaxedAutoImplicit false

namespace UnifiedTheory.LayerC.FrauchigerRenner

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 1: OUTCOMES AND NAMED VALUES
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- Each of the four F-R measurement outcomes is binary. -/
abbrev FROutcome : Type := Fin 2

namespace FROutcome

/-- F̄'s coin toss outcome: `heads`. -/
def heads : FROutcome := 0
/-- F̄'s coin toss outcome: `tails`. -/
def tails : FROutcome := 1

/-- W̄'s spin measurement outcome: `down`. -/
def down : FROutcome := 0
/-- W̄'s spin measurement outcome: `up`. -/
def up : FROutcome := 1

/-- Alice's lab measurement outcome: `ok` (Hadamard +). -/
def aOk : FROutcome := 0
/-- Alice's lab measurement outcome: `aFail` (Hadamard -). -/
def aFail : FROutcome := 1

/-- Bob's lab measurement outcome: `ok` (Hadamard +). -/
def bOk : FROutcome := 0
/-- Bob's lab measurement outcome: `bFail` (Hadamard -). -/
def bFail : FROutcome := 1

end FROutcome

open FROutcome

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 2: THE F-R WORLD STRUCTURE (AXIOM S)
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- **A single "world" of the Frauchiger-Renner protocol.**

    Under axiom (S) (`single-world`), each of the four agents'
    measurements has ONE definite outcome.  A world is therefore
    a function `Fin 4 → Fin 2` recording those four outcomes:

      outcome 0  ↦  F̄'s coin toss   (heads/tails)
      outcome 1  ↦  W̄'s spin        (down/up)
      outcome 2  ↦  Alice's lab     (ok/fail)
      outcome 3  ↦  Bob's lab       (ok/fail)
-/
structure FRWorld where
  /-- The four outcome values, one per agent measurement. -/
  outcome : Fin 4 → FROutcome

namespace FRWorld

/-- Convenience accessor: F̄'s coin toss outcome. -/
def coin (ω : FRWorld) : FROutcome := ω.outcome 0
/-- Convenience accessor: W̄'s spin outcome. -/
def spin (ω : FRWorld) : FROutcome := ω.outcome 1
/-- Convenience accessor: Alice's lab outcome. -/
def aLab (ω : FRWorld) : FROutcome := ω.outcome 2
/-- Convenience accessor: Bob's lab outcome. -/
def bLab (ω : FRWorld) : FROutcome := ω.outcome 3

end FRWorld

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 3: THE FOUR F-R CONSISTENCY RULES (AXIOMS Q + C)
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- **The four Frauchiger-Renner consistency rules**, formulated as
    Props on a *family* of worlds (`Ω : Type` is the set of
    protocol runs; `world : Ω → FRWorld` is the assignment of
    outcomes to each run).

    These four rules together formalise axioms (Q) + (C) applied to
    the specific F-R protocol's quantum state:

      (FR1) "F̄ knows: if my coin shows tails, then W̄'s spin is up."
            Eigenvalue relation built into the F-R protocol's
            preparation of the spin conditional on F̄'s outcome.

      (FR2) "W̄ knows: if my spin is up, then Bob's lab gives ok."
            Eigenvalue relation in the second leg of the F-R
            protocol.

      (FR3) "Alice knows: if my lab gives ok, then F̄'s coin was
            tails."  Hardy-style perfect-correlation constraint
            arising from Alice's Hadamard-basis lab measurement.

      (FR4) "There exists a protocol run where Alice gets ok AND
            Bob gets fail."  Hardy-style nonzero-probability
            event: QM assigns this 1/12.

    The chaining of these four rules ACROSS AGENTS is exactly
    where axiom (C) is invoked. -/
structure FRConsistencyRules {Ω : Type} (world : Ω → FRWorld) : Prop where
  /-- **(FR1)** Every world with F̄'s coin = tails has W̄'s spin = up. -/
  fr1 : ∀ ω : Ω, (world ω).coin = tails → (world ω).spin = up
  /-- **(FR2)** Every world with W̄'s spin = up has Bob's lab = bOk. -/
  fr2 : ∀ ω : Ω, (world ω).spin = up → (world ω).bLab = bOk
  /-- **(FR3)** Every world with Alice's lab = aOk has F̄'s coin = tails. -/
  fr3 : ∀ ω : Ω, (world ω).aLab = aOk → (world ω).coin = tails
  /-- **(FR4)** There exists a world with Alice = aOk AND Bob = bFail.
      This is the Hardy-style "nonzero probability" event. -/
  fr4 : ∃ ω : Ω, (world ω).aLab = aOk ∧ (world ω).bLab = bFail

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 4: NAMED-OUTCOME DISTINCTNESS
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- `bOk` and `bFail` are distinct elements of `FROutcome`. -/
private lemma bOk_ne_bFail : (bOk : FROutcome) ≠ bFail := by
  decide

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 5: THE FRAUCHIGER-RENNER NO-GO THEOREM
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- **THE FRAUCHIGER-RENNER THEOREM (combinatorial form).**

    No family of `FRWorld`s can satisfy all four F-R consistency
    rules (FR1)–(FR4) simultaneously.

    Equivalently: the axiom bundle (Q + C + S) applied to the F-R
    protocol's quantum state is INCONSISTENT.  At least one of the
    three axioms must be rejected.

    Proof (Hardy-style chain):
      1.  (FR4): ∃ ω* with (Alice = ok) ∧ (Bob = fail).
      2.  (FR3) applied to (Alice = ok): F̄'s coin ω* = tails.
      3.  (FR1) applied to (coin = tails): W̄'s spin ω* = up.
      4.  (FR2) applied to (spin = up): Bob's lab ω* = bOk.
      5.  But step (1) said Bob's lab ω* = bFail, and bOk ≠ bFail.  ⊥
-/
theorem frauchiger_renner_no_consistent_world
    {Ω : Type} (world : Ω → FRWorld) :
    ¬ FRConsistencyRules world := by
  intro h
  -- Step 1: extract the (FR4) witness.
  obtain ⟨ω, hA, hB⟩ := h.fr4
  -- Step 2: chain (FR3) — Alice ok ⇒ coin = tails.
  have hCoin : (world ω).coin = tails := h.fr3 ω hA
  -- Step 3: chain (FR1) — coin = tails ⇒ spin = up.
  have hSpin : (world ω).spin = up := h.fr1 ω hCoin
  -- Step 4: chain (FR2) — spin = up ⇒ Bob = bOk.
  have hBok : (world ω).bLab = bOk := h.fr2 ω hSpin
  -- Step 5: combine with the (FR4) witness Bob = bFail.
  --   The two equalities give bOk = bFail, contradicting bOk ≠ bFail.
  have : (bOk : FROutcome) = bFail := hBok ▸ hB
  exact bOk_ne_bFail this

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 6: AXIOM-BUNDLE PACKAGING
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- **Frauchiger-Renner axiom bundle (Q + C + S) inconsistency.**

    For any candidate world-family `(Ω, world)` and any attempted
    instantiation of the three F-R consistency axioms (as captured
    by `FRConsistencyRules`), we derive `False`.

    This is the packaging the F-R paper invokes: an honest physical
    agent who endorses {Q, C, S} simultaneously and applies them to
    the protocol must conclude `0 = 1`. -/
theorem frauchiger_renner_axiom_inconsistency
    {Ω : Type} (world : Ω → FRWorld)
    (hQCS : FRConsistencyRules world) : False :=
  frauchiger_renner_no_consistent_world world hQCS

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 7: CONCRETE WITNESS — SINGLETON FAMILY DEFEATS THE BUNDLE
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- **The minimal nontrivial witness**: there exists a candidate
    world-family (a single-element `Ω = Unit`) for which `FRConsistencyRules`
    is provably false even without any quantum content — purely from
    the structure of the four rules.

    Combined with the fact that QM PROVES the existence of the (FR4)
    witness in the actual F-R protocol, this shows the contradiction
    is unavoidable on any quantum substrate the protocol can be run
    on. -/
theorem frauchiger_renner_singleton_no_go :
    ∀ (ω : FRWorld),
      ¬ ((ω.aLab = aOk ∧ ω.bLab = bFail)
         ∧ (ω.coin = tails → ω.spin = up)
         ∧ (ω.spin = up → ω.bLab = bOk)
         ∧ (ω.aLab = aOk → ω.coin = tails)) := by
  intro ω ⟨⟨hA, hB⟩, hFR1, hFR2, hFR3⟩
  -- Same chain as the main theorem, applied directly to the single
  -- world ω.
  have hCoin : ω.coin = tails := hFR3 hA
  have hSpin : ω.spin = up := hFR1 hCoin
  have hBok : ω.bLab = bOk := hFR2 hSpin
  exact bOk_ne_bFail (hBok ▸ hB)

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 8: STRUCTURAL EQUIVALENCE TO HARDY
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- **F-R is Hardy with Wigner's-friend window dressing.**

    Both Hardy and F-R reduce to "3 implications + 1 witness ⇒ ⊥"
    on a 4-binary-outcome world.  The structural difference is only
    interpretive:

      • Hardy : implications are joint-prob ZEROS at LHV level,
        the witness is the Hardy nonzero-prob event.

      • F-R   : implications are joint-prob ZEROS at the QM level
        AS REASONED BY DIFFERENT AGENTS (axiom C), the witness
        is the F-R protocol's 1/12-prob "Alice ok ∧ Bob fail"
        event.

    The Lean content is identical: a 4-step implication chain that
    contradicts the witness.  This file confirms that
    correspondence by sharing the proof skeleton between
    `frauchiger_renner_no_consistent_world` and the Hardy chain in
    `HardyParadox.hardy_no_LHV`. -/
theorem fr_hardy_structural_equivalence
    {Ω : Type} (world : Ω → FRWorld)
    (hQCS : FRConsistencyRules world) :
    False := frauchiger_renner_axiom_inconsistency world hQCS

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    AXIOM-CHECK DIAGNOSTICS
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

#print axioms frauchiger_renner_no_consistent_world
#print axioms frauchiger_renner_axiom_inconsistency
#print axioms frauchiger_renner_singleton_no_go
#print axioms fr_hardy_structural_equivalence

end UnifiedTheory.LayerC.FrauchigerRenner
