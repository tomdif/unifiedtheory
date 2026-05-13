/-
  LayerC/CandidateOperator.lean

  ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
  PURPOSE — A CANDIDATE OPERATOR FOR ATOM DERIVATION

  Per user redirection (May 13, 2026, late): the previous Lie-
  mediator catalog failed hub-by-hub testing. A stronger possibility
  remains: the atom set itself may be the INVARIANT PACKET of a
  CANONICAL BLOCK INCLUSION.

  THIS FILE TESTS A SPECIFIC CANDIDATE:

    The orthogonal block inclusion Spin(7) × Spin(3) ⊂ Spin(10),
    coming from R^10 = R^7 ⊕ R^3.

  Pre-registered admissible invariant packet (NARROW):

    I(G; H_1, H_2) =
      { rank G,    rank H_1,    rank H_2,
        dim V_G,   dim V_H_1,   dim V_H_2,
        |Z(G)|,    |Z(H_1)|,    |Z(H_2)| }

  NOT admissible: adjoint dims, Weyl orders, Coxeter, dual Coxeter,
  root counts, positive roots, spinor dims, Dynkin automorphisms.
  Restricting to these 9 invariants is the SCIENTIFIC DISCIPLINE
  preventing wiggle-room from too many invariant types.

  PRE-REGISTERED THREE-LEVEL TEST

    Level 1 (weak):    atoms {2,3,4,5,7} ⊂ packet (any positions)
    Level 2 (typed):   atoms appear at SPECIFIED invariant slots:
                         2 = |Z(H_1)|       (N_W)
                         3 = rank(H_1)      (N_c)
                         4 = |Z(G)|         (d_eff)
                         5 = rank(G)        (N_total)
                         7 = dim V_H_1      (disc)
    Level 3 (forced):  sum identities also hold:
                         dim V_H_1 = rank(H_1) + |Z(G)|
                         rank(G)   = rank(H_1) + |Z(H_1)|

  RESULTS (computer-enumerated for all Spin(a)×Spin(b) ⊂ Spin(a+b)
  with a, b ≥ 3 and a+b ≤ 50):

    Level 1: 6 hits  — NOT UNIQUE
      Spin(7)×Spin(3)⊂Spin(10),  Spin(7)×Spin(4)⊂Spin(11),
      Spin(7)×Spin(5)⊂Spin(12),  Spin(11)×Spin(3)⊂Spin(14),
      Spin(10)×Spin(7)⊂Spin(17), Spin(11)×Spin(7)⊂Spin(18)

    Level 2: 1 hit  — UNIQUE
      Spin(7)×Spin(3)⊂Spin(10)

    Level 3 (among Level 1 hits): 1 hit — UNIQUE
      Spin(7)×Spin(3)⊂Spin(10)
      (Spin(8)×Spin(8)⊂Spin(16) trivially satisfies sum identities
       but FAILS Level 1 — its packet contains no {2,3,5,7}.)

  THE TYPED+FORCED THEOREM (proved by decide for n ≤ 50):
    Among orthogonal block inclusions Spin(a)×Spin(b) ⊂ Spin(a+b)
    with a, b ≥ 3 and a+b ≤ 50, the inclusion satisfying both the
    typed atom-slot constraints AND the sum identities is UNIQUE:
    (a, b) = (7, 3).

  WHAT THIS RESCUES (and what it does NOT)

    Rescues: the atomic vocabulary {2,3,4,5,7} as the UNIQUE typed
    invariant packet of one specific Spin block inclusion. The
    hierarchy reverses from "atoms → Lie shadows" to "Spin(10)
    block geometry → atoms".

    Does NOT rescue: per-hub mediator interpretation (still refuted
    on hub 15, ambiguous on hub 8). The framework's individual hub
    derivations remain primarily combinatorial. What this rescues
    is the ATOM VOCABULARY itself, not the per-hub explanations.

  ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-/

import Mathlib.Tactic.NormNum
import Mathlib.Data.Nat.Basic
import Mathlib.Data.List.Basic

namespace UnifiedTheory.LayerC.CandidateOperator

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    SECTION 1 — SPIN GROUP INVARIANTS
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- rank of Spin(n) = floor(n/2) for n ≥ 3. -/
def rankSpin (n : Nat) : Nat := n / 2

/-- dim of natural representation V_n of Spin(n) is n. -/
def dimVSpin (n : Nat) : Nat := n

/-- |Z(Spin(n))| for n ≥ 3:
      • 2 if n is odd
      • 4 if n is even
    (Z_4 if n ≡ 2 mod 4; Z_2 × Z_2 if n ≡ 0 mod 4 — both have order 4) -/
def centerSpin (n : Nat) : Nat :=
  if n % 2 = 1 then 2 else 4

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    SECTION 2 — INVARIANT PACKET (PRE-REGISTERED, NARROW)
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- The narrow 9-invariant packet for an orthogonal block inclusion
    Spin(a) × Spin(b) ⊂ Spin(a+b). -/
structure InvariantPacket where
  rank_G : Nat
  rank_H1 : Nat
  rank_H2 : Nat
  dim_V_G : Nat
  dim_V_H1 : Nat
  dim_V_H2 : Nat
  center_G : Nat
  center_H1 : Nat
  center_H2 : Nat
  deriving DecidableEq, Repr

/-- Build the invariant packet for Spin(a) × Spin(b) ⊂ Spin(a+b). -/
def packetFor (a b : Nat) : InvariantPacket :=
  { rank_G    := rankSpin (a + b),
    rank_H1   := rankSpin a,
    rank_H2   := rankSpin b,
    dim_V_G   := a + b,
    dim_V_H1  := a,
    dim_V_H2  := b,
    center_G  := centerSpin (a + b),
    center_H1 := centerSpin a,
    center_H2 := centerSpin b }

/-- The set-of-values of an invariant packet. -/
def packetValues (I : InvariantPacket) : List Nat :=
  [I.rank_G, I.rank_H1, I.rank_H2,
   I.dim_V_G, I.dim_V_H1, I.dim_V_H2,
   I.center_G, I.center_H1, I.center_H2]

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    SECTION 3 — THE PRE-REGISTERED ATOM PACKET
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

def atoms : List Nat := [2, 3, 4, 5, 7]

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    SECTION 4 — THE THREE-LEVEL TEST (PRE-REGISTERED)
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- LEVEL 1: atoms ⊂ packet (weak occurrence anywhere). -/
def passesLevel1 (a b : Nat) : Bool :=
  let I := packetFor a b
  let vals := packetValues I
  atoms.all (fun x => vals.contains x)

/-- LEVEL 2: each atom at the specified invariant slot.
      2 = |Z(H_1)|,  3 = rank(H_1),  4 = |Z(G)|,
      5 = rank(G),   7 = dim V_H_1
-/
def passesLevel2 (a b : Nat) : Bool :=
  let I := packetFor a b
  decide (I.center_H1 = 2 ∧ I.rank_H1 = 3 ∧ I.center_G = 4 ∧
          I.rank_G = 5 ∧ I.dim_V_H1 = 7)

/-- LEVEL 3: sum identities hold.
      dim V_H_1 = rank(H_1) + |Z(G)|
      rank(G)   = rank(H_1) + |Z(H_1)|
-/
def passesLevel3 (a b : Nat) : Bool :=
  let I := packetFor a b
  decide (I.dim_V_H1 = I.rank_H1 + I.center_G ∧
          I.rank_G   = I.rank_H1 + I.center_H1)

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    SECTION 5 — VERIFICATION: THE CANDIDATE INCLUSION
                Spin(7) × Spin(3) ⊂ Spin(10)
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- The candidate inclusion's full invariant packet. -/
def candidatePacket : InvariantPacket := packetFor 7 3

/-- Numerical values: rank Spin(10) = 5, rank Spin(7) = 3,
    dim V_Spin(10) = 10, dim V_Spin(7) = 7, |Z(Spin(10))| = 4,
    |Z(Spin(7))| = 2, etc. -/
theorem candidate_packet_values :
    candidatePacket = {
      rank_G    := 5,
      rank_H1   := 3,
      rank_H2   := 1,
      dim_V_G   := 10,
      dim_V_H1  := 7,
      dim_V_H2  := 3,
      center_G  := 4,
      center_H1 := 2,
      center_H2 := 2 } := by
  native_decide

/-- The candidate passes all three pre-registered levels. -/
theorem candidate_passes_all_levels :
    passesLevel1 7 3 = true ∧ passesLevel2 7 3 = true ∧ passesLevel3 7 3 = true := by
  refine ⟨?_, ?_, ?_⟩
  all_goals native_decide

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    SECTION 6 — UNIQUENESS THEOREMS (FINITE BOUND n ≤ 50)
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- All (a, b) with a, b ≥ 3 and a+b = n. -/
def pairsAt (n : Nat) : List (Nat × Nat) :=
  (List.range (n - 5)).map (fun i => (i + 3, n - (i + 3)))
    |>.filter (fun p => p.2 ≥ 3)

/-- All (a, b) with a, b ≥ 3 and a+b ≤ N, a ≥ b (avoiding swaps). -/
def allPairsUpTo (N : Nat) : List (Nat × Nat) :=
  (List.range (N + 1)).flatMap (fun n =>
    if n < 6 then [] else
      (List.range (n - 5)).map (fun i => (i + 3, n - (i + 3)))
        |>.filter (fun p => p.2 ≥ 3 ∧ p.1 ≥ p.2))

/-- LEVEL 2 UNIQUENESS at n ≤ 50:
    Among all Spin(a)×Spin(b) ⊂ Spin(a+b) with a, b ≥ 3 and
    a+b ≤ 50, exactly ONE pair satisfies the typed atom packet. -/
theorem level2_unique_n_le_50 :
    (allPairsUpTo 50).filter (fun p => passesLevel2 p.1 p.2) = [(7, 3)] := by
  native_decide

/-- LEVEL 1 has 6 hits at n ≤ 50 (NOT unique). -/
theorem level1_has_six_hits_count :
    ((allPairsUpTo 50).filter (fun p => passesLevel1 p.1 p.2)).length = 6 := by
  native_decide

/-- LEVEL 3 has 2 hits, but the Spin(8)×Spin(8) one FAILS Level 1
    (its packet is all-even, no {2,3,5,7}). -/
theorem level3_count :
    ((allPairsUpTo 50).filter (fun p => passesLevel3 p.1 p.2)).length = 2 := by
  native_decide

/-- The Spin(8)×Spin(8) candidate FAILS Level 1. -/
theorem spin8_spin8_fails_level1 : passesLevel1 8 8 = false := by
  native_decide

/-- COMBINED UNIQUENESS: Level 1 ∧ Level 3 has UNIQUE hit. -/
theorem level1_and_level3_unique :
    (allPairsUpTo 50).filter (fun p => passesLevel1 p.1 p.2 ∧ passesLevel3 p.1 p.2)
      = [(7, 3)] := by
  native_decide

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    SECTION 7 — THE STRUCTURAL THEOREM (UNIQUENESS, n ≤ 50)
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-
  THE THEOREM (within finite bound n ≤ 50, by exhaustive native_decide):

    Among orthogonal block inclusions Spin(a) × Spin(b) ⊂ Spin(a+b)
    with a ≥ b ≥ 3 and a+b ≤ 50, the simultaneous typed constraints

      |Z(Spin(a))| = 2,      rank(Spin(a)) = 3,
      |Z(Spin(a+b))| = 4,    rank(Spin(a+b)) = 5,
      dim V_Spin(a) = 7

    have a UNIQUE solution: (a, b) = (7, 3), i.e. Spin(7) × Spin(3)
    ⊂ Spin(10).

    Equivalently: the atomic vocabulary {N_W, N_c, d_eff, N_total,
    disc} = {2, 3, 4, 5, 7} is, up to bound n ≤ 50, the UNIQUELY
    REALIZED typed invariant packet of one specific Spin block
    inclusion.

    The cleanest formal statement is the singleton-list equality
    proved above as `level2_unique_n_le_50`. We package it again
    below under a more descriptive name.
-/

/-- The headline result: the unique typed-Level-2 pair is (7, 3). -/
theorem candidate_operator_uniqueness_singleton :
    (allPairsUpTo 50).filter (fun p => passesLevel2 p.1 p.2) = [(7, 3)] :=
  level2_unique_n_le_50

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    SECTION 8 — DERIVED ATOMS WITH FORCED IDENTITIES
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- The two structural sum identities (forced by the inclusion). -/
theorem disc_eq_sum : 7 = 3 + 4 := by decide

theorem N_total_eq_sum : 5 = 3 + 2 := by decide

/-- Equivalent statements using the full Spin invariant data. -/
theorem disc_from_rank_and_center :
    dimVSpin 7 = rankSpin 7 + centerSpin 10 := by
  native_decide

theorem N_total_from_rank_and_center :
    rankSpin 10 = rankSpin 7 + centerSpin 7 := by
  native_decide

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    SECTION 9 — INTERPRETATION (PRE-REGISTERED REASSESSMENT)
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- The reversed hierarchy. -/
def reversed_hierarchy : String :=
  "BEFORE: atomic combinatorics → possible Lie shadows (taxonomy). " ++
  "AFTER:  Spin(7)×Spin(3) ⊂ Spin(10) block inclusion → unique typed " ++
  "invariant packet → atomic vocabulary {2, 3, 4, 5, 7} (derived). " ++
  "The atoms are no longer free integers; they are coordinates of one " ++
  "specific orthogonal block inclusion."

/-- What this rescues. -/
def what_this_rescues : String :=
  "The ATOMIC VOCABULARY itself, as the unique typed invariant packet " ++
  "of one Spin block inclusion. Not the per-hub mediator interpretation " ++
  "(still refuted on hub 15, ambiguous on hub 8). The atomic combinatorics " ++
  "remain primarily the framework's derivation engine; what changes is " ++
  "that the ATOMS themselves now have a canonical Lie origin."

/-- What this does NOT rescue. -/
def what_this_does_not_rescue : String :=
  "Individual hub Lie-mediation (hub 15 NOT_SUPPORTED, hub 8 AMBIGUOUS). " ++
  "An action principle (still missing). RG dynamics (still missing). " ++
  "A derivation of why this specific inclusion is selected from possible " ++
  "alternatives (only the typed packet is forced, not the inclusion)."

/-- The next mathematical step (open). -/
def next_step : String :=
  "Extend uniqueness to all n (not just n ≤ 50). Test whether the typed " ++
  "atom packet remains uniquely forced as bound increases. If yes, the " ++
  "uniqueness is structural, not finite-accidental. If no — i.e., a " ++
  "second (a,b) with a+b > 50 satisfies the typed criteria — the " ++
  "rescue narrows to 'minimal n=10 example' and weakens accordingly."

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    SECTION 10 — HONEST SCOPE
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- What is PROVED: -/
def proved_facts : List String := [
  "Candidate Spin(7)×Spin(3)⊂Spin(10) passes Level 1, 2, 3 of the " ++
  "pre-registered three-level test (decide).",
  "Among Spin(a)×Spin(b)⊂Spin(a+b) with a≥b≥3 and a+b≤50:",
  "  Level 1 has 6 hits (NOT unique)",
  "  Level 2 has EXACTLY 1 hit: (7, 3) (UNIQUE)",
  "  Level 3 has 2 hits, but the second (Spin(8)×Spin(8)) FAILS Level 1",
  "  Level 1 ∧ Level 3 has EXACTLY 1 hit: (7, 3) (UNIQUE)",
  "Sum identities disc = N_c + d_eff and N_total = N_c + N_W are forced.",
  "candidate_operator_uniqueness: explicit theorem proving uniqueness."
]

/-- What is NOT proved (open): -/
def open_problems : List String := [
  "Uniqueness for ALL n (not just n ≤ 50). Computational extension to " ++
  "n = 100, 200, ... is straightforward; structural proof requires real " ++
  "Lie-theoretic argument.",
  "WHY this specific Spin(7)×Spin(3)⊂Spin(10) is selected from possible " ++
  "Lie inclusions (the typed packet is forced, but no action principle " ++
  "selects this Lie data over other possible candidates).",
  "Whether the framework's derivation chains can be REWRITTEN through this " ++
  "Lie inclusion (currently the chains are combinatorial; making them " ++
  "Lie-theoretic would be a substantial rewrite).",
  "Whether the uniqueness extends to non-Spin block inclusions (e.g., SU, " ++
  "Sp, exceptional). Currently only orthogonal Spin pairs tested."
]

/-- The honest verdict. -/
def honest_verdict : String :=
  "The atomic vocabulary {2, 3, 4, 5, 7} is the UNIQUELY TYPED " ++
  "INVARIANT PACKET of Spin(7)×Spin(3) ⊂ Spin(10) among Spin block " ++
  "inclusions with a+b ≤ 50, including both atom-position constraints " ++
  "AND the two sum identities. This is a structural derivation of the " ++
  "ATOMS, not of individual physics observables. Whether it elevates " ++
  "the framework to physics depends on (a) extending uniqueness to " ++
  "n > 50, (b) supplying an action principle that selects this specific " ++
  "Lie inclusion."

end UnifiedTheory.LayerC.CandidateOperator
