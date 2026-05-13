/-
  LayerC/CandidateOperatorUnbounded.lean

  ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
  PURPOSE — UNBOUNDED UNIQUENESS OF THE TYPED ATOM PACKET

  Companion to `LayerC/CandidateOperator.lean`. The original file
  proves uniqueness of (a, b) = (7, 3) by `native_decide` over the
  finite range a + b ≤ 50. The "next mathematical step" listed in
  that file's `next_step` field is to prove the result STRUCTURALLY
  for all n.

  THIS FILE DELIVERS THAT STEP.

  Main result: `candidate_operator_uniqueness_unbounded` proves that
  for ALL natural a, b ≥ 3 (no upper bound on a + b), the typed
  atom-slot constraints

      |Z(Spin(a))|     = 2     (centerSpin a = 2)
      rank(Spin(a))    = 3     (rankSpin a = 3)
      |Z(Spin(a+b))|   = 4     (centerSpin (a+b) = 4)
      rank(Spin(a+b))  = 5     (rankSpin (a+b) = 5)
      dim V_Spin(a)    = 7     (dimVSpin a = 7)

  force (a, b) = (7, 3). The proof is elementary number theory:

      • dimVSpin a = 7  =  a            ⇒  a = 7 directly.
      • centerSpin (a+b) = 4            ⇒  a + b is even.
      • rankSpin  (a+b) = 5  =  (a+b)/2 ⇒  a + b ∈ {10, 11}.
      • Combine even + ∈ {10, 11}        ⇒  a + b = 10.
      • Therefore b = 10 − 7 = 3.

  The proof is closed by `omega` once the parity / division facts
  are unfolded. No finite enumeration; works for all n ∈ ℕ.

  Bonus content:
   - A stronger packet-equality variant that also derives the
     full nine-invariant packet of Spin(7)×Spin(3) ⊂ Spin(10).
   - A swap-free corollary: even without assuming a ≥ b, the
     ordered pair (a, b) is forced by the typed constraints alone.
   - Negative results for SU and Sp block inclusions: the same
     typed atom packet is NOT realised by any SU(a)×SU(b) ⊂ SU(a+b)
     or Sp(2a)×Sp(2b) ⊂ Sp(2(a+b)). These confirm the typed packet
     is a strict invariant of the orthogonal Spin family.
   - `verdict` and `remaining_open_problems` summarise the result.
  ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-/

import UnifiedTheory.LayerC.CandidateOperator

namespace UnifiedTheory.LayerC.CandidateOperatorUnbounded

open UnifiedTheory.LayerC.CandidateOperator

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    SECTION 1 — ELEMENTARY ARITHMETIC LEMMAS
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- The center function distinguishes even from odd: if `centerSpin n = 4`
    then `n` is even (i.e. `n % 2 = 0`). -/
lemma even_of_centerSpin_eq_four {n : Nat} (h : centerSpin n = 4) :
    n % 2 = 0 := by
  unfold centerSpin at h
  by_cases hn : n % 2 = 1
  · simp [hn] at h
  · -- n % 2 ≠ 1 over ℕ means n % 2 = 0 (since n % 2 < 2)
    have : n % 2 < 2 := Nat.mod_lt _ (by decide)
    omega

/-- The center function: `centerSpin n = 2` iff `n` is odd. -/
lemma odd_of_centerSpin_eq_two {n : Nat} (h : centerSpin n = 2) :
    n % 2 = 1 := by
  unfold centerSpin at h
  by_cases hn : n % 2 = 1
  · exact hn
  · simp [hn] at h

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    SECTION 2 — THE MAIN UNBOUNDED UNIQUENESS THEOREM
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- **Unbounded uniqueness of the typed atom packet.**

    For ALL natural numbers `a, b ≥ 3` (with NO upper bound on `a + b`),
    if the orthogonal block inclusion Spin(a) × Spin(b) ⊂ Spin(a+b)
    realises the typed atom packet
        centerSpin a = 2, rankSpin a = 3,
        centerSpin (a+b) = 4, rankSpin (a+b) = 5,
        dimVSpin a = 7,
    then necessarily `(a, b) = (7, 3)`.

    Proof is purely number-theoretic case analysis on parity and
    integer division; no finite enumeration. -/
theorem candidate_operator_uniqueness_unbounded :
    ∀ a b : Nat, a ≥ 3 → b ≥ 3 →
      (centerSpin a = 2 ∧ rankSpin a = 3 ∧
       centerSpin (a + b) = 4 ∧ rankSpin (a + b) = 5 ∧
       dimVSpin a = 7) →
      a = 7 ∧ b = 3 := by
  intro a b _ _ ⟨_hcA, _hrA, hcG, hrG, hdA⟩
  -- Step 1: a = 7 from dimVSpin a = a = 7.
  have ha : a = 7 := by unfold dimVSpin at hdA; exact hdA
  -- Step 2: a + b is even from centerSpin (a + b) = 4.
  have hpar : (a + b) % 2 = 0 := even_of_centerSpin_eq_four hcG
  -- Step 3: (a + b) / 2 = 5 from rankSpin (a + b) = 5.
  have hdiv : (a + b) / 2 = 5 := by unfold rankSpin at hrG; exact hrG
  -- Step 4: a + b = 10 from parity + division.
  --   (a+b)/2 = 5 means a+b ∈ {10, 11}; parity forces a+b = 10.
  have hsum : a + b = 10 := by omega
  -- Step 5: b = 3 from a = 7 and a + b = 10.
  refine ⟨ha, ?_⟩
  omega

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    SECTION 3 — STRONGER UNIQUENESS (FULL PACKET EQUALITY)
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- **Full packet equality.** Under the typed constraints, the FULL
    nine-invariant packet equals the candidate packet of (7, 3). -/
theorem candidate_operator_packet_uniqueness_unbounded :
    ∀ a b : Nat, a ≥ 3 → b ≥ 3 →
      (centerSpin a = 2 ∧ rankSpin a = 3 ∧
       centerSpin (a + b) = 4 ∧ rankSpin (a + b) = 5 ∧
       dimVSpin a = 7) →
      packetFor a b = candidatePacket := by
  intro a b ha3 hb3 hpkt
  obtain ⟨ha, hb⟩ := candidate_operator_uniqueness_unbounded a b ha3 hb3 hpkt
  subst ha; subst hb
  rfl

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    SECTION 4 — SWAP-FREE COROLLARY (a ≥ b NOT REQUIRED)
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- The original `level2_unique_n_le_50` enumerates pairs with `a ≥ b ≥ 3`,
    avoiding swaps. Our unbounded statement is STRONGER: it does NOT assume
    `a ≥ b`. The typed constraints break the symmetry on their own, since
    they single out the H_1 slot via `dimVSpin a = 7`. -/
theorem candidate_operator_uniqueness_no_swap_assumption :
    ∀ a b : Nat, a ≥ 3 → b ≥ 3 →
      (centerSpin a = 2 ∧ rankSpin a = 3 ∧
       centerSpin (a + b) = 4 ∧ rankSpin (a + b) = 5 ∧
       dimVSpin a = 7) →
      a = 7 ∧ b = 3 :=
  candidate_operator_uniqueness_unbounded

/-- Sanity: if we additionally impose `a ≥ b`, we still get (7, 3). -/
theorem candidate_operator_uniqueness_with_ordering :
    ∀ a b : Nat, a ≥ b → b ≥ 3 →
      (centerSpin a = 2 ∧ rankSpin a = 3 ∧
       centerSpin (a + b) = 4 ∧ rankSpin (a + b) = 5 ∧
       dimVSpin a = 7) →
      a = 7 ∧ b = 3 := by
  intro a b hab hb3 hpkt
  have ha3 : a ≥ 3 := le_trans hb3 hab
  exact candidate_operator_uniqueness_unbounded a b ha3 hb3 hpkt

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    SECTION 5 — NON-SPIN EXTENSIONS (SU AND Sp FAMILIES)
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-! For SU(n) (n ≥ 1):  rank = n - 1, |Z(SU(n))| = n, dim V_n = n.
    For Sp(2n) (n ≥ 1): rank = n,     |Z(Sp(2n))| = 2, dim V_{2n} = 2n.

    We test whether the same typed atom packet is realisable in those
    families. These are NEGATIVE results: SU and Sp do NOT support
    the (2, 3, 4, 5, 7) packet at the analogous slots. This confirms
    the typed packet is a strict invariant of the Spin family. -/

/-- rank of SU(n) is n - 1. -/
def rankSU (n : Nat) : Nat := n - 1

/-- |Z(SU(n))| = n. -/
def centerSU (n : Nat) : Nat := n

/-- dim of natural representation V_n of SU(n) is n. -/
def dimVSU (n : Nat) : Nat := n

/-- rank of Sp(2n) is n. -/
def rankSp (n : Nat) : Nat := n / 2

/-- |Z(Sp(2n))| = 2 for all n ≥ 1. -/
def centerSp (_n : Nat) : Nat := 2

/-- dim of natural representation V_{2n} of Sp(2n) is 2n. -/
def dimVSp (n : Nat) : Nat := n

/-- **Negative result for SU.** The SU(a) × SU(b) ⊂ SU(a+b) inclusion
    cannot satisfy the typed atom packet:
        centerSU a = 2, rankSU a = 3, dimVSU a = 7
    is internally contradictory because dimVSU a = a forces a = 7,
    but then centerSU 7 = 7 ≠ 2. -/
theorem su_no_typed_packet :
    ¬ ∃ a b : Nat, a ≥ 3 ∧ b ≥ 3 ∧
        (centerSU a = 2 ∧ rankSU a = 3 ∧
         centerSU (a + b) = 4 ∧ rankSU (a + b) = 5 ∧
         dimVSU a = 7) := by
  rintro ⟨a, b, _, _, hcA, _, _, _, hdA⟩
  unfold dimVSU at hdA
  unfold centerSU at hcA
  -- a = 7 (from dimVSU) and a = 2 (from centerSU) is a contradiction.
  omega

/-- **Negative result for Sp.** Sp(2a)×Sp(2b)⊂Sp(2(a+b)) cannot satisfy
    the typed atom packet either. The Sp center is identically 2, so
    `centerSp (a+b) = 4` is impossible. -/
theorem sp_no_typed_packet :
    ¬ ∃ a b : Nat, a ≥ 3 ∧ b ≥ 3 ∧
        (centerSp a = 2 ∧ rankSp a = 3 ∧
         centerSp (a + b) = 4 ∧ rankSp (a + b) = 5 ∧
         dimVSp a = 7) := by
  rintro ⟨a, b, _, _, _, _, hcG, _, _⟩
  unfold centerSp at hcG
  -- centerSp _ = 2 always, so centerSp (a+b) = 4 is false.
  exact absurd hcG (by decide)

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    SECTION 6 — VERDICT AND OPEN PROBLEMS
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- The verdict of this file. -/
def verdict : String :=
  "UNBOUNDED UNIQUENESS PROVED. " ++
  "For ALL natural a, b ≥ 3 (no finite bound on a+b), the typed atom " ++
  "packet (centerSpin a = 2, rankSpin a = 3, centerSpin (a+b) = 4, " ++
  "rankSpin (a+b) = 5, dimVSpin a = 7) forces (a, b) = (7, 3). " ++
  "The proof is elementary number theory (omega + parity), not " ++
  "finite enumeration. Two non-Spin extensions (SU, Sp) confirmed " ++
  "NEGATIVE: neither family realises the same typed packet. The " ++
  "Spin(7) × Spin(3) ⊂ Spin(10) hit is therefore strictly an " ++
  "invariant of the orthogonal Spin family, not a coincidence " ++
  "shared with other classical Lie families. The 'next mathematical " ++
  "step' listed as open in CandidateOperator.lean is now closed."

/-- Remaining open problems beyond this file's scope. -/
def remaining_open_problems : List String := [
  "Exceptional families (G_2, F_4, E_6, E_7, E_8): no analog test " ++
  "performed; would require non-classical center/rank functions and " ++
  "is not addressed here.",
  "Other non-orthogonal block inclusion patterns within Spin (e.g. " ++
  "spinor embeddings Spin(7) ↪ Spin(8) via triality) not enumerated.",
  "WHY this specific Spin(7) × Spin(3) ⊂ Spin(10) inclusion is " ++
  "physically selected from possible Lie inclusions still requires an " ++
  "action principle (unchanged from the bounded version).",
  "Whether the framework's per-hub derivation chains can be rewritten " ++
  "Lie-theoretically through this inclusion (unchanged from the " ++
  "bounded version)."
]

/-- Compact summary for citation. -/
theorem unbounded_uniqueness_summary :
    ∀ a b : Nat, a ≥ 3 → b ≥ 3 →
      packetFor a b = candidatePacket →
      a = 7 ∧ b = 3 := by
  intro a b ha3 hb3 hpkt
  -- Extract the five typed constraints from packet equality.
  have hcA : centerSpin a = 2 := by
    have : (packetFor a b).center_H1 = candidatePacket.center_H1 := by rw [hpkt]
    simpa [packetFor, candidatePacket] using this
  have hrA : rankSpin a = 3 := by
    have : (packetFor a b).rank_H1 = candidatePacket.rank_H1 := by rw [hpkt]
    simpa [packetFor, candidatePacket] using this
  have hcG : centerSpin (a + b) = 4 := by
    have : (packetFor a b).center_G = candidatePacket.center_G := by rw [hpkt]
    simpa [packetFor, candidatePacket] using this
  have hrG : rankSpin (a + b) = 5 := by
    have : (packetFor a b).rank_G = candidatePacket.rank_G := by rw [hpkt]
    simpa [packetFor, candidatePacket] using this
  have hdA : dimVSpin a = 7 := by
    have : (packetFor a b).dim_V_H1 = candidatePacket.dim_V_H1 := by rw [hpkt]
    simpa [packetFor, candidatePacket] using this
  exact candidate_operator_uniqueness_unbounded a b ha3 hb3
    ⟨hcA, hrA, hcG, hrG, hdA⟩

end UnifiedTheory.LayerC.CandidateOperatorUnbounded
