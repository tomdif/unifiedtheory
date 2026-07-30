# The Covariance Gate: Born-from-growth × Varadarajan–Rideout

**Date:** 2026-07-30.  **Status:** gate run and closed.  **Scripts:**
`commensurability_check.py`, `root_zero_propagation.py` (superseded analysis,
retained), `vr_era_gate.py` (authoritative).  **Lean:**
`Audit/KFCausalSetActionNeutralExtension.lean` (5 theorems, axiom-clean).

## Provenance tags
[LEAN] machine-checked · [MECH] mechanically verified by script ·
[PHYS] physical-framework claim · [LIT] literature.

## 1. The action-neutral extension theorem  [LEAN]

Conjectured from the n ≤ 4 scan; proof (two lines, due to the reviewer):
birth an event whose past is exactly one **minimal** element x.  Since
past(x) = ∅, transitivity adds nothing; the only new interval is [x,e] with
0 elements between; ΔS = σ(1 − W(0)) = 0.  Formalized as
`actionUnits_coverExtension` + `exists_action_neutral_extension` over the
existing `CardinalCausalOrder` growth infrastructure, with `exists_minimal`.
Consequences: the lazy tower's satisfiability was **unwinnable by design**;
iterating the cover of the same minimal element produces the **broom**
(maximally non-manifoldlike).

## 2. Root determinism, with the degenerate-phase carve-out  [LEAN]

`root_step_deterministic`: for every φ with cos φ ≠ 1, consistency at the
root forces p(2-antichain) = 0, p(2-chain) = 1.  φ ∈ 2πℤ (all phases = 1,
no phase information) is excluded by fiat and appears as the hypothesis.

## 3. The correct comparison family  [LIT]

Varadarajan–Rideout (gr-qc/0504066, PRD 73 104021): with vanishing
transition probabilities the general covariant + Bell-causal dynamics is
NOT the RS t-family with leading zeros.  It is a **tower of turtles**: RS
dynamics (t₀ = 1, t_k ≥ 0; all q_n > 0 for finite t) up to a freely chosen
stage n where q_n = 0 is imposed; there every real parent takes its
**timid** child (new element above the entire parent) with probability 1,
seeding a fresh RS era with *new* couplings, relative to which growth is
confined to seed-timid causets.  Bell causality is generalized to
conditions (i)–(iv) on ratios with zeros.  (The earlier
`root_zero_propagation.py` "empty at n ≤ 4" verdict analyzed the naive
t₀ = 0 boundary and is superseded — the era-2 couplings are free.)

## 4. The gate, run against the era structure  [MECH + LEAN arithmetic]

- **Era 1 must end at stage 1** (root determinism cannot hold with finite
  couplings) → every real causet has a **minimum element** (Big-Bang atom),
  stronger than originary.  [MECH + LEAN]
- **In-era interiors are two-child** (gregarious + timid; every proper
  nonempty relative downset of the relative antichain has weight
  s_{|D|} = 0 by the lazy induction).  Verified j ≤ 4, provable ∀j. [MECH]
- **Era 2 is the broom**: its gregarious gap is 0 (minimal cover), and a
  two-branch node containing a zero-gap child is degenerate
  (born_quadrature_law ⇒ p = cos²0 = 1).  Each coupling s_j = 0 in turn.
- **Era exits are doubly constrained**: exit at broom height m needs
  g_m·φ ≡ 0 (2π) (timid gap), and the first birth of the next era is
  *forced* (unique seed-timid extension) with gap h_m, needing
  h_m·φ ≡ 0 (2π).  Closed forms, verified against direct action
  computation for m ≤ 12 [MECH]:
      g_m = 9, −17, 6, then 1 − m (m ≥ 4);   h_m = −7, 26, then 9m (m ≥ 3).
  Survivors need gcd(|g_m|,|h_m|) > 1, and gcd(m−1, 9m) = gcd(m−1, 9) ∣ 9:
  the pinned phase is ALWAYS φ = 2πk/b with **b ∣ 9, b odd**.
  m = 1 (pure chain tower) dies by gcd(9,7) = 1
  (`chain_tower_incommensurable` [LEAN]); m = 2 dies by gcd(17,26) = 1;
  m = 3, 4, and m ≡ 1 (mod 3) survive with b = 3 (b = 9 iff m ≡ 1 mod 9,
  first at m = 10, i.e. n = 12).
- **No branching, ever**: at pinned odd b, both-positive two-branch
  quadrature needs 4kΔ = b(1+2j) — even = odd
  (`quadrature_parity_obstruction` [LEAN]).  Root-of-unity scan [MECH]:
  b = 3 admits NO multi-support consistency solutions at all; b = 9 admits
  many 3- and 4-support solutions — but reachable nodes are two-child, so
  they are never populated.  (b = 6 would branch with p = (1/9,4/9,4/9)
  and b = 8 with p = (1/2,1/2) — both arithmetically unreachable.)

## 4b. The two-child induction, stated precisely (the load-bearing step)

The quantifier is the **strong** one: *no consistency solution puts support
on more than one child at any reachable node, for any admissible φ.*  It is
NOT the weak claim "the lazy solution exists"; intermediate children are
not assumed virtual — their virtuality is derived stage by stage, and the
per-node arithmetic is universal over all integer gap pairs, so no
unnoticed gap window can reopen the sector.

**Invariant.**  For an era E with seed C and couplings s, at relative stage
j ≥ 1:  I(j) := "the unique reachable relative causet is the j-antichain
over C, and s₁ = … = s_{j−1} = 0."

**Base I(1)** — structural, trivial: the empty relative causet has one
downset (∅); the first era birth is forced.  (No coupling assumed zero.)

**Step I(j) → I(j+1).**  Children of the j-antichain node are indexed by
subsets D:
  - proper nonempty D: an antichain with every element maximal
    (`antichain_subset_all_maximal` [LEAN]), so weight λ(|D|,|D|) = s_{|D|}
    = 0 by I(j) — virtual.  The coupling s_d was killed at stage d BEFORE
    it could appear in any intermediate weight (at stage d there are no
    intermediate children at all when d = 1, and inductively none later).
  - gregarious (weight s₀ = 1 > 0): gap 0 in era 2
    (`actionUnits_coverExtension` [LEAN] — the era-2 relative-gregarious
    birth covers the seed minimum, past = {bottom}); gap h(C) in later
    eras, with h(C)·φ ≡ 0 (2π) already imposed at era entry.
  - timid (weight s_j): gap G_j.
  Consistency at the two non-virtual children, p_greg = 1/(1+s_j) > 0:
  - s_j > 0 (both positive) is killed for EVERY φ in era 2
    (`two_support_zero_gap_deterministic` [LEAN]) and for every pinned
    φ = 2πk/b, b ∈ {3,9} odd, in later eras
    (`two_support_pinned_odd_deterministic` [LEAN], universal over g₁ ≠ g₂);
  - s_j = 0 advances the invariant;
  - an imposed era end (q_j = 0, VR timid moment) is deterministic and
    requires G_j·φ ≡ 0 (2π) — the sieve.  ∎

The ≥3-support solutions that exist at b = 9 never apply: they need ≥3
non-virtual children, and the invariant caps reachable nodes at two.

**Per-step status.**  Node arithmetic: [LEAN] (universal).  Antichain
maximality: [LEAN].  Zero gregarious gap in era 2: [LEAN].  Weight formula
λ(d,d) = s_d and the era framework (VR classification, forced first birth,
exit double-pinning): [LIT] + [MECH].  Gap closed forms g_m, h_m: [MECH]
m ≤ 12, elementary induction beyond.  gcd(m−1, 9m) = gcd(m−1, 9) ∣ 9:
elementary.  Remaining [MECH]→[LEAN] candidates, none load-bearing alone:
the closed forms and the era bookkeeping; the VR classification itself is
[LIT] and would be a formalization program of its own.

## 5. Verdict  [PHYS]

**The intersection of the Born-from-growth tower with classical covariance
+ Bell causality (VR, zeros allowed) contains only deterministic single
histories**: the eternal broom (φ free), and hierarchical broom towers with
era exits at 3-sieved heights (φ = 2πk/3 or 2πk/9).  The transition law
p = cos²(ΔS/ℏ) never takes a value in (0,1) on any reachable transition.
The quantum sector of the ansatz is **empty under classical covariance** —
a no-go with an arithmetic mechanism living entirely in the BD coefficients
(1, −9, 16, −8).

Reading: this does not kill probability-from-action; it proves the link
cannot coexist with *classical* sequential-growth covariance.  A genuine
quantum sector requires the covariance condition to be imposed at the level
of the decoherence functional (quantum sequential growth), where the
Markov sum rule is replaced by the grade-2 sum rule I₃ = 0 that the
committed `KFCausalQuantumMeasure` already satisfies.  That is the sharp,
motivated next question — and the b = 9 solution windows found above are
exactly the phase values any such quantum extension would have to use.

## 6. Deliverables

- `Audit/KFCausalSetActionNeutralExtension.lean`: `exists_minimal`,
  `coverExtension` (+ labeled-extension proof), `actionUnits_coverExtension`,
  `exists_action_neutral_extension`, `root_step_deterministic`,
  `chain_tower_incommensurable`, `quadrature_parity_obstruction`.
  All axiom-clean (propext, Classical.choice, Quot.sound).  Root build green.
- `vr_era_gate.py`: all [MECH] checks above, exit 0.
