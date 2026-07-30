# Probability-from-action is incompatible with classical sequential-growth covariance

**Draft 2026-07-30.**  Machine-checked artifacts:
`UnifiedTheory/Audit/KFCausalQuantumMeasure.lean`,
`UnifiedTheory/Audit/KFCausalSetActionNeutralExtension.lean` (Lean 4 +
Mathlib, axiom-clean); mechanical verification `vr_era_gate.py`,
`neutral_extension_n6.py`.

## Abstract

We consider the ansatz that assigns each causal-set growth history the
amplitude √P·e^{iS/ℏ}, with S the discrete Benincasa–Dowker (BD) action,
and ask whether the induced transition law p = cos²(ΔS/ℏ) — forced at
binary nodes by the consistency sum rule — can coexist with the classical
sequential-growth axioms of Rideout–Sorkin in the Varadarajan–Rideout (VR)
completion that admits vanishing transition probabilities.  The answer is
no, in a strong form: the intersection contains no stochastic dynamics at
all.  Every surviving dynamics is a single deterministic history, and every
survivor is a broom or a decorated broom — an unbounded antichain of covers
over a point — so the intersection contains no manifoldlike dynamics
either.  The no-go has two independent teeth: no interference, and no
geometry.  The mechanism is integer arithmetic of the 4D BD weights
(1, −9, 16, −8): a zero-gap child always exists (every finite causet
admits an action-neutral extension — cover a minimal element), forcing
laziness inside every VR era; era exits are doubly pinned by gap pairs
whose gcd always divides 9, so the phase is confined to odd roots of
unity, where a parity obstruction (4kΔ = b(1+2j), even = odd) forbids
branching.  The key steps are formalized in Lean 4.  The result sharpens,
rather than kills, the probability-from-action program: it proves the
covariance condition must be imposed at the level of the quantum measure
(decoherence functional), and it computes the exact phase windows
(ℏ = 9σ/2πk) any such quantum extension must use.

## 1. Setup

Sequential growth builds a causal set one element at a time; a dynamics
assigns transition probabilities on the poset of finite causets.
Rideout–Sorkin (RS) classified the generic dynamics obeying discrete
general covariance and Bell causality; Varadarajan–Rideout (VR) removed
the non-vanishing assumption and showed the general solution is a "tower
of turtles": RS eras with fresh couplings (t₀ = 1, t_k ≥ 0), separated by
imposed timid moments (q_n = 0: every real parent takes the child born
above its entirety, with probability 1), each seeding growth confined to
the future of its seed.

Separately, we take the quantum-measure ansatz A(γ) = √P(γ)·e^{iS_BD(γ)/ℏ}
on growth histories, with the decoherence functional D = A·Ā.  Strong
positivity is automatic (Gram form), the diagonal is the classical
measure, and the grade-2 sum rule holds.  Consistency of the amplitude
normalization at a node with children of integer action gaps g_c (in units
of σ = 4/√6; the 4D BD gaps are integers) reads

    Σ_c √p_c e^{i g_c φ} = 1,   Σ_c p_c = 1,   φ = σ/ℏ.

At a two-child node with both probabilities positive this forces the
quadrature law [Lean: born_quadrature_law]: cos θ_c = √p_c and
θ₁ − θ₂ ≡ π/2 (mod π), i.e. **p = cos²(ΔS/ℏ)** — probability from action.
We emphasize the honest reading: |A|² = p is an input of the ansatz; what
is derived is the *link* between probabilities and action gaps.  The
question of this paper: does this link survive contact with classical
covariance?

## 2. Two structural theorems

**Theorem 1 (action-neutral extension; Lean: actionUnits_coverExtension,
exists_action_neutral_extension).**  Every finite nonempty causet admits a
one-element extension of identical BD action: birth an event whose past is
exactly one minimal element.  The only new interval is a 2-interval and
ΔS = σ(1 − W(0)) = 0.
*Verified mechanically for all 405 causets with n ≤ 6; from n = 5 the
minimal cover is not the unique neutral extension (4 others at n = 5, 67
at n = 6).*  Iterating the cover of one point produces the **broom** — a
maximally non-manifoldlike causet.

**Theorem 2 (root determinism; Lean: root_step_deterministic).**  For
every φ with cos φ ≠ 1, consistency at the root (gaps 0, 1) forces
p(2-antichain) = 0.  Since RS eras with finite couplings have all
gregarious probabilities positive, era 1 must end at stage 1 with a VR
timid moment: **every real causet acquires a minimum element** — a
combinatorial Big-Bang atom.  (φ ∈ 2πℤ carries no phase information and is
excluded by fiat.)

## 3. The gate

Within an era with seed C, define the invariant I(j): the reachable
relative causet at stage j is the j-antichain over C, with couplings
s₁ = … = s_{j−1} = 0.  I(1) is structural (the first era birth is forced).
Given I(j), all intermediate children are virtual — a proper nonempty
subset of an antichain is an antichain of maximal elements [Lean:
antichain_subset_all_maximal], so its weight is the already-killed
coupling s_{|D|} — leaving exactly two non-virtual children: gregarious
(weight 1) and timid (weight s_j).  The consistency condition then kills
s_j > 0:

- in era 2 the gregarious gap is 0 (Theorem 1: the relative-gregarious
  birth covers the seed minimum), and a gap pair containing 0 is
  degenerate for every φ [Lean: two_support_zero_gap_deterministic];
- in later eras the phase is already pinned (below) to φ = 2πk/b with
  b ∈ {3, 9} odd, and any two distinct integer gaps are degenerate there:
  quadrature demands 4kΔ = b(1+2j), even = odd [Lean:
  two_support_pinned_odd_deterministic, quadrature_parity_obstruction].

So each era is a broom over its seed, and the only events are era exits:
a timid moment at height m needs g_m·φ ≡ 0 (2π), and the next era's first
birth is forced with gap h_m, needing h_m·φ ≡ 0 (2π).  Closed forms
(verified mechanically to m = 12, elementary beyond):

    g_m = 9, −17, 6, 1−m (m ≥ 4);    h_m = −7, 26, 9m (m ≥ 3),

whence gcd(|g_m|, |h_m|) = gcd(m−1, 9) ∣ 9.  The pure chain tower (m = 1)
dies by gcd(9, 7) = 1 [Lean: chain_tower_incommensurable]; m = 2 by
gcd(17, 26) = 1; survivors have m ≡ 1 (mod 3) or m ∈ {3, 4}, with b = 9
first available at broom height 10 (n = 12).  The multi-support solutions
that do exist at b = 9 (e.g. supports {0, 1, 8} mod 9) require ≥ 3
non-virtual children and are never reachable.

## 4. The no-go

**Theorem 3.**  The intersection of the consistency condition for
A = √P·e^{iS_BD/ℏ} with the VR classification of covariant, Bell-causal
sequential growth contains only deterministic single histories: the
eternal broom (φ free) and hierarchical broom towers with 3-sieved era
exits (φ = 2πk/3 or 2πk/9).  In particular p = cos²(ΔS/ℏ) never takes a
value in (0, 1) on any reachable transition, and no survivor is
manifoldlike.

The two teeth are independent: even granting the deterministic sector,
every survivor is a broom or decorated broom — an unbounded antichain of
covers — so classical covariance leaves the ansatz no physical dynamics at
all.  The integers doing the killing — the 9s, 7s, 17s — are the 4D BD
weights (1, −9, 16, −8) speaking.

## 5. Discussion: the quantum gate

The result does not touch probability-from-action itself; it proves the
link cannot be married to *classical* growth covariance.  The natural
continuation imposes covariance on the decoherence functional (quantum
sequential growth).  There the ansatz must be restated before computing:
there is no classical p to match — only amplitudes, the grade-2 sum rule,
and covariance in the Surya–Zalel sense (extension of the quantum measure
to the covariant σ-algebra, which is exactly where the known pathologies
live).  Probability-from-action becomes the statement that on decohering
stem events the diagonal of D equals cos² of the action gaps, with the
b = 9 windows ℏ = 9σ/2πk as the forced carrier — and whether that is a
constraint imposed or a consequence derived from grade-2 + covariance +
strong positivity is precisely the input/output distinction separating
conditional structure from a derived Born rule.  The committed quantum
measure already satisfies strong positivity and I₃ = 0; the extension
criteria are measure theory with Mathlib substrate.  That gate has never
been run mechanically.  It is next.

## Status ledger

[LEAN] born_quadrature_law; actionUnits_coverExtension;
exists_action_neutral_extension; root_step_deterministic;
two_support_zero_gap_deterministic; two_support_pinned_odd_deterministic;
quadrature_parity_obstruction; chain_tower_incommensurable;
antichain_subset_all_maximal — all axiom-clean.
[MECH] gap closed forms (m ≤ 12); survivor table; two-child enumeration
(j ≤ 4); root-of-unity solution sets (b = 3, 6, 8, 9); neutral-extension
census (n ≤ 6).
[LIT] VR classification (gr-qc/0504066); RS dynamics (gr-qc/9904062).
[PHYS] the ansatz itself, and the identification of consistency with the
physical normalization of the growth amplitude.
