# The Benincasa–Dowker action is not a function of the growth signature: a two-gate no-go for probability-from-action

**Draft 2, 2026-07-30.**  Machine-checked artifacts:
`UnifiedTheory/Audit/KFCausalQuantumMeasure.lean`,
`UnifiedTheory/Audit/KFCausalSetActionNeutralExtension.lean` (Lean 4 +
Mathlib, axiom-clean, 14 theorems); mechanical verification
`vr_era_gate.py`, `quantum_gate_b9.py`, `era_boundary_sweep.py`,
`resonant_exit_pricing.py`, `neutral_extension_n6.py`.

## Abstract

The transition amplitude of a covariant, Bell-causal sequential-growth
dynamics for causal sets — classical (Rideout–Sorkin/Varadarajan–Rideout)
or complex — depends on a birth's precursor set only through its
*signature*: cardinality and number of maximal elements.  The discrete
Benincasa–Dowker (BD) action does not: from three-element pasts on, the
action distinguishes precursor posets the signature cannot (the 3-chain
and Λ precursors share signature (3,1) but their births carry gaps 1 and
26, incongruent mod 9 — machine-checked).  **The BD action is not a
function of the growth signature.**  We show this single arithmetic fact
closes both gates on the ansatz A = √P·e^{iS_BD/ℏ}, which links
probability to action via p = cos²(ΔS/ℏ) at binary nodes.  Classically,
the intersection with the Varadarajan–Rideout classification contains
only deterministic single histories, all of broom class — no
stochasticity, no manifoldlike geometry.  Quantum-mechanically, at the
phase windows ℏ = 9σ/2πk the classical gate forces, interference does
exactly what a quantum escape requires — at depth 2 it reopens the
transition the classical gate closed — and the structure it thereby
creates kills it at depth 3; to the checked depth only the quantum broom
and a phase-free real remnant survive, and an exhaustive sweep of era
seeds shows the death is seed-stable.  The quantum kill uses only the sum
rule, signature-factoring, and the ansatz — grade-2 additivity, strong
positivity, and the measure-extension problem are never needed.  Every
load-bearing integer is certified in Lean 4.  The constructive residue is
a sharp open problem: whether covariance in the quantum-measure sense
forces signature-factoring at all — the one door this no-go leaves open,
and the only place a Born-from-growth dynamics can still live.

## 1. Setup

Sequential growth builds a causal set one element at a time; a dynamics
assigns transition data on the poset of finite causets.  Rideout–Sorkin
(RS) proved that discrete general covariance and Bell causality force the
transition probability of a birth to depend only on the precursor
signature (ϖ, m), giving the coupling family λ(ϖ,m; t)/λ(n,0; t);
Varadarajan–Rideout (VR) extended the classification to vanishing
probabilities ("tower of turtles": RS eras separated by imposed timid
moments, each seeding growth confined above its seed).

The ansatz under test assigns growth histories the amplitude
A(γ) = √P(γ)·e^{iS_BD(γ)/ℏ}, decoherence functional D = A·Ā.  Strong
positivity is automatic; the diagonal is the classical measure; the
grade-2 sum rule holds.  Consistency of amplitude normalization at a node
with children of integer action gaps g_c (units σ = 4/√6) reads
Σ_c √p_c·e^{ig_cφ} = 1 with φ = σ/ℏ, and at a genuinely two-branch node
forces the quadrature law p = cos²(ΔS/ℏ) [Lean: born_quadrature_law] —
probability from action.  Honest reading: |A|² = p is an input; the
derived content is the *link*.  The question: does the link survive
covariance?

## 2. Structural theorems

**Theorem 1 (action-neutral extension) [Lean].**  Every finite nonempty
causet admits a one-element extension of identical BD action: cover a
minimal element (past = {x}; the only new interval is a 2-interval;
ΔS = σ(1 − W(0)) = 0).  Verified against enumeration on all 405 causets
with n ≤ 6; the census of distinct neutral children, 1, 2, 6, 22, 105,
634, has no OEIS match (super-Catalan departs at n = 5) — a candidate new
entry.  Iterating the cover produces the **broom**, a maximally
non-manifoldlike causet.

**Theorem 2 (root determinism) [Lean].**  For every φ with cos φ ≠ 1,
consistency at the root forces p(2-antichain) = 0; era 1 must end at
stage 1 and every real causet acquires a minimum element.

**Theorem 3 (gap locality) [MECH].**  The BD gap of a birth depends only
on its precursor poset.  Hence the collision table:

    sig (1,1): {0}        (2,1): {2}        (2,2): {1}       [mod 9]
    sig (3,1): {1, 8}     (3,2): {0, 7}     (3,3): {6}
    sig (4,1): {0,1,2,4,8}  (4,2): {0,1,3,7,8}  (4,3): {0,6,7}  (4,4): {6}

The (3,1) entry — 4-chain precursor gap 1 vs diamond precursor gap 26,
same signature, 25 ≢ 0 mod 9 — is certified in Lean
(collision_signatures_agree, collision_gap_chain, collision_gap_diamond,
collision_forces_closure).

## 3. The classical gate

Within a VR era the invariant I(j) (reachable relative causet = the
j-antichain; earlier couplings dead) holds inductively: intermediate
children carry the single already-killed coupling
[antichain_subset_all_maximal], and the two-child node arithmetic is
degenerate for every gap pair — era 2 by the zero gregarious gap
[two_support_zero_gap_deterministic], later eras by parity at the pinned
odd phases [two_support_pinned_odd_deterministic,
quadrature_parity_obstruction].  Degeneracy has a direction: the
gregarious weight is identically s₀ = 1, so the surviving singleton is
gregarious [singleton_support_is_gregarious]; probability-1 timid steps
are era ends, priced by the double sieve (g_m, h_m) with
gcd(m−1, 9m) ∣ 9, whence φ = 2πk/b, b ∈ {3, 9}.  The chain tower dies by
gcd(9,7) = 1 [chain_tower_incommensurable]; rapid exits die in all
checked branches and the exit gaps are seed-independent from height 3 on,
so the sieve repeats in every era.

**Classical verdict.**  Only deterministic single histories survive:
the eternal broom (φ free) and stacks of brooms of height ≥ 3 joined by
single caps (φ = 2πk/3 or 2πk/9).  p = cos²(ΔS/ℏ) never lands in (0,1);
nothing manifoldlike survives.  Two independent teeth: no interference,
no geometry.

## 4. The quantum gate at the forced windows

At the b = 9 windows the classical verdict leaves, we test the complex
completion: amplitudes a = ρ·e^{igφ}, ρ ≥ 0, against complex-RS
(signature-factored) dynamics.  The sum rule Σa_c = 1 is the RS binomial
identity — automatic; the path phase telescopes to the endpoint action,
so amplitude path-independence holds by construction.  Two of our own
theorems make the gate finite: gap locality (constraints act per
signature) and the zero gregarious gap (all reachable denominators are
forced real positive).  Interference contributes the one genuinely
quantum move: closing a transition class by cancellation (λ = 0).  The
gate is a search over zero-patterns with a linear feasibility problem
each (1024 patterns × 4 windows) [quantum_gate_b9.py].

**The escape route fires, and fails.**  This is the sharpest finding of
the arc, and it is not a search coming up empty.  At depth 2 the quantum
theory does exactly what a Born-from-growth rescue requires: with s₁
free, interference reopens the 3-chain transition the classical gate had
closed.  At depth 3, the relative 2-chain which that reopening created
imposes the (2,1) constraint — signature class 2 against s₁'s forced real
phase — and kills it.  The theory was caught trying the escape route and
failing one level down.  Above depth 3 the collision table forces the
(3,·)/(4,·) closures, and denominator reality annihilates every coupling
with a non-real forced phase.

**Results.**  k = 1, 2, 4 (and conjugates): only the quantum broom.
k = 3: a remnant with s₃, s₄ ≥ 0 — but every live amplitude is real
positive, with no relative phase anywhere: a classical stochastic process
wearing notation.  Its survival confirms rather than qualifies the
verdict.  An exhaustive sweep over all unique-maximum era seeds |C| ≤ 5
[era_boundary_sweep.py] shows the death is seed-stable: at every b = 9
window, every entry-admissible seed (9 ∣ h(C)) is broom-only; at k = 3
every admissible seed carries only the real remnant.  The era-boundary
caveat is closed to the checked scope.

**Fewer axioms than pre-registered.**  The kill used only: the sum rule,
signature-factoring, and the ansatz phases.  Grade-2 additivity, strong
positivity, and the extension to the covariant σ-algebra — the
pre-registered heavy machinery — were never invoked.  A no-go that never
needs its strongest assumptions is a stronger no-go.

## 5. The boundary of the claim, and the open problem

Signature-factoring — couplings depending only on (ϖ, m) — is not an
axiom of quantum growth.  Classically it is a *theorem*: the output of
discrete general covariance plus Bell causality in the RS derivation.  No
quantum analogue of that theorem exists.  Amplitude path-independence
holds here by construction (the phase is a coboundary of the action), but
covariance in the quantum-measure sense — extension of the decoherence
functional to the covariant σ-algebra (Surya–Zalel) — is a logically
independent condition, and nothing yet shows it forces factoring.

The honest scope of the quantum verdict is therefore: **no dynamics whose
couplings factor through the RS signature can carry
probability-from-action, to the checked depth.**  Read constructively,
the collision table proves that any surviving Born-from-growth dynamics
must have precursor-poset-dependent couplings — it must break the
classical sufficient statistic, which classical Bell causality forbids
and quantum theory has not been shown to.  We pose as the paper's open
problem:

> **Does quantum-measure covariance (Surya–Zalel extension) together with
> strong positivity force transition amplitudes to factor through the
> precursor signature?**

If yes, the no-go is unconditional.  If no, the non-factoring window is
the only place a Born-from-growth dynamics can live, and the collision
table says exactly which precursor pairs its couplings must split.

## 6. Conclusion

The mechanism sentence of both gates: the Benincasa–Dowker action
distinguishes precursor posets that covariance and Bell causality cannot.
The 9s, 7s, 17s, and 25s doing the killing are the 4D BD weights
(1, −9, 16, −8) speaking — to probabilities and to amplitudes alike.
This is not the derivation of the Born rule; it is the decisive negative
that tells the field where such a derivation cannot live, with every
load-bearing integer machine-checked, and a well-posed question marking
the one door left open.

## Status ledger

[LEAN] born_quadrature_law; actionUnits_coverExtension;
exists_action_neutral_extension; root_step_deterministic;
two_support_zero_gap_deterministic; two_support_pinned_odd_deterministic;
quadrature_parity_obstruction; chain_tower_incommensurable;
antichain_subset_all_maximal; singleton_support_is_gregarious;
collision_signatures_agree; collision_gap_chain; collision_gap_diamond;
collision_forces_closure — all axiom-clean (propext, Classical.choice,
Quot.sound).
[MECH] gap locality (all hosts r ≤ 4); collision table (ϖ ≤ 4); classical
gate closed forms and survivor sieve (m ≤ 12; era-3 pricing, 4 branches);
quantum gate (1024 patterns × 4 windows, depth 5); era-boundary sweep
(25 seeds, depth 3); neutral-extension census (n ≤ 6, OEIS-novel).
[LIT] RS (gr-qc/9904062); VR (gr-qc/0504066); Surya–Zalel covariance
criterion.
[PHYS] the ansatz; consistency = amplitude normalization; quantum era
boundaries as amplitude analogs of VR timid moments.
