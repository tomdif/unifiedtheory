# The Necessity Theorem: gate support ⊆ hereditary-real, at every depth and every resonance

**2026-08-03.**  The unproven half of the central conjecture (seven
set-equalities, then an exact-witness sufficiency at depth 8) is the
necessity direction: no covariant solution assigns positive amplitude
to a non-hereditarily-real causet at a resonance.  It is now a
theorem, by induction on depth, with no computational base.

## Setting

Resonance: ε = p/m, φ = 2πq with W₀φ ∈ 2πℤ.  A causet is
*hereditarily real* iff every element's jump sum Σ_k Δ_k(z)·c_k is an
integer (equivalently every downset's phase is ±1).  Real causets
have χ = e^{iSφ} ∈ {±1}; a non-real causet has some element with
non-integral jump.  The depth-N gate: wave equations at levels
≤ N−1, amplitudes ≥ 0, root = 1, support downward-closed.

## Theorem

For every depth N, every solution's support contains only
hereditarily real causets.

## Proof (three moves, induction on N)

**Move 1 (projection).**  A depth-N solution restricted to levels
≤ N−1 satisfies the depth-(N−1) system (its equation set is a
subset, since level-k equations reference levels k, k+1 only).  By
induction, non-real causets at levels ≤ N−1 carry zero amplitude.

**Move 2 (jump locality + closure).**  Removing a maximal element y
changes no other element's jump: y lies in no one's past and — being
maximal — is never strictly between two comparable elements.  Let C
be non-real at level N with bad-jump element w.
  - If w is not maximal, or C has ≥ 2 maximal elements: remove a
    maximal y ≠ w; the (N−1)-downset C∖y retains w's bad jump, is
    non-real, hence dead by Move 1 — and C dies by support closure.
  - Otherwise C has a unique maximal z which is its only bad element.
    Unique maximal forces past(z) = C∖z =: P, so C is the APEX
    extension of the real causet P.

**Move 3 (lone apex channel).**  The apex extension is the unique
child of P adjoining an element above all of P (a downward-closed
cover set containing all maximals of P must be all of P), so C is
the ONLY potentially-surviving non-real child of P: every other
non-real child falls under Move 2's first bullet.  The imaginary
part of P's equation in its ±1 frame is then μ·sin θ·Ã(C) = 0 with
θ = the apex jump ∉ πℤ, so sin θ ≠ 0 and Ã(C) = 0.  ∎
[LEAN kernel: lone_nonreal_channel / lone_imaginary_channel,
KFCausalResonantSector.lean.]

## Verification of the combinatorial core

At ε = 1/4, φ = 8π, n = 8: the 12,264 non-real 8-causets partition
exactly as the proof requires — 11,501 with a non-real 7-downset,
763 apex extensions of real 7-causets, ZERO in neither class; apex
uniqueness confirmed by enumeration on sampled parents.  (The seven
prior gate==predicate set-equalities are now explained rather than
empirical.)

## Scope and consequence

The proof uses only: the resonance property (real causets have ±1
phases), jump locality, and downward closure — so it holds at every
resonance ε = p/m, in every dimension's weight system, at every
depth.  THE CENTRAL EQUALITY now stands as: gate ⊆ hereditary-real
(THEOREM, all depths); hereditary-real ⊆ gate (exact witnesses
through depth 8; general depth open, with witness minima thinning as
exp(−c·h²)).  Every future resonance scan is replaced by the
predicate in the necessity direction unconditionally.
