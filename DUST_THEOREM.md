# The Dust Theorem — composability is incompatible with branching in the resonant sector

**2026-08-01.**  The third no-go of the arc (after the funding theorem
and the aging theorem).  Convention: ORBIT counting — one amplitude per
isomorphism class, factorization Ã(C₁⊔C₂) = Ã(C₁)·Ã(C₂), no
interleaving multiplicities.  The labeled and event conventions give
different theorems and are left open; notably the EVENT-form cluster
gate's root obstruction is cos φ = 1 (Paper 3 ledger), which is
*satisfied* at the resonances — the third sector is exactly where that
obstruction vanishes, so the event-form question is live and untested.

## Statement (hypotheses in the name)

**Dust theorem for orbit-factorizing members.**  At every resonant phase (φ = 2πq with W₀φ ∈ 2πℤ, i.e. 2εq ∈ ℤ), the
only member of the covariant smeared-2D growth family satisfying BOTH
orbit-factorization AND support downward-closure is the pure dust
spine: Ã = 1 on antichains, 0 elsewhere.  Depth-independent.

NOT a statement about the resonant family as a whole: the phi = 8pi
web has 247 branching nodes and an 833-dimensional solution space —
all of it non-factorizing.  The theorem quantifies over the
factorizing slice only; that quantifier IS the content (composability
is what costs you the branching), and it stays attached to the name:
dust_telescope_orbit_factorizing [LEAN].

## Proof (three steps, each hand-checkable)

1.  **Antichains are pinned.**  The n-antichain is the disjoint union
    of n points and Ã(point) = 1 (root normalization), so
    factorization forces Ã(nA) = 1 for every n.

2.  **The claw telescope** [LEAN: dust_telescope_orbit_factorizing, axiom-clean].  The
    children of the n-antichain are: the (n+1)-antichain (gap 1) and,
    for each nonempty D ⊆ points with |D| = d, the causet
    claw_d ⊔ (n−d) points, with multiplicity C(n,d) and gap 1 − dW₀
    (all new links have k = 0 because D is an antichain).  At a
    resonance the channel phase is e^{iφ}·(e^{−iW₀φ})^d = 1 for every
    d.  The n-antichain's sum rule therefore reads

        1 = 1 + Σ_{d=1}^{n} C(n,d) · Ã(claw_d),

    a sum of nonnegative terms equal to zero: **every claw dies**
    (claw_1 = the 2-chain, claw_2 = V, ... — the n = 1, 2 cases
    reproduce the forced values found directly from the root and
    2-antichain equations).

3.  **Every non-antichain contains a claw as a principal downset.**
    A non-antichain causet has an element y of height 2; its past
    consists of minimal elements only, so the downset ↓y is exactly
    claw_{|past(y)|}.  Support downward-closure (definitional: the
    transition amplitude a(C→C′) = [Ã(C′)/Ã(C)]e^{iθ} requires
    Ã(C) ≠ 0 on any live path) then kills every non-antichain.  ∎

## Why this is the right statement

- The mechanical probe (composability_probe.py) confirms both halves:
  without the closure constraint the LP finds a spurious "member" with
  Ã(3-chain) > 0 above Ã(2-chain) = 0 (an infinite transition ratio —
  not a dynamics; retracted in-session); with closure enforced the
  fixed point is exactly the dust spine (support 7, branching 0).
- The proof uses only W₀φ ∈ 2πℤ, factorization, closure and
  nonnegativity — none of the congruence structure — so it holds at
  every resonance in every dimension's weight system, not just the
  three 2D points computed.
- Consequence for real-amplitude quantum mechanics (Renou et al.,
  Nature 2021): the resonant sector is real-amplitude but its
  branching members are necessarily NON-composable, and its composable
  member is deterministic.  The network-Bell premises (independent
  sources, tensor composition) cannot be instantiated on any branching
  resonant dynamics under orbit counting: the sector evades the
  real-QM falsification and violates cluster factorization for one
  common cause — at resonance the antichain→claw channels are
  phase-neutral, which simultaneously realifies the web (no complex
  interference) and telescopes the claw kill (no composable
  branching).

## Scope

Orbit convention only; event and labeled conventions open (event-form
passes its root gate at resonances — the natural next probe).  The
theorem is about the resonant (third) sector; in-window quantum
members are untouched by it.
