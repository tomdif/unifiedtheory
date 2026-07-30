# The Quantum Covariance Gate at the b = 9 Windows

**Date:** 2026-07-30.  **Script:** `quantum_gate_b9.py` (exit 0).
**Scope:** era 2 (seed = the forced Big-Bang atom), relative depth r ≤ 4
(absolute n ≤ 6), constraint form of the pre-registered question, all
windows φ = 2πk/9, k ∈ {1, 2, 3, 4} (5–8 conjugate; 3 ≡ the b = 3 window).

## The pre-registered question, made finite

Constraint form: does a complex-RS dynamics (Surya–Zalel covariant +
Bell-causal: amplitudes λ(ϖ,m; s)/λ(r,0; s), complex couplings s, sum rule
automatic by the binomial identity) exist whose every transition amplitude
is ρ·e^{igφ} with ρ ≥ 0 and g the BD gap?  Two structural facts make the
gate finite and sharp:

1. **The gap of a birth depends only on its precursor poset** P = {x₀}∪D
   (between-counts live inside the past) — verified mechanically across
   all hosts r ≤ 4.  [MECH]
2. **The era-2 gregarious gap is 0** (the minimal-cover theorem), so every
   reachable denominator D_r = Σ C(r,j)s_j must be REAL POSITIVE, and each
   constraint reads:  arg λ(signature) ≡ (gap mod 9)·φ — per signature.

Interference adds one genuinely quantum move the classical gate lacked:
a transition class can be CLOSED by cancellation (λ = 0 with complex s).
The gate is then a finite search over zero-patterns of the 10 signatures
(ϖ ≤ 4), with reachability-aware constraint collection and a linear
feasibility problem per pattern (1024 patterns × 4 windows).  [MECH]

## The collision table (the heart of the result)

Gap classes mod 9 per RS signature, over all precursor posets ϖ ≤ 4:

    (1,1): {0}         coherent          (3,3): {6}      coherent
    (2,1): {2}         coherent          (4,4): {6}      coherent
    (2,2): {1}         coherent
    (3,1): {1, 8}      COLLISION   (4-chain vs diamond precursor)
    (3,2): {0, 7}      COLLISION
    (4,1): {0,1,2,4,8} COLLISION
    (4,2): {0,1,3,7,8} COLLISION
    (4,3): {0,6,7}     COLLISION

**The BD action is not a function of the RS transition signature** from
three-element pasts on: covariance + Bell causality can only distinguish
(cardinality, #maximal) of the precursor, while the action sees its full
interval structure.  This is the core incompatibility, and it is
phase-independent — the collisions force λ = 0 for every colliding
signature whose instances are jointly reachable, in every window.

## Results

- **k = 1, 2, 4 (primitive b = 9, and conjugates): dead.**  All 64
  feasible zero-patterns per window have NO live signature: the only
  dynamics is the quantum broom (all couplings zero, single deterministic
  history).  Mechanism: collisions force the (3,·)/(4,·) closures, and
  denominator-reality kills the rest — s₂, s₃, s₄ carry forced phases
  2πk/9·{1, 6, 6} ∉ ℝ, incompatible with Im D_r = 0, hence vanish; s₁ is
  real-phased (class 0) but the reachable (2,1) constraint (class 2)
  forces arg s₁ = 4πk/9 ≠ 0, hence s₁ = 0.  The interference-reopening
  mechanism DOES fire at depth 2 (with only r ≤ 1 nodes constrained, s₁ is
  free and the 3-chain transition the classical gate closed is reopened)
  — and dies at depth 3 when the rel-2-chain it created imposes (2,1).
  Interference reopens transitions locally but cannot survive depth 3.
- **k = 3 (the b = 3 window): a real-amplitude remnant.**  s₁ = s₂ = 0
  forced; s₃, s₄ ≥ 0 survive (classes ≡ 0 mod 3 ⇒ phases 1).  All live
  amplitudes are real positive: NO relative phases anywhere, no
  interference, decoherence functional real.  Reachable geometry:
  antichains-over-seed and their caps — broom-forest class.  This is a
  quantumly-degenerate (phase-free) family, not a quantum dynamics.

## Verdict

**The null hypothesis fails.**  A quantum extension decohering onto
non-broom geometry would have had to exploit interference to reopen
classically-closed transitions; interference exists in the formalism, it
fires at depth 2 — and the signature collisions plus the reality
constraint imposed by the action-neutral gregarious channel extinguish it
by depth 3–5.  To the checked depth (era 2, r ≤ 4, all b = 9 windows):

> Even quantum-mechanically, probability-from-action grows no spacetime.
> The intersection of the ansatz with covariant Bell-causal complex
> sequential growth contains only the quantum broom and a phase-free real
> remnant at b = 3 of the same broom-forest geometry.

The "consequence" direction of the pre-registered distinction is
thereby moot at this depth: with the constraint form empty of quantum
content, there is nothing for grade-2 + covariance + strong positivity to
derive the cos² law FROM.

The one-sentence mechanism, now common to both gates: **the
Benincasa–Dowker action distinguishes precursor posets that covariance
plus Bell causality cannot** — the 9s and 7s and 17s are (1, −9, 16, −8)
speaking, and they say the same thing to amplitudes as to probabilities.

## Caveats and residue

- Quantum era boundaries (amplitude analogs of VR timid moments) beyond
  the forced stage-1 boundary are not classified; an early era-2 exit
  re-runs the same gate with seed-shifted precursor gaps, and the
  collision mechanism is generic — but this is [PHYS]-level expectation,
  not yet [MECH].
- Depth: r ≤ 4 within era 2.  The collision table only grows with ϖ
  (more precursor posets per signature), so deeper reach adds constraints,
  not freedom.
- Gauge: the phase assignment is the literal ansatz (path phase =
  endpoint action).  Rephasing by an arbitrary per-causet χ is equivalent
  to redefining the action S → S + χ/φ, i.e. a different theory, not a
  gauge of this one.
- Lean candidates: the collision integers (gap(4-chain precursor) = 1 vs
  gap(diamond precursor) = 26, ≢ mod 9) and the denominator-reality
  argument are small and formalizable; queued.

## Relation to the classical no-go

The classical paper's two teeth survive intact and are now joined by the
quantum tooth at the checked depth.  The stronger abstract is available:
probability-from-action is incompatible with sequential-growth covariance
classically (no stochasticity, no geometry) AND quantum-mechanically at
the forced phase windows (no interference beyond depth 2, no geometry).
Both papers were worth having; the evidence now says the stronger one is
true.
