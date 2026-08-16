# Prior art: Gudder's unitary transition amplitudes (2013–2014)
# — the double-conservation kernel has an antecedent (2026-08-15)

Deep-read of S. Gudder, "An Isometric Dynamics for a Causal Set
Approach to Discrete Quantum Gravity" (arXiv:1409.3770, Sept 2014),
building on "A Dynamics for Discrete Quantum Gravity"
(arXiv:1303.0433, 2013).  Verdict: the double-conservation
constraint pair IS in Gudder, on a restricted arena; everything
this program built on top of it — the action-phase selection, the
feasibility geometry, the expansion law, the uniqueness leg — is
not.  All papers must cite him.  Details, exact.

## 1. The exact match: uta = double conservation (binary case)

Gudder's transition amplitude ã : P × P → ℂ satisfies (his 2.1)
    Σ_k ã(x_{n,j}, x_{n+1,2j+k}) = 1        [coherent / stochastic]
and is a "unitary transition amplitude" (uta) if also (his 2.2)
    Σ_k |ã(x_{n,j}, x_{n+1,2j+k})|² = 1     [Born / unitary]
— exactly our double conservation Σa = 1, Σ|a|² = 1, per parent.
PRIORITY: Gudder 2014.  Our program formulated the same pair
independently in 2026; the concept must be attributed to him.

His Theorem 2.1 (the binary solution continuum):
    a + b = |a|² + |b|² = 1  ⟺  ∃! θ ∈ [0,π):
        a = cos θ e^{iθ},   b = −i sin θ e^{iθ}.
His remark: real-valued uta forces a deterministic (0/1) branch —
our `real_binary_bi_normalized_deterministic` is the machine-checked
form of that remark.

## 2. The striking identity: our π/4 root = his θ = π/4 point

At θ = π/4 his continuum gives
    a = (√2/2) e^{iπ/4},   b = −i(√2/2) e^{iπ/4} = (√2/2) e^{−iπ/4}
— EXACTLY our root solution ρ e^{±iπ/4} with ρ = √2/2
(root_phase_is_pi_div_four).  So the Born-quadrature point this
program derived is the SYMMETRIC (equal-modulus) point of Gudder's
solution continuum.  What selects it: our action-phase ansatz —
amplitude modulus depends only on the parent, phase only on the
action gap (a locality/isotropy axiom justified in the covariance
leg).  Gudder leaves θ_{n,j} as free coupling constants; we select
a point of his continuum by a principle, and the selection is what
generates all downstream physics.  Honest framing forever after:
"the π/4 law is the symmetric point of Gudder's uta continuum,
selected by the action-phase ansatz."

## 3. The structural divergence: why his arena hides the physics

Gudder restricts to c-causets — covariant causets with a UNIQUE
labeling.  Consequence (his ref [3]): every c-causet has exactly
TWO offspring (widen the top shell, or open a new shell); the
growth tree is binary; geometry is the integer shell sequence.
In binary branching, double conservation is ALWAYS satisfiable
(Thm 2.1: a full continuum per node).  Therefore in his arena:
  - there is NO feasibility question — no infeasible parents,
    no cone/octant conditions, no walls;
  - there is NO width–depth law — widening the universe is always
    allowed, at every step, for free;
  - phases are free parameters — nothing ties them to geometry.
Our program works on the FULL Rideout–Sorkin downset tree
(arbitrary branching, gap multiplicities from causal structure).
There the same constraint pair becomes an overdetermined moment
system whose FEASIBILITY is a real, geometry-selecting condition —
and everything new lives exactly in that gap: infeasible parents,
octant-coverage geometry (§26), the width–depth expansion law
w_max(n) ≈ n/c*, phase–width commensurability.  One sentence:
IN GUDDER'S WORLD THE BORN RULE NEVER SAYS NO; IN THE FULL GROWTH
TREE ITS REFUSALS ARE THE PHYSICS.

## 4. Resonances worth recording

  - His Thm 2.7: same-producer children never interfere (uses both
    conditions) — same flavor as our class-diagonal phase-freedom
    (CoherentRecordAccretion), different mechanism.
  - His stationary amplitudes: a(ω) = cos^ℓθ (−i)^r sin^rθ e^{inθ}
    — a quarter-turn of phase per NEW SHELL (height increment).
    Phase-metered geometry is thus implicit in Gudder (height
    side); our §26 meter is the width side, made exact and
    law-level (one octant per width cell, ζ⁸ = 1).
  - His "double-down" blocks V₂ = [[c⁰,c¹],[c¹,c⁰]] are unitary AND
    doubly stochastic — the same two-port structure as our
    beam-splitter blocks; his Hamiltonian has energies 2θ (phase =
    energy), our φ·gap is phase = action.

## 5. Required updates (executed)

  - This file; PAPER_P1_SPINE prior-art section updated (Gudder
    cited for the constraint pair; P2/P3 must lead with the
    attribution).
  - Reframe in all future writing: double conservation → "Gudder's
    stochastic-unitary pair, generalized from binary c-causets to
    the full downset tree"; π/4 → "the symmetric point of Gudder's
    continuum, selected by the action-phase ansatz"; the program's
    novel core = the SELECTION PRINCIPLE + the FEASIBILITY
    GEOMETRY + the uniqueness leg + the falsifiable λ-observable.
