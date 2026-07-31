# Paper 1 — Weight parity and the quantum character of discrete gravity: a dimensional dichotomy for action-coupled sequential growth

**Draft 1, 2026-08-01.**  Machine-checked artifacts:
`UnifiedTheory/Audit/KFCausalQuantumMeasure.lean`,
`UnifiedTheory/Audit/KFCausalSetActionNeutralExtension.lean` (Lean 4 +
Mathlib, 18 theorems, axiom-clean).  Verification scripts cited inline.
Vocabulary: DEFINITIONS.md.

## Abstract

We study sequential-growth dynamics for causal sets whose transition
amplitudes carry the phases of the discrete Benincasa–Dowker (BD)
action, a(C→C′) = ρ·e^{iΔS/ℏ} with ρ ≥ 0, under the Markov sum rule and
discrete general covariance.  Whether such a theory is classical or
quantum is decided by the integer arithmetic of the action's weights.
In four dimensions (weights 1, −9, 16, −8) the action has exact zero
modes under growth — every finite causet admits an action-neutral
one-element extension (cover a minimal element; Lean-verified) — and
three successively weaker gates (classical Rideout–Sorkin/
Varadarajan–Rideout dynamics; signature-factored complex dynamics;
fully non-factored covariant dynamics) each collapse onto the
degenerate zero-mode sector: deterministic broom cosmologies and a
phase-degenerate "null web" with no interference at any depth checked.
In two dimensions (weights 2, −4, 2, all even) every gap is odd (parity
theorem, Lean-verified), no zero modes exist, no deterministic channel
exists at any phase, and the covariant family is *forced* quantum: the
root equation itself mandates equal-amplitude superposition.  The
mechanism at every step is certificate-grade integer arithmetic — the
collision table (the BD action is not a function of the Rideout–Sorkin
growth signature; first collision at three-element precursors,
Lean-verified), gcd sieves on era-exit gap pairs, and a parity
obstruction to quadrature at odd root-of-unity phases.  We conclude
that within this ansatz class, the classical-versus-quantum character
of discrete gravity is a theorem about the action's weight system, with
dimension entering only through those weights.

## 1. Setup

Sequential growth, the BD action in interval-abundance form, the
ansatz, the sum rule, and the two covariance notions (amplitude-level;
measure-level) are as in DEFINITIONS.md.  The consistency condition at
a node with children of integer gaps g_c reads Σ √p_c e^{ig_cφ} = 1;
at a genuinely two-branch node it forces the quadrature law
p = cos²(ΔS/ℏ) [Lean: born_quadrature_law] — the probability-from-
action link whose fate the paper decides.  We emphasize: |A|² = p is an
input of the ansatz; only the link is derived.

## 2. The 4D collapse (three gates)

**Gate I (classical).**  Against the Varadarajan–Rideout completion of
Rideout–Sorkin dynamics (vanishing probabilities allowed; tower of
turtles), the tower of consistency conditions forces: era 1 ends at
stage one (the universe acquires a minimum element — root determinism,
Lean-verified with the φ ∈ 2πℤ carve-out); each era is a broom (the
zero-gap gregarious channel plus born-quadrature degeneracy); era exits
are doubly pinned by gap pairs (g_m, h_m) with gcd(m−1, 9m) | 9, so
surviving phases are φ = 2πk/b with b ∈ {3, 9}; the pure chain
cosmology dies by gcd(9, 7) = 1 [Lean: chain_tower_incommensurable];
and at odd b the parity obstruction 4kΔ = b(1+2j) [Lean:
quadrature_parity_obstruction] forbids every branching node.  Verdict:
deterministic single histories only, all broom-class.  (Scripts:
vr_era_gate.py, resonant_exit_pricing.py.)

**Gate II (quantum, signature-factored).**  For complex-RS amplitudes,
the sum rule is the binomial identity and the gates reduce to phase
arithmetic per signature.  The collision table — sig (3,1) carries gaps
{1, 26}, incongruent mod 9 [Lean: collision_gap_chain,
collision_gap_diamond, collision_forces_closure] — forces interference
closures; the zero-gap gregarious channel forces real denominators; all
b = 9 windows die to the quantum broom; the b = 3 window leaves a
phase-free real remnant ("a classical stochastic process wearing
notation").  Interference genuinely fires at depth 2 — reopening the
3-chain transition the classical gate closed — and is extinguished at
depth 3 by the structure it created.  An era-seed sweep (25 seeds)
shows the death is seed-stable.  (Scripts: quantum_gate_b9.py,
era_boundary_sweep.py.)

**Gate III (quantum, non-factored).**  Dropping Bell causality and
factoring entirely, covariance reduces the theory to the wave equation
on the causet tree (DEFINITIONS.md).  Full covariance = downward-closed
support; the 2-antichain (root-killed) is an ancestor of every
disconnected causet; lone imaginary channels die; the exact search
yields the mod-9 null web: 24 causets to n = 6, all action ≡ 1 mod 9,
every amplitude real — branching without interference.  (Script:
sz_covariance_gate.py.)

## 3. The 2D inversion

The 2D weights are all even, so every gap is odd [Lean: gap_parity_2D,
no_neutral_extension_2D]: no zero-gap children exist, c₂(n) ≡ 0, and
the entire 4D degeneracy apparatus (neutral extensions, lazy towers,
brooms, null webs) is absent.  Consequences, mechanically verified:
the root equation forces Ã(2-chain) = Ã(2-antichain) = 1/(2cos φ) —
equal-amplitude superposition at every admissible phase; no
probability-1 channel exists generically; the classical era sieve
gcd(2m−1, 4m−1) = 1 is dead at every height.  Any surviving 2D dynamics
is stochastic; and the covariant family exists *maximally*: full
support (all 2045 seven-element causets; all 16999 at depth 8 with
level-7 equations active), machine-precision telescoping unitarity, 87
branching nodes, eleven distinct action values among 5-stems (genuine
relative phases).  One anomaly: φ = π/4 — the Born-quadrature point —
is the unique dead phase, by a two-line certificate (the shared child
L = 2-chain⊔point is demanded at 1/2 and 1/4 by the two root-children's
equations; the μ = 2 multiplicity kill).  (Scripts: collision_2d.py,
wave_gate_2d.py, deep_2d.py; PI4_CERTIFICATE.md.)

## 4. The mechanism, stated once

The BD action is not a function of the growth signature (both
dimensions, first collision at three-element precursors, Lean-verified
in 4D); its integer gaps carry arithmetic (gcds, parities,
multiplicities) that covariant sum rules must respect; and the weight
system decides which sector survives.  4D: zero modes exist ⇒ the
classical sector exists and swallows everything.  2D: zero modes do not
exist ⇒ no classical sector, quantum forced.  Dimension enters only
through (1, −9, 16, −8) versus (2, −4, 2).

## 5. Scope note: the sharp action, and what smearing changes

All 4D results above concern the sharp integer-weight action.  The
fluctuation-taming smeared action of Sorkin and Dowker–Glaser
(f₄(n, ε), non-integer weights, infinite layer support) destroys the
exact zero modes for generic ε — the minimal-cover gap becomes 1 − ε —
and a first computation (smeared_4d_gate.py) shows that 4D growth then
supports covariant, everywhere-branching, forced-quantum dynamics with
full support — but so far only in the barely-smeared regime: the
exhibit is ε = 0.8, which in four dimensions means l/ξ = 0.8^{1/4} ≈
0.946, a nonlocality scale six percent above the discreteness scale.
The physically motivated regime (Dowker–Glaser: l/ξ ≈ 0.4–0.5, i.e.
ε ≈ 0.026–0.063) is an order of magnitude below, where the root
branching windows shrink to width ~kπε/(1−ε) and the resonance set
ε = 1/m (exact zero modes from m-antichain covers) accumulates with
spacing ~ε² — natural parameter choices land on or beside islands
(l/ξ = 0.5 is ε = 1/16 exactly).  The decisive computations have now run
(smeared_physical_probe.py): at depth n ≤ 6 the physical band is DEAD —
every window phase (k = 1, 2, 3, three offsets each) at four ε values
across [0.026, 0.063] returns empty support, with large min|gap|
(0.69–0.85), so the deaths are structural, not resonance kills.  The
irrational discriminator settles the archipelago's nature: ε = 0.45 and
its irrational neighbors (±(√2−1)/100, and 1/e) all die at the same
phase — geography, not resonance proximity.  Two structural facts
emerged: (i) the 1/m resonances are invisible to a depth-n gate unless
the tree contains m-antichain covers, so island width is a
depth-coupled quantity and the physical band has no gate-visible
islands at n ≤ 6; (ii) the 2D/4D contrast at small ε localizes in the
root gap signs — 2D's (−1, +1) permit cancellation at every phase,
smeared-4D's (1−ε, 1) only in the shrinking sliver.  A depth-7 probe
(physband_n7.py) leaves every window phase empty at both tested ε — and
finds the deterministic-root phases φ = 2πj/(1−ε) alive, with support
identified exactly: the broom spine (plus one capped variant), i.e. the
same survivor class the sharp-action VR gate produced by exact zero
modes.  Two computations with different mechanisms — degeneracy there,
phase winding here (the smeared cover gap 1−ε winds to unity) —
converge on the same survivor set: evidence that the two gates describe
one object.  The classical channel thus survives on a quantized phase
set, with ℏ and ε tied by ℏ = σ′(1−ε)/2πj — a countable family
constraining the combination of two parameters, holding precisely on
the channel where the dynamics is deterministic; it is a consistency
condition on the classical sector, not a prediction of either constant.
A disclosure on coverage: the original window derivation used only the
imaginary part of the root equation; adding the real part, the true
root-feasible regions are slivers just above multiples of 2π of width
~2πjε, so of the probed phases only the k = 2 set genuinely tested the
band (three phases per ε per depth) — those died, and the corrected
coverage is stated here rather than discovered by a reader.  Within the
true windows every node retains both a gregarious (phase-upper) and a
minimal-cover (phase-lower) channel, so per-node cone conditions are
satisfiable and the observed deaths are a global consistency
obstruction.  The margin analysis (margin_probe.py) locates and grades
it: the L1 distance-to-feasibility GROWS with depth (0.0617, 0.0678,
0.0715 at n = 5, 6, 7), and its dominant component is the root
equation's imaginary part at every depth — the root's Im-cancellation
is unfundable by the tree, with each added level contributing further
irreducible slack rather than relief.  One scope bound on the word
"depth-robust": at φ = 2πj + δ the level-n stem phases (S−1)φ wrap
around the circle only once n·j·ε ~ 1, so the entire enumerable range
is pre-wrap; the wrap scale ~1/(jε) ≈ 22 coincides with the
resonance-visibility scale, meaning all of the physical band's
nontrivial structure lives at depths enumeration cannot reach.  The
sharpened open theorem is therefore the PRE-WRAP NO-GO — infeasibility
for all n < c/(jε) by a root-seeded funding/telescoping induction, of
which the growing margin is the numerical shadow — together with the
general moment-criterion question: when does a gap menu's phase image
admit globally consistent positive cancellation?

**Closing scope.**  Within this ansatz class, at every depth we can
enumerate (n ≤ 7) and at every smearing value tested across the
physical band, 4D action-phase growth yields only broom-class dynamics,
with the classical channel restored on a quantized phase set.  Whether
a quantum sector exists at greater depth or in the continuum
formulation is open.  To date, 2D is the only place this framework has
produced one.  What stands independent of their outcome:
the sharp-4D collapse is not robust to weak smearing, the resonance set
of a fixed-depth gate is finite and algebraic (gaps are
integer-coefficient polynomials in ε), and the deeper invariant of the
dichotomy is the zero-mode structure, which the nonlocality scale
controls.

## 5′. Status ledger

[LEAN] 18 theorems (list in the repository file header), axiom-clean.
[MECH] all gates exit 0; enumerations validated against A000112;
unitarity telescoping at machine precision.
[PHYS] the ansatz itself; the identification of consistency with
amplitude normalization; VR-analog era boundaries in the quantum case.
Open: depth beyond n = 8; other weight systems (the trichotomy
classification); the counting-convention axiom (see Paper 3).
