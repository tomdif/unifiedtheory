# Paper 1 — Weight parity and the quantum character of discrete gravity: a dimensional dichotomy for action-coupled sequential growth

**Draft 2, 2026-08-01.**  Machine-checked artifacts:
`UnifiedTheory/Audit/KFCausalQuantumMeasure.lean`,
`UnifiedTheory/Audit/KFCausalSetActionNeutralExtension.lean`,
`UnifiedTheory/Audit/KFCausalSmearedNoGo.lean` (Lean 4 + Mathlib, 19
theorems, axiom-clean).  Verification scripts cited inline.
Vocabulary: DEFINITIONS.md.

## Abstract

We study sequential-growth dynamics for causal sets whose transition
amplitudes carry the phases of the discrete Benincasa–Dowker (BD)
action, a(C→C′) = ρ·e^{iΔS/ℏ} with ρ ≥ 0, under the Markov sum rule and
discrete general covariance.  For the sharp integer-weight action,
whether such a theory is classical or quantum is decided by the
arithmetic of the action's weight system.  For the physically smeared
action the verdict is instead an ℏ-window law, uniform across
dimensions.  The truncation-2 subsystem of the in-window growth
equations depends only on the cover-channel winding W₀φ, the weight
ratio W₁/W₀, and the window offset; it is infeasible for every winding
W₀φ < π/2 (the funding theorem, Lean-verified, whose hypotheses cover
exactly this region because W₁/W₀ = 1 − (1+|C₂|)ε < 1 in every
dimension), and by the closure lemma these equations recur verbatim at
every depth, so low-winding smeared growth admits no covariant quantum
sector at any depth; the survivors there are two measure-zero
classical spines.  Numerically, the first-winding feasibility region
is exactly the band W₀φ ∈ (π/2, π) — boundaries bisected to 10⁻⁹,
independent of the ratio and the offset — and full wave-hierarchy
computations confirm the band is genuinely quantum: full support to
depth 7 (2450/2450 causets cumulative over n ≤ 7; 2045 at n = 7
alone, A000112 — both denominators appear in this paper and differ
by exactly this bookkeeping) in 2D at ε = 0.16
(winding j = 1) and, reversing our own earlier no-go — which, we
disclose, had only probed windings j ≤ 3 — in 4D at physical-band
ε = 0.045–0.0625 with winding j = 4–6.  The winding-band consequence
j ∈ (1/(4W₀), 1/(2W₀)) reproduces every scan integer-for-integer and
predicted in advance the 3D result (ε = 0.100 alive at j ∈ {3, 4};
confirmed).  Dimension therefore does not decide whether a smeared
quantum sector exists — every dimension has one; it decides where in ℏ
the sector sits, through W₀ = p_d(l/ξ)^d — the geometry of the
nonlocality scale.  The sharp action remains the arithmetic story
(4D collapses classically; 2D is forced quantum, below); smearing
replaces arithmetic with geometry, and the two stories meet in the
sharp limit.  All claims above the Lean-verified core are scoped to
weight ratio W₁/W₀ ∈ (0, 1), i.e. smearing below ε = 1/(1+|C₂|); the
barely-smeared regime (the one prior observed window, ε = 0.8 in 4D)
lies outside this scope and its structure is unexplained.
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

## 3′. The closure lemma and the funding theorem

**Closure Lemma.**  The wave equation at a causet C references only the
amplitudes of C and of its one-element extensions.  Hence the equations
at the root, the 2-chain and the 2-antichain involve exactly eight
amplitudes (levels 1–3) with coefficients independent of the system's
depth, and the truncation-2 subsystem is common to every depth-N
system, N ≥ 3.  Infeasibility of the subsystem is therefore inherited
by all depths.  (Proof: immediate from the definition of the sum rule;
the Lean theorem is stated over the eight amplitudes precisely so that
any depth-N solution instantiates it.)

**Funding Theorem** [Lean: smeared_truncation2_infeasible,
strengthened].  For 0 < δ < π/2, 0 < β < π/2, β < γ, 0 < η,
γ + δ < π, η + δ < π, no nonnegative amplitudes satisfy the
truncation-2 equations.  The hypothesis β < γ is W_ε(1) > 0, i.e.
ε < 1/(1+|C₂|) (1/10 in 4D): the physically-smeared regime, every
dimension.  The strengthening (the original statement demanded
γ + δ < π/2, η + δ < π/2; inspection of the proof showed the cosine
positivity is needed only for δ and β) matters because it makes the
theorem's reach exact: for in-window phases with W₁/W₀ < 1 — always
true — the hypotheses hold for ALL cover windings W₀φ < π/2, so the
theorem kills the entire sub-quadrant winding region, meeting the
numerical feasibility boundary at W₀φ = π/2 from below.

**The ℏ-window law** [MECH: trunc2_hbar_window.py].  The truncation-2
system is dimension-blind (channels {0, W₀, W₀+W₁, 2W₀}) and depends
only on the cover winding A = W₀φ, the ratio r = W₁/W₀ ∈ (0, 1), and
the offset δ.  Its feasibility region at first winding is exactly the
band A ∈ (π/2, π): both boundaries bisected to 10⁻⁹, independent of r
across [0.3, 0.75] and of the offset fraction — the open problem
posed in the previous draft (the boundary surface in (W₀φ, W₁φ, δ))
has this one-parameter answer, plus narrow slivers near A ≳ 2.2π at
offset extremes whose in-window pullback is open (probes land on
δ-aliased resonances; at 2D ε = 0.25, φ = 8π exactly, the full gate
finds a partial-support survivor, 1081/2450 cumulative — a new
object, on a measure-zero phase).  A seam to keep visible: every
resonance sits at a rational ε and a measure-zero phase, and the
physical-band verdict at generic in-window phases is untouched by
them — the resonance program is arithmetic structure in the theory,
not a claim about where the theory lives.  In window j the band reads
j ∈ (1/(4W₀), 1/(2W₀)): every prior scan is reproduced
integer-for-integer (4D ε = 0.045/0.055/0.0625 → j = 6–11/5–9/4–7),
and the law predicted in advance — pre-registered, then run — 3D
ε = 0.100 alive at j ∈ {3, 4} (it had been reported dead from a j ≤ 2
scan) and 4D ε = 0.045 alive at j ∈ {10, 11}.  One prediction failed
informatively: "2D ε = 0.25 dead at all j" (its window (0.5, 1.0)
contains no integer) returned t2-alive hits at j = 3–6, which
inspection shows are δ-aliasing artifacts of the window
parametrization landing on resonant phases, not genuine windows.
Dimension enters the law only through W₀ = p_d·ε = p_d(l/ξ)^d — the
prefactor and the geometry of the nonlocality scale decide *where in
ℏ* the quantum band sits, not whether it exists: 2D's band-bottom
sits inside the window at j = 1; 4D's physical band requires j = 4–9;
3D crosses within its band (t2 crossing at ε* = 0.1114, j = 2, i.e.
l/ξ = 0.481 — the one place the boundary is directly observable
inside a recommended band, so "3D is alive" is well-posed only once
l/ξ is fixed).

**Full-hierarchy confirmation** [MECH: smeared_2d_wave_gate.py,
smeared_crossing_and_4d_winding.py].  Truncation-2 feasibility is
necessary, not sufficient; the full wave gate (tree n ≤ 7, equations
n ≤ 6, exact LP with proven-death removal) confirms the band is
genuinely quantum at depth: 2D ε = 0.16, j = 1 — full support
2450/2450, every node branching, zero forced deaths, at all window
offsets tested; 4D ε = 0.055 (j = 5) and 0.0625 (j = 4) — full
support 2450/2450 at depth 7.  Near the upper boundary the hierarchy
bites: the 2D full-gate crossing at offset fraction 1/2 is
ε* ∈ (0.19375, 0.19406), i.e. A ≈ 0.96π, strictly inside the
truncation-2 crossing at A = π — the first observed case of
truncation-2 feasible but full-gate dead (also at ε = 0.18, offset
0.75).  The full-gate band is a hair narrower than the truncation-2
band; whether the gap grows with depth is open.

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
(l/ξ = 0.5 is ε = 1/16 exactly).  The low-winding computations
(smeared_physical_probe.py): at depth n ≤ 6 the physical band is DEAD
at windings j ≤ 3 — every window phase (k = 1, 2, 3, three offsets
each) at four ε values across [0.026, 0.063] returns empty support,
with large min|gap| (0.69–0.85), so the deaths are structural, not
resonance kills.  A scope disclosure that section 3′ resolves: those
probes never tested windings above j = 3, and the band is ALIVE at
j = 4–9 (the ℏ-window law); every "physical band is dead" statement
in this section is a W₀φ < π/2 statement.  The
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
enumerate (n ≤ 7): below the winding π/2, 4D action-phase growth
yields only broom-class dynamics, with the classical channel restored
on a quantized phase set (Lean-verified via the strengthened funding
theorem); inside the winding band (π/2, π), every dimension tested —
2D at j = 1, 4D at j = 4–6, 3D at j = 2–4 — supports covariant,
everywhere-branching, forced-quantum dynamics with full support, in
the physical smearing band.  The earlier draft's claim that the
physical 4D band is dead was a low-winding artifact of our probe
range, and is corrected here on the record.  What decides is not
dimension but the winding W₀φ = a·p_d(l/ξ)^d/ℏ: the quantum sector
exists in every dimension, in an ℏ-window set by the nonlocality
scale.  Whether the full-gate band edge (0.96π at depth 7 in 2D)
recedes further with depth, and whether the high-winding sliver
structure supports genuine dynamics beyond the resonant
partial-support survivor at φ = 8π, are open.

## 5′. Status ledger

[LEAN] 18 theorems (list in the repository file header), axiom-clean.
[MECH] all gates exit 0; enumerations validated against A000112;
unitarity telescoping at machine precision.
[PHYS] the ansatz itself; the identification of consistency with
amplitude normalization; VR-analog era boundaries in the quantum case.
Open: depth beyond n = 8; other weight systems (the trichotomy
classification); the counting-convention axiom (see Paper 3).
