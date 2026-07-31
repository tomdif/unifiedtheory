# Paper 2 — Existence and non-uniqueness: the covariant landscape of quantum sequential growth in two dimensions

**Draft 1, 2026-08-01.**  Companion to Paper 1 (which establishes that
2D action-phase growth is forced quantum).  Vocabulary: DEFINITIONS.md.
Scripts: wave_gate_2d.py, deep_2d.py, continuum_select_2d.py,
asymptotic_select_2d.py.

## Abstract

We show that covariant quantum sequential-growth dynamics carrying the
2D Benincasa–Dowker action phases exist, are maximally abundant, and
cannot be made unique by any amount of consistency.  Amplitude-level
general covariance reduces the theory to a linear "wave equation on the
causet tree" — one nonnegative amplitude per isomorphism class, one
complex equation per supported causet, with the Markov sum rule
telescoping to exact unitarity level by level.  At every generic phase
the solution family has full support (every finite causal set through
n = 8 carries amplitude in some member), verified by exact linear
programming with proven-death removal loops; the unique dead phase is
the Born-quadrature point π/4 (two-line certificate).  The family's
affine dimension grows with depth (234, 1553, 12435 at depths 6, 7, 8)
because the equations couple adjacent levels only; the sole mechanism
by which depth could constrain the past — death cascades reaching back
through removed terms — is verified never to fire at any depth checked
(every witness-zero individually LP-refuted as a forced death); the
adjacent-level coupling structure itself is exact.  Confinement to the manifoldlike sector is *exactly* free:
killing every causet of order dimension ≥ 3 (the crown family and its
relatives, 0.9% → 4.4% → 13% of causets at n = 6, 7, 8) removes nothing
else, at every depth checked — the two-dimensional orders are closed
under the wave equation.  A covariant, unitary, forced-quantum dynamics
whose universe never develops non-2D-embeddable geometry therefore
exists through n = 8; and the growing dimension counts show that
neither consistency, nor covariance, nor manifold confinement — nor all
three together — can select the dynamics.  Existence is abundant;
selection requires new physics (Paper 3).

## 1. The wave equation and its exactness properties

Covariance ⟺ coboundary ⟺ Σ μ Ã(child) e^{igφ} = Ã(parent) (derivation
in DEFINITIONS.md).  Three exactness properties make the numerics
theorem-adjacent: (i) telescoping unitarity: Σ_stems ext·Ã·e^{i(S−1)φ}
= 1 exactly at every level (machine residuals ≤ 3×10⁻⁹ at depth 8);
(ii) support downward-closure is forced, and future cones are the
descendant sets of the growth tree; (iii) all constraints are linear,
so feasibility, forced deaths (max Ã = 0), and dimension counts are
exact LP/rank computations, not optimizations.

## 2. Existence: full support at generic phases

At φ ∈ {π/6, π/3, 5π/12, 0.50, 0.90, 1.20} the exact search converges
to full support at depth 6 (405/405) and persists at depth 7
(2450/2450) and depth 8 (level-7 equations active; all causets
supportable).  The 2D root forces equal-amplitude branching; no
deterministic channel exists; eleven distinct action values among the
5-stems give genuine relative phases between geometries.  The unique
dead phase π/4 carries a hand-checkable infeasibility certificate (the
μ = 2 kill; PI4_CERTIFICATE.md) — notable because it is the phase at
which the probability-from-action reading p = cos²(ΔS/ℏ) is most
literal.

## 3. Non-uniqueness is structural

Dimension counts: 234 (depth 6), 1639 (depth 7), 14548 (depth 8,
unrestricted).  The equations couple levels (n, n+1) only; therefore
depth constrains earlier amplitudes exclusively through reach-back
death cascades, and none occur: every witness-zero is liftable (LP-
verified individually).  The freedom is not gauge: distinct members
assign genuinely different stem statistics (Paper 3, steering).  Any
selection must be an additional principle.

## 4. Manifold confinement is exactly free

Order dimension ≤ 2 is the natural finite-n proxy for 2D-manifoldlike
compatibility (2D causal sets are 2-orders); it is monotone under
induced subposets, hence automatically closed under downsets and
sub-sampling.  Killing all dim-≥3 causets (3 at n = 6; 89 at n = 7;
2205 at n = 8) triggers zero collateral deaths at every depth: the
final support is exactly the two-dimensional orders (315/318,
1956/2045, 14794/16999).  Consumed dimensions: 86 (depth 7), 2113
(depth 8) — the selector's bite tracks the growing non-manifold
fraction — while the confined family's own dimension still grows
(1553 → 12435): confinement will consume an ever-larger share without
ever reaching uniqueness.  Conjecture (proof path open): every 2-order
possesses 2-order children realizing the phase cone its equation
requires — which would make the closure exact at all n.

## 5. Discussion

Two readings coexist.  Constructively: where classical growth dynamics
notoriously fail to produce manifoldlike causets, the quantum measure
admits dynamics in which non-manifoldlike geometry never carries
amplitude at all — an existence result the classical theory cannot
match, aligned with (and sharpening) the interference-suppression
results of the causal-set path-integral literature.  Critically: the
same computations show the landscape is irreducible by consistency-type
reasoning, so the ansatz-class does not by itself predict spacetime; it
permits it.  The selection problem — what physics chooses the member —
is taken up in Paper 3, where locality, factorization, and stationarity
are eliminated with certificates and a coarse-graining fixed point
survives.

## Status ledger

[MECH] all results exit-0 scripts with A000112-validated enumeration,
LP feasibility/rank exactness, per-death LP verification.  [LEAN] the
parity mechanism and the π/4-adjacent arithmetic (Paper 1 file).
[PHYS] the ansatz; the dim ≤ 2 proxy for manifoldlikeness at small n.
Open: the 2-order-closure conjecture; depth ≥ 9; measure-level (weaker)
covariance in place of amplitude-level.
