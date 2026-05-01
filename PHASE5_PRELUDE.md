# Phase 5 Prelude — Pencil exploration for path (α)

**Date:** 2026-05-01
**Branch:** `phase-4` (Phase 5 work has not started; this is the pencil-exploration that gates it)
**Status:** Candidate-σ assessment for the discrete Moretti–Oppio analogue. No code yet.

## Context

`PHASE4_DIAGNOSTIC.md` identified the surviving open question (a)/(b): does causal-poset / K_F structure single out an SO(2) action / 2D commutative real division algebra on the K/P plane? Path (α) — "Moretti–Oppio analogue + K_F-based amplitudes" — proposes to close (a)/(b) by exhibiting a discrete-substrate analogue of [Moretti–Oppio (1611.09029)](https://arxiv.org/abs/1611.09029).

Before writing any Lean code for this path, this document does the analogue of Phase 0's pencil exploration: identify which group-action candidate in the existing framework is plausibly the discrete-Poincaré σ that Moretti–Oppio's argument would consume.

If a clean candidate exists, path (α) is plausible and we proceed to Phase 5 implementation. If no candidate exists, we either stop or pivot to one of paths (β)–(ε) (operational reconstruction, decoherent histories, categorical, Sorkin's quantum measure).

## Moretti–Oppio's hypotheses, restated for the discrete setting

Moretti–Oppio prove: given a real Hilbert space `H_ℝ` carrying

- **(M1)** a *locally faithful* representation of the Poincaré group;
- **(M2)** that representation is *continuous*;
- **(M3)** that representation is *irreducible*;
- **(M4)** the *squared-mass operator* `M² := P_μ P^μ` (constructed from the translation generators) has *non-negative spectrum*;

then there exists a **natural, Poincaré-invariant, unique-up-to-sign complex structure J on H_ℝ** that commutes with the entire algebra of observables. Equivalently: `H_ℝ` admits a unique-up-to-sign complex Hilbert space structure consistent with the Poincaré action.

For our discrete setting, the candidate σ must satisfy *discrete analogues* of (M1)–(M4):

- A continuous (or asymptotically continuous) group representation, locally faithful and irreducible, on the K_F-induced real Hilbert space;
- A "squared-mass-like" operator with non-negative spectrum, constructed from the abelian (translation-like) subgroup of σ.

The framework's K_F structure is finite-dimensional for fixed `(m, d)`; continuity must be recovered in the continuum / large-m limit. Phase 3's `K_F_matrix_C_isHermitian` gives us the Hermitian operator on `Fin d → α` indexing — the "history Hilbert space" for the discrete setting.

## Candidate σ's catalogued from the framework

Searched the symmetry-bearing files in `LayerA/` and `LayerB/`:
`RotationInvariance.lean`, `BoostInvariance.lean`, `LatticeReflectionPositivity.lean`,
`PoissonFaithfulness.lean`, `RepStructureForced.lean`, `SpectralGapInvariance.lean`,
`CausalFoundation.lean`, plus references in `KFComputable.lean`.

Four distinct candidate σ's emerge:

### (A) Internal SL(2,ℝ) on the K/P plane

Already formalized in `LayerB/BoostInvariance.lean` and `LayerA/RotationInvariance.lean`:

- **SO(2) rotations**: `(K, P) → (K cos θ − P sin θ, K sin θ + P cos θ)`
- **SO(1,1) boosts**: `(K, P) → (e^t · K, e^{−t} · P)`

Together they generate the SL(2,ℝ) action on ℝ². Each has a canonical Casimir:

| Subgroup | Invariant quadratic |
|---|---|
| SO(2) | `K² + P²` (Born rule) |
| SO(1,1) | `K · P` (Berry–Keating Hamiltonian) |

### (B) Spacetime Poincaré on Poisson-sprinkled Minkowski

Not directly formalized as a Lean object, but morally present in the framework:

- The underlying causal set is a Poisson sprinkling of Minkowski spacetime in dimension `d`.
- The Poisson distribution is invariant under the full Poincaré group `Pᵈ = ISO(d−1, 1)`.
- Lorentz boosts move individual sprinkled points but preserve the causal order, hence preserve the order kernel `ζ`, hence preserve K_F structurally.
- Translations preserve all of the above.

This is the standard "kinematic Lorentz invariance of causal sets" used throughout the Sorkin program.

### (C) Discrete automorphism group of K_F at fixed (m, d)

For fixed m, d, K_F has a finite automorphism group: the chamber-point permutations that preserve K_F's matrix structure. Includes the R-symmetry (chamber reflection) used in the Feshbach decomposition. **Not continuous.** Fails (M2).

### (D) Asymptotic (continuum-limit) Lorentz on K_F's spectrum

In the limit `m → ∞`, K_F's spectrum becomes continuous (per `SpectralGapInvariance.lean`'s convergence result `le/lo → (d+1)/(d−1)`). The continuous spectrum may carry a Lorentz-like action via the spectral parameter. Not formalized; would emerge from (B) at the appropriate level.

## Scoring matrix against Moretti–Oppio's hypotheses

| Candidate | (M1) loc. faithful | (M2) continuous | (M3) irreducible | (M4) M² ≥ 0 | Already formalized? | Derived from order? |
|---|---|---|---|---|---|---|
| **(A) SL(2,ℝ) on K/P** | ✓ | ✓ | ? (depends on K-P coupling) | **✗ — no SL(2,ℝ)-invariant non-negative form** | ✓ | ✗ — stipulated |
| **(B) Spacetime Poincaré** | ✓ in continuum | ✓ in continuum | needs analysis | ✓ — `M² = P_μ P^μ ≥ 0` for physical particles | ⚠ partial — Poisson isotropy formalized via Lebesgue invariance | **✓** — Poincaré IS the symmetry group of the spacetime that the sprinkling samples |
| **(C) Aut(K_F) at fixed (m, d)** | ✓ | ✗ — discrete | ? | depends on whether group has a translation-like subgroup | partial (R-symmetry) | derived |
| **(D) Continuum-limit Lorentz on spectrum** | ✓ in limit | ✓ in limit | depends | possibly ✓ | ✗ — not formalized | derived |

**Verdict: candidate (B) — spacetime Poincaré on Poisson-sprinkled Minkowski — is the primary path-(α) candidate.**

## Why (A) fails the (M4) test

The most tempting candidate is (A) because the SL(2,ℝ) action on (K, P) is already formalized and continuous. But Moretti–Oppio require the squared-mass operator constructed from the *abelian translation subgroup* of σ to have non-negative spectrum. SL(2,ℝ) has no abelian translation subgroup; its abelian subgroups are SO(2) (compact, with imaginary spectrum) and SO(1,1) (non-compact, with mixed-sign spectrum). The non-compact subgroup is the closest analogue, but its Casimir is `K · P`, which is **indefinite** (not non-negative): it can be positive, zero, or negative depending on the relative sign of K and P.

So while SL(2,ℝ) on (K, P) is structurally elegant — it's the manifest symmetry group of the K/P plane — Moretti–Oppio's argument with σ = SL(2,ℝ) does not produce a complex structure, because (M4) fails. This is a sharp finding: the existing framework's most visible continuous symmetry is *not* the right one for closing (a)/(b).

## Why (B) is the right candidate

Spacetime Poincaré has all four M-O properties in the right places:

- **(M1) local faithfulness**: any non-trivial Poincaré transformation moves Poisson points and changes the chamber-point structure; the kernel of the action is trivial in the generic-sprinkling sense. Formalizing this requires a measure-theoretic statement at the level of sprinkling distributions.
- **(M2) continuity**: Poincaré is a Lie group; its action on continuous-density sprinklings is jointly continuous. Discrete K_F approximates this continuously in the `m → ∞` limit.
- **(M3) irreducibility**: needs analysis. The chamber-point Hilbert space of a single sprinkling decomposes under Lorentz into infinitely many sectors as `m → ∞`; the question is whether the full Poincaré (with translations) produces an irreducible representation in the GNS-completion of the sprinkling-class.
- **(M4) `M² ≥ 0`**: the translation generators `P_μ` give the squared-mass `M² = P_μ P^μ`. For physical (timelike or null) momenta, `M² ≥ 0`. This is the standard Wightman-axiom condition and is automatic for sensible representations.

Crucially, **(B) is derived from order-theoretic data**: Poincaré IS the symmetry group of the spacetime that the causal-poset sprinkling samples. The order kernel `ζ` is Poincaré-invariant (causal precedence is a Lorentz scalar). K_F is built from `ζ`. So the Poincaré action on the chamber-points is induced from the action on spacetime, *not stipulated separately on (K, P)*.

If (B) gives a Moretti–Oppio-style complex structure J on the K_F real Hilbert space, then **the (K, P) decomposition of eigenvectors inherits J** — and the framework's stipulated SO(2) action on (K, P) becomes a *theorem*, not a postulate. **Closing question (a)/(b).**

## What "Phase 5 implementation" of path (α) actually looks like

If we proceed with (B), the work is:

1. **Define the framework's history Hilbert space.** Build `K_F.realHilbertSpace : Type` from the chamber-point indexing of K_F, treating it as a real Hilbert space (the usual `Fin d → α → ℝ` with K_F as the inner product or as a self-adjoint endomorphism). 1–2 weeks.

2. **Define the Poincaré action.** For Poisson-sprinkled Minkowski, define `poincare : ISO(d−1,1) → K_F.realHilbertSpace ≃ₗ K_F.realHilbertSpace`. The action is sprinkling-class-equivariant, so this involves an averaging step over the sprinkling measure. 3–4 weeks.

3. **Verify the M-O hypotheses.** (M1)–(M4) become four separate theorems on the action. (M4) is the cleanest; (M3) irreducibility is the hardest. 4–6 weeks.

4. **Apply the M-O theorem.** Either import a Lean formalization of Moretti–Oppio (which does not exist, to my knowledge), or formalize the relevant portion. The latter is itself a major project: M-O's proof uses Solèr's theorem (also not formalized) plus continuous-representation theory in real Hilbert spaces. 8–12 weeks for a self-contained version, or shorter if we can outsource the M-O step.

5. **Descend J to (K, P).** Show that the J on K_F's real Hilbert space, restricted to the K/P decomposition of any eigenvector, is the standard complex structure on ℝ². This closes (a). 1–2 weeks.

**Total estimate: 4–6 months of Lean work**, plus the standalone M-O formalization which is its own multi-month project.

This is comparable to the full Phases 1–3 of `kf-hermitian-lean`, with substantially more risk because the upstream M-O lemma is not formalized and the irreducibility analysis at (M3) has no obvious template.

## Risks identified

1. **The M-O formalization itself is not done.** The headline "discrete Moretti–Oppio analogue" is only as strong as the underlying continuum theorem we lift. If we have to formalize Moretti–Oppio first, the project doubles in scope.

2. **(M3) irreducibility is the hardest step.** For continuous unitary representations of Poincaré on the GNS-completed sprinkling Hilbert space, irreducibility requires understanding the spectrum of the translation generators in detail. There is no obvious shortcut.

3. **Sprinkling-class equivariance is delicate.** The Poincaré action is on the *measure class* of sprinklings, not on a fixed sprinkling. Formalizing this in Lean requires either (a) building a measure-class completion of `K_F.realHilbertSpace`, or (b) restricting to Poisson-invariant aggregate observables. Both add scope.

4. **Computational verification is expensive.** For `(m, d) = (4, 4)` the chamber-point space is already 70-dimensional; for any meaningful continuum-limit story, we need to handle large m systematically, which means the K_F infrastructure has to scale.

## Recommendation before committing 4–6 months

**Two concrete sub-explorations to do first**, each ~1 week, that would substantially de-risk Phase 5 implementation:

- **Sub-exploration 5.1 — Verify M² ≥ 0 numerically on small K_F instances.** For `(m=4, d=2)` and `(m=5, d=3)`, compute the spectrum of K_F and identify a translation-like operator (e.g., the diagonal-shift on chamber-points corresponding to Minkowski translation in the `t`-direction). Numerical evidence that its squared-norm is positive-semidefinite is necessary before any Lean formalization.

- **Sub-exploration 5.2 — Search arXiv for partial M-O formalizations.** Solèr's theorem in Lean / Coq / Isabelle. If any subset of the M-O chain is already formalized in some prover, that sets the upstream-import budget. If nothing is formalized, the Phase 5 estimate jumps from 4–6 months to 8–12 months.

If both 5.1 and 5.2 produce promising results — `M² ≥ 0` empirically, and at least Solèr's theorem available somewhere — I'd recommend committing to Phase 5 implementation. If either fails, we should consider path (β) (operational reconstruction) as a faster alternative even though it doesn't directly close (a)/(b).

## Decision request

1. **Confirm path (α) candidate σ = (B) spacetime Poincaré on Poisson-sprinkled Minkowski.** Or argue for (A), (C), (D), or a candidate I missed.

2. **Approve sub-explorations 5.1 (numerical M² ≥ 0 check) and 5.2 (M-O literature search) before any Lean implementation.** Or override and proceed directly to implementation.

3. **Budget acceptance.** 4–6 months of Lean work for path (α) implementation, *assuming* M-O is at least partially formalized upstream. 8–12 months if we have to build it ourselves.

4. **Scope of "discrete Moretti–Oppio."** Do we aim for the full theorem (existence + uniqueness up to sign), or just existence? The uniqueness part is what would actually close (b) — the existence part alone closes (a).
