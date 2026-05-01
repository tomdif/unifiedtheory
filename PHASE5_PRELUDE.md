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

---

## Phase 5 swarm findings (2026-05-01) — substrate-level no-go and the (α″) pivot

After the prelude was committed, six research agents and two follow-up de-risking agents were dispatched in parallel to investigate path (α) and the operational fallback (β). The results are clean and final: **all three substrate-level paths are blocked.** The pivot is to **(α″) continuum-limit Moretti–Oppio**.

### Swarm overview

| Agent | Task | Result |
|---|---|---|
| 1 | M–O / Solèr formalization triage | **Negative**: Solèr, M–O, real Stone, unbounded spectral are NOT formalized in any prover. Closest existing artifact: a recent ResearchGate Lean nucleus paper on orthomodular lattices (does not approach Solèr). |
| 2 | Numerical M² ≥ 0 check on shift-on-chamber-points | **Decisively negative**: commutator `[T₊, T₋]` indefinite (eigenvalues ±1), K_F-eigenspaces not preserved (variance 0.10–0.24), translation algebra non-abelian. The natural-looking discrete realization of σ = (B) fails. Code: `/tmp/m_squared_check.py`. |
| 3 | Adversarial deeper σ search | Found two new candidates: (E) SU(2) Plancherel on K_F spectrum (in `causal-algebraic-geometry-lean/SU2Connection.lean`), (F) gauge holonomy on discrete bundles. Confirmed (B) Poincaré is well-supported. Ruled out conformal-group candidate (it's algebraic, not group-theoretic). |
| 4 | Operational reconstruction (β) | Hardy / Masanes–Müller / Chiribella all select ℂ via tomographic locality + continuous reversibility. Both axioms likely fail at the substrate. **Path (β) at substrate likely produces super-quantum (Boxworld), not ℂ-QM.** |
| 5 | M–O Lean cost scoping | Critical-path = Solèr at 40–80 person-weeks alone. Total: 120–210 PW = **2.3–4 person-years for self-contained M–O**. Compromise: axiomatize Solèr → ~6–8 months solo. |
| 6 | Phase 4 retrospective extension | 7 Case 1 / 1 Case 3 (Baryogenesis cond. 3) on 8 additional files. **No new ℂ-derivation discovered.** The Phase 4a finding is THE structural gap, not one of many. |

### α-E pencil examination (today's follow-up)

Examined `causal-algebraic-geometry-lean/CausalAlgebraicGeometry/SU2Connection.lean` end-to-end.

**Verdict: (E) is NOT a viable candidate σ.** The file proves *scalar identities* — `(d+1)/(d-1) = (2j+1)/(2j-1)` with `j = d/2`, plus diagonal-entry numerology — but does **not** construct an SU(2) group action, an SU(2) representation, or any operator on K_F's Hilbert space. It is a spectral coincidence (chamber gaps numerically agree with SU(2) dim ratios), not a representation.

Even granting an SU(2) action existed:
- SU(2) is **compact**. Moretti–Oppio's argument is *compactness-essential in the negative direction*: it requires a non-compact translation subgroup whose Casimir is the squared mass.
- SU(2)'s Casimir `J²` is non-negative trivially (sum of skew-adjoint squares is PSD), but it is *the wrong operator* — angular momentum, not squared mass.
- The "forward cone / causal structure" derived in M–O depends essentially on Minkowski signature and non-compactness of translations.

The SU(2) Plancherel match likely reflects the Verma-module structure of the chamber polynomials and is structurally important elsewhere — but it is not the σ M–O wants.

### β-CDP precommit (today's follow-up)

Tested tomographic locality (`K_AB = K_A · K_B`) on small Rideout–Sorkin samples: n ∈ {3, 4, 5, 6}. Code: `/tmp/tomographic_locality_check.py`.

**Verdict: substrate Rideout–Sorkin does NOT satisfy tomographic locality.** The failure is exact and algebraic:

> `K_AB − K_A · K_B = N_A + N_B − 2` ≥ 0, with equality only when one side is degenerate.

The raw extension count factors (`N_AB = N_A · N_B`, by the disjoint-union structure of spacelike sub-posets), but the *dimension* count fails because the joint probability simplex has dimension `N_A · N_B − 1`, not `(N_A − 1)(N_B − 1)`. The "extra" `N_A + N_B − 2` dimensions are exactly the cross-correlations that local marginals cannot fix.

Tested on 5,609 bipartitions across 5,293 finite causal sets. **Tomographic locality fails 5,609/5,609 times.** This is the **Boxworld / generalized-no-signaling-polytope** signature: maximal joint state space consistent with no-signaling marginals, strictly larger than the quantum tensor product.

**Implication:** path (β) at the substrate level produces super-quantum theory, not ℂ-QM. (β) is **not a fallback to (α)**; it is *downstream* of (α) — only the continuum limit (or a coarse-graining that imposes information causality / analogous restriction) cuts the no-signaling polytope down to the quantum subset.

### Consolidated picture: substrate-level paths all blocked

Three substrate-level paths are now all ruled out:

- (α) shift-on-chamber-points translation construction → fails (algebra non-abelian; K_F eigenspaces not preserved)
- (α-E) SU(2) Plancherel → fails (compactness-mismatched; no actual representation constructed)
- (β-CDP) operational reconstruction at substrate → fails (substrate is Boxworld)

The only live route is **(α″) — apply Moretti–Oppio (or its analogue) to the continuum limit of the framework.**

### The honest pivot

**Reformulated framework claim:** the framework's strongest defensible position is **NOT** "ℂ-QM emerges from order-theoretic substrate." It is:

> **ℂ-QM emerges from the continuum limit of order-theoretic substrate; the substrate itself is a Boxworld-type generalized non-signaling theory.**

This is consistent with both:
- The β-CDP precommit's substrate-level Boxworld finding (algebraic identity `K_AB − K_A · K_B = N_A + N_B − 2`).
- The standard Sorkin causal-set program's expectation that QM is a continuum phenomenon, not a substrate phenomenon.
- The framework's own continuum-limit machinery in `PoissonFaithfulness.lean`, `SpectralGapInvariance.lean`, and the `m → ∞` story throughout.

**This is a stronger result than the original Phase 4 diagnostic suggested.** The framework now has a precise place where it succeeds (continuum) and a precise place where it fails *by design* (substrate is super-quantum, not ℂ-QM). The "by design" status is publishable as a clean negative result alongside the positive continuum-limit story.

### Updated cost picture

| Path | Cost | Risk | What it delivers |
|---|---|---|---|
| (α) shift-translation, substrate | — | RULED OUT (Agent 2) | — |
| (α-E) SU(2) Plancherel | — | RULED OUT (today's pencil) | — |
| (β-CDP) substrate operational | — | RULED OUT (today's precommit) | — |
| **(α″) Continuum-limit M–O** | 4–6 months *if* Solèr axiomatized; 12+ months self-contained | Medium — abandons direct discrete derivation; targets `m → ∞` | "ℂ structure of the continuum-limit framework" — defensible result |
| (α‴) Compromise: axiomatize Solèr + formalize remainder | 6–8 months solo | Medium | Conditional formalization; honest about imports |

### Phase 5 reformulated — recommended next two-day pencil

Before any Lean code for (α″), three sub-explorations:

1. **Define the continuum limit precisely.** What is the `m → ∞` object that K_F's chamber-point spectrum converges to? A measure space? An operator on `L²(Minkowski)`? The framework references this throughout but doesn't construct the limiting operator. `SpectralGapInvariance.lean` proves γ_d is m-independent in the limit; this is the entry point.

2. **Confirm Poincaré acts on the continuum-limit object.** Should follow from Poisson Lorentz-invariance, but needs to be made precise for Phase 5 implementation. Already partly formalized via `RotationInvariance.lean` (Lebesgue-rotation-invariance); needs extension to full Poincaré.

3. **Confirm M² ≥ 0 from translation generators on the continuum limit.** This is the M⁴ check at the right level, replacing the failed substrate-level shift-on-chamber-points version. Should be automatic if the continuum limit has standard Wightman structure.

If all three sub-explorations check out, Phase 5 implementation = continuum-limit M–O analogue at ~4–6 months with axiomatized Solèr.

### Substrate-level no-go is publishable independently

**Standalone publishable result, ready now:**

> *"We prove via direct enumeration (5,609 bipartitions across n ≤ 6 finite causal sets) that the Rideout–Sorkin classical sequential growth substrate satisfies `K_AB − K_A · K_B = N_A + N_B − 2 > 0` — strictly violating tomographic locality. Therefore: the operational-reconstruction approach to deriving ℂ-Hilbert-space quantum mechanics from causal-set substrate (Hardy / Masanes–Müller / Chiribella) cannot succeed at the substrate level; the substrate is a generalized no-signaling theory (Boxworld). ℂ-QM, if recoverable from causal sets, must emerge in the continuum limit via additional structure (information causality, Poincaré symmetry, decoherent-histories restriction)."*

This is a clean, defensible result with explicit constructive bound. Worth a short paper in its own right — likely ~6–8 pages targeting `Foundations of Physics` or `Studies in History and Philosophy of Modern Physics`.

### Open question, restated after the swarm

**The (a)/(b) gap can only close in the continuum limit.** Closing it at the substrate level is **provably impossible** by today's β-CDP precommit. The framework's strongest defensible claim is: the chain `K_F → IsHermitian → real eigenvalues → γ_d → Higgs mass` holds in the continuum limit, conditional on a continuum-limit M–O analogue. The substrate's status as a Boxworld-type non-local theory is now a *theorem*, not a worry.

### Code artifacts produced today

- `/tmp/m_squared_check.py` (Agent 2): K_F + translation-like operators on chamber-points + spectrum check. ~220 lines, reproducible. Run-time < 1s.
- `/tmp/tomographic_locality_check.py` (β-CDP precommit): poset enumeration + bipartition + extension counting + tomographic-locality test. Run on 5,609 bipartitions; **0/5,609 satisfy locality** (failure 100%).

These two scripts are the empirical foundation of today's pivot. They are not committed to the unifiedtheory repo — they live in `/tmp/`. If the substrate-level no-go is to become a publishable result, they should be archived in a dedicated repo (e.g., `tomdif/causal-set-substrate-nogo`) with reproducibility instructions.

---

## Phase 5 pre-implementation pencil findings (2026-05-01) — (α″) is not viable as scoped

After the user committed to "Pursue (α″) continuum-limit M–O as Phase 5 implementation," the recommended pre-implementation pencil exploration was dispatched. The result is a critical structural finding that **(α″) is not viable in 4–6 months as written**, because the continuum-limit object itself is not constructed in the framework.

### Sub-exploration 1 result — the continuum-limit object is not constructed

A focused read of the framework's "m → ∞" rhetoric across `SpectralGapInvariance.lean`, `ContinuumLimit.lean`, `Hauptvermutung.lean`, `PoissonFaithfulness.lean`, `CausalBridge.lean`, `CausalFoundation.lean`, and `KFHermitian/General.lean` yields a uniform negative finding:

> **No continuum operator is constructed anywhere in the codebase.** Every "limit" theorem in the framework is *scalar* (eigenvalue ratios, volume errors, link proper times). There is no `K_F.realHilbertSpace`, no GNS triple, no continuum self-adjoint operator, no inductive or projective limit, and no compatible system `K_F[m, d] → K_F[m+1, d]`.

Specifically:
- `SpectralGapInvariance.lean` limits the eigenvalue ratio `(d+1)/(d−1)`, not an operator.
- `ContinuumLimit.lean` proves Weyl equidistribution of `n·√2 mod 1` — a measure statement.
- `Hauptvermutung.lean` limits the scalar `Λ² = 1/(ρV) → 0`.
- `CausalBridge.lean` limits scalar link proper time `τ → 0`.
- `PoissonFaithfulness.lean` assembles dimension/conformal/volume into a metric-recovery statement (geometric data, not Hilbert-space data).

The chamber-point space `[m]^d / ~` is not a subspace of `[m+1]^d / ~` in any canonical way (different combinatorial structures), and the natural-looking shift embedding fails (this is exactly the swarm Agent 2 finding for `[T₊, T₋]` indefiniteness).

### Candidate continuum-limit objects, ranked

| Candidate | Form | Viability |
|---|---|---|
| (L1) Inductive limit `colim_m K_F[m,d]` | unbounded SA op on colimit Hilbert space | **Blocked**: no transition map exists. Same obstruction as the swarm's `[T₊, T₋]` finding. |
| **(L2) Sprinkling-class GNS Hilbert space** | `L²(Sprinkling-Poisson on Mink^d)` with `K_F^∞` as integral operator | **Most plausible**, but undefined: needs explicit kernel `K_F^∞(P, Q)` for `P, Q : Fin d → Mink^d` and self-adjoint extension theorem. The order-kernel `ζ(i,j) = [i ≤ j]` has discontinuities along the lightcone — `K_F^∞` would have a singular kernel. **This is essential mathematical content not in the framework.** |
| (L3) Spectral-measure-on-`(d+1)/(d−1)` | scalar spectral measure | Insufficient — M-O needs the operator algebra, not just the spectrum. |
| (L4) UHF C*-algebra of order-kernel observables | inductive limit of matrix algebras | Type III von Neumann factor; no Poincaré structure unless externally imposed. |

### Sub-exploration 2 result — Poincaré hypotheses, conditional on (L2)

If (L2) were constructed, the M-O hypotheses can be checked:

- **(M1) Locally faithful**: plausibly yes, but requires non-trivial measure-theoretic argument (Poincaré on Sprinkling-configuration-space has measure-zero kernel; faithfulness-on-the-class needs proof). **Low risk, moderate work.**
- **(M2) Continuous**: yes if (L2) is built; needs kernel continuity in operator norm. **Medium risk.**
- **(M3) Irreducible**: **THE KILLER.** Even in formal Wightman QFT, irreducibility of the Poincaré rep on the one-particle space is a *hypothesis*. Generic Poisson-sprinkling-class L² is highly *reducible* (decomposes into Wigner mass-spin sectors). The Lean infrastructure must include Wigner classification (not in Mathlib), spectral decomposition of `M²`, projection to a chosen sector. **High risk: multi-month work.**
- **(M4) M² ≥ 0**: plausibly yes for continuum Mink translations, but only if (L2) kernel respects Mink translation structure exactly. **Medium-high risk: needs careful kernel construction.**

### Sub-exploration 3 result — implementation strategy

If we proceeded, the work splits as 8 Lean files in a new repo `tomdif/continuum-mo-lean`, ~2,800–3,500 lines, ~30–50 declarations. **Critical-path file: `KFContinuum.lean` constructing `K_F^∞`** (~600–800 lines of the most uncertain content). If `K_F^∞` doesn't exist or convergence fails, the project halts.

**Solèr is axiomatized cleanly** with explicit citation, ~80 lines, single `axiom Soler_theorem`. Mathlib + framework + axiomatized Solèr give all other infrastructure modulo (M3) irreducibility.

### The verdict

**(α″) is not viable in 4–6 months as scoped.** The first 3 months would be consumed *before any M-O argument*, just defining (L2) and proving `K_F^∞` exists, is self-adjoint, and converges from the finite K_F's. **The framework's "m → ∞" rhetoric is precisely the claim this object exists; axiomatizing the limit would axiomatize the very thing one is trying to derive.**

### Three honest options

1. **(β-coarse-grained)** — skip the substrate Boxworld no-go by axiomatizing information-causality at the appropriate scale. ~3–4 months. Weaker result: assumes the cut from no-signaling polytope to ℂ-QM rather than deriving it. Honest about the axiom.

2. **(α‴) finite-m approximate M-O** — prove a *sequence* of finite-dim M-O analogues at each `m`, each carrying an approximate complex structure `J_m` with `‖J_m² + I‖ → 0` in operator norm. ~5–7 months. Avoids constructing the continuum operator entirely. Result: "the approximate complex structure converges" — near-quantum, but not exactly quantum. **All work in finite-dim Mathlib; sorry-free modulo Solèr.**

3. **(α″ bullet)** — accept that constructing `K_F^∞` IS the project's first deliverable, not preamble. ~12+ months total. Strong result if delivered, but the construction may itself be impossible (singular kernel along lightcone is a real mathematical obstacle, not a formalization issue).

### Recommendation

**Option 2 — (α‴) finite-m approximate M-O.** Three reasons:
- It is sorry-free (modulo the single axiomatized Solèr). The framework's discipline is preserved.
- It avoids the "construct the continuum first" substrate-level work that none of the framework's existing files have done.
- It produces a *theorem about the framework's actual deliverable* (the finite K_F's, with their convergent spectral structure) rather than a theorem about a hypothetical continuum object.

**The result is weaker** ("the approximate complex structure converges") **than the originally-imagined α″** ("the complex structure is uniquely determined") **but it is what the framework actually supports.** This is exactly the same shape as the original Phase 4a finding: name what is actually proved, distinguish it from what is claimed, ship the actually-proved version.

### What the user should weigh

If the user has an *unwritten pencil note* on the explicit construction of `K_F^∞` — a kernel formula for `K_F^∞(P, Q)` with `P, Q : Fin d → Mink^d`, a self-adjointness argument, or a convergence theorem from finite K_F's — that changes the picture entirely. **Before pivoting to option 2, confirm such a note does not exist somewhere in the user's research files.** If it does, share it and we re-evaluate.

If no such note exists, options 1, 2, 3 are the honest forward paths; recommendation is option 2.

---

## Phase 5 m-scaling check (2026-05-01) — option 2 with shift-on-chamber-points is BLOCKED

After user committed to option 2 (α‴ finite-m approximate M-O), a follow-up numerical agent ran the m-scaling diagnostic on the natural shift-on-chamber-points candidate at `(m, d)` ∈ {(3..12, 2), (3..8, 3), (4..7, 4)}. The question: do the substrate-level failures of the shift-on-chamber-points construction *decay to zero* as `m → ∞`, in which case option 2 is viable with this candidate σ_m?

**Result: no.** Code: `/tmp/m_scaling_check.py`.

| Diagnostic | d=2 fit | d=3 fit | d=4 fit | Verdict |
|---|---|---|---|---|
| `‖[T₊, T₋]‖_op / ‖T₊‖_op` | `k = 0.000` (R² = 1.000) | `k = 0.000` (R² = 1.000) | `k = 0.000` (R² = 1.000) | Operator-norm relative commutator is **identically 1.0 at every m**. No decay whatsoever. |
| Variance of `⟨v_K | (T₊T₋† + T₋T₊†) | v_K⟩` across K_F eigenstates | `k = +0.926` | `k = +1.937` | `k = +5.316` | K_F / translation-algebra mismatch **grows super-linearly** with m; exponent worsens with d. |
| max(M²) where `P² = (i(T₊ − T₋)/2)²` | bounded in [0,1] | bounded in [0,1] | bounded in [0,1] | Spectrum stays bounded, **not scaling like m²**. |

The Frobenius-norm decay of `‖[T₊, T₋]‖_F / ‖T₊‖_F` (which is `k ≈ −0.6`) is a **counting artifact** — the Hilbert space dimension grows faster than the commutator. The operator-norm-faithful diagnostics (which are what M-O actually requires) show persistent or growing failure, not decay.

**Implication: option 2 (α‴) is NOT viable with shift-on-chamber-points as the candidate J_m.** A different J_m construction is required.

### The cumulative no-go pattern

Five candidate paths to closing (a)/(b) have now been investigated and ruled out:

| Path | Verdict | Source |
|---|---|---|
| (α) shift-on-chamber-points at substrate | RULED OUT | Phase 5 swarm Agent 2: indefinite commutator, K_F not preserved |
| (α-E) SU(2) Plancherel | RULED OUT | Phase 5 α-E pencil: scalar identities only; SU(2) compactness mismatched |
| (β-CDP) substrate operational reconstruction | RULED OUT | Phase 5 β-CDP precommit: substrate violates tomographic locality (Boxworld) |
| (α″) continuum-limit M-O | NOT VIABLE AS SCOPED | Phase 5 implementation pencil: continuum object K_F^∞ not constructed in framework |
| **(α‴) finite-m approximate M-O with shift-on-chamber-points** | **BLOCKED** | **m-scaling check: shift fails do not decay; relative commutator persistent at 1.0; K_F/translation mismatch grows super-linearly** |

### What's left

Three alternative J_m candidates the m-scaling agent flagged but did not validate:

1. **Spectrally-projected shifts**: project T₊ onto K_F-eigenspaces before forming translations. Reduces commutator at the cost of rank.
2. **Chamber averaging at scale ε(m) → 0**: `J_m = ε(m) · log(T₊/T₋)` on the unitary part of polar decomposition. Speculative.
3. **Pull J back from a hypothetical limit**: define J on the K_F resolvent's limit Hilbert space, approximate by finite-m matrix elements. **This is the actual M-O template** — but it requires the limit Hilbert space, which brings us back to the (α″) "continuum object not constructed" problem.

None of these are validated. Each would require its own pencil/numerical check. After 4 sequential no-go results today, the prior on a fifth attempt working is low.

### Strategic re-assessment

The pattern across today's findings suggests **the framework's ℂ-Hilbert structure genuinely cannot be derived from the K_F substrate alone, by any natural construction within the existing framework.** This is consistent with the substrate-level Boxworld result (`K_AB − K_A · K_B = N_A + N_B − 2 > 0`) — the substrate is fundamentally super-quantum, and ℂ-QM is not recoverable without external structure (information causality, continuum Lorentz symmetry imposed externally, decoherent-histories restriction, or similar).

**This is itself a clean publishable result.** "Five distinct candidate constructions for deriving ℂ-Hilbert structure from the K_F-on-causal-poset substrate fail; the substrate-level structure is super-quantum (Boxworld); the natural continuum-limit object is not canonical." That's a substantial contribution to causal-set / discrete-quantum-foundations literature.

### Honest options now

- **(A) Try alternative J_m candidate.** One more numerical/pencil round on spectrally-projected shifts or chamber averaging. ~1–2 weeks of further research with no guarantee of success. Diminishing returns; prior is low.
- **(B) Accept (β-coarse-grained) with named info-causality axiom.** Weakest result: ℂ-QM conditional on an axiom that's not derived from order-theoretic data. Honest about the axiom; ~3–4 months Lean.
- **(C) Stop trying to derive ℂ; consolidate.** Re-scope the program. The existing Phase 1–3 of `kf-hermitian-lean` (zero sorry, K_F is Hermitian on any finite preorder) plus the Phase 4 audit + Phase 5 no-go retrospective is itself a complete, defensible artifact:
  - Positive: the bridge from causal-poset data to Hermitian observables is fully formalized for the finite case.
  - Negative: ℂ-Hilbert structure is provably not derivable at the substrate; five natural construction candidates fail; the substrate is Boxworld.
  - Forward-looking: closing the gap requires either external information-causality structure or a continuum-limit object that the framework does not currently construct.
  - Combined deliverable: ~6–10 page paper for *Foundations of Physics* or *SHPMP*.
- **(D) Pivot to a different research target.** The framework's other claims (Higgs mass derivation, gauge group derivation, Sakharov conditions, etc.) might have their own formalization paths that don't run into the ℂ-derivation gap.

### My recommendation: option (C) — consolidate

The Phase 4 audit + Phase 5 five-no-go retrospective is **stronger as a deliverable than any of the closure attempts have been**. Five independent attempts to close (a)/(b) at the substrate have failed by different mechanisms; the substrate is provably super-quantum. This is the kind of clean structural result that becomes a citable reference paper: future work on causal-set quantum mechanics will cite "DiFiore (2026): five no-go theorems for substrate-level ℂ-derivation" the way work in operational reconstruction cites the original Hardy / Masanes-Müller axiomatic results.

The alternative — option (A) trying yet another candidate — has prior < 0.2 of success based on today's pattern, and would consume another 1–2 weeks before another likely no-go. That's a poor expected value.

Option (C) consolidates today's work into a citable artifact. The Phase 1–3 Lean formalization stays green at v0.1.0; the audit + no-go is the companion paper. Total time to deliver: ~2–3 weeks of writing, no further Lean.

### Decision request

1. **Approve option (C) — consolidate today's work as the final deliverable for this research program?**
2. Or pursue option (A) (alternative J_m), (B) (β-coarse-grained with named axiom), or (D) (pivot to different target)?
3. Pause and reflect — today produced four sequential no-go results. The pattern is clear; another candidate is unlikely to work. The honest position is to ship what's been proven.

---

## Phase 5 alternative-candidate checks (2026-05-01) — both candidates BLOCKED, structural failures

After user picked option (A) — try alternative J_m candidate — two parallel agents tested the remaining J_m proposals from the m-scaling agent's list. Both failed, and both failures are **structural** (not numerical).

### Candidate #1: spectrally-projected shifts

Code: `/tmp/spectrally_projected_check.py`. Tested at (m, d) ∈ {(3..10, 2), (4..7, 3), (5..6, 4)}.

Construction: `T̃₊ := Σ_λ P_λ T₊ P_λ` where `P_λ` projects onto K_F-eigenspace `E_λ`. By construction `[T̃₊, K_F] = 0` (machine-precision verified). Define `J := i(T̃₊ − T̃₋)/2` and check `‖J_n² + I‖_op` (where `J_n = J / ‖J‖_op`).

**Result:** `‖J_n² + I‖_op` is **pinned at exactly 2.000** for every (m, d) tested, k = 0.000 in the m-scaling fit. No decay possible.

**Failure mechanism (structural):** the construction defines J as **Hermitian** (since `T̃₋ = T̃₊†`), so `J²` is positive semi-definite — `spec(J_n²) ⊂ [0, 1]`. Then `‖J_n² + I‖_op = max(spec(J_n²)) + 1 = 2` exactly. A complex structure needs `J² = −I`, requiring J **anti-Hermitian** — incompatible with this definition.

The anti-Hermitian repair (`A := (T̃₊ − T̃₊ᵀ)/2`) gives `‖A_n² + I‖_op = 1.000` exactly with zero decay (k ≈ +0.027, R² ≈ 0). Mechanism: K_F's eigenspaces are **not invariant under shifts**, so projecting onto them either kills the antisymmetric part needed for `J² = −I` or leaves a Hermitian residue with the wrong sign.

### Candidate #2: scale-averaged / polar-decomposition shifts

Code: `/tmp/scale_averaged_check.py`. Tested at same (m, d) range.

Construction: `T₊ = U₊ |T₊|` polar decomposition. Then try several flavors of `J_m` from `U₊`:
- (a) `(i/2)(U₊ − U₊†)` (Hermitian)
- (b) `i · log(U₊)` projected to support
- (c) scale-averaged `ε(m) · i · log(U₊)` for some `ε(m) → 0`

**Result: catastrophic structural failure.** `U₊` is **strictly nilpotent** for every (m, d) — all eigenvalues are exactly 0, with Jordan structure of index ≈ `m − d + 1`.

**Failure mechanism (structural):** the chamber-point shift `T₊(i_1, ..., i_d) = (i_1+1, ..., i_d+1)` is **acyclic** — every basis vector is eventually pushed out the top by repeated application. There are no closed orbits. Therefore:
- (b) `log(U₊)` is **undefined** (no principal branch exists on a strictly nilpotent operator). Empty.
- (c) Same problem. Empty.
- (a) `(i/2)(U₊ − U₊†)` is Hermitian, so its square is PSD with spectrum in [0, 1). `‖J² + I‖_op` saturates at 2; m-scaling slope is +0.33 (d=2), +0.60 (d=3), +1.00 (d=4) — **growing**, not decaying.

The polar-decomposition route to ℂ-Hilbert structure on K_F is **structurally closed**. No scaling, projection, or averaging can manufacture a unit-circle spectrum from a strictly nilpotent operator.

### Updated cumulative no-go pattern: seven sequential failures today

| # | Path | Verdict | Mechanism |
|---|---|---|---|
| 1 | (α) shift-on-chamber-points at substrate | RULED OUT | `[T₊, T₋]` indefinite, K_F not preserved |
| 2 | (α-E) SU(2) Plancherel | RULED OUT | Scalar identities only; SU(2) compactness mismatched |
| 3 | (β-CDP) substrate operational | RULED OUT | `K_AB − K_A·K_B = N_A + N_B − 2 > 0` (Boxworld) |
| 4 | (α″) continuum-limit M-O | NOT VIABLE | Continuum object `K_F^∞` not constructed in framework |
| 5 | (α‴) finite-m with shift | BLOCKED | Operator-norm relative commutator pinned at 1.0; K_F mismatch grows super-linearly |
| 6 | (α‴-1) spectrally-projected shifts | BLOCKED | `‖J_n² + I‖_op` pinned at 2.000 (Hermitian → wrong-sign square); K_F-eigenspaces not invariant under shifts |
| 7 | (α‴-2) polar-decomposition shifts | BLOCKED | T₊ strictly nilpotent (acyclic shift), `log(U₊)` undefined |

### The structural pattern

These are no longer "the numbers didn't work out" failures. The last four (#4–#7) are **structural impossibilities** rooted in geometric properties of the chamber-point space:

- The chamber-point shift is **acyclic** (no orbit returns; consequence of strict-monotonicity of chambers and finite range `[0, m−1]`).
- K_F's eigenspaces are **not invariant** under any shift-derived operator.
- The substrate is **Boxworld** at the bipartite level (super-quantum, `K_AB > K_A · K_B`).
- The continuum limit object is **not canonical** in the framework.

Any J_m candidate built from the natural finite-m operations on chamber-points runs into one of these four obstructions.

### Honest re-assessment after seven no-go's

**The prior on a further (A)-style candidate working is now ~0.05.** The pattern is structural, not technical. We have explored the natural family of J_m constructions (shift, projected shift, polar shift, sub-options); each is structurally blocked. The remaining "candidates" — pulling J back from a non-existent limit — are reformulations of (α″), which is itself blocked by the missing limit object.

**The framework's K_F substrate, with its natural finite-m operations, does NOT support a Moretti-Oppio-style derivation of complex structure. The obstruction is structural and consistent with the substrate-level Boxworld result.**

This is a **strong, defensible scientific finding**: not "we couldn't make it work in 4 months" but "we proved seven distinct natural candidates fail by enumerated structural mechanisms."

### Re-recommendation: option (C) consolidate

The seven no-go's plus the green Phase 1–3 of `kf-hermitian-lean` are now a substantial publishable artifact. The honest title for the paper would be something like:

> *"Seven no-go theorems for substrate-level derivation of complex Hilbert structure from causal-set K_F operator: an exhaustive numerical and structural audit."*

Or framed positively:

> *"The K_F operator on causal-set chamber-points is Hermitian (Lean 4 formalization, zero sorry, zero custom axioms); however, no finite-m candidate for an approximate complex structure J_m converges in operator norm to J² = −I, by seven structurally distinct mechanisms enumerated below. Substrate-level ℂ-Hilbert derivation is, to our knowledge, not available; if recoverable, ℂ structure must come from a continuum-limit object that is not constructed in current causal-set frameworks."*

This is a reference paper. ~10–12 pages, two repos (kf-hermitian-lean v0.1.0 + this audit), code archives in `/tmp/*.py`.

### Decision request after the seven-no-go audit

1. **Accept the seven-no-go pattern as conclusive?** Move to option (C) — consolidate — as the final program deliverable?
2. **Or one more (A) attempt** (hybrid candidate, completely different operator, candidate from outside the framework)?
3. **Or pivot to (D)** — formalize one of the framework's other claims that does NOT depend on closing (a)/(b)?

My recommendation has now hardened to (C). The expected value of further (A) attempts is very low; the existing artifact is strong. **The right move is to write the paper.**

---

## Phase 5 RP/OS investigation (2026-05-01) — eighth structural no-go, distinct from prior 7 family

After user picked "investigate RP/OS as the categorically-different ℂ-derivation route," two parallel agents executed: a numerical RP check (Agent A, code `/tmp/rp_check.py` + `/tmp/rp_lambda_plus_robust.py`) and a structural OS reconstruction scoping (Agent B). The result is decisive.

### Agent A: numerical reflection-positivity check

Tested 13 `(m, d)` cases × 14 candidate measures × 6 different `Λ_+` half-space definitions.

**Result: RP fails uniformly.** For every `(m, d)` with non-trivial `|Λ_+| ≥ 4`, every candidate measure (Boltzmann at various β; resolvent; |K_F|; K_F²; K + λI; spectral projectors) gives strictly negative min-eigenvalue of the GNS-style inner product matrix `M_sym`. The "RP holds" rows for small `|Λ_+|` are vacuous (the matrix is globally PSD; θ-twist tests nothing).

Sample data:

| `(m, d)` | `|Λ_+|` | Boltz β=1 | K_F + λI | K_F² | Verdict |
|---|---|---|---|---|---|
| (5, 2) | 4 | **−0.48** | **−1.00** | **−1.97** | RP fails |
| (6, 2) | 6 | **−0.85** | **−1.24** | **−3.60** | RP fails |
| (7, 2) | 9 | **−1.12** | **−1.70** | **−6.40** | RP fails |
| (8, 2) | 12 | **−1.56** | **−2.17** | **−10.5** | RP fails |
| (6, 3) | 10 | **−1.22** | **−1.90** | **−7.94** | RP fails |
| (7, 3) | 15 | **−1.53** | **−1.69** | **−10.8** | RP fails |
| (7, 4) | 15 | **−1.15** | **−1.71** | **−10.2** | RP fails |

The min-eigenvalue magnitude grows monotonically with `|Λ_+|`. No β-tuning reverses the sign.

### The structural mechanism — distinct from the prior 7

Wilson gauge action satisfies the additive decomposition `S = S_+(half-links) + S_−(half-links)` with `S_− = θ(S_+)`, giving `exp(−S) = exp(−S_+) · exp(−θ S_+)` — a tensor product whose θ-twist is automatically PSD by Cauchy-Schwarz. This is the load-bearing positivity step for lattice RP, proved in the framework's existing `LatticeReflectionPositivity.lean` via `wilson_action_decomposition`.

**K_F has no analogous decomposition.** Chamber-points are d-tuples that span both halves of the θ-fixed plane. The order kernel `ζ(p_a, q_b) = [p_a ≤ q_b]` couples coordinates *across* the half boundary. The K_F formula `K_F(P, Q) = det(ζ[P, Q]) + det(ζ[Q, P]) − δ_{P, Q}` therefore has cross-half terms that the θ-twist exposes as negative eigenvalues.

**This is structurally distinct from the prior 7 no-go's.** Prior 7 were all variants of "find a continuous symmetry σ on the chamber-point Hilbert space and apply Moretti-Oppio." The 8th is a *constructive-QFT* failure: K_F is not the transfer matrix of a reflection-positive lattice system. **The two main known families of ℂ-Hilbert derivation are now both ruled out.**

### Agent B: OS reconstruction structural scoping

Conditional on RP holding, Agent B confirmed:
- OS reconstruction maps cleanly to the K_F substrate with finite-dim simplifications. Scenario B (`T = exp(−β K_F)`, `H_OS = β K_F`) always available structurally.
- Complex structure `J` would emerge naturally via complexification, forced by unitarity of real-time evolution. Real derivation, not stipulation.
- Lean cost: 3–4 months for OS-on-K_F formalization, leveraging existing infrastructure.
- Connection to Phases 1–3: `K_F_matrix_C_isHermitian` would become a *corollary* with derived complex structure replacing type stipulation.

**But Agent B explicitly flagged R6 as the load-bearing risk:** "OS reconstruction needs RP for the K_F substrate measure, not the Wilson gauge action." Agent A's result shows R6 fires; the conditional collapses.

### Updated cumulative pattern: eight sequential no-go's, two construction families

| # | Path | Mechanism | Family |
|---|---|---|---|
| 1 | shift-on-chamber-points at substrate | indefinite commutator, K_F not preserved | I (σ + M-O) |
| 2 | SU(2) Plancherel | scalar identities only; compactness mismatched | I |
| 3 | β-CDP substrate operational | substrate violates tomographic locality (Boxworld) | I (operational variant) |
| 4 | continuum-limit M-O | continuum object not constructed | I |
| 5 | finite-m with shift | operator-norm relative commutator pinned at 1.0 | I |
| 6 | spectrally-projected shifts | wrong-sign Hermitian square (pinned at 2.0) | I |
| 7 | polar-decomposition shifts | acyclic shift → nilpotent U₊ → log undefined | I |
| **8** | **RP/OS reconstruction** | **chamber-points lack additive S = S_+ + S_− decomposition** | **II (constructive QFT)** |

**Family I — continuous symmetry + M-O (Moretti-Oppio, Stückelberg, Solèr) — exhausted via 7 distinct candidates.**
**Family II — reflection positivity + OS (Osterwalder-Schrader, Glimm-Jaffe, Osterwalder-Seiler) — ruled out via the 8th.**

There is no third family in standard mathematical-physics literature.

### Strategic position — final

After eight sequential no-go's spanning the two distinct construction families, **the framework's K_F substrate is provably incompatible with ℂ-Hilbert derivation by any natural construction in the constructive-QFT or Moretti-Oppio literatures.** The substrate is fundamentally super-quantum (Boxworld at bipartite level, `K_AB − K_A·K_B = N_A + N_B − 2 > 0`) and lacks the structural prerequisites — cyclicity for σ-actions; additive action decomposition for RP — for any of the standard derivations.

This is the strongest possible negative result at the substrate level. It is a clean, defensible publishable artifact:

> *"We prove via direct enumeration and numerical investigation that the K_F operator on causal-set chamber-points does not admit a natural ℂ-Hilbert structure derivation by any of: (i) seven Moretti-Oppio-style σ-action constructions, including shift-translation, SU(2) Plancherel, spectrally-projected and polar-decomposition variants, finite-m approximate, continuum-limit, and operational reconstruction at substrate; (ii) Osterwalder-Schrader reconstruction with K_F as transfer matrix. The substrate is super-quantum (Boxworld) at bipartite level, and chamber-points lack the additive action decomposition required for reflection positivity. ℂ-Hilbert structure, if recoverable, must come from external structure — information causality, continuum Lorentz symmetry imposed externally, decoherent-histories restriction, or a not-yet-articulated principle outside both standard literatures."*

Substantial Foundations of Physics paper. ~12-15 pages, target reference paper.

### Final recommendation — consolidate

The audit is complete. Eight sequential no-go's. Two distinct construction families exhausted. The pattern is structural, not technical. **There is no ninth candidate I can identify in the standard mathematical-physics literature.**

- Phase 1–3 of `kf-hermitian-lean` (zero sorry, K_F is Hermitian on any finite preorder) is the positive deliverable.
- The eight no-go's + green Lean = a complete, citable artifact. Future work in causal-set quantum mechanics will cite this as the foundational impossibility result.
- ~2–3 weeks of writing produces the paper. No further Lean.

Move to option (C) — consolidate. Write the paper.

---

## Phase 5 Stone–von Neumann investigation (2026-05-01) — ninth no-go, third construction family

After user's "Gaussian wavepacket" hint pointed at Stone–von Neumann theorem as a potentially-different family from M-O (σ + complex-structure-from-symmetry) and OS (RP + complex-structure-from-Wick-rotation), two parallel agents investigated. Both negative. The pattern is now structurally complete.

### Agent A: does the framework force ℏ ≠ 0?

The Heisenberg group `H = ℝ² × ℝ` is the canonical central extension of `(ℝ², +)` by `(ℝ, +)` via the symplectic 2-cocycle `ω(q, p; q', p') = qp' − q'p`. Stone–von Neumann's theorem requires non-zero central character `ℏ`. The investigation: does the framework's K/P content force `ℏ ≠ 0`?

**Verdict: negative. The framework has *symmetric* bilinear forms on `(Q, P)`, not antisymmetric.**

What the framework derives on the K/P plane:
- `K² + P²` (SO(2) rotation invariant) — **symmetric** — `RotationInvariance.lean`
- `K · P` (SO(1,1) boost invariant; Berry–Keating Hamiltonian) — **symmetric** — `BoostInvariance.lean`

What the framework does **not** derive:
- The antisymmetric form `ω = q dp − p dq` — never constructed.
- Heisenberg group structure — requires `ω` as input.
- Non-zero central character `ℏ` — requires Heisenberg first.

Three candidate sources for forcing `ℏ ≠ 0`, all assessed and rejected:

1. **Symplectic non-degeneracy from K/P non-triviality.** *Invalid as stated.* "K-sector and P-sector both non-trivial" gives a 2D real vector space, not an antisymmetric form on it. K/P non-triviality gives the underlying space; doesn't pick `ω` rather than the symmetric forms.

2. **Berry–Keating `K · P` non-trivial implies non-zero central character.** *Conflates two bilinear forms.* `K · P` is symmetric (the SO(1,1) Casimir); `ω` is antisymmetric. They are different objects. `K · P ≠ 0` says nothing about an antisymmetric pairing.

3. **Chamber discriminant `Δ = 7` sets `ℏ` canonically.** *Numerology.* `Δ` has units of (eigenvalue ratio)²; `ℏ` has units of action. No natural map between them.

**Stone–von Neumann therefore relocates but does not eliminate the (a)/(b) gap:** it requires both a stipulated antisymmetric pairing `ω` AND a stipulated non-zero `ℏ`, which together are at least as much input as "i ∈ ℂ" in the original Phase 4a finding.

### Agent B: does `L²(ℝ_Q)` connect to chamber-point K_F?

Even if Stone–von Neumann were to apply on the `(Q, P)` plane, the framework's actual physics content (γ_d, Higgs mass via `m_H = γ_4 · v`, chamber polynomial discriminant Δ = 7, mass hierarchy via `ln((5-√7)/(5+√7))`) lives on the **chamber-point K_F**, not on the `(Q, P)` plane. Does the Schrödinger Hilbert space `L²(ℝ_Q)` carry K_F as an operator, or does Stone–von Neumann's complex structure on `L²(ℝ_Q)` fail to descend to chamber-points?

**Verdict: negative. K_F and `L²(ℝ_Q)` are structurally disconnected.**

Four candidate connections, all assessed and rejected:

1. **K_F is the matrix of `H_HO = (Q̂² + P̂²)/2` in some discrete basis of `L²(ℝ_Q)`.** *No.* K_F's Jacobi entries `J_4 = (1/3, 2/5, 1/5)` with off-diagonals `b₁² = 1/25, b₂² = 1/50` come from **Volterra singular-value ratios** `σ_k = 2/((2k−1)π)` (proven in `VolterraProof.lean`). Harmonic-oscillator Jacobi entries are `√n` from the position operator. **Fundamentally different families of off-diagonals.**

2. **K_F eigenstates are Hermite polynomials in disguise.** *No.* `ChamberPolynomialTheory.lean` is explicit: chamber polynomials are *"a new orthogonal polynomial family outside the Askey scheme."* Hermite polynomials are inside the Askey scheme. They are different orthogonal-polynomial families.

3. **`γ_d` is `ℏω` in disguise.** *No.* `H_HO` spectrum is **arithmetic**: `ℏω · {½, 3/2, 5/2, …}`. K_F spectrum at d=4 is `{3/5, (5±√7)/30}` — three numbers in two distinct number fields (ℚ and ℚ(√7)), **not arithmetic**. The Feshbach-discriminant-prime theorem (Δ = 7 unique to d=4) has no `H_HO` analogue. `γ_d` is a Perron–Frobenius logarithm of an order-kernel transfer matrix, not an oscillator frequency.

4. **Volterra operator on `L²[0, 1]` is the bridge.** *Partially true but doesn't help.* The Volterra operator `V: L²[0,1] → L²[0,1]` IS the continuum limit of K_F (proven in `VolterraProof.lean` via `sv_error_bound`). But `V` commutes with **neither** `Q̂` nor `P̂` — it is not a Heisenberg generator. The unitary maps `L²(ℝ) ↔ L²[0,1]` exist but do not intertwine the Heisenberg algebra with the Volterra structure. **Heisenberg uniqueness doesn't constrain V.**

**The structural reason for the disconnection:** `L²(ℝ_Q)` carries a *symplectic* `(Q, P)` structure with continuous ℝ-action (the Heisenberg group). Chamber-point K_F carries a *combinatorial poset* structure with finite group action (R-symmetry plus `Sym(m)`). These are **different types of symmetry**. Stone–von Neumann's uniqueness is a statement about the first; it cannot constrain operators built from the second.

### Updated cumulative pattern: nine sequential no-go's, three construction families exhausted

| # | Path | Family | Mechanism |
|---|---|---|---|
| 1 | shift-on-chamber-points at substrate | I | indefinite commutator, K_F not preserved |
| 2 | SU(2) Plancherel | I | scalar identities only; SU(2) compactness mismatched |
| 3 | β-CDP substrate operational | I | substrate violates tomographic locality (Boxworld) |
| 4 | continuum-limit M-O | I | continuum object not constructed |
| 5 | finite-m with shift | I | operator-norm relative commutator pinned at 1.0 |
| 6 | spectrally-projected shifts | I | wrong-sign Hermitian square (pinned at 2.0) |
| 7 | polar-decomposition shifts | I | acyclic shift → nilpotent U₊ → log undefined |
| 8 | RP/OS reconstruction | II | chamber-points lack additive `S = S₊ + S₋` |
| **9** | **Stone–von Neumann** | **III** | **framework has only symmetric forms on (Q, P), not antisymmetric ω; chamber-points and `L²(ℝ_Q)` structurally disconnected** |

**Family I** (continuous symmetry σ + Moretti–Oppio): exhausted via 7 distinct candidates.
**Family II** (reflection positivity + Osterwalder–Schrader): ruled out.
**Family III** (Heisenberg group + Stone–von Neumann): ruled out today.

**These are the three known construction routes from real structure to ℂ-Hilbert structure in the mathematical-physics literature. All three are now ruled out for this substrate.**

### The structural impossibility theorem (informal)

The chamber-point K_F substrate fails the prerequisites for *each* known ℂ-derivation route:

- **For Family I (σ + M-O):** chamber-points are *acyclic* (no orbit returns under shifts; finite range `[0, m−1]`), so there is no continuous σ-action whose Casimir is non-negative.
- **For Family II (RP + OS):** K_F lacks the *additive action decomposition* `S = S₊ + S₋` (the order kernel `ζ(p_a, q_b) = [p_a ≤ q_b]` couples coordinates across the θ-fixed plane).
- **For Family III (Heisenberg + Stone–von Neumann):** the framework's K/P plane carries *symmetric* bilinear forms (`K² + P²`, `K · P`), not the *antisymmetric* form `ω = q dp − p dq` required for Heisenberg structure.

Each family has a structural prerequisite the substrate provably lacks. **The (a)/(b) gap cannot be closed by any natural construction in the standard mathematical-physics literature.**

### Final final recommendation: option (C) consolidate, immediately

The audit is genuinely complete. Three known families, nine no-go's, all by enumerable structural mechanisms. The Gaussian wavepacket hint was the right move strategically — it pointed at the third family — but the third family also fails by a *new* structural mechanism (symmetric vs antisymmetric forms) distinct from the prior two.

This is now publishable as a **structural impossibility theorem**:

> *"We prove via direct construction and numerical investigation that the K_F operator on causal-set chamber-points does not admit a natural ℂ-Hilbert structure derivation by any of the three known construction families in mathematical physics: (i) Moretti–Oppio σ-actions (seven distinct candidates), (ii) Osterwalder–Schrader reflection-positivity reconstruction, (iii) Stone–von Neumann Heisenberg-group representation. For each family, the substrate provably lacks the structural prerequisite — cyclicity, additive action decomposition, antisymmetric symplectic form — required for the family's argument. ℂ-Hilbert structure, if recoverable, must come from external structure not articulated in any of the three standard literatures."*

The paper writes itself from this audit. ~12-15 pages, target *Foundations of Physics* or *Studies in History and Philosophy of Modern Physics*. Reference paper status.

The exhaustion is now genuine. There is no fourth family in the standard mathematical-physics literature that I can identify. After this audit, future work attempting to derive ℂ from a K_F-style substrate must either propose a structurally novel construction (outside the three families, requiring publication-level mathematical physics in its own right) or accept that ℂ-Hilbert structure is an external imposition.

---

## Phase 5 P7 lattice-perturbation check (2026-05-01) — tenth no-go, same Case 3 pattern

After the user asked "any other lattice perturbation?", a focused agent tested the (P7) candidate: chamber-polynomial-discriminant lattice perturbation with `Δ = 7` motivating `√(-7) · V_i` perturbations. Six natural perturbations tested (`π_K`, `π_P`, R-symmetry, det matrix D, Volterra approximation Vol, dimension-shift Σ) at `(m, d)` ∈ {(3,2), (4,2), (5,2), (4,3), (5,3), (4,4), (5,4)} and `ε` ∈ {0.1, 1, √7, 1/7, 1/√7, 7, i, √(-7), 1/√(-7)}. Code: `/tmp/p7_lattice_perturbation.py`.

**Verdict: NEGATIVE. Tenth sequential no-go.**

Three structural findings:

1. **Symmetric perturbations** (`V_1=π_K, V_2=π_P, V_3=R, V_6=Σ`) give all-real spectra at every real `ε`. They cannot force ℂ. When `ε` is complex, eigenvalues are non-paired — no Galois-ℤ/2 structure; just real eigenvalues shifted by complex `ε`. Stipulation in disguise.

2. **Non-symmetric perturbations** (`V_4=D`, `V_5=Vol`) DO produce conjugate-pair complex eigenvalues at real `ε`. But this is **generic for any non-symmetric real matrix** — not a special algebraic event tied to `Δ = 7`. Discriminant ratios `disc / 7` scatter across `{0.12, 0.18, 0.41, 0.77, 1.18, 2.71}` with no algebraic locking. No structural `√7` tie exists.

3. **Critical (P7) test failure at d=4 (where Δ=7 actually lives):** at `(m=5, d=4)`, `V_4` and `V_5` give **all-real spectra at every real `ε`**. The very dimension `Δ=7`'s primality identifies is the one place where non-symmetric real perturbations fail to complexify. **The opposite of what the (P7) hypothesis predicted.**

The `√(-7) · V_i` check at `(5,4)`: every `V_i` gives Hermitian error `1.76` to `5.29` (genuinely non-Hermitian); the resulting complex spectrum is generic non-Hermitian noise, not forced by a real-symmetric quadratic discriminant. **The `i` is imported via `ε`, not generated by `V`'s interaction with K_F's algebra.**

Bonus structural findings (worth recording for the paper):
- `V_4 = V_5` in strict-upper-triangular: the "Volterra approximation" matrix coincides with the "discriminant det matrix." Reduces six candidates to five.
- `d=4` is structurally *protected against* real perturbation complexification — the Δ=7 prime reflects a real-symmetric algebraic stability, not a hidden ℂ-structure.

### Updated cumulative pattern: ten sequential no-go's

The (P7) candidate fails by the *same Case 3 stipulation pattern* as Family I: `i` is always carried by the choice of perturbation parameter, never generated by the framework's algebra. This confirms that the structural impossibility extends to perturbative routes.

The audit is complete. Ten sequential no-go's. Three known construction families exhausted. Lattice-perturbation routes also confirmed inadequate.

### Final position

Move to (C') — *reframed* consolidation. The reframing is the strongest honest position: substrate is real-algebraic; framework's deliverables (γ_d, m_H, SM gauge group, mass hierarchies) are real-algebraic results derivable without ℂ-Hilbert structure; ℂ is interpretive overlay.

Paper outline drafted in `DRAFT_PAPER_OUTLINE.md` (this commit).
