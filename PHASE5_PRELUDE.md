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
