# Clay Yang-Mills Mass-Gap: Systematic Closure Plan

**Date**: 2026-05-11
**Scope**: This plan enumerates EVERY gap between the framework's current Lean state and a Clay-grade Yang-Mills mass-gap proof, and proposes specific actions to close each gap.

## The Clay Statement

> Prove that for any compact simple gauge group G, a non-trivial quantum Yang-Mills theory exists on R⁴ and has a mass gap Δ > 0.

## The Ten Gaps

The framework's complete Yang-Mills story currently consists of ~30 Lean files covering the algebraic chamber matrix → mass gap √7/15 derivation chain. The remaining gaps to a Clay-grade proof:

| # | Gap | Current Status | Phase |
|---|---|---|---|
| 1 | Multi-link Hilbert space L²(SO(10))^L | Single-link done (R2b) | A |
| 2 | Explicit H_Wilson as an operator | Abstract carrier only (Build1-3) | A |
| 3 | Volterra → link map ι | Construction half closed (iota6) | A |
| 4 | Matrix element matching ⟨v_i, H v_j⟩ = J₄ + N_c·I | Cross-block done (R1) | A |
| 5 | Thermodynamic limit L → ∞ | Chamber-level only | C |
| 6 | Continuum limit lattice → 0 | Chamber-level (R4) | D |
| 7 | Wightman / OS axioms verified | Substantially built (CL2, Clay2) | B |
| 8 | Glimm-Jaffe constructive measure | Conditional (CL3) | E |
| 9 | Reflection positivity | Not addressed | B |
| 10 | RG / asymptotic freedom | Not addressed | D |

## Phase A — Make the Chamber-Matrix Matching Real

**Goal**: Promote the chamber/bath identification from "definitional input" to "derived theorem" by computing matrix elements ⟨v_i, H_Wilson v_j⟩ on the iota6 axes and verifying they equal J₄ + N_c·I entry by entry.

This is the IDENTIFICATION residue of R1 plus Gaps 1, 2.

### Key insight

The construction half of R1 (closed) handles **cross-block = 0** via centroid + disjoint-permutation tricks. The identification half requires **diagonal entries** ⟨v_i, H v_i⟩ = correct values, which decomposes into:

- ⟨oneLp, E² oneLp⟩ = 0 (trivial irrep has Casimir 0)
- ⟨traceLp, E² traceLp⟩ = C₂(V_10) · ‖traceLp‖² = (9/2) · 10 (vector rep Casimir × trace inner product)
- ⟨f3Lp, E² f3Lp⟩ = C₂(Sym²₀) · ‖f3Lp‖² = 20 · ‖f3Lp‖² (symmetric traceless rep Casimir; corrected from 18 in initial draft per Phase_A3_CasimirSpectrum.lean Slansky+Cahn+Wybourne cross-check)
- ... etc.

Each entry decomposes into (irrep identification) × (Casimir lookup) × (norm computation).

### A1 — Multi-link Hilbert space

**Construct** L²(SO(10), Haar)^L via Mathlib's `MeasureTheory.Measure.Pi`:
- `multiLinkHaar L := Measure.pi (fun _ : Fin L => haarMeasureSO10)`
- `linkHilbert L := Lp ℝ 2 (multiLinkHaar L)`

Mathlib has Pi measures and Lp on them. Tractable.

### A2 — Identify iota6 axes' SO(10) irreps

**Already partially done** in `R1_VolterraSO10Embedding.lean` and downstream:
- oneLp ∈ trivial rep (1-dim)
- traceLp ∈ vector rep V (10-dim, fundamental)
- f3Lp = (g₀₁)² − (g₀₂)² ∈ symmetric-traceless Sym²₀ V (54-dim)
- f4Lp = (g₀₃)² − (g₀₄)² ∈ symmetric-traceless Sym²₀ V (54-dim, different basis vector)
- h1Lp = g₀₁·g₀₂·(g₀₃ − g₀₄) ∈ V⊗Sym²₀V or similar (needs identification)
- h2Lp = g₁₃·g₂₄·(g₀₅ − g₀₆) ∈ similar 3-form irrep

**Action**: write `LayerB/Phase_A2_IrrepIdentification.lean` formalizing these assignments with proofs.

### A3 — Casimir eigenvalues

**Lookup**: For SO(2n+1) and Spin(2n), Casimir eigenvalues are tabulated. For SO(10):
- C₂(trivial) = 0
- C₂(V_10) = 9 (in standard normalization where C₂(V) = (n-1) for SO(n))
- C₂(Sym²₀) = 2·(n-1) = 18
- C₂(adjoint = ∧²V) = 2·(n-2) = 16

**Action**: write `LayerB/Phase_A3_CasimirSpectrum.lean` recording these as `def`s with citations.

### A4 — Matrix element computation

**Compute** ⟨v_i, H_Wilson v_j⟩ for the 21 distinct (i,j) pairs (15 strict + 6 diagonal of iota6), verify they match J₄ + N_c·I.

Three components per matrix element:
- KE ⟨v_i, E² v_j⟩ — Casimir × δ_{ij} (different irreps don't mix under E²)
- PE ⟨v_i, (1 - Re Tr U_p) v_j⟩ — plaquette functional (Wilson loop expectation)
- Bath dressing — color N_c factor on bath modes

**Action**: write `LayerB/Phase_A4_MatrixElementMatching.lean`.

**Expected outcome**: either (1) matching holds — identification proved; (2) matching fails — framework's J₄ + N_c·I prediction is empirically wrong, framework needs revision.

## Phase B — Reflection Positivity + OS Axioms

**Goal**: Prove reflection positivity for the Wilson action at finite L, then OS reconstruction yields Wightman theory.

### B1 — Reflection positivity (Wilson)

Standard result (Osterwalder-Seiler 1978): the Wilson lattice gauge theory is reflection positive about hyperplanes between time-slices. Formalize this for SO(10).

**Action**: `LayerB/Phase_B1_ReflectionPositivity.lean`. Builds on Build4's expectation values.

### B2 — OS reconstruction

**Already substantially built** in CL2_LorentzianWightmanDirect (1233 lines) and Clay2_HaagRuelleConstruction (529 lines). Wire up to B1.

**Action**: `LayerB/Phase_B2_OSReconstruction.lean` connecting B1 + existing CL2/Clay2.

## Phase C — Thermodynamic Limit (L → ∞)

**Goal**: Show the mass gap √7/15 survives the limit L → ∞ with appropriate scaling.

### C1 — Strong-coupling cluster expansion

Glimm-Jaffe-style polymer expansion. Mass gap stability proven at strong coupling first, then extended.

**Action**: `LayerB/Phase_C1_ClusterExpansion.lean`. Major open mathematical work — multi-week engineering even given a clean strategy.

### C2 — Spectral continuity

Continuity of the chamber gap as L varies. Already proved at chamber level in CL1_ContinuumLimit; need full-Hilbert-space version.

**Action**: `LayerB/Phase_C2_SpectralContinuity.lean`.

## Phase D — Continuum Limit + RG

**Goal**: Mass gap survives lattice spacing → 0, with renormalization.

This is the **deepest open mathematical problem** in the framework — the genuine Clay obstacle.

### D1 — Renormalization group setup

Wilson RG transformation, β-function, fixed-point analysis.

**Action**: `LayerB/Phase_D1_RGFlow.lean`. Major open research — not a single-agent task.

### D2 — Asymptotic freedom

For non-abelian gauge theories, β-function is negative at one loop. Ground-truth physics result; formalize and verify for SO(10).

**Action**: `LayerB/Phase_D2_AsymptoticFreedom.lean`.

### D3 — UV completion + mass gap survival

Show mass gap √7/15 is stable under RG flow as cutoff → ∞.

**Action**: `LayerB/Phase_D3_UVMassGapSurvival.lean`. **This is essentially the Clay problem.** Realistic scope: multi-year research.

## Phase E — Glimm-Jaffe Constructive Measure

**Goal**: Construct a probability measure on the space of field configurations, verifying all measure-theoretic properties.

### E1 — Cylinder sets, Borel σ-algebra

Standard constructive QFT setup.

**Action**: `LayerB/Phase_E1_CylinderConstructive.lean`. Builds on CL3_ConstructiveMeasure.

### E2 — Probability measure existence

Kolmogorov extension theorem for the lattice theory; continuum limit handled by Phase D.

**Action**: `LayerB/Phase_E2_ProbabilityMeasure.lean`.

## Honest Assessment

**Phase A** is **tractable in weeks**. The construction-half of R1 is closed; the identification-half is concrete computation with known representation-theoretic ingredients. If matrix element matching holds, Phase A closes the chamber/bath identification — major progress.

**Phase B** is **tractable in weeks** — both pieces (reflection positivity, OS reconstruction) are standard QFT and substantially started.

**Phase C** is **tractable in months** — Glimm-Jaffe cluster expansion is hard but standard mathematical physics.

**Phase D** is the **Clay problem itself**. No realistic timeline. The framework can contribute a chamber-level continuum limit (already proved, R4) and a sharply-stated full-theory conjecture, but the UV completion of 4D non-abelian gauge theory with mass gap is the open problem of mathematical physics.

**Phase E** is **tractable in weeks** — Kolmogorov extension on cylinder sets is well-trodden.

## Recommended Execution Order

1. **Phase A complete** (close identification residue)
2. **Phase B complete** (OS axioms wired to chamber)
3. **Phase E complete** (constructive measure)
4. **Phase C complete** (thermodynamic limit)
5. **Phase D — open** (state the residual conjecture precisely; this is the Clay problem)

Result after Phases A+B+C+E: a Clay-grade proof CONDITIONAL on UV completion (Phase D). The framework would have proved: "If 4D SO(10) Wilson YM has a continuum limit preserving the algebraic mass gap, then mass gap = √7/15."

## What's Being Launched Now

Three Phase A agents in parallel:
- A1: multi-link Hilbert space construction
- A2: irrep identification of iota6 axes
- A3: Casimir spectrum lookup for SO(10) irreps

After all three return, A4 (matrix element matching) becomes a concrete check.
