# Phase 4 Diagnostic and Retrospective

**Date:** 2026-05-01
**Bridge tag:** [`tomdif/kf-hermitian-lean@v0.1.0`](https://github.com/tomdif/kf-hermitian-lean/releases/tag/v0.1.0)
(commit `70f8e54`, Phases 1–3 + supporting API, build green, zero `sorry`, zero custom axioms)

**Phase 4 of the bridge program** is the integrative wiring of the existing `unifiedtheory` physics claims (`ComplexFromDressing`, `BornRuleUnique`, `PosetGrowthIsQuantum`, etc.) through the canonical Hermitian-observable interface formalized in [`tomdif/kf-hermitian-lean`](https://github.com/tomdif/kf-hermitian-lean). Unlike the additive Phases 1–3 of that bridge, Phase 4 is *integrative*: it rewrites type signatures and proof obligations in existing files, with the expectation that this surfaces previously-implicit assumptions.

This document is the running retrospective. Findings are added here as Phase 4 progresses. Sub-phases proceed `4a → 4b → 4c`; each may surface its own findings.

---

## Phase 4a — `LayerB/ComplexFromDressing.lean`

### Finding type: Case 3 (overclaim), refined to a sharper open-research statement

The file `LayerB/ComplexFromDressing.lean` does **not** derive complex amplitude structure from K/P decomposition. It defines complex amplitudes via the type signature `amplitudeFromKP : ℝ → ℝ → ℂ`, with the implementation `Q P ↦ ⟨Q, P⟩`, and proves properties of the resulting standard complex numbers.

The opening docstring of the file currently reads, in part:

> *"This is NOT an arbitrary complexification. It is FORCED by the existence of a dressing sector that is invisible to the source functional but contributes to the full energy/observable."*

That statement, taken at face value, claims a *derivation* of the choice of complex structure. The actual content of the file is closer to a *display* theorem — exhibiting the standard ℂ-amplitude properties of the canonical complexification `(Q, P) ↦ Q + iP`.

### What the framework actually proves (proper credit)

The diagnosis must give due weight to two genuine uniqueness theorems already present in the framework, which I missed on first read and which sharpen the picture substantially:

- **`LayerB/ComplexificationUniqueness.lean`** (~180 lines, fully proved): Every 2D commutative real division algebra with multiplicative norm is isomorphic to ℂ. (A 2D-restricted Frobenius theorem.)

- **`LayerB/ComplexUniqueness.lean`** (~145 lines, fully proved): Every rotation-invariant quadratic observable on ℝ² is `a · (Q² + P²)` for some `a > 0` — i.e., proportional to the standard complex norm-squared.

Each theorem is real, fully proved, and substantive. Their existence means the picture is *not* "the framework picked ℂ in the type signature." It is instead:

> Conditional on equipping the K/P real pair (Q, P) with **either** (i) a 2D commutative real division algebra structure with multiplicative norm, **or** (ii) an SO(2) action under which the observable is invariant, **ℂ is forced** (up to isomorphism / orientation / overall scale).

### Where the genuine open question lives

Both uniqueness theorems take the structure that does the work as a **hypothesis**, not as a derived consequence of K/P or causal-poset data. The remaining open research question, sharpened:

> **Open:** Does causal-poset / K_F structure single out either:
> - **(a)** an SO(2) symmetry acting on the K/P plane (rather than this being stipulated by the `phaseRotate θ := exp(iθ) · z` definition in `QuantumDefects.lean`), or
> - **(b)** a 2D commutative real division algebra structure on the K/P pair (rather than this being stipulated by the multiplication law in `ComplexificationUniqueness`)?

**Note that (a) and (b) are not independent.** SO(2) invariance on a 2D real space is the rotational structure that singles out complex multiplication: a 2D commutative real division algebra with multiplicative norm has its multiplication determined up to isomorphism by an SO(2) action on the pair. So a yes-answer to (a) implies a yes-answer to (b) and vice versa. They are two facets of the same missing structural claim, not two separate research programs.

A yes-answer to either — and hence both — would, via the existing uniqueness theorems, complete the derivation of ℂ from order-theoretic data. As of this writing, neither is presented as derived in the framework.

#### Prior literature: the question is well-posed and answered in adjacent settings

The question (a)/(b) has a well-developed continuum analogue. The Solèr–Stückelberg–Moretti–Oppio chain, in continuum relativistic quantum theory, asks whether the complex structure of the Hilbert space is forced or chosen — and answers it in the continuum case:

- **Solèr (1995)** — Quantum theories admit Hilbert space formulations only over ℝ, ℂ, or ℍ (the Solèr classification).
- **Stückelberg (1960)** — Real-Hilbert-space quantum mechanics has obstructions that point toward ℂ.
- **Moretti & Oppio, *"Quantum theory in real Hilbert space: How the complex Hilbert space structure emerges from Poincaré symmetry"*, [arXiv:1611.09029](https://arxiv.org/abs/1611.09029)** — For an elementary relativistic system (locally-faithful irreducible continuous unitary representation of the Poincaré group on a real Hilbert space, with non-negative squared mass), the system admits a **natural, Poincaré-invariant, unique-up-to-sign complex structure** that commutes with the algebra of observables.

Moretti–Oppio is the **direct continuum analogue** of our open question. Their Poincaré-symmetry hypothesis plays the role our SO(2)-action stipulation currently plays. They derive the complex structure J from a representation-theoretic consequence of Poincaré invariance. The result is non-constructive (existence + uniqueness up to sign) but rigorous.

**The shape a future closure of (a)/(b) would take, by analogy with Moretti–Oppio:**

> If the K_F-on-causal-poset structure carries an analogue of Poincaré symmetry — most naturally a discrete Lorentz-like representation arising from causal-poset automorphisms or from the K_F operator's spectral structure — then the same Solèr-style argument may force a unique-up-to-sign complex structure J on the K/P plane.

This is a research target with a well-defined shape. It is not an open-ended philosophical worry; it is a specific mathematical question with a known answer-form in the continuum, awaiting a discrete-substrate analogue. Recording this here both as legitimate intellectual lineage and as a falsifiable program: someone could prove a discrete analogue of Moretti–Oppio (or prove no such analogue exists), and either outcome is a paper.

### Adversarial search log

A targeted one-hour adversarial search was conducted before this finding was finalized, looking for places where the choice of complex structure might be implicit-but-derivable rather than implicit-and-arbitrary.

**This is a one-hour search, not a proof of absence.** It documents the scope so a future reader can see what wasn't checked.

#### Files and patterns examined

| Candidate | Files inspected | Patterns grepped | Result |
|---|---|---|---|
| (1) Time-orientation as half a complex structure | `LayerA/CausalFoundation.lean`, file listing for `Wick*`/`Time*`/`Boost*`/`Null*`/`Causal*` in `LayerA/` and `LayerB/` | `complex_from_time`, `J²`, `J ∘ J`, `imaginary_unit`, `TimeReversal`, `time_reversal` (across all `UnifiedTheory/`) | No `WickRotation.lean` exists. No grep hits. `CausalFoundation.lean` carries time-orientation via the partial order itself, but nothing connects it to the K/P plane's complex structure. |
| (2) R-symmetry composed with another involution | `LayerB/CPTFromKP.lean` (full read), references in `KFComputable.lean` | Catalog of involutions on (Q, P): R (chamber-point reflection, R²=Id), C (`(Q, P) → (−Q, P)`, C²=Id), P (`(Q, P) → (Q, −P)`, P²=Id). Compositions: C·P = −Id (squares to +Id), C·R, P·R, R·C·P (all reflections or 180° rotations). | No 90° rotation is constructible from any combination of these involutions. None squares to −Id. The standard complex-structure operator is not exhibited by any composition. |
| (3) Spectral structure of K_F | `KFHermitian/General.lean` (the formalized Hermitian structure), `LayerA/SpectralMassTheorem.lean`, `LayerB/AmplitudeUniqueness.lean`, `LayerB/KPProjectionTheorem.lean` | Eigenvalue API now exposed via `Matrix.IsHermitian.eigenvalues` (real-valued); searched for natural-pairing structures akin to Dirac-operator positive/negative spectra. | K_F is self-adjoint with real spectrum. Its Hermitian structure exists *because* the matrix is over ℂ; it does not supply ℂ. No anti-self-adjoint operator on the K/P plane is constructed from order-theoretic data. |

#### What the absence itself tells us

The most informative finding is what *isn't* present. In a framework with ~172 Lean files and substantial physics infrastructure, **no Wick-rotation-adjacent infrastructure exists at all**. There is no file named `WickRotation.lean`; no theorem connecting time-orientation to complex structure; no operator constructed to satisfy `J² = −Id` from poset data.

This absence is not damning, but it is informative: the program built physics on top of a presupposed complex structure rather than ever attempting an order-theoretic origin for ℂ. A referee reading the framework would be likely to notice this, so naming it explicitly here is defensive work that shows the program is aware of the gap.

#### What was not searched

The following were not exhaustively examined and may contain candidate structures:
- The `causal_higgs/` Python prototypes, particularly the CP² fiber definitions in `phase0/cp2_fiber.py` and `phase1/`. The CP² fiber is itself complex by definition; whether any aspect of it is order-derivable was not assessed.
- The full bodies of `LayerA/NullConeConformal.lean`, `NullConeGeneral.lean`, `NullConeTensor.lean` were not read end-to-end. Conformal/null-cone structure can sometimes induce a J via the Cayley transform; this avenue has not been ruled out.
- `LayerA/RotationInvariance.lean` was not read end-to-end. If it derives a rotational structure at any layer of the framework, that may bear on (a).
- The `causal-algebraic-geometry-lean` companion repository was not searched.

A future scan that closes any of these gaps and finds a candidate J would shift the finding from Case 3 to Case 1 (no overclaim) by giving the existing `complexification_from_parent` theorem a derivation path it currently lacks. The absence of such a candidate after a one-hour targeted search is consistent with — but does not prove — Case 3.

### Restatement plan

**(A) Cosmetic rename + docstring fix on `complexification_from_parent` and the file's opening paragraph.** No code changes; pure truth-in-labeling.

The new docstring for `complexification_from_parent`, integrating the proper credit and the forward pointer:

> *Given the canonical SO(2)-invariant complexification (Q, P) ↦ Q + iP — which is uniquely determined among 2D commutative real division algebras with multiplicative norm by `ComplexificationUniqueness`, and uniquely determined among rotation-invariant quadratic observables by `ComplexUniqueness` — the K/P amplitude has the standard complex-amplitude properties: |z|² = Q² + P², U(1) phase invariance, dressing-induced interference, classical limit, etc. The order-theoretic origin of either the SO(2) symmetry or the division-algebra structure is treated as open; see `PHASE4_DIAGNOSTIC.md`.*

**(C) Research note (this document).** Names questions (a) and (b) explicitly as the surviving open derivation questions, and notes that they are facets of one structural claim rather than two independent programs.

**(B) Explicit-J refactoring is deferred.** Adding `J` as an explicit parameter to the theorem is premature without a candidate `J` in hand. The right time to do (B) is when (a)/(b) is closed by exhibiting a specific J from order-theoretic data; at that point (B) becomes the formalization of *that* `J` as the canonical instance.

### What did not get committed

This document is the audit trail. **No edits to `ComplexFromDressing.lean` or any other file have been made yet.** The (A) cosmetic rename will be a separate commit, on this same `phase-4` branch, after this diagnostic is recorded.

The bridge wiring (re-typing `obs ∘ amplitudeFromKP` through `Matrix.IsHermitian.eigenvalues` from the bridge) was not attempted because the bridge inherits the same ℂ presupposition; wiring through it would not improve the situation. Phase 4b and 4c will proceed with the explicit caveat: "complex Hilbert space structure is presupposed, conditional on the open derivation question (a)/(b)."

---

## Phase 4b — `LayerA/BornRuleUnique.lean`

### Finding type: Case 1 (math correct) with Case 3 elements (file-naming + deferred-hypothesis chain)

The file's actual mathematical content is honest and correct: `BornRuleUnique.lean` proves that any SO(2)-invariant quadratic form on ℝ² is proportional to `Q² + P²`, via setting `θ = π/2` to extract `b = 0` and `a = c`. This is `so2_invariant_quadratic_unique` and `so2_invariant_eval`, ~150 lines of clean Lean.

But three observations:

1. **Triple redundancy.** This theorem is also proved in `LayerB/ComplexUniqueness.lean` (`complex_observable_unique`) and re-proved in `LayerB/PosetGrowthIsQuantum.lean` (`born_rule_for_growth`). All three are essentially the same uniqueness result with slightly different naming and structure. The duplication is not a bug per se, but it inflates the apparent body of evidence — three independently named files that all prove the same fact. Worth consolidating, or worth flagging in the paper that they are intentional re-statements rather than independent results.

2. **File-name vs file-content gap.** The file is named `BornRuleUnique` and the master theorem is `born_rule_uniqueness`, but the actual content is "the unique normalized SO(2)-invariant quadratic form on ℝ² is `Q² + P²`." This is the **algebraic content** of the Born rule — exactly as the opening docstring honestly states (*"This is the algebraic content of the Born rule"*). It does **not** address:
   - The probabilities-from-projectors face of the Born rule (`Pr(outcome i) = |⟨ψ|i⟩|²`).
   - The expectation-values face (`⟨A⟩ = Tr(ρ A)`).
   - Gleason-style projector-additivity.
   - Pure-vs-mixed states.
   - Connection to a Hilbert space at all (the file operates on `QuadForm` = (a, b, c) ∈ ℝ³, not on Hermitian operators).
   The docstring is internally honest about this but the file name is broader than the content.

3. **The deferred hypothesis chain does not close.** The master theorem `born_rule_uniqueness`'s docstring says the SO(2)-invariance hypothesis is justified physically by `RotationInvariance.lean` ("the physical content (why we need SO(2) invariance) comes from the isotropy of the Poisson sprinkling, proved in `RotationInvariance.lean`"). But `RotationInvariance.lean` itself proves only that **`Q² + P²` is rotation-invariant on ℝ² as a coordinate-rotation algebraic identity** (`norm_sq_rotation_invariant`). It does **not** prove that the K/P plane carries an SO(2) action **derived from** spatial isotropy of the underlying Poisson sprinkling. The connection between "spatial isotropy of points in the sprinkling" and "SO(2) action on the (Q, P) source/dressing pair" is asserted in the docstring but not formalized.

### Why this does not introduce a new open question

The deferred-hypothesis problem in 4b reduces to **the same** open question (a)/(b) from 4a. The chain:

- `BornRuleUnique` requires SO(2) invariance on (Q, P).
- It defers the justification to `RotationInvariance.lean`.
- `RotationInvariance.lean` proves `Q² + P²` is invariant under coordinate rotation in ℝ², but does not derive an SO(2) **action** on the K/P plane from poset isotropy.
- Therefore the SO(2) action remains stipulated.

This is the **same** stipulation diagnosed in 4a. Closing question (a) — deriving the SO(2) action on (Q, P) from causal-poset data — would close the deferred-hypothesis chain in 4b simultaneously.

### Bridge wiring is not directly applicable

`BornRuleUnique.lean` operates on `QuadForm` (three real coefficients), not on Hermitian matrices. There is no place where the bridge constructor's `K_F_matrix_C : Matrix _ _ ℂ` could plug in directly. To connect, one would need a separate file that:
- Takes a `Matrix.IsHermitian` hypothesis on K_F,
- Identifies a 2D subspace (e.g., a fixed-rank antichain block) carrying a quadratic form,
- Shows that subspace's quadratic form is SO(2)-invariant under some action,
- And only then invokes `BornRuleUnique` to conclude the form is `a(Q² + P²)`.

Each of those steps would be a new theorem and would surface its own assumptions. We do not attempt this here; the bridge wiring at this layer would not improve the situation given the open (a)/(b) question.

### Restatement plan for 4b

**(A) Cosmetic: tighten the master theorem docstring** to make the deferred-hypothesis status of SO(2) invariance honestly visible. Concretely, replace:

> *"The physical content (why we need SO(2) invariance) comes from the isotropy of the Poisson sprinkling, proved in `RotationInvariance.lean`."*

with:

> *"The SO(2) invariance is taken as hypothesis here. `RotationInvariance.lean` proves that `Q² + P²` is invariant under coordinate rotation on ℝ², but the derivation of an SO(2) **action on the K/P pair** from spatial isotropy of the underlying causal-poset structure is open; see `PHASE4_DIAGNOSTIC.md`."*

**(C-extension) Add to the research-questions section above:** the (a)/(b) open question is implicated by 4b's deferred-hypothesis chain, not just by 4a's structural setup. This is one open question with two file-level entry points, not two.

---

## Phase 4c — `LayerB/PosetGrowthIsQuantum.lean`

### Finding type: Case 3 (overclaim) — strongest of the three

The file's master theorem is named `poset_growth_is_quantum` and its docstring states:

> *"The growth of a finite partial order (adding elements one at a time) with dressing-invariant quadratic probability IS quantum mechanics."*

The actual content of the file is the **same uniqueness theorem** as `BornRuleUnique` and `ComplexUniqueness` — that an SO(2)-invariant quadratic function on ℝ² is `a(Q² + P²)` — applied to a `GrowthProb := ℝ → ℝ → ℝ` rather than a `QuadForm` or a complex observable.

What the file does **not** contain:

1. **No formalization of the Rideout-Sorkin sequential growth model** (referenced in the opening docstring but not implemented in Lean).
2. **No connection to the `KFComputable.lean` K_F operator** or to any actual poset-growth dynamics in the framework.
3. **No Hilbert space, no projectors, no unitary evolution.** The file does not derive that growth probabilities respect a unitary evolution; it derives the *shape* of an individual-step probability distribution.
4. **No connection to the standard quantum-mechanics formulation of the Born rule** for measurement outcomes.

The chain "growth probability ∝ Q² + P² ⇒ Born rule ⇒ quantum mechanics" is asserted in the docstring but only the first arrow is formalized, and that first arrow is the same algebraic uniqueness theorem proved in two other files.

### What "poset growth IS quantum" would actually require to be a derivation

For the file to deliver on its name, it would need to formalize at least:

- (G1) **Sequential growth dynamics.** A formal construction of a sequence of finite posets `P₀ ⊆ P₁ ⊆ P₂ ⊆ …` with addition probabilities at each step (Rideout-Sorkin classical sequential growth, or some variant).
- (G2) **A Hilbert space attached to the growth process.** The state space of "current poset" or "current poset history" carrying a complex inner product.
- (G3) **A unitary evolution operator** governing the sequential growth, with the Born rule recovering the step probabilities.
- (G4) **A derivation of (G3) from (G1)**: showing that the Rideout-Sorkin probabilities arise as `|amplitude|²` of unitary transitions, not the other way around.

None of these are in the file or in any other file the search located. The framework asserts the equivalence of poset growth and quantum mechanics by analogy, then formalizes the algebraic uniqueness step at the bottom of the analogy.

### Restatement plan for 4c

This is the strongest Case 3 finding of the three. The honest restatement is more invasive than (A) cosmetic alone:

**(A) Master-theorem rename**: renamed `poset_growth_is_quantum` to `dressing_invariant_quadratic_is_born_form` to truthfully reflect that the file proves a uniqueness result for quadratic dressing-invariant probability rules, not the equivalence of poset growth with quantum mechanics. (Done in this commit.)

**(A-ext) File-level docstring rewrite**: replace the opening claim *"The growth of a finite partial order ... IS quantum mechanics"* with the honest content: *"If poset-growth probability is quadratic in (Q, P) and dressing-invariant under the SO(2) action on the K/P plane, then it is proportional to `Q² + P²` — the same uniqueness result as `BornRuleUnique.lean` and `ComplexUniqueness.lean`, applied to growth dynamics rather than measurement observables."*

**(C-extension) Add to the research-questions section**: deriving "poset growth IS quantum mechanics" — with formal versions of (G1)–(G4) above — is a substantial open program. The current `PosetGrowthIsQuantum.lean` is a piece of that program, not a completion of it.

### Why we do not attempt to prove (G1)–(G4) here

Each of (G1)–(G4) is a multi-month research project. Formalizing Rideout-Sorkin alone is on the order of the Phases 1–3 of `kf-hermitian-lean`. The honest move at this stage is to name the gap and stop, not to wave at it.

---

## Cross-cutting observations after Phases 4a, 4b, 4c

- **Triple uniqueness theorem**: `BornRuleUnique`, `ComplexUniqueness`, and `PosetGrowthIsQuantum` all prove essentially the same algebraic uniqueness fact (SO(2)-invariant quadratic on ℝ² ⇒ `a(Q² + P²)`). They are differently framed (observable / amplitude / growth probability) but the underlying math is one theorem. This is not redundancy in a strict sense — each frames the result for a different consumer — but the bibliography of the framework should be honest about it.

- **Single open question, multiple entry points.** Phases 4a, 4b, and 4c each have their own apparent stipulation, but all three reduce to **the same** open derivation question: does causal-poset / K_F structure single out the SO(2) action on the K/P plane (equivalently, the 2D commutative real division algebra structure on the K/P pair)? Closing this one question would close all three deferred-hypothesis chains simultaneously.

- **The bridge does not change the diagnostic.** Wiring `kf-hermitian-lean`'s `K_F_matrix_C_isHermitian` into any of the three files would not eliminate the open question; the bridge produces `Matrix _ _ ℂ` whose `ℂ` is also presupposed. The bridge is valuable for *type-discipline* and for *eliminating ad-hoc matrix definitions*, but the deeper Case 3 finding of "complex/SO(2) structure presupposed, not derived" is invariant under bridge wiring.

- **The strongest claim of the framework that survives unambiguously** is the chain `K_F → IsHermitian → real eigenvalues → γ_d eigenvalue → Higgs mass`, *conditional* on the presupposed complex Hilbert space structure. Phases 1–3 of `kf-hermitian-lean` formalize this chain; Phase 4 has confirmed that conditioning on ℂ is the only structural presupposition (not multiple independent ones), which is a strong epistemic position even if the open question (a)/(b) is not yet closed.

---

## Related literature

The Phase 4 diagnostic should be read alongside the following prior and contemporaneous work. These are not exhaustive; they are the papers that bear most directly on the open question and on the Lean-formalized-physics audience.

### Continuum analogue of the open question (a)/(b)

- **Solèr, *"Characterization of Hilbert spaces by orthomodular spaces"*, Comm. Algebra 23 (1995)** — Quantum theories admit Hilbert space formulations only over ℝ, ℂ, or ℍ. The classification result that frames our (a)/(b) as well-posed.

- **Stückelberg, *"Quantum theory in real Hilbert space"*, Helv. Phys. Acta 33 (1960)** — Identifies obstructions to real-Hilbert-space quantum mechanics that point toward ℂ.

- **Moretti & Oppio, *"Quantum theory in real Hilbert space: How the complex Hilbert space structure emerges from Poincaré symmetry"*, [arXiv:1611.09029](https://arxiv.org/abs/1611.09029)** — The direct continuum analogue. Poincaré symmetry on a real Hilbert space, with non-negative squared-mass operator, forces a unique-up-to-sign Poincaré-invariant complex structure J commuting with the algebra of observables. Our (a)/(b) is the discrete-substrate counterpart of this question. A future closure of (a)/(b) would presumably take the form: *find a discrete analogue of Poincaré symmetry on the K/P plane, then run a Solèr-Moretti-Oppio-style argument.*

### Adjacent / foil programs

- **Smolin & Cortês, *"The universe as a process of unique events"* and *"Energetic Causal Sets"*, [arXiv:1308.2206](https://arxiv.org/abs/1308.2206)** — Propose a foundation for relativistic quantum theory in which operators play no role at the fundamental level: "only causality, energy, and momentum." This makes a different strategic choice from ours — they do not derive Hilbert space from causal structure; they put quantum amplitudes and causal structure on equal footing. Worth reading as a foil paper: their move is to refuse to do what our program is trying to do, on the grounds that the derivation may be impossible. Whether they are right is partly an empirical question about whether (a)/(b) admits closure.

- **Soulas, Franzmann & Di Biagio, *"On the emergence of preferred structures in quantum theory"*, [arXiv:2512.07468](https://arxiv.org/abs/2512.07468) (Dec 2025)** — Hilbert Space Fundamentalism: tries to recover tensor product structure, locality, and preferred observables from the Hamiltonian and state alone. Adjacent territory with **opposite directionality**: they derive structure from within QM; we try to derive structure upstream of QM. Their no-go obstacles and our (a)/(b) gap are pointing at the same structural difficulty — complex Hilbert space structure is hard to get for free, and any framework claiming to derive it must identify exactly where the work is being done.

### Lean-formalized physics — venue and methodological tradition

- **Meiburg, Lessa & Soldati, *"A Formalization of the Generalized Quantum Stein's Lemma in Lean"*, [arXiv:2510.08672](https://arxiv.org/abs/2510.08672) (Oct 2025)** — From the Lean-QuantumInfo group (Timeroot et al.) whose `HermitianMat` infrastructure the bridge in [`tomdif/kf-hermitian-lean`](https://github.com/tomdif/kf-hermitian-lean) is built on. ~1000 theorems, ~250 definitions, ~15K lines of Lean as of Oct 2025. The library is active and well-supported. **Template for our eventual writeup**: same authors, same library, same Lean-physics community.

- **Douglas, Hoback, Mei & Nissim, *"Formalization of Free Quantum Field Theory in Lean 4"*, [arXiv:2603.15770](https://arxiv.org/abs/2603.15770) (Mar 2026)** — Formalization of free bosonic QFT in 4D Euclidean spacetime satisfying the Glimm–Jaffe / Osterwalder–Schrader axioms in Lean 4 + Mathlib. **Methodologically directly relevant**: the bridge work is in the same tradition. Importantly, Michael R. Douglas (a coauthor) is now actively engaged in Lean-formalized physics, which makes the framing "Lean-formalized infrastructure for a discrete-substrate quantum framework, in the methodological tradition of Douglas et al." legible and serious to mathematical-physics audiences. Worth re-reading before any further endorsement / submission contact.

### Methodological references for the future dimension-test program (not Phase 4)

These are flagged for future work outside Phase 4, recorded here for completeness:

- **Carlip, *"Dimension and dimensional reduction in quantum gravity"*, [arXiv:1710.00938](https://arxiv.org/abs/1710.00938)** — Causal-set spectral dimension drops to ≈ 2 at small distances on Minkowski sprinklings of d=3,4,5. Important context for any Phase-1 sanity floor of a future dimension-test: short-distance dimensional reduction is a real feature of the substrate, not an estimator bug, and finite-size corrections must be calibrated against this known phenomenon.

- **Gorard, *"Algorithmic Causal Sets and the Wolfram Model"*, [arXiv:2011.12174](https://arxiv.org/abs/2011.12174)** — Reformulates local dimension estimation as generalizations of the midpoint scaling estimator on causal sets, compatible with the Myrheim–Meyer estimator. Useful prior art for any future two-estimator approach.

---

## Phase 4c — `LayerB/PosetGrowthIsQuantum.lean`

*Pending. Diagnostic to be added here when 4c is started.*

The 4c diagnostic is expected to be the most interesting because the unitarity-from-order-growth claim is the deepest structural claim of the chain. The same caveat-conditional approach applies; the same diagnostic discipline (name what is derived, name what is postulated, name additional Case 3 findings explicitly).

---

## Cross-cutting observations

Findings that span multiple sub-phases will be added here as Phase 4 progresses. As of 2026-05-01 (after 4a):

- **The complex Hilbert space structure is presupposed throughout.** All three Phase 4 target files (`ComplexFromDressing`, `BornRuleUnique`, `PosetGrowthIsQuantum`) inherit ℂ from the type signatures of their inputs. The bridge does not change this — the bridge produces `Matrix _ _ ℂ` whose `ℂ` is also presupposed. The single open structural question (a)/(b), once closed, would close the gap for all three files simultaneously.

- **The retrospective is a living document.** New findings get appended; nothing is removed. If a finding is later overturned by deeper analysis (e.g., a candidate J is found in a file not searched in 4a), the original entry stays and a new entry records the update. The audit trail is the value.

---

## Phase 4d — Retrospective extension (swarm, 2026-05-01)

A swarm of research agents was tasked with extending the Phase 4a–c diagnostic discipline to additional `LayerA` and `LayerB` files in the framework. Eight files audited:

`AmplitudeUniqueness.lean`, `BellTheorem.lean`, `CPTFromKP.lean`, `Decoherence.lean`, `NoSpookyAction.lean`, `BigBangIsPosetMinimum.lean`, `ContinuousTimeEmergent.lean`, `Baryogenesis.lean`.

### Tabulated findings

| File | Type | Overclaim? | New gap? | Inherits ℂ? |
|---|---|---|---|---|
| `AmplitudeUniqueness.lean` | Case 1 | No | No | Yes (SO(2) inherited) |
| `BellTheorem.lean` | Case 1 | No | No | Yes (ℂ + N_w inherited) |
| `CPTFromKP.lean` | Case 1 | No | No | No (ℝ-level proof) |
| `Decoherence.lean` | Case 1 | No | No | Yes (ℂ inherited) |
| `NoSpookyAction.lean` | Case 1 | No | No | No (order-theoretic) |
| `BigBangIsPosetMinimum.lean` | Case 1 | No | No | No (order-theoretic) |
| `ContinuousTimeEmergent.lean` | Case 1 | Minor physics gloss | No | No (order-theoretic) |
| `Baryogenesis.lean` | **Case 3** | **Yes (condition 3)** | **Yes (out-of-equilibrium not formalized)** | Implicit (SM structure) |

**Summary statistics:** 7 Case 1 / 0 Case 2 / 1 Case 3.

### Key cross-cutting finding

**The ℂ-presupposition is localized, not spreading.** Files operating at the ℝ level (`CPTFromKP`, `NoSpookyAction`, `BigBangIsPosetMinimum`, `ContinuousTimeEmergent`) avoid the ℂ-presupposition entirely. Files operating at the amplitude/observable level (`AmplitudeUniqueness`, `BellTheorem`, `Decoherence`) inherit it without adding new layers.

This is meaningful for the strategic position of the framework: the open question (a)/(b) from Phase 4a is **the** structural gap, not one of many. Closing it would close the framework's complex-structure derivation in one stroke.

### Baryogenesis Case 3 detail

`Baryogenesis.lean`'s opening docstring claims all three Sakharov conditions are "DERIVED, not assumed." The file proves:

- **(1) B violation** from gauge invariance of `qqql`: derived. ✓
- **(2) CP violation** from CKM with 3 generations: derived. ✓
- **(3) Out-of-equilibrium** from electroweak phase transition: **stated in a comment, not formalized in Lean**.

The master theorem `sakharov_conditions` does not include condition (3) as a formal hypothesis. The docstring's claim to derive condition (3) is not supported by the code.

**Recommended (A) edit (deferred for user decision):** reword the opening to distinguish DERIVED conditions (1)–(2) from STATED condition (3). Specifically: "Conditions (1) and (2) are derived from the framework. Condition (3) is stated as a hypothesis: the electroweak phase transition provides out-of-equilibrium dynamics. Note: in the SM the transition is a crossover (insufficient for baryogenesis); the framework's predicted Poisson-fluctuation contribution from the causal-set substrate is referenced but not formalized."

### Negative finding (no new ℂ-derivation discovered)

**No file in the 4d batch derives complex structure from order-theoretic data in a way the earlier diagnostic missed.** This was an explicit search target. The negative result strengthens the Phase 4a finding: there is one structural gap, not several latent ones.

### What 4d does NOT cover

The audit did not extend to `QuantumMechanicsIsATheorem.lean`, `PhysicsFromCounting.lean`, the Capstone files, or any of the `LayerC/` content. A future 4e batch could continue the discipline if needed.
