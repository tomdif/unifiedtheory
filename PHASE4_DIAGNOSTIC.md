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

*Pending. Diagnostic to be added here when 4b is started.*

Specific things to look for, given what 4a surfaced:

1. **Does `BornRuleUnique` invoke `ComplexUniqueness`?** If so, its headline claim is presumably some refinement that goes beyond "uniquely SO(2)-invariant quadratic observable" — perhaps "uniquely SO(2)-invariant quadratic that is also additive over orthogonal projectors" or similar. Worth understanding what additional constraint is being applied and whether it is derived or postulated.

2. **Probabilities (Born I) vs expectation values (Born II)?** The Born rule has two faces:
   - (Born I) Probabilities for measurement outcomes: `Pr(outcome i) = |⟨ψ|i⟩|²`.
   - (Born II) Expectation values of observables: `⟨A⟩ = Tr(ρ A)` for self-adjoint `A`.
   Gleason's theorem connects them. Does `BornRuleUnique` claim (I), (II), or both? If only (II), it is much closer to what the 2D-uniqueness theorems already give. If (I), there is additional structural content (probability assignment to projectors, additivity over orthogonal projectors) that needs separate auditing.

3. **Pure states vs density matrices?** Some "Born rule derivations" are really only rules for pure states and require extra work to extend to mixed states. The bridge produces Hermitian matrices generally; if `BornRuleUnique` is really a pure-state result, that is worth flagging explicitly.

---

## Phase 4c — `LayerB/PosetGrowthIsQuantum.lean`

*Pending. Diagnostic to be added here when 4c is started.*

The 4c diagnostic is expected to be the most interesting because the unitarity-from-order-growth claim is the deepest structural claim of the chain. The same caveat-conditional approach applies; the same diagnostic discipline (name what is derived, name what is postulated, name additional Case 3 findings explicitly).

---

## Cross-cutting observations

Findings that span multiple sub-phases will be added here as Phase 4 progresses. As of 2026-05-01 (after 4a):

- **The complex Hilbert space structure is presupposed throughout.** All three Phase 4 target files (`ComplexFromDressing`, `BornRuleUnique`, `PosetGrowthIsQuantum`) inherit ℂ from the type signatures of their inputs. The bridge does not change this — the bridge produces `Matrix _ _ ℂ` whose `ℂ` is also presupposed. The single open structural question (a)/(b), once closed, would close the gap for all three files simultaneously.

- **The retrospective is a living document.** New findings get appended; nothing is removed. If a finding is later overturned by deeper analysis (e.g., a candidate J is found in a file not searched in 4a), the original entry stays and a new entry records the update. The audit trail is the value.
