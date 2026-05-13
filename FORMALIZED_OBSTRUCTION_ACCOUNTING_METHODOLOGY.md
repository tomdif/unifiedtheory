# Formalized Obstruction Accounting: A Methodology for Separating Structure from Coincidence

A reusable workflow for pattern discovery in mathematics and physics,
distilled from the LayerC formalization at `UnifiedTheory/LayerC/`.

Version 1.0 — 2026-05-13

---

## 1. Executive Summary

**Formalized Obstruction Accounting** is a workflow for turning a
suggestive numerical or structural pattern into either (a) a small set
of proved structural anchors, or (b) a precisely characterized stack of
proved obstructions, with no claim left unfiled.

The methodology has four moving parts:

1. A **pattern surface** (an empirical observation: a numerical
   coincidence, a combinatorial regularity, a Lie-theoretic match).
2. An **initial formalization** in a proof assistant (Lean / Coq /
   Agda) that makes the pattern's content unambiguous.
3. A **strengthening loop**: for every plausible upgrade of the pattern
   ("this implies X"), the loop ends with either a Lean proof or a Lean
   refutation. Nothing is left as folklore.
4. An **obstruction catalog**, carrying equal status with the positive
   theorems, recording exactly which stronger interpretations have been
   ruled out and why.

It solves a specific problem: pattern-driven research routinely
produces results of the form "we found X; X looks deep." Reviewers
cannot easily separate the structural part of X from the coincidental
part. This methodology forces that separation into a single
machine-checked artifact. It is most useful in domains where the
ambient mathematics is rich enough that the pattern can be tested
against many strengthenings, and where formalization is tractable
(elementary number theory, finite Lie data, finite group representation
theory, combinatorial spectral data).

---

## 2. The Problem

Numerical and structural patterns are abundant in mathematics and
physics. Examples: the Riemann zeros' GUE-like statistics, dimensions
that "happen to be" Lie algebra dimensions, low-dimensional accidents
(Spin(6) ≃ SU(4), 248 = 8 + 240, etc.), and innumerable lattice
coincidences. Most such patterns are coincidental in the sense that no
deeper structural reason connects them to anything else. A few are
genuine. Distinguishing the two is hard, and reviewers' caution is
warranted.

The traditional defense against pattern-spotting is one of the
following:

- **Sociological**: experts dismiss the pattern as numerology.
- **Statistical**: argue the prior probability of the coincidence is
  high given the search space.
- **Local proof**: prove a single theorem that explains the pattern.

These are all reasonable, but each leaves residual fog. The skeptic
cannot easily tell which interpretations of the pattern have been
genuinely refuted and which are merely undiscussed. The pattern's
proponent has no protocol that forces them to refute their own
strongest interpretations. Conversely, when a pattern does carry real
structure, ad-hoc refutation of stronger claims is rarely catalogued,
so later researchers re-attempt the same dead ends. **Formalized
Obstruction Accounting** addresses both gaps with one mechanism: every
strengthening is filed, either as theorem or as refutation, in a single
machine-checked location.

---

## 3. The Methodology

The workflow proceeds in seven steps. The LayerC work on the typed
atomic packet `{2, 3, 4, 5, 7}` is used as the running example.

**(a) Pattern surface.**
Identify a specific, formalizable observation. In LayerC, the surface
observation was that the multiset `{2, 3, 4, 5, 7}` appeared as the
combined slot vector `(|Z(H1)|, rank H1, |Z(G)|, rank G, dim V_{H1})`
of a Spin(a) × Spin(b) ⊂ Spin(a+b) inclusion. The pattern surface
must be precise enough to encode in Lean's type system without
metaphors.

**(b) Initial formalization.**
Encode the pattern as Lean definitions and prove the immediate
structural facts. In LayerC, this produced `CandidateOperator.lean`
(uniqueness for n ≤ 50) and then `CandidateOperatorUnbounded.lean`
(uniqueness for all n, by elementary number theory). At this point the
pattern is no longer a numerical curiosity; it is a theorem with a
finite type signature.

**(c) Strengthening attempts.**
Enumerate the "stronger" claims that an enthusiastic reader might
infer: that the pattern implies a Lie algebra structure on the atoms;
that it implies a canonical Schur bridge to a chamber operator; that
it picks out a Pati-Salam mediator; that it gives a chirality
projection; that the three realizations are functorial co-images of a
common source. Each candidate strengthening is given its own Lean
file.

**(d) Obstruction proofs.**
Each strengthening file ends in one of two ways: a proof that the
strengthening holds, or a proof that it fails. LayerC produced nine
strengthening failures, each formalized as a no-go theorem:
`ChiralityObstruction.lean`, `Avenue2Test.lean`,
`ChiralityProjectionAttack.lean`, `OrbifoldObstruction.lean`,
`PacketRealizationFunctor.lean`, and others. Refutations are not
"nothing happened"; they are theorems. They restrict where the
pattern's content actually lives.

**(e) Retain only survivors.**
The structural anchors are the strengthenings that survived. LayerC
retained six: meta-selection of the typed packet
(`TypedPacketMetaSelection.lean`), uniqueness of the spin pair
(`CandidateOperatorUnbounded.lean`), effective rigidity of J_4
(`TypedPacketRigidityRigid.lean`), the unified meta-theorem
(`UnifiedSelectionSpectralTheorem.lean`), the affine residue 11
(`AffineResidueAnalysis.lean`), and the G1 Volterra derivation
(`G1ClosureVolterraDerivation.lean`).

**(f) Catalog obstructions.**
The obstruction list is its own first-class artifact, with equal
status to the anchor list. In LayerC, the obstruction catalog is
written into `MasterFormalization.lean` Section 3 alongside the anchor
catalog (Section 2). A reader can verify both by `decide`.

**(g) Honest scope statement.**
The final artifact states explicitly **what is proved**, **what is
not proved**, and **what gaps are labeled** (e.g., the Spin↔Volterra
correspondence in LayerC is checked at rational-equality level but
not lifted to an internalized functor; this is labeled, not silently
assumed). See Section 7 of `MasterFormalization.lean`.

The seven steps are deliberately mundane. The methodology's value is
that it forces every claim, positive or negative, into the same
filing format.

---

## 4. Obstruction-Accounting Protocol

The protocol is a set of bookkeeping rules. None are individually
deep. Together they prevent the standard failure modes of
pattern-driven research.

- **Every strengthening attempt ends with a proof or a refutation.**
  No strengthening is allowed to remain as folklore, "well-known to
  fail," or "left as future work." If the proof attempt is not yet
  closed, the file remains open and is listed under "scaffold," not
  under "anchor."

- **Refutations are theorems.** A refutation is filed in the same
  Lean module style as a positive theorem, with `theorem` keyword,
  imports, and statement. It is not a comment. In LayerC,
  `chirality_obstruction_theorem` and `single_Z2_obstruction_theorem`
  are first-class Lean theorems.

- **Obstructions sit equal to anchors.** The publishable artifact
  contains a list of anchors and a list of obstructions. Neither
  list dominates. The user's headline statement of the result must
  reference both lists or neither. (See `MasterFormalization.lean`
  Sections 4 and 5: `master_statement` and `obstruction_summary`,
  symmetric placement.)

- **Gaps are labeled, not hidden.** When a derivation is verified at
  a lower level (e.g., rational equality) but not at the desired
  level (e.g., internalized functor), this is recorded as a
  **functorial gap** or **definitional bridge**, with a one-line
  statement of what is and is not proved. LayerC's residual
  Spin↔Volterra map is the canonical example.

- **Minimality conditions are pre-registered.** Before
  strengthening a pattern by "the smallest case satisfying X," the
  exact X must be written into a Lean definition. This prevents
  retroactive curve-fitting. Pre-registration is the same discipline
  as `kitaev_chain_criteria_PRECOMMIT` and the BRS five-gate
  validator referenced in the user's project memory.

- **No "obvious" obstructions.** If an obstruction is "obvious," it
  is still given a file. The cost of writing the file is small; the
  cost of a missing entry that a referee catches is large.

- **Single-master-file rule.** All anchors and obstructions are
  re-exported from one file (LayerC's `MasterFormalization.lean`).
  Every count is verified by `decide` (`six_anchors`,
  `nine_obstructions`). The master file is the unit of citation.

---

## 5. Worked Example

The LayerC formalization advanced through the labelled versions v5.2
through v5.5.2 over two days. The arc is recorded in
`MasterFormalization.lean` Section 9 (`two_day_arc`, 13 entries). The
following is a compressed version focusing on how each obstruction
sharpened the surviving claims.

**v5.2 — Numerical taxonomy.**
The atomic vocabulary `{2, 3, 4, 5, 7}` was identified empirically.
At this stage the framework was vulnerable to "numerology" criticism.

**v5.3.0 — Paradigm shift.**
Moved from taxonomy to dynamics: rather than "these numbers appear,"
the question became "what operator-selection conditions force them?"

**v5.3.1–v5.3.2 — First anchors.**
`CandidateOperator.lean` and `CandidateOperatorUnbounded.lean`:
GIVEN the typed slots, the unique solution is (a, b) = (7, 3).
This is anchor 2. It survives.

**v5.3.4 — First obstruction.**
`Avenue2Test.lean`: the canonical Schur bridge from
Spin(7)×Spin(3)-invariant operators to a Feshbach-like J_4
block fails. By Schur's lemma the canonical Schur complement is
scalar, not a non-trivial matrix. Obstruction 4.

**v5.3.5 — Co-realization scope correction.**
`ChamberSpin10Bridge.lean`: the connection between structural,
spectral, and combinatorial realizations is **co-realization without
mechanism**. This is itself a constraint: it rules out claiming any
of the three realizations is "fundamental."

**v5.4.4–v5.4.6 — Chirality obstruction stack.**
Three independent strengthenings to Standard Model phenomenology
were attempted and refuted in sequence: subgroup branching
(`ChiralityObstruction.lean`), single-Z_2 projection
(`ChiralityProjectionAttack.lean`), and Z_2 × Z_2 orbifold
(`OrbifoldObstruction.lean`). Obstructions 6, 7, 8.

**v5.5.0 — Track H meta-selection.**
`TypedPacketMetaSelection.lean`: from three minimality conditions
on Spin block inclusions, the typed packet is forced. This is
anchor 1. It pre-registers the minimality conditions in Lean.

**v5.5.1 — J_4 effectively rigid.**
`TypedPacketRigidityRigid.lean`: J_4 is uniquely forced entry by
entry (anchor 3). The unified meta-theorem composes anchors 1–3
into one chained statement (anchor 4).

**v5.5.2 — G1 closure with labeled gap.**
`G1ClosureVolterraDerivation.lean`: the Volterra → spectral atoms
derivation is closed at rational-equality level. The Spin↔Volterra
functorial map is labeled as residual (anchor 6, the only one with
a labeled gap). `PacketRealizationFunctor.lean` simultaneously
refutes the strongest categorical reading of the co-realization
(obstruction 9).

End state: six anchors, nine obstructions, one labeled gap, zero
`sorry`, zero custom axioms across all anchor and obstruction files.
The headline is a chained statement plus an obstruction stack of
equal length, neither summarizable without the other.

---

## 6. Applicability Domain

Formalized Obstruction Accounting is well-suited to a specific
class of problem. Key conditions:

- **The pattern observation has multiple plausible interpretations.**
  If the only candidate strengthening is a single conjecture, the
  obstruction stack will be too thin to be informative.

- **The ambient mathematics has enough internal structure to test
  claims.** Representation theory of small Lie algebras, finite group
  theory, finite-dimensional spectral data, and elementary number
  theory all qualify. Combinatorial and lattice structure also
  qualifies when finite enumeration is tractable.

- **Formalization is tractable.** A Lean / Coq / Agda encoding of
  the basic objects should take days, not months. If the basic
  objects (e.g., a category of model-theoretic structures) require
  a full library build before the first definition, the methodology
  works but is heavy. Mathlib is sufficient for most cases the
  methodology was designed for.

- **The user is willing to accept negative results as informative.**
  This is the cultural prerequisite. The methodology's output is
  not "a theorem"; it is "a theorem and a list of theorems-that-fail."
  A user who only values positive results will under-invest in the
  obstruction catalog and the methodology will degrade to ordinary
  formalization.

The methodology is **not** suited to: open conjectures of
century-old standing (Goldbach, RH at top level); problems where
the obstruction set is unboundedly large; problems where the
"pattern" is informal or pre-mathematical.

---

## 7. AI-Assisted Variants

LLM-agent swarms (e.g., parallel ToolSearch / sub-agent runs) are
a natural multiplier inside Step (c) of the methodology
(strengthening attempts). They are less useful inside Steps (d–e)
(obstruction proofs and survivor retention), where verification
remains a deterministic Lean kernel check.

Useful agent roles:

- **Parallel strengthening enumeration.** An agent enumerates
  plausible strengthenings of the pattern in parallel, returning a
  candidate list. The user filters this list against
  pre-registered minimality conditions.

- **Literature scoping.** An agent searches whether each candidate
  strengthening has already been refuted in published mathematics.
  If so, the obstruction is filed by citation rather than re-proof.

- **Lean draft generation.** An agent drafts the file skeleton
  (imports, namespace, definition stubs) for a candidate
  strengthening. The user closes the proof or the refutation.

- **Cross-check on negative results.** Multiple independent agents
  attempt the strengthening; convergence on the refutation is a
  weak prior, not a proof. The methodology requires the proof
  itself to live in Lean.

The user's own past pattern (Pattern 13: "calibrate before hash";
the diagnostic-vs-name rule) is the directly relevant working-style
constraint: agents may surface candidates but cannot file
obstructions; only a Lean kernel check can. This keeps the agent
swarm honest.

---

## 8. Connection to Literature

Several existing methodologies overlap with Formalized Obstruction
Accounting. None do the same job.

- **Tarski-style formalization** (Tarski, Mizar, Isabelle/HOL,
  Lean/Mathlib): proves positive theorems in a formal system. Says
  nothing about pattern-discovery filtering. The current methodology
  *uses* Tarski-style formalization as substrate but adds the
  obstruction catalog as a first-class output.

- **Lakatosian proof-by-refutation** (Lakatos, *Proofs and
  Refutations*): philosophical account of how proofs are refined by
  counter-examples. The current methodology is the formal-systems
  analogue, with refutations as machine-checked artifacts rather
  than informal counter-examples in dialogue.

- **Bayesian conjecture testing**: prior/posterior probability that
  a conjecture is true given evidence. Useful at the
  surface-pattern stage; orthogonal to obstruction accounting,
  which deals in proofs, not priors.

- **Automated theorem proving / SMT / tactic search**: tools for
  closing individual proofs. The methodology consumes these tools
  but is silent on which tool is used.

- **Symbolic AI methodology** (e.g., classical knowledge bases,
  ontology engineering): structured cataloging of facts. Closest
  prior art in spirit. The novelty here is the **symmetric**
  treatment of negative theorems alongside positive ones, in a
  single proof-assistant artifact.

**What is new:** Formalized Obstruction Accounting elevates the
*obstruction catalog* to first-class status, parallel to the anchor
catalog, both verified by the same proof kernel and exported from
the same master file. The author is not aware of a methodology that
prescribes this symmetry as a workflow rule. The methodology itself
is boring; that is part of its value.

---

## 9. Reproducible Template

A user applying this methodology to a new pattern can expect the
following file layout in a `Project/PatternX/` directory:

1. `PatternSurface.md` — natural-language description of the
   pattern, with explicit candidate strengthenings (typically 5–15).

2. `BaseFormalization.lean` — Lean definitions of the objects in
   the pattern. Type-checked but minimal.

3. `Anchor_<N>.lean` (one file per surviving structural theorem) —
   each file proves one anchor theorem in isolation. Self-contained
   imports, single `theorem`, status string.

4. `Obstruction_<N>.lean` (one file per refuted strengthening) —
   each file proves one no-go theorem. Same shape as anchor files.
   The `what_is_blocked` string in the obstruction record should be
   one sentence.

5. `Scaffold_<N>.lean` (optional) — open conjectures, in-progress
   attempts that are neither proved nor refuted. Clearly labeled as
   such and not exported as either anchor or obstruction.

6. `MasterFormalization.lean` — single file that imports everything,
   exports the anchor list, the obstruction list, the scaffold
   list, the master-statement string, the obstruction-summary
   string, and an `honest_scope` statement. Counts verified by
   `decide`. See LayerC's
   `UnifiedTheory/LayerC/MasterFormalization.lean` for a template.

7. `README.md` (optional) — high-level narrative arc.

Citation: cite the master file. Individual anchors and obstructions
can be cited by their theorem name with `MasterFormalization`'s
qualified namespace.

---

## 10. Honest Limitations

The methodology has clear limits.

- **It does not produce new mathematics.** Steps (a), (c), (e)
  require human or domain-specific insight. The methodology adds
  discipline to a research workflow; it does not replace the
  workflow.

- **The obstruction catalog is incomplete by construction.** No
  finite catalog can refute every conceivable strengthening of a
  pattern. The user must accept that "the obstruction list is what
  we tried, not what is possible." A later researcher may find
  a strengthening route that this catalog did not consider.

- **Formalization cost can dominate.** For patterns whose ambient
  objects are not yet in a proof library, the cost of getting to
  Step (b) may exceed the cost of an informal pattern study. The
  methodology is most efficient when Mathlib (or equivalent) already
  carries the relevant objects.

- **Negative results have social costs.** Even when properly filed,
  refutations are less rewarded than positive theorems. A researcher
  who religiously applies the methodology may produce more
  obstructions than anchors and find their work undervalued.

- **The methodology cannot adjudicate between "the pattern is
  real but the structure is deeper than we tested" and "the pattern
  is coincidence."** It can only state: "of the K strengthenings
  we filed, J were refuted and (K − J) survived." The interpretation
  is left to the reader.

- **Pre-registration discipline is fragile.** Without explicit
  Lean definitions before strengthening attempts begin, the
  protocol degrades to post-hoc curve-fitting. This is the
  methodology's most failure-prone step in practice, and is
  closest in spirit to the user's locked rule about calibrating
  pipelines before hashing precommit thresholds.

The methodology is a tool, not a verdict. Its output is a clearly
filed pair of lists; whether those lists are scientifically valuable
is a separate question.

---

*Evidence base.* All claims about LayerC are verified against:
`UnifiedTheory/LayerC/MasterFormalization.lean` (master spine,
six anchors and nine obstructions enumerated and counted by
`decide`), `UnifiedTheory/LayerC/TypedPacketMetaSelection.lean`
(meta-selection conditions and uniqueness), and the obstruction
files `ChiralityObstruction.lean`, `Avenue2Test.lean`,
`ChiralityProjectionAttack.lean`, `OrbifoldObstruction.lean`,
`PacketRealizationFunctor.lean`. Status assertions are taken
verbatim from those files' status strings; counts are taken from
the `decide`-checked theorems `six_anchors`, `nine_obstructions`,
`manifest_count`, `arc_count`, `citation_count`.
