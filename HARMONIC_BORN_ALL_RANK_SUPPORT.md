# Canonical harmonic Born support at every rank

Date: 2026-09-09

The canonical positive-radial harmonic Born law retains every physical
one-element extension at every finite rank, in both chiralities. Every finite
physical history consequently has strictly positive Born probability under the
existing infinite trajectory measure.

Formal module:
[`KFCausalSetHarmonicBornAllRankSupport.lean`](UnifiedTheory/Audit/KFCausalSetHarmonicBornAllRankSupport.lean).

This removes the rank-139 cutoff in the previous canonical-support proof. It
also removes the need to switch to the separately chosen phase-safe law merely
to obtain full support. It preserves the existing canonical law exactly.

## The argument

For an n-element causal parent C, let its imaginary partition polynomial be

\[
P_C(X)=\sum_{D\text{ downset of }C}
  \operatorname{Im}(i^{m(D)})X^{|D|(|D|-1)}\in\mathbb Z[X],
\]

where m(D) counts the maximal elements of D. The old proof bounded every
coefficient by 2^n and checked the harmonic numerator against that bound for
ranks 2 through 139. The rational-root argument only needs the constant term.

Only empty and singleton downsets have exponent zero. The empty downset
contributes zero to the imaginary coordinate; each singleton contributes one.
Singleton downsets correspond exactly to minimal events, so for n > 0,

\[
1\le P_C(0)=\#\min(C)\le n.
\]

The formal proof establishes the singleton count and its linear bound directly.
For n >= 2, write the existing harmonic coupling in lowest terms as

\[
\lambda_n=1+\frac{H_n}{2(n-1)}=\frac{a_n}{b_n}>1.
\]

The classical identity
\(v_2(H_n)=-\lfloor\log_2 n\rfloor\) implies

\[
v_2(\lambda_n)
=-\lfloor\log_2 n\rfloor-1-v_2(n-1).
\]

Therefore

\[
a_n>b_n\ge2^{\lfloor\log_2 n\rfloor+1}>n.
\]

The valuation fact is already proved in the pinned Mathlib dependency as
`padicValRat_two_harmonic`; its mathematical background is described in
[Keith Conrad's harmonic-sum note](https://kconrad.math.uconn.edu/blurbs/gradnumthy/padicharmonicsum.pdf).
The new contribution here is its application to the causal partition and Born
support, not a new theorem about harmonic numbers in isolation.

If P_C(lambda_n) were zero, the rational-root theorem would force a_n to divide
P_C(0). The displayed inequalities exclude this at every rank. The existing
real-part noncancellation and transition-fiber signature rigidity then imply
that every normalized physical raw edge has a nonzero imaginary component.
The positive real radial Born correction cannot erase that component. Ranks
zero and one use the already proved exact formulas, and complex conjugation
supplies the second chirality.

## Checked consequences

- `canonicalHarmonicBornShellTransition_ne_zero_iff_physical`: exact transition
  support at every rank, for the canonical law and both chiralities.
- `harmonicBornStagePMF_pos_iff_physical`: strictly positive next-step
  probability exactly for physical extensions.
- `harmonicFiniteBornPathWeight_pos_iff_physical`: strictly positive finite
  path weight exactly for physical paths.
- `harmonicBornTrajectoryMeasure_finiteCylinder_pos_iff_physical`: the existing
  infinite measure gives positive mass exactly to finite cylinders specified
  by physical histories.

The core support theorem's axiom audit contains only `propext`,
`Classical.choice`, and `Quot.sound`. The proof does not use the old
`native_decide` rank scan, `Lean.trustCompiler`, a project axiom, or `sorry`.
Importing the older audit module does not introduce its finite-computation
axioms into this theorem's dependency footprint.

Reproduce with:

```sh
lake build UnifiedTheory.Audit.KFCausalSetHarmonicBornAllRankSupport
```

Validation on 2026-09-09: the targeted build passed (8,416 jobs), the full
repository `lake build` passed (8,905 jobs), and `git diff --check` passed.
All four printed axiom audits, including finite-cylinder positivity, contain
only `propext`, `Classical.choice`, and `Quot.sound`.

## Physical boundary and next target

Strict positivity is not a uniform lower probability bound, a conditioning
estimate, or positive mass for an individual infinite history. This result
does not select the canonical radial correction from physical dynamics,
exclude alternative normalized laws, or derive a manifold/GR/QFT limit.

The most consequential next target remains connecting the actual harmonic
growth law to order-derived geometric recovery. The current Gate-3 repair
theorem quantifies over a constructed repair relation. It does not show that
the growth kernel realizes that relation. Exact full support sharpens the
test: any physical extension violating a proposed deterministic descent law
has positive probability and cannot be discarded as an amplitude zero. A
finite census should first test that deterministic condition and the expected
drift of a specified geometric defect under this exact canonical law. If only
expected descent survives, the appropriate recovery theorem needs stochastic
drift and hitting-time hypotheses instead of deterministic rank descent.
