# Native Causal Resolution Law

## Law

For a finite causal parent `C`, let `Succ(C)` be its genuine unlabeled
one-element children and let

```text
H_C = ℓ²(Succ(C)).
```

The native causal resolution law is

```text
K_c = |c><c|,

R_C(ρ) = Σ_{c ∈ Succ(C)} K_c ρ K_c†.
```

Equivalently,

```text
R_C(ρ)_{cd} = ρ_{cc}  when c=d,
             = 0       when c≠d.
```

The causal alternatives themselves therefore select the record basis; no
external outcome labels, phase, rate, or normalization coefficient enters.

## Derivation

The strengthened formal theorem uses two microscopic principles.

1. **Sharp native Born effects.** The observable effect of child `c` is its
   native record projector: `K_c†K_c=|c><c|`. This specifies probabilities,
   not the post-measurement output direction.
2. **Coherent conservation.** An unresolved birth preserves every incoming
   carrier amplitude, equivalently `Σ_c K_c = I`.

Sharp effects imply exclusive response by positivity: every false-child
probability is a sum of squared complex amplitudes, so probability zero
forces each false amplitude to vanish. Sharp effects alone also imply
aggregate Born completeness. Coherent conservation then forces the remaining
column of `K_c` to be exactly the `c`-th basis vector. Thus exclusive
response, output nondemolition, full two-sided outcome locality, and Born
completeness are consequences rather than support assumptions. Hence

```text
K_c = |c><c|
```

is unique within the ansatz. Because these operators are orthogonal
projectors resolving the identity,

```text
Σ_c K_c† K_c = I
```

follows automatically. The law therefore also preserves every Born
quadratic form and defines a genuine CPTP instrument.

There is a second, independent channel-level characterization. If a
state-independent operation:

1. depends only on the registered diagonal successor data; and
2. fixes every already-resolved successor record,

then it is uniquely `R_C`. This uniqueness does not assume linearity,
positivity, complete positivity, or a Kraus representation. Those properties
are subsequently supplied by the forced projector realization.

Lean also contains an explicit two-outcome counterexample satisfying
exclusive response but violating output locality. This certifies that the
intermediate implication genuinely weakens the former hypothesis; it is not
a verbal repackaging of the same condition.

## Exact consequences

Lean proves that the law is:

- defined at every finite causal parent from its actual physical children;
- completely positive and trace preserving;
- coherently exhaustive and Born complete;
- idempotent: one resolved record is already stable;
- covariant under arbitrary renaming of successors;
- nondemolition on every classical child weight;
- exactly destructive on coherence between different child records;
- non-identity whenever a parent has two distinct physical children;
- the unique operation satisfying record sufficiency and record
  nondemolition;
- full output locality as a derived consequence of exclusive response and
  coherent conservation;
- exclusive response and aggregate Born completeness as consequences of the
  child-by-child sharp Born effects.

The capstone theorem is `causalNativeResolutionLaw_capstone` in
`UnifiedTheory/Audit/KFCausalNativeResolutionLaw.lean`.

## Physical claim boundary

This is a new **candidate microscopic law for the repository**, not yet an
empirically established law of nature. The pinching channel itself is standard
quantum mathematics; the distinctive synthesis is that causal successors
intrinsically provide both its Hilbert carrier and its pointer basis, while
the repo's conservation principle fixes the operators.

The remaining bridge is precise: causal microphysics must enforce the sharp
native Born effects and embed `H_C` as a protected observable record. This is
an operational probability principle rather than a hidden matrix-support
assumption, but it remains physical input. If the chiral datum is stored in
off-diagonal coherence of this same carrier, the law erases it. Thus a viable
physical realization must put chirality in a diagonal sector, a separate
protected carrier, or a derived larger observable algebra.

## Falsifiable form

If the native successor record is physically realized, one causal resolution
step predicts complete suppression—not gradual damping—of interference
between distinct registered successors while leaving their diagonal Born
weights unchanged. Observation of persistent cross-successor coherence in a
system known to instantiate this record algebra would falsify the sharp law
and require a partial-resolution generalization.
