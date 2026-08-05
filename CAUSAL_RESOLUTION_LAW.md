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

The formal theorem uses two microscopic principles.

1. **Outcome locality.** The operator belonging to child `c` has support only
   on the carrier ray labelled by `c`.
2. **Coherent conservation.** An unresolved birth preserves every incoming
   carrier amplitude, equivalently `Σ_c K_c = I`.

Outcome locality reduces each operator to one unknown diagonal coefficient.
Coherent conservation fixes every coefficient to one. Hence

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
- the unique state-independent map preserving all record weights while
  exactly separating distinct records.

The capstone theorem is `causalNativeResolutionLaw_capstone` in
`UnifiedTheory/Audit/KFCausalNativeResolutionLaw.lean`.

## Physical claim boundary

This is a new **candidate microscopic law for the repository**, not yet an
empirically established law of nature. The pinching channel itself is standard
quantum mathematics; the distinctive synthesis is that causal successors
intrinsically provide both its Hilbert carrier and its pointer basis, while
the repo's conservation principle fixes the operators.

The remaining bridge is precise: causal microphysics must enforce outcome
locality and embed `H_C` as a protected observable record. If the chiral datum
is stored in off-diagonal coherence of this same carrier, the law erases it.
Thus a viable physical realization must put chirality in a diagonal sector,
a separate protected carrier, or a derived larger observable algebra.

## Falsifiable form

If the native successor record is physically realized, one causal resolution
step predicts complete suppression—not gradual damping—of interference
between distinct registered successors while leaving their diagonal Born
weights unchanged. Observation of persistent cross-successor coherence in a
system known to instantiate this record algebra would falsify the sharp law
and require a partial-resolution generalization.
