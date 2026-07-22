# Regular three-product sheet bridge audit

## What is now derived

`UnifiedTheory/Audit/KFCausalProduct3SheetBridge.lean` formalizes the proposed
bridge on the elementary local tangent cube

```text
B3 = Set (Fin 3) ~= {0,1}^3.
```

Its intrinsic sheet type is the subtype of order atoms of `B3`. Lean proves:

1. the atoms are canonically equivalent to `Fin 3`, hence there are exactly
   three primitive directions;
2. every order automorphism preserves the atom subtype;
3. restriction to atoms and extension by direct image are inverse;
4. restriction preserves composition.

Consequently

```text
Aut_ord(B3) ~= Perm(Fin 3) = S3
```

as an automorphism law, not merely as an equal-cardinality observation.

This supplies a mathematically intrinsic source for the three-sheet symmetry:
the sheets are primitive local causal directions rather than three temporally
ordered slices.

## Directional birth current

For a complex incidence profile `chi : Sheet -> C`, the module defines

```text
J(chi) = sum_s chi(s) v_s,
```

where `v_s` are the canonical simplex vertices already constructed in the
zero-sum carrier. Coordinatewise, Lean proves

```text
J(chi)(s) = chi(s) - (sum_t chi(t))/3.
```

Thus `J` is exactly the trace-free projection of directional incidence. It is
equivariant under every relabeling. For binary incidence the exact outcomes
are:

| Active primitive directions | Current |
|---|---|
| none | `0` |
| one direction `s` | `v_s` |
| two directions | `-v_missing` |
| all three | `0` |

The one- and two-direction currents both have squared norm `2/3`. The carrier
therefore has a concrete geometric meaning: local directional anisotropy of a
causal birth. Isotropic growth remains in the discarded uniform line.

## Connection to twisted transfer

`RegularProduct3TransitionData` packages a causal target, complex edge weight,
and tangent-cube order automorphism on every edge. The automorphism theorem
turns each overlap into its unique `S3` sheet transport and instantiates
`TwistedSheetTransferData` from the previous module. Therefore every nonzero
unit twisted eigen-section automatically supplies a normalized Hermitian
strongly positive branch functional.

The transfer and positivity consequences are no longer missing. They remain
conditional on the chart/overlap data and eigen-section.

## Exact remaining bridge theorem

The repo still does **not** prove that a regular causal or CSpec neighborhood
comes with an intrinsic local order chart equivalent to `B3`, or more generally
to `C_m^3`, with overlap maps induced by the causal geometry. This is the new
geometric frontier:

```text
regular causal neighborhood
  -> unlabeled local three-product chart
  -> functorial overlap order isomorphisms.
```

If a fixed global factor labeling is retained, the resulting sheet bundle is
trivial and its apparent holonomy is gauge-removable. Genuine monodromy needs
locally chosen factor orderings with no preferred global ordering.

The current module proves the entire finite fiber theorem once that atlas
exists; it does not manufacture the atlas or claim that the neighboring
causal-algebraic repository already contains it.

## Secondary open dynamics

Even with a nontrivial atlas, a canonical pure state requires a selected
nonzero eigen-section of the standard-sector transfer. Scalar
Perron--Frobenius positivity does not automatically select one because the
rank-two standard representation is not an entrywise-positive scalar sector.
The birth current is now a canonical source vector, but a spectral existence
or source-response theorem is still required to turn it into a distinguished
global section.
