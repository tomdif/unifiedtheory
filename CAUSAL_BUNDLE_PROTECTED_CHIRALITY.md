# Causal bundle protection of chirality

## Result

Sequential growth derives the finite-cylinder record equation even after an
internal sheet carrier is attached to every history:

```text
Q_c V_n = V_n P_c.
```

The proof uses only the support law of sequential growth: every refined
history has exactly one retained prefix.  The transition amplitudes and the
internal transport matrices are otherwise arbitrary.

The carrier is a direct sum indexed by histories, represented finitely as

```text
History x Internal.
```

It is not introduced as a physical system-environment tensor factor.  A
history-block pinching removes entries between distinct histories while
leaving every internal matrix inside one history block unchanged.  Lean
proves that this map is idempotent and trace-preserving.

## The full-S3 obstruction and its unique escape

In the basis `e1=(1,-1,0)`, `e2=(0,1,-1)` of the intrinsic zero-sum
three-sheet carrier, the adjacent transpositions are

```text
S1 = [[-1, 1], [0, 1]],
S2 = [[ 1, 0], [1,-1]].
```

Their ordinary commutant contains only scalar operators.  Consequently a
non-scalar chirality observable cannot be invariant under full `S3`
holonomy.

There is, however, one parity-odd operator shape:

```text
J = [[1,-2],[2,-1]].
```

The formalization proves

```text
S1 J = -J S1,
S2 J = -J S2,
```

and the rigidity theorem

```text
S1 M = -M S1 and S2 M = -M S2
  implies M = M[0,0] J.
```

Thus the sign-twisted commutant is exactly one-dimensional.  This is not an
arbitrary choice of Pauli-like operator.

For the intrinsic Gram matrix

```text
G = [[ 2,-1],[-1, 2]],
```

the observable `iJ` satisfies

```text
(iJ)† G = G (iJ),
(iJ)^2 = 3 I.
```

It is therefore Gram-Hermitian and has a universal normalization by
`1/sqrt(3)`.

## Relational transport law

Let `Xi(h)` be an orientation label on a history.  If an odd sheet transport
reverses it,

```text
Xi(h,b) = -Xi(h),
```

then the two sign reversals cancel:

```text
(-Xi iJ) U_b = U_b (Xi iJ).
```

Lean promotes this edgewise identity to the full sequential-growth
intertwiner at every rank:

```text
O_(n+1) V_n = V_n O_n,
```

where `O_n` is the fiberwise relational chirality `Xi iJ`.  The same module
proves that history-block pinching fixes `O_n` exactly.  Therefore sharp
history records and nonzero relational chirality are compatible in this
finite bundle architecture.

## What was derived and what remains open

Derived:

- cylinder transport from sequential-growth prefix retention;
- the unique parity-odd full-`S3` operator up to scale;
- its intrinsic Gram-Hermiticity and normalization;
- exact all-rank relational transport when the edge orientation reverses;
- exact preservation by history-block pinching.

Not derived:

- that arbitrary physical causal-set growth universally generates the
  repository's finite continuation-derived CSpec atlas;
- that the finite CPTP history-block map is the physical laboratory
  instrument or preserves event-level `D(Omega,Omega)` normalization;
- a continuum limit or identification with the Standard Model weak current.

The theorem therefore closes the finite compatibility problem.  The paired
microscopic CSpec edge law is now derived in
`KFCausalCSpecDeterminantChirality.lean` as

```text
(sheet holonomy U_e, orientation transport Xi_e=sign(U_e)).
```

The remaining breakthrough target is to derive the finite atlas and its
record instrument universally from physical causal births, then construct
the event-algebra and continuum/laboratory bridge.

## Verification

The implementation is
`UnifiedTheory/Audit/KFCausalBundleProtectedChirality.lean`.  Its headline
theorems use only the repository's standard foundational axioms reported by
Lean (`propext`, `Classical.choice`, and `Quot.sound`), with no `sorry` and no
custom axiom.
