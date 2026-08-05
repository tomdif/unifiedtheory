# Causal cylinder record transport

## The derived law

Sequential growth supplies a canonical Hilbert carrier at every finite rank:
the basis is the finite set of growth prefixes.  For transition amplitudes
`a(h,b)`, the one-step refinement map is

```text
V_n |h> = sum_b a(h,b) |h,b>.
```

For any finite cylinder event `c`, let `P_c` be its diagonal projector before
refinement.  Its exhaustive one-step continuation is

```text
c↑ = {(h,b) | h in c},
```

and let `Q_c` be the diagonal projector onto `c↑`.  The new Lean theorem
proves, for every event and every transition function,

```text
Q_c V_n = V_n P_c.
```

This is not an axiom about a supplied measurement basis.  It follows
entry-by-entry from the defining prefix law of sequential growth: `V_n` has
support only between `h` and histories whose retained prefix is exactly `h`.
The result is independent of phases, coherent normalization, and the values
of the nonzero transition amplitudes.

## Quantum consequence

If the local amplitudes are Born normalized,

```text
sum_b |a(h,b)|^2 = 1,
```

the same canonical map is an isometry:

```text
V_n† V_n = I.
```

Combining this with the derived intertwiner gives

```text
V_n† Q_c V_n = P_c.
```

Therefore an exhaustively refined cylinder has exactly the original sharp
effect.  A realized history has unit weight for its own singleton cylinder;
every distinct history has weight zero.  The canonical harmonic Born-shell
law instantiates the theorem at every causal rank.

## Native causal children

An actual physical child of a causal prefix becomes a singleton cylinder as
soon as the birth occurs.  The theorem then transports that exact child
identity through every subsequent one-step refinement without an added
alignment postulate.  In this precise sense, causal facts are the finite
cylinder observables conserved by growth.

## Exact boundary

The theorem does not select a child before it exists.  Before a branching
birth, the parent prefix is one basis state; mutually exclusive future-child
projectors are not already present on that unresolved one-dimensional fiber.
Sequential growth therefore derives:

```text
realized causal fact -> exact nondemolition transport,
```

not:

```text
unresolved parent -> predetermined future outcome.
```

It also does not prove that a laboratory apparatus couples to the intrinsic
cylinder algebra, and the existing chirality tripwire remains: a protected
chiral algebra must be embedded compatibly rather than erased by native
history-basis resolution.

The machine-checked implementation is
`UnifiedTheory/Audit/KFCausalCylinderRecordTransport.lean`.
