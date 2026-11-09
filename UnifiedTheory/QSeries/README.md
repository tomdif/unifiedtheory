# Verified q-series input

This directory brings the self-contained Watson proof from RamanujanLean into
UnifiedTheory without changing its Lean 4.28.0 / Mathlib pin.

## Mathematical results

`Watson/` contains locally finite formal-power-series sums, q-Pochhammer products,
Euler expansions, the finite q-binomial identity, and Watson's proofs of

```
chi0(q) = 2 F0(q) - phi0(-q)
f0(q) + theta4(q) G(q) = 2 phi0(-q^2)
f0(q) - theta4(q) G(q) = 2 q psi(q^2) H(q^4) - 2 (F0(q^2) - 1).
```

The actual infinite series are defined in `PowerSeries ℤ`. These equalities have
no unproved mathematical input. `LayerA/WatsonSeriesBridge.lean` exports the R1
identity at every coefficient, the distinct-parts/odd-parts product identity,
and the following elimination of `F0` and `phi0`:

```
2 chi0(q^2) = 4 + 4 q psi(q^2) H(q^4) - 3 f0(q) + theta4(q) G(q).
```

`WeightedEuler.lean` defines, for every multiplicity function `w : ℕ → ℕ`,

```
weightedEuler(w) = product over k >= 1 of (1 - q^k)^(-w(k)).
```

It proves factor cancellation, stabilization of each coefficient after all
sizes up to that coefficient have been included, and equality with a computable
finite convolution of binomial coefficients. All coefficients are nonnegative.
No uniform bound on the multiplicities is required for these formal statements.

For `w(k) = k(k+1)/2`, `macMahonProduct` is the infinite MacMahon product.
`LayerA/MacMahonBridge.lean` now defines `mac3` by the proved convolution algorithm
for every degree, instead of a table that returned zero after degree six.
In particular, the coefficients 141 at degree six and 310 at degree seven are
kernel-checked consequences of the product definition.

## Occupation states and the reconstructed constraint

`Audit/KFCausalOccupationSeries.lean` connects the Euler machinery to the
existing `KFCausalFiniteOccupationLadders.Active m R` basis. For `m > 0` and
`n <= R`, an explicit equivalence with multisets proves

```
card {v : Active m R | total v = n}
  = choose (m - 1 + n) (m - 1)
  = [q^n] product_k (1 - q^k)^(-occupationMultiplicity m k),

occupationMultiplicity m k = if k = 1 then m else 0.
```

The same coefficient is the dimension of complex amplitudes on that shell.
The finite character is a sum over actual retained states; its coefficients
match the infinite product through degree `R` and vanish above `R`.
The number operator is proved to be the sum of the actual unit-weight
annihilator-adjoint products, including the capacity boundary.

`Audit/KFCausalOccupationConstraintSeries.lean` then imposes the model's
translation charge `n1 - n2 + n3 - n4 = 0`. Its `neutralCoefficient` enumerates
all six-tuples at each degree and is proved to count the retained neutral
shell whenever the capacity is large enough. The first coefficients are
`1, 2, 7, 12, 26`, versus `1, 6, 21, 56, 126` for the unrestricted six-mode
occupation character. These values are derived from states, not supplied as
degeneracy data.

An explicit linear equivalence identifies neutral amplitudes with the kernel
of the **existing reconstructed constraint**, provided its scalar diagonal
coefficients are nonzero. This condition is proved for unit radial weights
and any nonzero `hbar`, including at the top shell. For general radial weights
the condition remains explicit: zero weights can introduce extra kernel
states. The kernel dimension is consequently

```
sum n = 0..R, neutralCoefficient n.
```

The constraint commutes with occupation-shell projectors. The specified
polynomial Hamiltonian preserves translation charge, but the occupation
grading is not generally conserved. `Audit/KFCausalOccupationEnergyObstruction.lean`
computes an exact counterexample in that existing Hamiltonian: at capacity
`R = 1`, unit radial weights, `hbar = 2`, zero mass/quartic/vacuum parameters,
and time zero, the vacuum-to-single-clock matrix element is `-63/32`.
Both states have zero translation charge and different total occupations.
The Hamiltonian therefore fails to commute with the number operator and
cannot equal `E0 I + gap N` for any constants in this example.

This establishes state counting and a constraint-kernel identification within
the specified finite model. It also rules out a universal occupation-equals-energy
interpretation of these characters for that Hamiltonian family. It does not
rule out a different conserved grading, a special parameter regime, a
unitary spectral transformation, or a separately justified limiting theory.
No Watson/R1 character is identified with this sector by these results.

## Scope and current follow-up

The operator-domain, field, and Wilson-theory developments that used this
machinery live in [the audit sources](../Audit) and the
[Yang–Mills program](../Clay/YangMills/README.md). They have separate hypotheses
and physical identification obligations. Formal q-series identities and
occupation counts do not establish a continuum physical field theory or a
physical mass gap. [Current status](../../STATUS.md).

## Provenance and verification

The seven files under `Watson/` are from RamanujanLean commit
`ce2dd48f96d62c81117ceeafd52faba5febd20ac`. Their original proofs are retained;
only imports, namespaces, and provenance headers were changed. The upstream
MIT license and source hashes are preserved alongside them.

From the repository root:

```sh
lake build UnifiedTheory.LayerA.WatsonSeriesBridge UnifiedTheory.LayerA.MacMahonBridge
lake env lean scripts/CheckQSeriesIntegration.lean
lake env lean scripts/CheckOccupationSeries.lean
lake env lean scripts/CheckOccupationSpectralSearch.lean
```

The checkers name their exact declarations. Accepted axiom dependencies are
`propext`, `Classical.choice`, and `Quot.sound`; historical validation records
are snapshots. The [repository audit](../../data/repository_audit_2026_11_09.json)
reports the current build scope separately.
