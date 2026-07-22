# Causal–cubic twisted-transfer bridge audit

## Result

`UnifiedTheory/Audit/KFCubicTwistedTransfer.lean` formalizes the exact abstract
junction between causal transitions and the intrinsic three-sheet carrier.
For a causal state `b`, outgoing edge `e : b -> b'`, scalar edge weight `k_e`,
and sheet transport `sigma_e : S_b' ~= S_b`, it defines

```text
(T_W psi)(b) = sum_e k_e U_e psi(b').
```

If `T_W psi = lambda psi` and `lambda != 0`, the normalized branch amplitudes

```text
A_b(e) = lambda^-1 k_e U_e psi(b')
```

sum exactly to `psi(b)`. Lean proves the same equality after every finite
number of exhaustive refinement steps. At every unit-norm parent, these branch
amplitudes generate a normalized Hermitian strongly positive decoherence
functional. Arbitrary relabelings of every sheet fiber conjugate `T_W`, carry
eigen-sections to eigen-sections with the same eigenvalue, and leave the branch
Gram kernel unchanged.

This closes an interface theorem. It does not produce its microscopic input.

## Source-level audit of `causal-algebraic-geometry-lean`

The neighboring repository is conceptually relevant, but its current Lean
declarations do not yet instantiate the interface:

| File | What Lean currently proves | Missing for the twisted bridge |
|---|---|---|
| `GrowthRule.lean` | `ThreeSliceValid` and a four-step chain through the empty slice | No normalized Markov law, complex edge weights, or eigen-section |
| `TransferMatrixComputable.lean` | Decidable transition relation, branching factors, and small-`L` transition counts | The transfer matrix and Perron–Frobenius conclusions occur in prose, not as a carrier-valued operator/eigenpair theorem |
| `HolonomyComposition.lean` | Composition laws for diagonal interval-projection matrices in a causal algebra | No three-sheet bundle and no `S_3`-valued edge transport |
| `FIELD_THEORY.md` | Describes principal eigenvectors for comparability/profile operators, with exact, conditional, and numerical layers | No theorem identifying one of those states with an eigen-section of the sequential growth operator |

Accordingly, the word “holonomy” must not be conflated across the two
constructions. The causal-algebra interval projector and an `S_3` permutation
local system are different objects until a bridge theorem relates them.

## Exact instantiation contract

To turn the abstract theorem into a causal model, the causal repository must
supply three independent witnesses:

1. **Cubic sheet functor:** a three-element type `S_b` for every causal state,
   derived from causal data rather than attached by hand.
2. **Edge monodromy:** a bijection `S_b' ~= S_b` for every allowed birth,
   compatible with causal relabeling and composition.
3. **Spectral dynamics:** complex edge weights and a nonzero eigen-section of
   the resulting twisted transfer operator, with unit carrier norm at the
   chosen root/state.

The new Lean capstone then supplies automatically:

- atomic and all-finite-depth exhaustive amplitude consistency;
- Hermiticity and strong positivity;
- normalization at every unit-norm parent;
- gauge covariance of the eigen-section;
- gauge independence of the decoherence kernel.

The decisive unresolved physics is therefore not another Hilbert-space
identity. It is a causal-geometric construction of the cubic sheet functor and
its edge monodromy, followed by existence or selection of a nonzero twisted
eigen-section.
