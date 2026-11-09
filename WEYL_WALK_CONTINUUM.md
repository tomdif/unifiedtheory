# A local quantum update with a controlled Weyl limit

Date: 2026-09-09.

An explicit quantum update now connects the repository's consistency
program to a relativistic wave equation. The construction is exactly
unitary and has finite spatial propagation. Its finite-time propagator
converges to the massless Weyl propagator with an explicit error bound.
The complete spectrum also has opposite-handed cones, including one at
the same zero quasienergy as the desired cone. A single low-momentum
expansion therefore does not establish chiral matter.

The lattice, its three spatial directions, the two-component carrier, and
the update order are specified model choices. This is a free one-particle
benchmark. It does not derive gravity, gauge interactions, a physical
vacuum, or the Standard Model.

Formal results are in
[`KFCausalWeylWalk.lean`](UnifiedTheory/Audit/KFCausalWeylWalk.lean).
The [audit script](scripts/weyl_walk_audit.py) and
[results](data/weyl_walk_audit.json) distinguish exact algebraic checks
from floating-point convergence checks.

## 1. The actual microscopic law

Use the Pauli matrices X, Y, Z. For dimensionless momentum q=(x,y,z), set

```text
R_j(q_j) = cos(q_j) I − i sin(q_j) σ_j,
U(q) = R_z(z) R_y(y) R_x(x).
```

Each σ_j is Hermitian and squares to I, so R_j† R_j=I exactly, and U is
unitary at every momentum, not just near zero. The Lean theorem
`walk_complete` proves this for the specified matrices.

This symbol comes from an actual finite-range position-space update.
Let T_{±e_j} translate lattice wave functions and
P_j^±=(I±σ_j)/2. The conditional translation

```text
S_j = P_j^+ T_{e_j} + P_j^- T_{−e_j}
```

is unitary: the cross terms vanish by P_j^+ P_j^-=0, and the two remaining
terms sum to I. With the Fourier convention that T_d contributes
exp(−i q·d), the full update S_z S_y S_x has symbol U.

Its eight displacements d=(s_x,s_y,s_z), s_j=±1, have exact coefficients

```text
A_d = P_z^{s_z} P_y^{s_y} P_x^{s_x},
ψ_{n+1}(r) = sum_d A_d ψ_n(r−d).
```

The audit computes these Gaussian-rational matrices and checks both
unitarity correlation identities for all 27 possible displacement
differences, giving 54 exact matrix equalities. It also verifies their
Fourier symbol against the defined U. These identities establish
unitarity on the infinite one-particle space ℓ²(ℤ³)⊗ℂ², as well as on
periodic finite lattices.

After n steps, each coordinate displacement is at most n. In physical
units with spatial and temporal step a, the coordinate speed bound is
one and the Euclidean bound is √3. This discrete propagation bound is
not exact Lorentz invariance at the cutoff.

The full cubic lattice separates into four invariant sectors labeled by
(r_x−r_y mod 2, r_x−r_z mod 2). Each is a body-centered cubic lattice.
These spatial copies must be accounted for when counting momentum cones.

## 2. Derive the generator rather than supply it

Write c_j=cos(q_j), s_j=sin(q_j). Direct multiplication gives

```text
U(q) = d(q) I − i v(q)·σ,
d   = c_x c_y c_z + s_x s_y s_z,
v_x = s_x c_y c_z − c_x s_y s_z,
v_y = c_x s_y c_z + s_x c_y s_z,
v_z = c_x c_y s_z − s_x s_y c_z.
```

The formal theorem `walk_quaternion` verifies these expressions.
They obey d²+|v|²=1, so the eigenvalues are exp(±iω) with cos ω=d.

For fixed physical momentum k, evaluate U(a k). Its derivative at a=0 is

```text
d/da U(a k)|_{a=0} = −i H(k),
H(k) = k_x X + k_y Y + k_z Z,
H(k)² = |k|² I.
```

Lean proves the derivative entry by entry in `walk_generator` and the
dispersion identity in `hamiltonian_square`. Consequently the limiting
energies are ±|k|. Fourier transformation yields

```text
i ∂_t ψ = −i (X ∂_x + Y ∂_y + Z ∂_z) ψ,
```

the free massless Weyl equation in the stated orientation convention.
This derives the wave equation for a two-component amplitude. Fermionic
quantization, a physical vacuum, and interacting quantum field theory
would require further constructions.

## 3. A finite-time continuum bound

All norms in this section are the Hilbert-space operator norm. They are
not an arbitrary default norm on Lean matrices.

Set K(k)=|k_x|+|k_y|+|k_z|, F(a)=U(a k), and V(a)=exp(−i a H(k)).
For the three rotation factors,

```text
‖R_j(a k_j)‖ = 1,
‖d/da R_j(a k_j)‖ = |k_j|,
‖d²/da² R_j(a k_j)‖ = k_j².
```

Twice differentiating the product therefore gives

```text
‖F''(a)‖ ≤ sum_j k_j² + 2 sum_{j<l} |k_j k_l| = K(k)².
```

For V, unitarity and H²=|k|²I give ‖V''(a)‖=|k|²≤K(k)².
Both F and V have value I and derivative −iH at zero. The integral
Taylor remainder, bounded by half the squared step times the uniform
second-derivative bound, thus gives

```text
‖U(a k) − exp(−i a H(k))‖
  ≤ a² [K(k)² + |k|²]/2
  ≤ a² K(k)².
```

For contractions A and B, the telescoping identity implies

```text
A^n−B^n = sum_{j=0}^{n−1} A^{n−1−j}(A−B)B^j,
‖A^n−B^n‖ ≤ n ‖A−B‖.
```

The second inequality is formalized in `power_error` for any normed
ring with norm-one identity. Take a=t/n, t≥0, n≥1, to obtain the actual
finite-time estimate

```text
‖U(t k/n)^n − exp(−i t H(k))‖ ≤ t² K(k)²/n.
```

This is uniform on every fixed physical momentum band K(k)≤K₀.
For sufficiently small a that the band lies in the lattice Brillouin
zone, the Fourier-space identification with continuum wave packets
therefore gives the same bound on their propagators in L². In particular,
the dynamics converges at fixed finite time on that band.

This also supplies a direct comparison between two resolutions. In the
same Fourier-space identification, write F_n=U(t k/n)^n. Then

```text
‖F_n−F_m‖ ≤ t² K₀² (1/n+1/m).
```

For a normalized state in the common band and a bounded observable O,
expanding the difference of the two expectations gives

```text
|<F_n ψ, O F_n ψ> − <F_m ψ, O F_m ψ>|
  ≤ 2 ‖O‖ t² K₀² (1/n+1/m).
```

The bound extends to mixtures by convexity. Taking a measurement effect
0≤O≤I gives a bound on its Born-probability discrepancy. Thus this model
has controlled observational consistency between lattice resolutions,
for the stated common momentum sector and finite evolution time.

The integral remainder and this continuum identification are analytic
proofs in this note. The Lean module proves the actual generator and
the generic repeated-step estimate, but does not yet formalize the
second-derivative operator-norm estimate or the full Fourier-space limit.
The audit checks 105 finite-time examples numerically; those examples
are not a substitute for the uniform analytic argument.

The earlier [tensor-refinement result](QUANTUM_REFINEMENT_PROOF.md)
admits the unitary at each finite description. That admission alone does
not identify dynamics at different lattice spacings. The bound above
supplies a common continuum propagator for the stated momentum sector.

## 4. An exact mirror cone

Let q*=(π/2,π/2,π/2). The explicit symbol satisfies the identity

```text
U(q*+(x,y,z)) = U(x,−y,z).
```

This holds for all real x,y,z, not merely to first order. It follows
directly by substituting cos(θ+π/2)=−sin θ and
sin(θ+π/2)=cos θ into d and v. Lean proves it in `mirror_identity`.
Thus U(q*)=I, and the generator near q* is

```text
H_mirror(k) = k_x X − k_y Y + k_z Z.
```

The origin's velocity matrix is I₃. The mirror's is diag(1,−1,1), with
determinant −1. These are opposite Weyl orientations relative to the
same spatial orientation. The derivatives and the determinant sign
are formalized in `mirror_generator` and `mirror_orientation`.

Although q*/a goes to high physical momentum as a→0, its quasienergy
is zero. Slowly varying envelopes centered on that momentum have their
own gapless limit. Restricting the initial data to a band near the
origin selects a sector; it does not eliminate the other sector from
the microscopic theory.

### Count all the cones without counting spatial copies twice

A band degeneracy requires U=εI, ε=±1. Rearranging the factorization,

```text
R_y(y) R_x(x) = ε R_z(−z),
```

forces cos(y) sin(x)=0 and sin(y) cos(x)=0, by comparing its X and Y
coefficients. Since sin²+cos²=1, either sin(x)=sin(y)=0, or
cos(x)=cos(y)=0. The remaining coefficients then force sin(z)=0 in
the first case and cos(z)=0 in the second.

All degeneracies are therefore:

- q_j ∈ {0,π} modulo 2π for all three axes;
- q_j ∈ {π/2,−π/2} modulo 2π for all three axes.

There are sixteen representatives in a cubic Brillouin zone. For one
connected BCC sector, reciprocal shifts by π(1,1,0), π(1,0,1), and
π(0,1,1) identify groups of four. There are **four inequivalent cones
per connected sector**: one of each orientation at quasienergy zero,
and one of each orientation at quasienergy π.

One choice of representatives is:

| Momentum q | U(q) | Quasienergy | Relative Weyl orientation |
| --- | --- | --- | --- |
| (0,0,0) | I | 0 | +1 |
| (π/2,π/2,π/2) | I | 0 | −1 |
| (π,0,0) | −I | π | +1 |
| (−π/2,π/2,π/2) | −I | π | −1 |

The audit verifies every listed node, its relative velocity matrix
after factoring out ε, its determinant, and its reciprocal-lattice
class. Completeness comes from the coefficient argument above,
not from a finite momentum scan.

## 5. Consequence for completing the theory

This is a constructive bridge from an explicit microscopic update to
a relativistic continuum wave equation, with controlled finite-time
error. It is also a test of the full proposed spectrum: the same law
has opposite-handed gapless sectors. No assignment of Standard Model
gauge representations or mechanism for handling the extra sectors
has been derived.

The update law is still not selected uniquely. Reversing the three
rotation factors leaves the leading generator unchanged while changing
physical predictions at finite momentum. At q=(π/4,π/4,0), the initial
spin state |+X> has probability zero for the subsequent +Z outcome under
U, but probability 1/2 under the reversed update. The audit verifies the
generator equality and these probabilities symbolically. A correct Weyl
limit therefore does not fix finite-momentum predictions under this
fixed identification of axes, preparations, and observables. In fact,
with B=(X+Z)/√2, the exact relation
U_reverse(x,y,z)=B U(z,−y,x) B holds. Reversal alone is therefore not a
proof of inequivalence under simultaneous coordinate and spin-basis changes.

There is a stronger discriminator in the broader finite-range class.
Define a local unitary commutator loop and a modified update by

```text
C(q) = R_y(y) R_x(x) R_y(y)† R_x(x)†,
U_modified(q) = C(q) U(q).
```

Here C(0)=I and d/da C(a k)|₀=0, so U_modified has the same Weyl
generator: the four loop derivatives at zero sum to
−i k_y Y − i k_x X + i k_y Y + i k_x X = 0.
It remains finite-range and unitary, although its maximal
coordinate range is larger than the eight-neighbor law's. At
q=(π/4,π/4,0), however, Tr U_modified=0, whereas Tr U=1 for every
signed permutation of those three momentum coordinates. The magnitude
of the trace is unchanged by spin-basis conjugation or a global phase.
Thus the modified law cannot be reduced to the original by a cubic
axis symmetry, spin-basis change, or global phase. The exact audit checks
the loop's zero generator and all 48 signed axis permutations, including
repeated momentum tuples.

This demonstrates underdetermination by finite-range locality, unitarity,
and the leading Weyl generator. It does not establish nonuniqueness under
every additional minimal-range or isotropy axiom, and no complete spectrum
or mirror-removal claim is made for the modified law.

These constructions belong to established quantum-walk theory.
Bialynicki-Birula's
[Dirac and Weyl Equations on a Lattice as Quantum Cellular Automata](https://arxiv.org/abs/hep-th/9304070)
gives local unitary lattice constructions with relativistic limits.
D'Ariano, Erba, and Perinotti's
[Isotropic quantum walks on lattices and the Weyl equation](https://arxiv.org/abs/1708.00826)
classifies a specified family of isotropic two-component walks.
The repository contribution is this explicit verified benchmark and
its continuum and spectrum audit; no novelty claim is made for
deriving Weyl dynamics from quantum walks.

The next physical obligation is an explicit microscopic carrier and
interaction with the required chiral gauge spectrum, including all
momentum sectors. Gravity additionally requires a dynamical geometry
and a derivation of the equilibrium/continuum inputs presently assumed
by the [Einstein bridge](UnifiedTheory/Audit/KFCausalCSpecEinsteinEquations.lean).
The full [GUT/TOE frontier](GUT_CLOSURE_FRONTIER.md) remains open.

## 6. Reproduce the checks

```sh
python3 scripts/weyl_walk_audit.py --output data/weyl_walk_audit.json
lake build
git diff --check
```

The JSON includes the exact stencil, all node representatives, numerical
errors and their analytic bounds, dependency versions, and source hashes.
Exact checks and numerical checks are kept separate.

Validation completed on 2026-09-09: all symbolic identities, 54 exact
stencil checks, node and reciprocal-class checks, 48 signed-axis checks,
and 105 numerical continuum checks pass. Both recorded source hashes
match. The ten printed Lean theorem audits use only propext,
Classical.choice, and Quot.sound; the new module builds without errors
or warnings. The full integrated build passes (8,914 jobs), and
`git diff --check` passes.
