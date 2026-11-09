# Can weak constraint preservation repair the compact gravity model?

Date: 2026-09-10

For the fixed compact tensor code, replacing exact commutation with
preservation of the physical subspace does not enlarge the possible
local Hamiltonians acting within that subspace. An explicit average
over the checks produces a Hamiltonian with the same physical action,
no larger interaction supports or term norms, and exact commutation
with every check. This closes one proposed escape from the preceding
wave obstruction.

The conclusion about waves remains conditional: if the resulting local
neutral interactions have the regular continuum expansion specified in
[the compact dynamics note](COMPACT_TENSOR_DYNAMICS.md), their quadratic
tensor dynamics cannot have a nonzero linear wave speed. The averaging
theorem itself does not determine the phase or dispersion of an
arbitrary finite-state quantum model. No Einstein continuum or TOE is
proved here.

## 1. Averaging leaves the physical Hamiltonian unchanged

Let S be a finite stabilizer group of tensor-product Weyl operators,
with no nontrivial scalar phase times the identity. Let P project onto
its common eigenvalue-one space. This includes the all-active tensor
code of [the compact parent](COMPACT_TENSOR_CONSTRAINTS.md). Define

```
T(A) = (1/|S|) sum_(s in S) s A s^dagger.                 (1)
```

Every s fixes P on both sides. Directly averaging gives

```
[T(A),s]=0 for every s,
P T(A) P = P A P,
||T(A)|| <= ||A||.                                       (2)
```

For a Hermitian Hamiltonian H, preservation of the physical subspace
means (I-P) H P=0, equivalently [H,P]=0. It does not require [H,s]=0
outside that subspace. But then

```
T(H) P = P H P = H P,
exp(-it T(H)) P = exp(-it H) P.                           (3)
```

Thus every physical energy, transition amplitude, and time evolution
is identical for H and T(H). The Hamiltonians can still differ on all
the excluded sectors. Equality of their physical actions alone does
not determine the ground energies or gaps of those other sectors.

There is also a useful preservation of an existing protection bound.
The map T is positive and unital, with T(P)=P. Hence, if the proposed
Hamiltonian already satisfies

```
H-E_0 I >= delta (I-P),
```

then so does T(H), with the same E_0 and delta. If H preserves the
code and E_0 is its physical ground energy, (3) preserves that energy
exactly. Averaging therefore retains any proved separation of excluded
sector energies above the physical ground energy. It does not create
such a bound when none was established.

This uses the standard stabilizer framework of
[Gottesman](https://arxiv.org/abs/quant-ph/9705052) and finite group
averaging, often called twirling. Hamiltonian engineering by averaging
also has established precedent, for example
[Conrad](https://arxiv.org/abs/2010.13853). The result here is the direct
application to the repository's proposed weak-preservation escape,
not a claim that group averaging is new.

## 2. The average is local despite the size of the group

Write H=sum_R h_R, where h_R is supported on a finite set R. Every
stabilizer is a tensor product. Consequently

```
s h_R s^dagger = s_R h_R s_R^dagger tensor I_(outside R).
```

The support of T(h_R) is contained in R, and its operator norm is no
larger than that of h_R. In particular,

```
sup_x sum_(R containing x) ||T(h_R)||
          <= sup_x sum_(R containing x) ||h_R||.          (4)
```

Neither the range nor the local interaction budget increases with
volume. One need not implement an exponentially long physical pulse
sequence: (1) defines the local Hamiltonian that has the required
code action. For a fixed local support and local dimension its Weyl
expansion is finite independently of total volume.

More explicitly, write W(u,v)=X^u Z^v. For a stabilizer s, conjugation
multiplies W by its symplectic character, a p-th root of unity.
Character orthogonality gives

```
T(W)=W if W commutes with every check,
T(W)=0 otherwise.                                        (5)
```

For the tensor code the surviving patterns satisfy

```
B u=0 mod p,                  G^T v=0 mod p.             (6)
```

It follows that even a sum of individually constraint-violating local
terms, whose violations cancel only on the code, has an equally local
representative made solely from neutral Weyl patterns. Invariance of
each original term is not an additional restriction on the exact
physical Hamiltonian of this fixed code.

The same conclusions, including preservation of an existing protection
bound, extend to the full four-spin space. Extend each X and Z by the
identity on the eleven unused states. Adjoin at every cell the unitary
F_s=P_2,s+omega(I-P_2,s), so its eigenvalue-one space is exactly the
active quintet. Generate a group from these F_s and the unguarded
extended tensor checks. The group need not be Abelian on inactive
sectors, but it is finite: each cell factor belongs to the finite
group of Weyl matrices times p-th-root phases on the quintet, with
an independent p-th-root scalar phase on the unused states.

Its common fixed space is exactly the all-active code. All its elements
remain tensor products of cell unitaries, so (1)-(4), including the
support and protection bounds, apply unchanged. Those averaging
arguments do not require an Abelian group. Restricted to all-active
states the group maps onto the original stabilizer group; its average
there is the same neutral-pattern projection (5). This avoids assuming
that unguarded extended checks commute on the entire spin Hilbert space.

The special negative-cosine family in the previous note was needed to
derive an initial energetic protection bound. The present averaging
argument preserves a bound already proved for H; it does not prove
that arbitrary Hermitian interactions have that bound in the first place.

## 3. A Hamiltonian that is weakly but not strongly invariant

Use three p=5 qudits and two commuting checks

```
S_X=X_1 X_2,                 S_Z=Z_1 Z_2^(-1).
```

The code is spanned by
5^(-1/2) sum_n |n,n,t>, with t=0,...,4. Let Pi_X be the
eigenvalue-one projector of S_X. Consider

```
H_w = -0.7 Re X_3 - 1.1 Re Z_3
      +0.6 (I-Pi_X) Re X_1 (I-Pi_X).                    (7)
```

The last term annihilates the code, so H_w preserves it exactly.
That term does not commute with S_Z in excluded sectors. The audit
finds ||[H_w,S_Z]||=0.6708203932, while the norm difference between
H_w and T(H_w) acting on the code is below 4e-16. Full-output time
evolution from the code also agrees to numerical precision.

Adding 3[(I-Pi_X)+(I-Pi_Z)] to (7) gives an example with an explicit
excluded-sector bound of 2.4 above the physical ground energy: the
parent is at least 3(I-P), and the last term of (7) is at least
-0.6(I-P). The logical part has the same ground-energy bound in all
sectors. Independent full-matrix inequalities verify that both this
Hamiltonian and its average retain the bound.

Twelve further tests start with independent dense local operators on
two of three qudits, at p=3 and p=5. Partial traces verify that the
average retains no action on the idle site. They also check physical
compression, commutation, and norm contraction. Exact polynomial
character identities are checked at p=3,5,7.

A 256-state test retains all eleven unused states per four-spin cell.
It checks the full-space averaging on a dense single-cell operator
and on a Hamiltonian with an explicit physical-sector protection
bound. The unguarded checks have a nonzero mutual commutator, but
the full average commutes with them and preserves the required code
action, locality, and protection.

## 4. Approximate preservation gives a quantitative time bound

For any Hermitian H let Q=I-P and epsilon=||Q H P||. Define the
block-diagonal comparison H_d=P H P+Q H Q. Its difference from H is
the off-diagonal block Q H P+P H Q, of norm epsilon. Duhamel's identity
and unitarity give

```
||(exp(-it H)-exp(-it H_d))P|| <= |t| epsilon.
```

H_d and T(H) have identical code evolution, so

```
||(exp(-it H)-exp(-it T(H)))P|| <= |t| epsilon.            (8)
```

All output components are retained in this bound; leakage is not
discarded by projecting the answer back into the code. The full-spin
group described after (6) gives exactly the same argument there.
Nine finite tests deliberately add small leaking terms to (7) and
check (8) at three strengths and three times.

The norm epsilon is a global operator norm and can grow with volume
for an extensive perturbation. No volume-independent error bound
follows just from calling the microscopic perturbations small. On
infrared observation times t of order 1/|k|, proving epsilon=o(|k|)
on the relevant full-input domain would force the two evolutions to
coincide asymptotically there. A weaker error estimate cannot justify
using the exactly constrained spectrum on those times. This does not
exclude a different phase obtained by finite mixing with charged
states.

## 5. Virtual defects produce neutral logical interactions

Constraint-violating microscopic terms can nevertheless generate
nonzero dynamics perturbatively. This must be distinguished from
assuming that they change the derivative structure of the effective
tensor theory.

For the three-qudit code above take

```
H_0=Delta[(I-Pi_X)+(I-Pi_Z)],     Delta>0,
H(t)=H_0+t V,
V=-a Re X_1-b Re(X_1^(-1) X_3)
  -c Re Z_1-d Re(Z_1^(-1) Z_3).                          (9)
```

Every term of V changes a check eigenvalue, so P V P=0. Each term
acting on the code violates exactly one check, with energy Delta.
The second-order effective Hamiltonian is therefore

```
H_eff^(2) = -P V Q (Q H_0 Q)^(-1) Q V P
          = -(1/Delta)[(a^2+b^2+c^2+d^2)/2
                       +a b Re X_3+c d Re Z_3] P.       (10)
```

The inverse acts on Q only. To obtain (10), products with opposite
X-type charges yield X_3, X_3^(-1), or identity; the corresponding
Z products yield Z_3, Z_3^(-1), or identity. Mixed charge types cannot
return to the code in two steps. At p=5 two equal nonzero charges
do not cancel. This is a concrete generation of a noncommuting
logical Hamiltonian through virtual charged states.

The audit checks (10) against the full 125-state matrix with
(a,b,c,d)=(0.7,0.4,0.9,0.3), Delta=1.6, with error below 2e-15.
It compares the five lowest exact energies with the second-order
prediction at t=0.005,0.01,0.02,0.04.

A conservative finite-volume control follows directly from the
Schur complement. Write nu=||V|| and assume 2|t|nu<Delta. Weyl's
eigenvalue bound gives |E|<=|t|nu for the low band descended from P.
For an exact eigenvector with physical component phi=P psi,

```
[ -t^2 P V Q (Q H_0 Q+t Q V Q-E)^(-1) Q V P ] phi=E phi.
```

The resolvent identity bounds the difference from t^2 H_eff^(2) by

```
2 |t|^3 nu^3 / [Delta (Delta-2|t|nu)].                   (11)
```

Thus the residual of phi in the second-order eigenvalue equation,
divided by ||phi||, obeys (11); in particular E lies within this bound
of the second-order spectrum. The audit checks that residual using
the exact eigenvectors. This is finite-volume control. The global
nu is not a thermodynamic perturbation bound. General effective
Hamiltonian and cluster expansions require further hypotheses; see
[Bravyi, DiVincenzo, and Loss](https://arxiv.org/abs/1105.0675).

The same charge bookkeeping applies to a sequence of Weyl errors
on the tensor lattice. Starting in the code, a nonzero contribution
that ends in the code has total charge zero. Its Weyl product is
neutral and its support is contained in the union of the input
supports. Denominators from the commuting parent depend on the
intermediate syndrome, not the logical input state. A fixed connected
sequence of local terms therefore gives a finite-support neutral
operator. This statement alone does not prove convergence, cluster
cancellation, or locality of a resummed infinite-order theory.

For the previously constructed local tensor Weyl pair, the audit
splits each pattern into single-cell charged operations. The X path
visits syndrome weights 4,8,4,0. The Z path has fifteen steps and
returns to zero charge only at its last step. These exhibit possible
virtual paths; neither minimal order nor a nonzero coefficient after
all perturbative cancellations is asserted.

## 6. What this does and does not rule out for Einstein waves

Sections 1-2 establish an exact finite-system statement with no
continuum assumption. Its implication for gravity additionally needs
the assumptions in Section 6 of the preceding dynamics note: finite
regular quadratic coefficients, analytic continuum-neutral lifts of
the surviving local Weyl patterns, and the fixed tensor canonical
variables and linear gauges. Under those hypotheses, (6) forces

```
u(k)=O(|k|),                 v(k)=O(|k|^2).
```

Consequently the quadratic blocks are of orders |k|^2, |k|^4, |k|^3
for momentum, coordinate, and mixed terms. Canonical rescaling makes
the entire Hamiltonian-flow matrix O(|k|^3). Since (3) leaves exact
physical evolution unchanged, weakening [H,s]=0 to [H,P]=0 supplies
no route to linear waves within that same regular expansion.

This conclusion is not restricted to positive cosine coefficients;
averaging applies to arbitrary Hermitian local terms, and the derivative
orders apply to any stable regular quadratic expansion of the stated
neutral phases. The earlier uniform energetic protection theorem still
has its own narrower sign and interaction assumptions.

A finite-depth local unitary U defining a dressed code P'=U P U^dagger
also does not change this conclusion when the pulled-back Hamiltonian
retains the same regular continuum description. Pull back H' with U,
apply (1), then conjugate back. Bounded gate range and bounded depth
give bounded enlargement of local supports, and the physical spectrum
is unchanged. This is a conditional statement about regular local
changes of encoding, not a classification of all phases of matter.

An arbitrary compact quantum model can fail the expansion hypotheses.
For example a collective continuum limit can be singular in the
single-cell Weyl variables. Modular neutrality does not by itself
imply a real analytic neutral lift. The averaging theorem does not
turn either issue into a proved cubic dispersion at p=5.

There is no contradiction with the continuum Fierz-Pauli Hamiltonian
that preserves its constraints only up to other constraints. Its
noncompact canonical constraints are not the finite stabilizer
projector P: gauge-orbit states generally require a quotient or
distributional treatment, and its off-constraint quadratic energy is
unbounded below. The bounded finite-group averaging argument cannot
be transferred to that continuum operator without a controlled limit.
Treating its finite-spin replacement as automatic would skip exactly
the required proof.

## 7. Revised construction requirement

Keeping the exact compact code and merely changing how a local
Hamiltonian acts on excluded states cannot repair its regular wave
expansion. Nor does adding a few virtual charge processes automatically
remove the derivative factors. The explicit averaged representative
must be examined before claiming such an escape.

The next microscopic model must demonstrably change the effective
constraint realization or establish a controlled limit outside these
regular expansion assumptions. A candidate has to show its selected
physical sector, two positive linear tensor modes, and then the
metric-dependent normal/spatial bracket and common matter sources
required by [the conditional Einstein target](GRAVITY_FROM_CLOCK_CONSTRAINTS.md).
A declaration that the constraints are nonlinear is insufficient;
their operators, physical domain, and closure must be constructed.

The overarching consistency target remains that different local clock
deformations describe compatible evolution of the same physical state.
The compact code realizes exact finite check consistency, but this
alone neither implements the metric-dependent clock algebra nor
selects its gravitational continuum. That distinction now has a
precise local-operator test rather than an assumed loophole.

## 8. Reproduction and scope

```sh
OPENBLAS_NUM_THREADS=1 python3 -W error::RuntimeWarning scripts/compact_constraint_normalizer_audit.py
```

The [script](scripts/compact_constraint_normalizer_audit.py) writes
[the source-hashed report](data/compact_constraint_normalizer_audit.json).
It includes fifteen exact character identities, twelve dense local
compression tests, an exactly weakly invariant example, nine leakage
tests, the full 256-state embedding check, the second-order calculation
with four spectral/residual checks,
and explicit charged tensor paths. It also reruns the exact derivative
coefficient elimination on which the conditional wave implication rests.

The proofs are written analytical arguments with independent algebra
and matrix audits. No new Lean theorem is claimed. The checks do not
establish a gravitational quantum phase, a thermodynamic perturbation
expansion, spacetime emergence, or a theory of everything.
