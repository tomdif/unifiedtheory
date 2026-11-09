# Exact local tensor constraints in finite spin blocks

Date: 2026-09-10

This constructs a new finite-spin **constraint parent Hamiltonian**.
It supplies exact local commuting checks, a nonempty constrained space,
and a volume-independent excitation gap above that space. It implements
a discrete version of the four linear tensor constraints. The checks
are explicitly engineered model inputs, not consequences of the old
spin hopping or causal-growth law.

The parent gives no propagation within its ground space. A separate
continuous canonical benchmark with the same stencils has two positive
linear tensor waves at every nonzero momentum. Obtaining that dynamics
inside the compact spin model remains unproved. Neither nonlinear clock
consistency nor Einstein gravity follows from this construction.

## 1. An integer local constraint complex

Use a supplied periodic cubic carrier with V=L^3 vertices. At each
vertex label six coordinates by
`h=(h_xx,h_yy,h_zz,h_xy,h_yz,h_zx)`. These are independent unweighted
symmetric components; their canonical momenta therefore have twice the
off-diagonal entries of the tensor pi used with a Frobenius pairing.

Let T_i translate a field by one positive lattice step, and define

```
f_i=T_i-1,       b_i=1-T_i^(-1),
ell_i=f_i b_i=T_i+T_i^(-1)-2.
```

The vector-to-tensor integer matrix G and scalar row B are

```
(G xi)_ii=2 f_i xi_i,
(G xi)_ij=f_i xi_j+f_j xi_i                    (i<j),

B h=sum_i T_i^(-1) (sum_{j!=i} ell_j) h_ii
                       -2 sum_{i<j} b_i b_j h_ij.       (1)
```

The placement factors T_i^(-1) align diagonal and off-diagonal tensor
components on a staggered lattice. They matter: independently mixing
forward and backward derivatives would generally spoil the identity.
All translations commute and `T_i^(-1) f_i=b_i`. Collecting the
coefficient of each xi_i in B G gives

```
2 b_i sum_{j!=i} ell_j-2 b_i sum_{j!=i} b_j f_j=0,
                         B G=0.                        (2)
```

This is an exact integer identity before imposing periodicity or
reducing modulo a prime. The matrices on a finite lattice have sizes
`G:6V x 3V` and `B:V x 6V`. It is the discrete compatibility condition
for three momentum constraints and one linear scalar-curvature
constraint. Defining this complex does not yet give the nonlinear
metric-dependent deformation algebra.

## 2. Compact constraints have discrete violation energies

Place a p-state qudit on each tensor component, with p an odd prime.
Write `X|n>=|n+1 mod p>`, `Z|n>=omega^n|n>`, and
`omega=exp(2pi i/p)`, so Z X=omega X Z. For a column g_a of G and
a row b_x of B, define

```
S_a=X^(g_a),             T_x=Z^(b_x).
```

Their mutual phase is `omega^(b_x g_a)=1` by (2). The X checks commute
among themselves, and so do the Z checks. All checks have order p.
The invariant projector of a check U is

```
Pi_U=(1/p) sum_{r=0}^{p-1} U^r,
H_check=Delta sum_checks (I-Pi_U),          Delta>0.     (3)
```

Each summand is an orthogonal projector times Delta. The Hamiltonian
is nonnegative, the checks commute exactly, and a violated check costs
Delta, regardless of wavelength. This evades the specific failure of
the earlier noncompact quadratic derivative penalties: the spectrum
of the constraint test is now discrete. It does not rely on taking
Delta to infinity as spatial volume grows.

The constrained Hilbert space is explicit. For each coset
`[u] in ker(B)/im(G)` over F_p, an orthonormal ground state is

```
|[u]> = |im(G)|^(-1/2) sum_{g in im(G)} |u+g>.           (4)
```

The Z conditions impose B u=0 and the X conditions identify the G
orbits. Hence

```
dim H_code=p^(6V-rank(G)-rank(B)).                       (5)
```

This uses the established finite Weyl/stabilizer framework; see
[Gottesman's treatment](https://arxiv.org/abs/quant-ph/9705052).
The compact tensor-constraint strategy also has direct precedent in
[Gu and Wen](https://arxiv.org/html/0907.1203). The result here is an
explicit repository realization and audit, not a claim to have
invented compact tensor gauge models.

## 3. The count is two encoded qudits per nonzero momentum

Assume p does not divide L. Work over a splitting field of the lattice
translations in characteristic p. Since L is nonzero in the field,
the translation representation is diagonalizable. For a Fourier
character w_i, choose a nonzero square root z_i and set
`d_i=z_i-z_i^(-1)`.

After invertible component phase transformations, G has the symbol
`xi -> d xi^T+xi d^T`; B has the symbol
`h -> -(d d^T-(d.d)I):h`. If d!=0, the first map is injective:
choose d_i!=0, use its diagonal entry and p!=2 to set xi_i=0,
then its off-diagonal entries set every other xi_j=0. The second
symbol is nonzero: `d d^T=(d.d)I` would force d=0. This remains
true even for a nonzero isotropic d over the splitting field.

Thus G has rank three and B rank one at each nontrivial character.
Only w_x=w_y=w_z=1 gives d=0; both symbols vanish there. Therefore

```
rank(G)=3(V-1),      rank(B)=V-1,
dim H_code=p^(2V+4)=p^(2(V-1)+6).                       (6)
```

The six global coordinates are retained explicitly. The Fourier
argument is a finite-field rank calculation, not a decomposition into
physical particle helicities. At fixed p, the code has no continuous
spatial rotation representation established here and no propagating
spectrum under H_check.

The coprimality hypothesis is material. For p=L=3 the audit instead
finds ranks 75 and 23, with 64 encoded qudits instead of 58. An adjacent
pair of opposite scalar-check syndromes is then forbidden. The
additional relations reflect the failure of the semisimple Fourier
argument in that characteristic; the generic count is not asserted
for such lattice sizes.

## 4. Embed the checks in the existing four-spin quintet

For p=5 use one four-spin-half cell per tensor component. Its
total-spin-two subspace is the five-dimensional symmetric Dicke space:

```
|n>=(binomial(4,n))^(-1/2) sum_{strings of weight n} |string>,
n=0,...,4.
```

Let W embed this basis and P_2=W W^dagger. Exact spin algebra gives
`J_total^2 W=6W` and `P_2=J_total^2(J_total^2-2I)/24`, the same
quintet projector used previously. The new Hamiltonian selects this
quintet as the local encoding space instead of selecting the old
singlet vacuum. There are six such cells, or 24 spin halves, per
carrier vertex. The choice of cyclic X and diagonal Z within the
quintet is supplied; it does not itself derive physical spatial
rotation covariance.

One cannot simply extend X and Z by the identity on the eleven unused
states and assume all many-cell checks still commute. If only part of
a check overlap lies in the active quintets, the cancelling Weyl phases
can be lost. The audit gives an explicit nonzero full-space commutator
for that unguarded extension.

For each check a with support S_a, use instead the active support guard
`P_S=product_{s in S_a} P_2,s`. Let U_a be its product of unitary
identity-extended Weyl operators. Define

```
h_a=P_S [I-(1/5) sum_{r=0}^4 U_a^r],
H_parent=M sum_s (I-P_2,s)+Delta sum_a h_a,       M,Delta>0. (7)
```

Each h_a is an orthogonal projector. Every term commutes with all
active-space projectors. On a fixed inactive-site pattern, a check is
either disabled or is an ordinary Weyl check with its complete support
active. Any two enabled checks retain all their overlap phases, so
(2) makes them commute. Disabled checks are zero. This proves that
the full Hamiltonian is a sum of commuting nonnegative projectors on
the complete microscopic spin Hilbert space, including unused states.

Its ground space is exactly the all-active code (4). Generally the
gap above this degenerate space is at least `min(M,Delta)`.
For L>=2 and 5 not dividing L there is a sharper exact result:

```
gap(H_parent)=min(M,2Delta).                             (8)
```

To see this, each of the three X-check families has one product
relation, and the Z-check family has one. The ranks in (6) show these
are all the relations. Any nontrivial all-active syndrome therefore
violates at least two checks. A pair of opposite scalar syndromes
exists since im(B) is the full zero-sum scalar subspace; applying the
corresponding X operator to a code state gives energy 2Delta. A state
with one inactive cell and all remaining enabled checks satisfied has
energy M: the enabled checks are still a phase-free commuting CSS
system with a nonempty common invariant space. Every other inactive
sector costs at least M. These facts prove (8).

This is an exact constraint-sector gap, not a graviton mass. Every
state inside H_code has energy zero under H_parent. No robustness
theorem for arbitrary perturbations of this extensively degenerate
space is being asserted.

## 5. Microscopic locality is uniform

An X check involves at most six four-spin cells. A Z check involves
at most twenty-seven. Equation (1) uses offsets of lattice L1 length
at most two. A diagonal tensor cell participates in at most seven
checks, and an off-diagonal cell in at most eight. Periodic aliasing
can reduce these bounds on small lattices.

Consequently the sum of norms of Hamiltonian terms touching any
individual microscopic spin is bounded by

```
                         M+8Delta,                     (9)
```

uniformly in L, with fixed interaction range on the supplied carrier.
The largest check acts on at most 108 spin halves. This is an explicit
bounded-range many-spin Hamiltonian; no reduction to two-spin
interactions is established. The carrier itself is not selected by it.

## 6. The same stencils admit a separate local linear-wave benchmark

Replace the qudits by continuous canonical coordinates. Place
diagonal components at offsets e_i and off-diagonal components at
`(e_i+e_j)/2`; place vector parameters at e_i/2. These component offsets
are only a useful way to describe the local translation stencils.
For dimensionless lattice momentum k define

```
v_i=2 sin(k_i/2),
U_h=diag(exp(i k.s_alpha)),
A=diag(1,1,1,sqrt(2),sqrt(2),sqrt(2)),
h_F=U_h^dagger A h,       p_F=U_h^dagger A^(-1) p.       (10)
```

The F variables are Frobenius-normalized tensor coefficients. The
stencils (1) become the usual symmetrized gradient and scalar tensor
constraint with wavevector v, including the appropriate factors of i.
Their four linear canonical constraints commute exactly and have rank
four whenever v!=0.

Use the continuous Fierz-Pauli quadratic forms already derived in
[the bond-tensor diagnostic](BOND_TENSOR_CONSTRAINTS.md), replacing k
there by v. On the nonzero-momentum constraint quotient, transverse
traceless representatives give

```
H_TT=J |p_TT|^2/2+g |v|^2 |h_TT|^2/2,
omega(k)=sqrt(Jg) |v|,                  J,g>0.           (11)
```

There are exactly two positive oscillators per nonzero momentum.
The Fourier amplitudes retain the real-field conjugacy condition;
the complex notation does not double the physical degrees of freedom.
In the Brillouin zone, v vanishes only at the origin, including on
even lattices. This avoids the extra zero corners of the ordinary
unstaggered centered derivative sin(k).

With physical lattice spacing a, replace v_i by
`2 sin(a k_i/2)/a`. For fixed physical k this converges to k_i with
error at most `a^2 |k_i|^3/24`, giving a linear continuum wave cone.
Its speed sqrt(Jg) remains an input. The supplied torus's homogeneous
metric modes are excluded from the positive wave statement; the
linear constraints vanish there and the unconstrained trace kinetic
direction is not removed by this calculation.

This benchmark is local before the gauge quotient. An exact Laurent
expansion after undoing (10) contains only integer translations: the
kinetic matrix uses offsets of L1 length at most two and the potential
matrix at most three. The nonlocality of a TT choice of representative
does not imply nonlocality of these unreduced constrained equations.
Their off-constraint quadratic energy is indefinite, so it cannot
simply be substituted into (7) as a positive compact-spin Hamiltonian.

## 7. The remaining dynamical gap

Equations (7) and (11) are two distinct constructions. The first has
finite local Hilbert spaces and an exact constraint gap, but flat
ground-space dynamics. The second has positive linear waves after
constraint reduction, but supplied continuous canonical fields and a
supplied Fierz-Pauli Hamiltonian. Matching their constraint symbols and
counts does not identify their spectra or prove a common limit.

The new task is a bounded microscopic interaction whose effective
dynamics on the compact code has the two linear tensor poles, with
control of constraint violations and the joint field/volume limit.
The positive local curl/curvature-square benchmark instead gives cubic
dispersion; it remains a useful comparison, not the desired result.

The commuting linear checks also cannot be declared the full nonlinear
clock generators. Any c-number weighted sum of these same commuting
checks has zero commutator with every other such sum. GR's off-shell
normal-deformation bracket has a nontrivial total spatial generator.
Nonlinear constraints and their geometric action must be constructed
and tested separately. Checking commutators only on states where all
constraints vanish cannot establish that off-shell algebra.

This distinction has precedent in discrete gravity: exact linear
constraints can coexist with broken symmetry at the next orders.
[Dittrich and Hoehn](https://arxiv.org/abs/0912.1817) analyze that issue
for linearized and higher-order Regge dynamics. Our compact code does
not resolve it merely by having exact linear checks.

## 8. Verification

The [audit](scripts/compact_tensor_constraint_audit.py) and
[report](data/compact_tensor_constraint_audit.json) include the exact
integer identity B G=0, nine finite-field rank tests through 384
qudits, the exact four-spin quintet and Weyl algebra, and a 256-state
test of the guarded embedding including every inactive state. The
separate wave benchmark checks 724 nonzero momenta on four lattices,
including even sizes. Its staggered-symbol and reduced-energy errors
are below 1e-14. Exact Laurent expansions certify its finite range.

The all-volume rank, guarded-parent gap, and locality arguments are
analytical proofs above, supported by those checks. The numerical
wave test does not establish compact-model propagation. No Lean file
is added or changed in this step.

```sh
OPENBLAS_NUM_THREADS=1 python3 -W error::RuntimeWarning scripts/compact_tensor_constraint_audit.py
```
