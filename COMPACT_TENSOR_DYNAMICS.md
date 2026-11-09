# Local dynamics in the compact tensor constraint space

Date: 2026-09-10

The compact spin construction now admits nontrivial local dynamics with
a volume-independent energy bound protecting its constrained sector.
For the interaction family below, this bound holds at arbitrary positive
coupling strength. It closes the previous absence of motion inside the
code. It does not give Einstein gravity: the regular quadratic expansion
has cubic waves, and a derivative-counting argument explains why tuning
ordinary local interactions with these fixed linear gauges cannot give
linear waves in that expansion.

These are analytical finite-dimensional arguments, exact symbolic checks,
and numerical audits. No new Lean theorem is claimed. The carrier lattice,
quintet encoding, checks, and interactions remain engineered inputs.
Neither spacetime emergence nor a physical gravitational phase follows.

## 1. Local operators that preserve the constraints

Use the integer matrices G and B of
[the compact tensor parent](COMPACT_TENSOR_CONSTRAINTS.md), with B G=0.
There are six qudits per cubic-lattice vertex, in component order
xx, yy, zz, xy, yz, zx. The checks are X to columns of G and Z to
rows of B. Their common eigenvalue-one space is called the code.
For p=5 each qudit occupies the total-spin-two quintet of four spin
halves; the other eleven states of that cell are inactive.

Two finite-range integer matrices give useful logical operators:

```
C : 6V -> 9V,              R : 6V -> 9V,
C B^T=0,                   R G=0.                         (1)
```

C is a staggered twice-curl of trace-adjusted canonical momentum;
R is double curl of the symmetric coordinate. Here is an explicit
definition that fixes the staggering and off-diagonal normalization.
Let w_i denote translation, f_i=w_i-1, and epsilon the alternating tensor.
For row (a,b) of C, sum over m,n:

```
n != b:  C_(ab),(nb) += epsilon_(amn) f_m / w_b,
n == b:  C_(ab),(jj) += epsilon_(amb) f_m (2 delta_(jb)-1)/w_j
                          for every j.                    (2)
```

The label (nb) denotes the single canonical off-diagonal component.
For R, form the usual cross-product matrix F of the vector f and set
R h=F h F^T, listing all nine entries of its output. In translation
symbols the first identity in (1) means C B*=0, where star transposes
and replaces w by w^(-1). Both identities hold over the integers,
before periodic reduction or reduction modulo p.

For a row c of C and a row r of R, set

```
U_c=X^c,                   V_r=Z^r.
```

Equation (1) makes these commute with every check. They need not commute
with each other. On the L=3, p=5 torus, the audit finds a C row supported
on four cells and an R row supported on fifteen cells with

```
c.r = 1 mod 5,             V_r U_c = exp(2 pi i/5) U_c V_r. (3)
```

Neither operator is a stabilizer on the code, because a stabilizer
would commute with all operators preserving the code. Their restriction
therefore supplies a five-dimensional Weyl algebra, with multiplicity.
The concrete local Hamiltonian

```
H_pair = -0.7 Re U_c - 1.1 Re V_r
```

has nonzero commutator with V_r. In one irreducible block, evolution of
a V_r eigenstate for time 0.8 has return probability 0.8565966111.
This is exact motion within the many-spin constrained space. It is a
local logical-pair example, not a measurement of lattice dispersion.
The report records the full integer patterns so the example can be
reconstructed without enumerating the exponentially large code.

## 2. A bounded local spin Hamiltonian

On the active qudits choose nonnegative coefficients j_c and g_r and
negative real cosine interactions:

```
V = -sum_c j_c Re X^c - sum_r g_r Re Z^r.                 (4)
```

On the full spin space multiply every term by the projector P_S onto
active quintets at all cells in its support. Extend each Weyl matrix
by the identity on the unused states. Support always means the actual
nonidentity Weyl factors after combining periodic aliases and reducing
exponents modulo p. A term with empty support is a global constant.
This convention matters for the inactive-sector argument below.

Add these guarded interactions to the previous parent:

```
H = M sum_s (I-P_2,s) + Delta sum_a h_a + V_guarded,
M>0, Delta>0.                                             (5)
```

All active/inactive patterns and all enabled check eigenspaces are
invariant. To verify this on an inactive pattern, a guarded term is
either zero or acts entirely on active cells. Whenever two terms are
enabled their original Weyl cancellation is intact. Thus each new
dynamic term commutes with the parent checks, although dynamic terms
can fail to commute with one another.

C rows involve at most eight cells, R rows at most fifteen. Both have
maximum offset of two lattice steps in the L1 norm. Their incidence
counts per tensor component are respectively

```
C: (12,12,12,8,8,8),       R: (14,14,14,26,26,26).
```

If j_c<=j_C and g_r<=j_R, a safe sum of interaction norms incident on
any microscopic spin is

```
M + 8 Delta + 12 j_C + 26 j_R.                            (6)
```

This bound and the interaction range are independent of lattice volume
at fixed p and fixed couplings. They do not establish a uniform bound
in a large-p limit whose interaction normalization grows with p.

## 3. Why strong dynamics cannot favor a violated constraint

The following comparison applies to any finite Weyl system with pure-X
and pure-Z commuting checks, and a Hamiltonian of the form (4) commuting
with those checks. No small-interaction assumption is required.

Let psi be normalized in one simultaneous check eigenspace, possibly
with nontrivial eigenvalues. In the coordinate basis replace its
coefficients by their absolute values, phi(q)=|psi(q)|. Then

```
Re sum_q conjugate(psi(q)) psi(q-c)
    <= sum_q |psi(q)| |psi(q-c)|.                         (7)
```

Consequently every negative X cosine has nonincreasing energy. Every
Z cosine is diagonal, so its expectation is unchanged. Taking absolute
values removes all X-check eigenvalue phases: phi is invariant under
their translations. Its Z-check eigenvalues are unchanged, since its
coordinate support is unchanged.

Now Fourier transform phi, take absolute values again, and transform
back:

```
psi_0 = F^(-1) |F |psi| |.                                (8)
```

In the Fourier basis the Z cosines are negative hopping terms, so the
same inequality lowers their energy. The X energy is diagonal and
unchanged. This second operation removes the Z-check phases. The
already-trivial X-check eigenvalues remain trivial because their
Fourier support condition is preserved. Norms are preserved at both
steps. Thus psi_0 lies in the code and

```
<psi_0,V psi_0> <= <psi,V psi>.                            (9)
```

Let E_0 be the minimum eigenvalue of V restricted to the all-active
code. Equation (9) proves that every other all-active check sector has
dynamic energy at least E_0. The same bound applies to arbitrary
all-active states and density matrices: V commutes with the checks,
so decompose into check sectors and then into pure states.

Positivity arguments selecting a trivial check sector have precedent
in the Perron-Frobenius treatment of CSS gauge-code Hamiltonians; see
[Burton, Section 3](https://arxiv.org/html/1801.03243).
Here the two explicit absolute-value operations give the non-strict
comparison needed for the finite-p tensor construction. We do not
assume the stronger irreducibility hypotheses needed to compare
dynamic sector minima strictly.

If an all-active sector violates s checks, its full energy is at least
E_0+s Delta. For the tensor torus with L>=2 and p not dividing L,
the four global check-product relations imply that any nontrivial
syndrome violates at least two checks. The previous rank calculation
establishes these relations and their completeness. Hence

```
H on all-active noncode states >= E_0 + 2 Delta.          (10)
```

This is a lower bound after adding dynamics. Equality of the old
parent gap does not automatically persist.

## 4. Inactive spin states cannot undercut the code either

Consider any density matrix in a sector with r inactive cells. Replace
each inactive cell by a maximally mixed active qudit, leaving the state
of the other active cells unchanged. This produces an all-active
density matrix. Every previously enabled dynamic term has the same
expectation. Every newly enabled term has zero expectation, since it
contains a nonidentity Weyl factor on at least one newly mixed cell.
Therefore the expectation of the full-active V equals that of the
guarded dynamics before the replacement.

By (9), that dynamic energy is at least E_0. The inactive penalties cost
r M and the enabled constraint penalties are nonnegative. It follows
that inactive sectors have energy at least E_0+r M. Combining this
with (10), for p=5 and L>=2 coprime to five,

```
H restricted to the complement of the all-active code
                    >= E_0 + min(M,2 Delta).             (11)
```

All ground states therefore lie in the code, and the spectral subspace
below this threshold is contained in the code. More generally, with
delta_*=min(M,2 Delta) and P_code the all-active code projector,

```
H-E_0 I >= delta_* (I-P_code),
Tr rho (I-P_code) <= (Tr rho H-E_0)/delta_*.              (11a)
```

The second inequality bounds the excluded-sector weight of any density
matrix; a low energy expectation alone need not make that weight zero.
The statement is uniform in volume and in the strength of the
nonnegative coefficients in (4). Equation (6) remains the separate
locality budget for the chosen coefficients.

The negative-cosine convention in (4) is essential for the mixed-state
completion as written. Replacing a guarded -Re U by a guarded I-Re U
changes inactive-sector energies, because the added constant depends
on the active pattern. Truly global constant shifts cause no problem.

Equation (11) protects the bottom of the physical sector against all
excluded sectors. It does not prove a full many-body spectral gap:
excitations inside the code can have arbitrarily small energies. Nor
does it separate the entire code spectrum from all excluded spectra;
high-energy code states can overlap them. Arbitrary phases, negative
couplings, or mixed XZ interactions are outside this comparison theorem.

## 5. The regular wave expansion gives cubic dispersion

The following is a conditional smooth expansion, not a continuum
theorem for the five-state quantum model. In an unwrapped large-p
description use epsilon=sqrt(2 pi/p), and canonical coordinates and
momenta Q,P with X^c approximated by exp(-i epsilon c.P) and Z^r by
exp(i epsilon r.Q). Expanding the cosines near small phases gives

```
V - constant = (j_C epsilon^2/2) ||C P||^2
             + (j_R epsilon^2/2) ||R Q||^2 + higher terms. (12)
```

With j_C=J/(4 epsilon^2), j_R=g/epsilon^2, J,g>0, the quadratic
Hamiltonian is J/2 times the squared curl of trace-adjusted momentum
plus g/2 times squared double curl of the coordinate. The factor four
comes from the twice-curl convention in (2). In the staggered
Frobenius canonical coordinates of the preceding audit, its two
transverse-traceless modes have

```
v_i=2 sin(k_i/2),
K_PP = J |v|^2 I_2,        K_QQ = g |v|^4 I_2,
omega = sqrt(J g) |v|^3.                                 (13)
```

The independent symbol audit checks these identities at 192 generic
nonzero momenta. This agrees with the local cubic tensor construction
in [Gu and Wen](https://arxiv.org/html/0907.1203), which also distinguishes
it from their linearized gravity target. Neither their precedent nor
our symbol calculation supplies a controlled ground-state expansion
for the fixed p=5 Hamiltonian (5). No gapless phase or pole has been
proved for that model. The six homogeneous code coordinates also
remain in the construction; (13) concerns nonzero momentum.

## 6. Why another regular local interaction cannot fix the power

Assume finite-support Weyl patterns admit an analytic continuum-neutral
lift at k=0, with finite regular quadratic coefficients. Modular charge
neutrality alone is insufficient for this assumption. Keep the same
linear scalar and vector constraints, and the same tensor canonical
variables, with no additional gapless fields.

An X pattern u gives a symmetric tensor satisfying, to leading
continuum order,

```
(k k^T-|k|^2 I):u(k)=0.
```

Its constant coefficient u_0 would obey
k^T u_0 k=|k|^2 tr(u_0) for every k. Thus u_0=tr(u_0) I;
taking the trace gives u_0=0. Every such pattern starts at one
derivative: u(k)=O(|k|).

A Z pattern gives a symmetric dual tensor satisfying v(k) k=0.
Its constant part vanishes. Write a possible linear part as
v_ij(k)=T_ijm k_m, where T is symmetric in i,j. The constraint
makes T antisymmetric in j,m. These two symmetries imply

```
T_ijm = T_jim = -T_jmi = -T_mji
      = T_mij = T_imj = -T_ijm,
```

so T=0. Thus v(k)=O(|k|^2). Exact coefficient elimination in the
audit independently finds zero kernels for all six constant X
coefficients, all six constant Z coefficients, and all eighteen
linear Z coefficients. No rotational-invariance assumption is needed.
The staggering only changes higher terms after these leading
coefficients vanish.

A regular quadratic expansion of local neutral phases therefore has

```
K_PP=O(|k|^2),  K_QQ=O(|k|^4),  K_PQ=O(|k|^3).           (14)
```

This derivative bound also applies to mixed neutral Weyl phases,
although their sector protection is not established by Sections 3-4.
For each nonzero k reduce to transverse-traceless canonical variables
and rescale Q=|k|^(-1/2) Q', P=|k|^(1/2) P'. This rescaling is
canonical, and every block of the quadratic energy becomes O(|k|^3).
Hence all linear Hamiltonian-flow eigenvalues are O(|k|^3). A stable
mode with omega/|k| tending to a positive constant is impossible
within these assumptions.

This is an obstruction to the specified regular local quadratic
route, not a theorem excluding all strongly interacting spin phases.
Singular limits of coefficients or support, modular patterns without
the continuum lift, additional fields, and a different nonperturbative
phase require separate analysis. The Fierz-Pauli benchmark escapes
the stated class: its local off-constraint Hamiltonian preserves the
scalar constraint only up to other constraints. It is not a sum of
the strongly gauge-neutral local phases assumed in (14).

## 7. A precise diagnostic for the missing linear dynamics

Formally dividing both quadratic blocks in (13) by |v|^2 gives
K_PP=J I_2, K_QQ=g |v|^2 I_2 and linear waves. In the invariant
variables this requires an inverse lattice Laplacian:

```
H_diagnostic = J/2 <C_0 P,(-Delta_lattice)^(-1) C_0 P>
             + g/2 <R Q,(-Delta_lattice)^(-1) R Q>,
C_0=C/2.                                                 (15)
```

The inverse is restricted to nonzero momentum. It has a nonlocal
kernel. The audit checks its linear dispersion alongside (13), but
(15) is not an interaction added to the finite-spin Hamiltonian.
Uniformly gapped local Gaussian auxiliaries have an analytic inverse
quadratic block near zero momentum, so their Schur complement cannot
directly supply this 1/|k|^2 singularity. Gapless or constrained
auxiliaries would need a new stability and degree-of-freedom argument.

The model decision is consequently sharper: retain the finite-spin
encoding and protected constraint construction as a benchmark, but
revise the fixed-constraint route before claiming Einstein waves.
One target is a constraint deformation whose Hamiltonian preserves
the physical space up to constraints and whose continuum brackets
realize the metric-dependent algebra in
[the conditional Einstein derivation](GRAVITY_FROM_CLOCK_CONSTRAINTS.md).
Such a deformation must be explicitly realized and checked; it is not
implied by having two encoded qudits per nonzero momentum. Linear
dispersion, nonlinear closure, universal matter coupling, and an
emergent gravitational continuum remain open.

## 8. Reproducible checks

Run:

```sh
OPENBLAS_NUM_THREADS=1 python3 -W error::RuntimeWarning scripts/compact_tensor_dynamics_audit.py
```

The [audit script](scripts/compact_tensor_dynamics_audit.py) writes
[the source-hashed report](data/compact_tensor_dynamics_audit.json).
It checks the exact integer identities, support and incidence counts,
and a noncommuting logical pair. It tests the two absolute-value
operations on 75 states across 25 charge sectors and independently
diagonalizes all 25 dynamic sector blocks of a three-qudit example.

A second check uses a 216-dimensional representation of three cells,
including every active/inactive pattern. Each inactive label has eleven
identical copies in the full 4,096-dimensional spin Hilbert space.
Four interaction strengths from 0.1 to 100 preserve the code and obey
the predicted sector bounds. This toy has independent check relations,
so its charge lower bound is Delta, whereas the periodic tensor
construction has 2 Delta. These finite tests support the analytical
proof; they do not enumerate the many-body tensor spectrum.

The exact derivative-coefficient tests and the 192 momentum checks
verify the expansion and its nonlocal diagnostic. They do not establish
that the actual compact quantum model has either continuum dispersion.
