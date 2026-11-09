# A microscopic four-spin seed for propagating tensor excitations

Date: 2026-09-10

This construction starts with explicit spin-1/2 operators on four qubits
per cell. A local polynomial Hamiltonian has a unique singlet vacuum,
a lowest excited spin-2 quintet, and higher local states separated by
chosen positive gaps. A bounded local hopping interaction gives an
exact propagating quintet band. Low-occupation collective operators
approach bosonic commutators with an explicit operator-norm error.

This supplies a microscopic tensor-excitation **candidate**, not gravity.
The exact band has five internal spin polarizations and quadratic
dispersion when tuned gapless. The two gravitational helicities, linear
dispersion, constraint algebra, universal coupling, and causal-order
origin of the spatial spin interpretation remain unproved. The new
Hamiltonian is an explicit extension proposed for testing; it is not
claimed to have been hidden in the old XY Hamiltonian.

## 1. Four qubits, a singlet vacuum, and a selected quintet

Let s_a^i=sigma_a^i/2 for four microscopic spins a=1,2,3,4. Define the
two pair spins A=s_1+s_2, B=s_3+s_4, total J=A+B, and C=J^2. The pair
Casimirs have eigenvalues 0 and 2. The projector

```
P_tt=(A^2/2)(B^2/2)                               (1)
```

selects the nine-dimensional triplet-times-triplet subspace. Within
it, total spin is 0,1,2. The following are exact four-qubit projectors:

```
P_0=P_tt (C-2I)(C-6I)/12,       rank 1,
P_2=C(C-2I)/24,                 rank 5,
P_1=P_tt-P_0-P_2,               rank 3,
P_bad=I-P_tt,                   rank 7.           (2)
```

They are orthogonal, sum to I, and commute with all total-spin
generators. P_2 already lies in P_tt. No canonical bosonic coordinates
are assumed in these definitions.

Write the pair triplets as |+>,|0>,|->. The P_0 state is

```
|Omega>=(|+,->-|0,0>+|-,+>)/sqrt(3).              (3)
```

For 0<mu<min(M,K), choose

```
H_cell=mu P_2+M P_1+K P_bad.                      (4)
```

The vacuum is unique with energy zero, its first excited multiplet is
the spin-2 quintet at mu, and the other levels are M and K. Equation
(4) is a finite polynomial in microscopic spin matrices. It uses
engineered four-spin interactions; it is not asserted to arise from
nearest-neighbor Heisenberg exchange alone. The couplings and the grouping
of spins into cells are explicit model inputs.

## 2. Tensor transitions derived from pair quadrupoles

Let E_alpha, alpha=1,...,5, be a Frobenius-orthonormal basis of real
traceless symmetric three-by-three matrices. Use
`diag(1,-1,0)/sqrt(2)`, `diag(1,1,-2)/sqrt(6)`, and the three normalized
off-diagonal symmetric matrices. The pair A is spin 1 on P_tt, and
its quadrupole components are

```
Q_alpha=sum_ij (E_alpha)_ij (A_i A_j+A_j A_i)/2.
```

The trace subtraction drops out because E_alpha is traceless. Direct
four-qubit algebra gives

```
P_2 Q_alpha |Omega>=Q_alpha|Omega>,
<Omega|Q_alpha Q_beta|Omega>=delta_alpha beta/3.
```

Thus the normalized quintet basis and transition operators are

```
|alpha>=sqrt(3) Q_alpha|Omega>,
b_alpha^dagger=sqrt(3) P_2 Q_alpha P_0
              =|alpha><Omega|,
b_alpha=|Omega><alpha|.                           (5)
```

These are explicit matrices on the original sixteen-dimensional
four-qubit Hilbert space. They transform in the rank-two representation
of the microscopic spin rotations because P_0 is a singlet and the
quadrupoles transform as tensors. An identification with physical
spatial rotations still requires a spatial coupling or an independently
derived relation to the carrier frame.

The exact local algebra is

```
b_alpha b_beta^dagger=delta_alpha beta P_0,
b_beta^dagger b_alpha=|beta><alpha|,
sum_alpha b_alpha^dagger b_alpha=P_2=:N.           (6)
```

Only one quintet excitation fits in a cell, irrespective of polarization.
These are hard-core transition operators, not exact local canonical
bosons. P_0+P_2 is a six-dimensional invariant active space.

## 3. A bounded local microscopic Hamiltonian with exact propagation

Place the cells on a supplied graph of bounded degree. For nearest cell
neighbors r,s and hopping coefficient t_h>0 define

```
H_seed=sum_r[mu N_r+M(P_1)_r+K(P_bad)_r]
       +t_h sum_<rs>,alpha
          (b_r,alpha^dagger-b_s,alpha^dagger)
          (b_r,alpha-b_s,alpha).                  (7)
```

Each term is nonnegative. A bond acts on eight microscopic spins and
has operator norm 2t_h; its two-cell spectrum is checked on all 256
states. The onsite norm is max(mu,M,K). Interaction range and the sum
of norms incident on one cell are bounded independently of volume:
`max(mu,M,K)+2 z t_h` for maximal cell degree z. This is a finite local
spin Hamiltonian, with no oscillator or large-spin approximation.

For mu,M,K>0 the product of singlets is its unique ground state:
zero energy requires the onsite state at each cell to lie in P_0.
Every P_1 and P_bad projector commutes with H_seed, and all transitions
annihilate those sectors. The total quintet number sum N_r is conserved.
The all-active sector is exact, not selected by sending a penalty to
infinity.

Restrict (7) to the one-excitation basis |r,alpha>. One obtains exactly

```
H_one=(mu I+t_h L_cell) tensor I_5.               (8)
```

In fact the full many-body spectral gap is exactly mu, uniformly in
the number of cells, for 0<mu<min(M,K). Let P_vac be the product-vacuum
projector. Commuting onsite vacuum projectors give
`sum_r(I-(P_0)_r)>=I-P_vac`; hence positivity of the hopping implies
`H_seed>=mu(I-P_vac)`. A normalized constant one-excitation mode
attains energy mu because the graph Laplacian kills constants. This
proves both bounds on the gap for the complete finite spin system,
without a harmonic approximation. It does not apply after H_mix is added.

For a cubic cell lattice, in cell momentum units,

```
epsilon(k)=mu+4t_h sum_i sin^2(k_i/2),             (9)
```

with all five polarizations. The Fourier transform of
`X_r,alpha=b_r,alpha+b_r,alpha^dagger` creates precisely this
one-excitation state from the vacuum. Therefore its exact vacuum
spectral measure and Euclidean two-point function are

```
dS_alpha beta(E,k)=delta_alpha beta delta_epsilon(k)(dE),
C_alpha beta(i nu,k)=delta_alpha beta
                              2epsilon(k)/(nu^2+epsilon(k)^2). (10)
```

These are genuine poles of the complete microscopic seed Hamiltonian,
not just a classical harmonic calculation. At mu=0 the selected product
vacuum remains a ground state but is no longer unique: zero-momentum
one-excitation states also have zero energy. For nonzero small k,
epsilon(k)~t_h |k|^2. A linear macroscopic clock scaling does not turn
this band into a relativistic one. With mu=a^2 m and k=a p, the
quadratic time scaling gives the controlled one-particle limit
`epsilon(a p)/a^2 -> m+t_h|p|^2`. No many-body continuum is claimed.

## 4. Collective bosonic commutators with a density error

On a periodic lattice of V cells, within the all-active sector, define

```
B_k,alpha=(1/sqrt(V)) sum_r exp(-ik.r) b_r,alpha.
```

Equation (6) gives the exact identity

```
[B_k,alpha,B_l,beta^dagger]
 =delta_alpha beta delta_kl I
  -(1/V)sum_r exp(i(l-k).r)
             [delta_alpha beta N_r+|beta><alpha|_r]. (11)
```

Let P_<=n project onto at most n excited cells. A phase-weighted sum of
N_r has norm at most n there. The same bound holds for the sum of local
flavor changes |beta><alpha|: on a sector with m occupied cells it is a
sum of m norm-one operators, with occupation positions unchanged.
Consequently

```
|| P_<=n ([B_k,alpha,B_l,beta^dagger]
            -delta_alpha beta delta_kl I) P_<=n || <= 2n/V. (12)
```

This is an operator-norm estimate on the stated low-occupation sector,
not only a vacuum expectation identity. It produces canonical collective
commutators in the dilute limit n/V->0. It does not supply canonical
operator-norm commutators on the full finite-dimensional Hilbert space,
or prove a finite-density tensor phase. No finite-dimensional matrices
can satisfy a nonzero constant canonical commutator on their full space.

## 5. A stable coupling to the existing scalar strain

The scalar sector in the preceding notes is still the supplied large-spin
field model. It can be coupled to the microscopic seed without declaring
the seed to be gravity. Define the spin tensor

```
X_ij=sum_alpha (E_alpha)_ij X_alpha.
```

For any real three-vector d the matrix X(d)=sum_ij d_i X_ij d_j is a
vacuum-to-quintet star. Its exact norm is

```
||X(d)||=sqrt(sum_alpha (d^T E_alpha d)^2)
        =sqrt(2/3)|d|^2.                          (13)
```

It annihilates all higher local sectors. For a symmetric central
field difference d_s at the carrier vertex assigned to cell s, add

```
H_mix=(gamma/2)sum_s (d_s)_i (X_s)_ij (d_s)_j.     (14)
```

Cell centers are distinct carrier vertices, and neighboring cells have
a carrier separation bounded independently of volume. Both this
placement and its spatial frame are supplied model data.

This contracts microscopic spin indices with specified spatial
directions: an explicit spin-orbit type coupling, not a derivation of
that identification from the causal-order law. Central differences
transform as vectors under carrier cubic rotations. Their summed
squared norm is bounded by the reference nearest-neighbor field energy,

```
sum_s |d_s|^2 <= q^T L_0 q.                       (15)
```

For all vertices this follows from
`((a+b)/2)^2<=(a^2+b^2)/2` and translation of edges; summing only the
selected cell centers makes the left side smaller. Combining (13)–(15)
with the old configuration-wise lower bound A(n)>=(kappa/4)L_0 gives

```
q^T A(n)q/2+H_mix
 >= (1/2)[kappa/4-|gamma|sqrt(2/3)] q^T L_0 q.     (16)
```

Thus the coupled field potential is uniformly positive on relative
coordinates whenever |gamma|sqrt(2/3)<kappa/4. The spin seed and original
geometry Hamiltonians are nonnegative as well. This proves stability of
this explicit extension at finite volume without a field occupation
cutoff. At kappa=1/4, gamma=0.02 satisfies the sufficient condition.

The P_1 and P_bad sectors remain inert: b, X, and N annihilate them.
Replacing a cell in either sector by an independent vacuum leaves
the expectation of all its interaction terms unchanged and removes
its positive onsite cost. This variational replacement shows that a
ground state lies in the all-active sector; a sector with such defects
has minimum energy at least M or K per defect above the all-active
minimum. It does not force the active state to remain the product vacuum
after H_mix is introduced.

The interaction is nonzero on gradients that were invisible to the old
x-directed switches. For example, d along y gives X(d)|Omega>!=0.
The tensor now can respond to scalar strain. This is not universal
coupling to the full stress tensor, nor a gravitational constraint.

The exact poles in (10) concern gamma=0. Coupling can shift or broaden
them; no persistence theorem for gamma!=0 is claimed. Noncommuting spin
tensor coefficients also do not automatically preserve the positive
geometry-history representation used in the earlier Gaussian covariance
proof. The operator stability bound (16) is established directly and
does not make that additional claim.

## 6. The microscopic starting point and the remaining gravity test

The construction derives a local singlet vacuum, selected quintet,
transition algebra, exact propagating poles, and dilute collective
commutators from finite microscopic spin matrices. It also supplies an
explicit small, stable coupling to scalar strain. Those ingredients
were assumptions in the earlier purely canonical tensor discussion.

What has emerged here is a propagating **five-component internal
spin-2 excitation with quadratic low-energy dispersion**. Identifying
it with gravity would be incorrect. The
[bond-tensor constraint diagnostic](BOND_TENSOR_CONSTRAINTS.md) specifies
the next test: a stable microscopic mechanism must select the appropriate
two polarizations and produce the linear constrained dynamics, rather
than merely penalizing four or three soft directions with derivative
terms. Nothing in (7) provides those gravitational constraints.

The five traceless quintet amplitudes also do not supply the six
unconstrained canonical coordinates of the bond-tensor ansatz. A
microscopic scalar channel or a justified constrained reduction would
be needed to relate those descriptions; the four-constraint count
cannot simply be copied onto five canonical pairs.

The microscopic spin choice, cell grouping, carrier, couplings, and
clock calibration are still explicit inputs. No complete emergent
spacetime, Einstein equation, Standard Model, or TOE is established.

## 7. Verification

The audit checks the sixteen-state cell projectors and all twenty-five
transition identities exactly with symbolic spin matrices. It verifies
the full 256-state bond spectrum, embeds the one-excitation band into
a 4,096-dimensional three-cell microscopic Hilbert space, and compares
its propagation with the graph-Laplacian formula. Separate active-space
calculations check (11)–(12), while exact tensor contractions and finite
carrier differences check the strain-coupling bound.

The fifteen supporting Lean results supply scalar projector-polynomial,
energy, dilute-error, and stability algebra. The finite matrix calculation, general
tensor-product argument, and operator estimates in this note remain
separate mathematical suppliers. They are not advertised as a formal
proof of emergent gravity.

The [audit script](scripts/microscopic_spin_two_audit.py) writes a
detailed [report](data/microscopic_spin_two_audit.json). The 256-state
bond has eigenvalues 0,1,2 in units of t_h, with multiplicities
126,100,30. The full-space one-excitation intertwining residual is
below 3.1e-15. Twenty-seven finite collective-commutator checks,
fifty tensor-coupling spectra, and four hundred scaled band comparisons
pass. The sufficient coupled stiffness margin is 0.04617006838 for
kappa=0.25 and gamma=0.02. These finite checks accompany the general
analytical bounds above; they are not substitutes for thermodynamic
or interacting continuum theorems.

The [Lean module](UnifiedTheory/Audit/KFCausalMicroscopicSpinTwo.lean)
uses only the standard `propext`, `Classical.choice`, and `Quot.sound`
axioms. Reproduce from the repository root:

```sh
OPENBLAS_NUM_THREADS=1 python3 -W error::RuntimeWarning scripts/microscopic_spin_two_audit.py
lake env lean UnifiedTheory/Audit/KFCausalMicroscopicSpinTwo.lean
```
