# Polynomial nonlinear spin constraints and the energy of incompatible sources

Date: 2026-09-11

The [unitary transport construction](COVARIANT_CONSTRAINT_TRANSPORT.md)
needed interactions involving an increasing number of spins. A
stereographic spin-coherent condition removes that problem for a
commuting-source control: the new Hamiltonian has terms on at most
ten qubits, bounded summed strength, an exact nonlinear kernel, and
a proved quantum limit on three fixed blocks.

The same construction does not independently accommodate the
noncommuting Einstein sources. Their commutators produce a positive
fourth-order energy operator in the intended physical band. That
coefficient is independent of spin-block size. A concrete Einstein
source pair has a nonzero contribution. A leading coupled correction
cancels it, but an all-order compatible local tensor parent is still
missing. Neither the control model nor this obstruction proves a TOE.

## 1. An exact polynomial spin-coherent condition

On the symmetric space of R qubits, let N count down spins and set

    B=R^(-1/2)sum_a |0><1|_a,
    Z=1-2N/R,
    B|n>=sqrt[n(1-(n-1)/R)] |n-1>,
    [B,B^dagger]=Z.

Let alpha be a Hermitian source acting on other degrees of freedom,
and commuting with this block. Define

    c_R(alpha)=B-alpha Z-alpha^2 B^dagger/R.             (1)

For a scalar alpha, set t=alpha/sqrt(R). The normalized vector

    Phi_R(alpha)=sum_(n=0)^R sqrt[binom(R,n)]
                   t^n (1+t^2)^(-R/2)|n>              (2)

satisfies c_R Phi_R=0 exactly. A rotation around the collective
y axis gives

    c_R=(1+t^2) U_t B U_t^dagger,
    U_t=exp[-2i arctan(t) J_y].                         (3)

Thus the kernel is one-dimensional and the first positive eigenvalue
of c_R^dagger c_R is (1+alpha^2/R)^2, since the smallest positive
eigenvalue of B^dagger B is one. The entire spectrum is

    (1+alpha^2/R)^2 n(1-(n-1)/R), n=0,...,R.            (4)

These are standard spin-coherent states; their group representation
framework is described by [Perelomov](https://arxiv.org/abs/math-ph/0203002).
The coefficient recurrence and (3) provide direct checks here.

For an arbitrary finite Hermitian source, spectral calculus applies
(2)-(4) in each source eigenspace. The exact isometry

    I_R psi=sum_n |n> Phi_(R,n)(alpha) psi               (5)

has I_R^dagger I_R=1, and the normal gap is at least one, regardless
of source norm. A single Hermitian source may itself depend on both
physical coordinates and momenta. The issue in Section 4 concerns
several sources that do not mutually commute.

## 2. A parent with fixed interaction order and bounded strength

Use three blocks of R qubits, one normal block 0 and two physical
control blocks 1,2. Put

    Q_i=(sum_a X_(i,a))/sqrt(2R),
    alpha_R=lambda Q_1 Q_2/sqrt(2),
    D_R=c_R(alpha_R)^dagger c_R(alpha_R),
    F_R=N_1+N_2+nu N_0^3, nu>0,
    H_R=R^(-2) D_R+R^(-3) F_R.                         (6)

This is a control model with a specified commuting source, not the
six-channel tensor lattice. The normal energy and slow energy have
both changed from the previous construction. Their ratio is R, so
normal excitations still separate in physical energy.

Every term in c_R has support on at most five microscopic qubits.
Consequently D_R has a decomposition with support at most ten.
Here are explicit summed-strength bounds that include repeated cell
indices. Write

    a=|lambda|/(2sqrt(2)), b=lambda^2/8.

The sums of absolute monomial norms in its three summands are
sqrt(R), a R and b R^(3/2). Therefore their total L and maximum
per-qubit sum l satisfy

    L<=R^(3/2)(1+a+b),
    l<=sqrt(R)(1+a+2b).

For c^dagger c the per-qubit sum is at most 2Ll, by assigning a
qubit's occurrence to the left or right factor. Multiplication by
R^(-2) in (6) yields the R-independent bound

    B_fast<=2(1+a+b)(1+a+2b).                           (7)

The slow number terms contribute at most R^(-3), and N_0^3 expands
into at most three-cell terms with per-qubit sum at most 3nu/R after
scaling. A convenient total bound is

    B_parent=2(1+a+b)(1+a+2b)+1+3nu.                   (8)

The [permutation-sector selection theorem](TENSOR_VERTEX_SELECTION.md)
applies with q=2,k=10 and C_(q,k)=480. Complete exchange with
J=2(480B_parent+Delta) selects the three symmetric blocks and gives
an excluded-sector ground gap at least Delta, uniformly in R.
Exchange adds at most 2J to the per-qubit budget. All these constants
are conservative. The block range is fixed, while complete exchange
still has growing connectivity within a block; fixed Euclidean
microscopic range is not established.

This differs from truncating the earlier trigonometric Hamiltonian.
The rotation angle is 2arctan(alpha/sqrt(R)), and the positive factor
in (3) changes the Hamiltonian away from its kernel. That factor
allows an exact polynomial parent. The previous high-weight Pauli
obstruction for its different unitary family remains valid.

## 3. The interacting quantum limit of this control

Embed the three symmetric blocks in three-mode Fock space. The
control quadratures Q_(i,R) converge on the finite-particle core to
q_i. The conditional normal rotation in (3) is generated by

    sqrt(2R) arctan[lambda Q_(1,R)Q_(2,R)/sqrt(2R)] P_(0,R).

The three quadratures act on different tensor factors. Their joint
spectral convergence and local uniform convergence of the displayed
function give strong unitary convergence to

    U=exp[-i lambda p_0 q_1 q_2].                       (9)

The exact kernel projectors therefore converge strongly, and (5)
converges to the shifted Gaussian isometry I=U(|0>_0 tensor identity).
In particular I^dagger q_0 I=lambda q_1 q_2.

There is no cutoff-dependent approximate-kernel error to amplify:
D_R I_R=0 exactly and D_R>=1-I_R I_R^dagger on the three symmetric
blocks. The physical Hamiltonian is R D_R+F_R. Its slow part obeys

    F_R>=min(1,nu)(N_0+N_1+N_2).                        (10)

Its limiting compression is the explicit two-coordinate operator

    H_eff=N_1+N_2+(lambda^2/4)(q_1^2+q_2^2)
                     +nu(m^3+3m^2+m),
    m=lambda^2 q_1^2 q_2^2/2.                         (11)

Here N_i=(p_i^2+q_i^2-1)/2 and hbar=1. The geometric quadratic term
is retained: (6) uses bare physical number operators rather than
the covariantly transported ones. The polynomial interaction and
its coefficient nu are supplied. This theory is not claimed to be
massless or Einstein gravity.

For clarity, the convergence of the slow quadratic forms can be
verified without differentiating an unbounded similarity. Conditional
on alpha, N_0 has the binomial distribution with probability
p=alpha^2/(R+alpha^2). Its third moment is

    R p+3R(R-1)p^2+R(R-1)(R-2)p^3,

which tends to alpha^2+3alpha^4+alpha^6 and is bounded by that
same polynomial for all R. This proves the last term of (11) on
finite-particle control inputs, whose quadrature moments are uniform.

For the control-number terms, use the X eigenbasis of each qubit.
Flipping one X eigenvalue in block 1 changes alpha by
delta alpha=+/-lambda Q_2/sqrt(R). The overlap of its two normal
states is

    g_R(alpha,alpha')=
      [(1+alpha alpha'/R)/sqrt((1+alpha^2/R)(1+alpha'^2/R))]^R.

The vectors (2) are real and normalized, with
||partial_alpha Phi_R||^2=(1+alpha^2/R)^(-2)<=1.
It follows that 0<=1-g_R<=|delta alpha|^2/2. On bounded control
quadratures,

    1-g_R=lambda^2 Q_2^2/(2R)+o(R^(-1)).

The exact compression of N_1 is N_1+(1/2)sum_a Z_(1,a)(1-g_(R,a)).
Using sum Z/R=1-2N_1/R gives its form limit
N_1+lambda^2 q_2^2/4. The analogous result for N_2 gives (11).
The global overlap bound and uniform higher quadrature moments on
fixed finite-particle inputs control the tails outside bounded
quadratures; hence this step is not a pointwise replacement over
the full spin spectrum.

These ingredients prove spectral and finite-time quantum convergence.
Finite-particle kernel trials have convergent slow forms. Conversely,
bounded physical energy gives a uniform total-number bound by (10),
which implies norm compactness at these fixed three blocks. The
distance of a bounded-energy state from ran I_R is O(R^(-1/2)).
Every norm limit is in ran I. Fatou's inequality for the positive
number form gives the lower variational bound, and the exact kernel
trials give the upper bound. The min-max principle then identifies
all fixed low eigenvalues and multiplicities. Isolated low spectral
projectors converge in norm after embedding. Bounded kernel-trial
energy controls the spectral tail and gives strong evolution,
uniformly on compact time intervals.

The limiting operator (11) is a confining polynomial Schrodinger
operator with compact resolvent; its positive quadratic potential
controls the axes where its higher mixed powers vanish. Finite
Hermite sums are a form core. These facts justify the trial-space
approximation in the preceding argument. No spatial continuum or
volume-uniform tensor-field limit follows from this three-block proof.

## 4. Noncommuting sources produce a definite energy in the fast band

Now take m normal spin blocks and bounded Hermitian matrices S_i
on a finite physical space. Supply the conditions independently:

    c_i=B_i-lambda S_i Z_i-lambda^2 S_i^2 B_i^dagger/R,
    D_R(lambda)=sum_i w_i c_i^dagger c_i, w_i>0.         (12)

At lambda=0 the common normal vacuum has the full physical
dimension. At small lambda its effective low-band Hamiltonian is

    H_band(lambda)=lambda^4 A_w+O(lambda^6),
    A_w=sum_(i<j) [w_i w_j/(w_i+w_j)]
                         [S_i,S_j]^dagger[S_i,S_j].     (13)

The coefficient is independent of R, including R=1. This is the
energy of the fast parent itself, distinct from the slow kinetic
correction in the preceding two notes.

A short derivation also fixes the coefficient and its sign. Write
a candidate state as |0>v+lambda psi_1+lambda^2 psi_2+.... Its first
correction is forced to have one-normal-particle coefficients S_i v.
The same-block two-particle coefficient in psi_2 is
sqrt[(R-1)/(2R)] S_i^2 v and cancels the single-source residual
exactly (it vanishes when R=1). For two different blocks let the
common coefficient of |1_i,1_j> be T_ij v. Its two residuals are

    (T_ij-S_i S_j)v, (T_ij-S_j S_i)v.

Minimizing their squared norms with weights w_i,w_j gives
T_ij=(w_i S_i S_j+w_j S_j S_i)/(w_i+w_j) and residual energy
the corresponding summand in (13). The residual is orthogonal to
the range of the unperturbed stacked annihilator, so higher state
coefficients cannot remove this leading energy. Normalization does
not alter it, since the lower energy coefficients vanish.

This perturbative claim has an R-independent small-coupling scope.
For unit weights put s=sum_i ||S_i||. On the resolvent circle
|z|=1/2 of D_R(0), expand D_R(lambda)-D_R(0) in powers of lambda.
Using |Z_i|<=1, B_i B_i^dagger<=B_i^dagger B_i+1 and
||B_i||<=sqrt(R), one obtains

    ||[D_R(lambda)-D_R(0)](D_R(0)-z)^(-1)||
      <=(2+2sqrt(2))rho+6rho^2+4rho^3+2rho^4,
    rho=|lambda|s.                                    (14)

For rho<=1/64 this is less than 0.08. The spectral projection and
its direct rotation to the vacuum sector therefore have analytic
bounds uniform in R. Normal parity identifies lambda with -lambda
on that sector, so the effective matrix is even. Cauchy estimates
then bound the remainder in (13) by C|lambda|^6 on a smaller disk,
with C independent of R. Bounded positive weights are handled with
constants depending on their upper and lower bounds. This uses
standard degenerate perturbation theory; see
[Bravyi, DiVincenzo and Loss](https://arxiv.org/abs/1105.0675).
The residual calculation above identifies the particular fourth
coefficient rather than assuming it from that general framework.

If [S_i,S_j] is invertible for some pair, (12) has no nonzero common
kernel at any nonzero lambda. Indeed the single-block kernel has the
unnormalized graph coefficients sqrt[binom(R,n)](lambda S_i/sqrt(R))^n.
The |1_i,1_j> coefficient computed in two orders requires
[S_i,S_j]v=0 for the all-normal-vacuum coefficient v. The graph
recurrences then force every coefficient to vanish.

Absence of an exact kernel is not by itself absence of a physical
band. The stronger issue is the matrix A_w. For example, for unit
weights choose

    S_1=diag(sigma_x,2sigma_x), S_2=diag(sigma_z,sigma_z).

Then A_w has eigenvalues 2,2,8,8. For sufficiently small fixed
nonzero lambda, the two pairs of physical states are separated by
6lambda^4+O(lambda^6), uniformly in R. Under the R fast/slow ratio
of (6), that splitting diverges in physical units. Subtracting a
scalar vacuum energy cannot retain all four intended physical states.
If A_w were scalar, its leading shift could instead be subtracted;
the conclusion about splitting must not be inferred merely from
noncommutativity or a positive common energy.

## 5. The actual Einstein sources encounter this obstruction

Use the three canonical TT pairs in
[the previous tensor-source calculation](NONLINEAR_CONSTRAINT_DRESSING.md),
with homogeneous xz shear (q_0,p_0) and one transverse wave's cosine
and sine pairs (q_c,p_c),(q_s,p_s), wave number k>0. Two normalized
real source coefficients are

    b=[p_c^2-p_s^2+(k^2/4)(q_s^2-q_c^2)]/sqrt(2),
    f=(k/4)(q_0 p_c-p_0 q_c).                           (15)

These are the scalar B cosine coefficient at 2k and the transverse
f_x sine coefficient at k, using unit-norm real Fourier profiles.
Their normal stiffnesses in M=diag(8L,K_vector) are
omega_b=32k^2 and omega_f=k^2. Their exact canonical bracket is

    {b,f}=k p_0 p_c/(2sqrt(2))-k^3 q_0 q_c/(8sqrt(2))
         =:r,                                         (16)
    {b,{b,f}}=(k^2/2)f.

In the quadratic Weyl algebra [b_hat,f_hat]=i hbar r_hat exactly.
For canonical conditions
a_i-lambda s_i/sqrt(2hbar omega_i), weighted by hbar omega_i,
(13) gives this pair's contribution

    lambda^4 hbar r_hat^2/[4(omega_b+omega_f)].          (17)

It is positive and nonzero. Its leading quartic classical symbol at
q_0=q_c=1 with all other displayed coordinates zero is
lambda^4 hbar k^4/16896. Equation (17), rather than the classical
symbol alone, fixes the operator ordering: the Weyl symbol of the
square may also have a constant quantum term. This is a contribution
within the specified TT truncation and auxiliary Fourier-mode test;
it is not a full periodic Einstein solution or a computed physical
graviton energy. The bounded-matrix uniform estimate (14) does not
justify removal of the physical cutoff for these unbounded sources.

There is an explicit leading coupled repair of (12):

    delta c_i=lambda^2 sum_(j!=i) [w_j/(w_i+w_j)]
                            Z_i B_j^dagger [S_i,S_j].  (18)

It cancels the two-particle residual used in (13). It also cancels
the order-lambda^2 commutator of different c_i exactly on the finite
spin algebra, since [B_i,B_i^dagger]=Z_i. Its positive parent therefore
has low-band energy O(lambda^6), rather than (13). Higher orders
have not been cancelled. In particular (16) shows that the actual
source algebra is not nilpotent: nested commutators do not simply
terminate. A fixed-order repair leaves an error at fixed coupling
that the growing fast/slow ratio can amplify. It is not an exact
nonlinear Einstein constraint construction.

## 6. What has changed in the proposed model

There is now a proved nonlinear quantum spin control with both fixed
interaction order and bounded summed microscopic strength. It uses
an exact polynomial normal condition, not a finite-order approximation
to a unitary Hamiltonian, and its kernel survives the scale limit.
This establishes feasibility of that combination for commuting
sources on a fixed carrier.

The Einstein extension must couple its normal conditions from the
start. Independent spin-coherent source displacements generate the
matrix (13); increasing block size does not suppress its coefficient.
The next required construction is an all-order compatible completion
of such conditions, with the covariant physical observables and
locality bounds established together. Its gravitational coefficients,
clock algebra, homogeneous constraint, physical G and continuum limit
must still be derived. The exact control's stabilizing interaction
and its two massive physical coordinates are not an Einstein model.
The TOE remains unproved.

## 7. Verification

Run

    OPENBLAS_NUM_THREADS=1 python3 -W error::RuntimeWarning scripts/polynomial_spin_constraints_audit.py

Exact symbolic identities and 36 numerical cases pass. The report is
[data/polynomial_spin_constraints_audit.json](data/polynomial_spin_constraints_audit.json).
It checks coherent kernels and their complete normal spectra,
microscopic monomial budgets, full small-block Hamiltonians, the
interacting control limit, the noncommuting effective energy matrix,
the leading coupled repair, and the actual Einstein source bracket.
Numerical cutoff comparisons support the analytical arguments; they
are not interval certificates. No new Lean theorem is claimed.
