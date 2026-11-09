# A positive metric algebra on growing microscopic spin blocks

Date: 2026-09-11

The single-component logarithmic repair in
[the spin-clock calculation](SPIN_CLOCK_BRACKET.md) extends to a full
positive three-dimensional metric. There are six logarithmic
coordinates and nine self-adjoint generators of changes of frame.
Finite symmetric blocks of the existing four-spin cells represent
Galerkin approximations to these operators. On every fixed finite
oscillator input space, their affine Lie brackets, bounded metric
observables and finite-time affine transformations converge as the
block size grows. The estimates keep all output components.

This closes a local representation problem. It does not select a
microscopic gravitational phase or derive Einstein dynamics. The
construction chooses its encoding and operators, with no uniform
bound on their microscopic interaction order.

Positive metric variables and affine commutation relations are
established ideas: see John R. Klauder,
[An Affinity for Affine Quantum Gravity](https://arxiv.org/abs/1003.2617),
especially its opening algebra. This note adapts that kinematic idea
to the repository's spin block and states the cutoff/domain estimates.
It does not establish the gravitational constraint or continuum claims
of that program.

## 1. Which canonical variables can be globally self-adjoint?

Let Q be a positive metric diagonal entry. A self-adjoint operator
Pi cannot implement the full Weyl translation law

    exp(it Pi) Q exp(-it Pi) = Q + t I

for every real t: unitary conjugation preserves the spectrum, whereas
arbitrary negative translations cannot preserve a nonempty spectrum
bounded below. This is a global translation obstruction. It does not
exclude formal commutators on restricted, non-invariant domains.

It also does not contradict
[the classical cotangent reconstruction](CANONICAL_METRIC_RECONSTRUCTION.md).
Canonical momenta for unrestricted logarithmic coordinates remain
available. What fails is promoting each positive metric entry and its
classical conjugate to a global self-adjoint translation pair.

Here h ranges over Sym(3), including its trace, and q=exp(h). This is
the full six-component metric before spatial constraint reduction.
The five trace-free variables in the preceding classical construction
are its shape variables; the trace is subsequently fixed there by
the conformal constraint. We do not impose that constraint here.

## 2. The complete affine action and its quantum generator

Use the Frobenius inner product and an orthonormal symmetric basis
E_a, a=1,...,6. For any real three-by-three matrix A the congruence

    q(t) = exp(t A) q exp(t A^T)                              (1)

is positive for every real t. Write its logarithmic flow as phi_A^t.
The differential of exp and the induced vector field are

    J_h(X) = integral_0^1 exp(s h) X exp((1-s)h) ds,
    F_A(h) = J_h^(-1)(A exp(h) + exp(h) A^T).                (2)

In an eigenbasis of h, J_h multiplies X_ij by

    exp((lambda_i+lambda_j)/2)
      sinh((lambda_i-lambda_j)/2)/((lambda_i-lambda_j)/2).

The continuous value at coincident eigenvalues is understood.
Every factor is strictly positive, so (2) is globally defined.

On L^2(Sym(3),dh), take the unitary half-density transport

    (U_A(t)f)(h)
      = |det D phi_A^(-t)(h)|^(1/2) f(phi_A^(-t)(h)).

Change of variables proves unitarity. It is a strongly continuous
one-parameter group, with self-adjoint generator whose expression is

    D_A = -i (F_A^a partial_a + (1/2) partial_a F_A^a),
    U_A(t) = exp(-it D_A).                                  (3)

The half-divergence term is necessary for the flat dh inner product.
We use the self-adjoint transport generator, not an unspecified
extension of a formal differential expression. Compactly supported
smooth functions form a core: the flow is complete with at most
linear growth, so transport-compatible cutoffs and smooth
approximation give graph-norm approximation. The estimates below
also put Schwartz functions in its domain.

The vector fields have the sign convention

    [F_A partial, F_C partial] = -F_[A,C] partial.

For example, differentiating A q+q A^T in the direction
C q+q C^T and antisymmetrizing gives this sign. Half-density Lie
derivatives obey the same vector-field bracket. Consequently,

    [D_A,D_C] = i D_[A,C],
    i[D_A,q] = A q+q A^T,
    [q_ij,q_kl] = 0.                                       (4)

For unbounded q, these differential identities hold on compactly
supported smooth functions. The integrated statement is

    U_A(t)^* q U_A(t) = exp(tA) q exp(tA^T)

as multiplication operators with their corresponding domains.
There are nine GL(3) generators, but only six configuration
coordinates: the rotations in the stabilizer of a given metric
do not add independent canonical pairs.

## 3. A bounded observable that retains the full metric

To control the cutoff without assuming inverse-metric moments, use
the matrix logistic transform

    B = q(I+q)^(-1) = (I+exp(-h))^(-1),   0 < B < I.         (5)

B is a multiplication operator on C^3 tensor L^2(Sym(3)).
It determines q=B(I-B)^(-1) in the continuum representation.
The inequalities in (5) are strict quadratic-form inequalities,
not a uniform spectral distance from 0 or 1.

Since delta B=(I+q)^(-1) delta q (I+q)^(-1), (4) gives

    i[D_A,B] = V_A(B),
    V_A(B) = (I-B) A B + B A^T (I-B)
           = A B+B A^T-B(A+A^T)B.                          (6)

This is a bounded matrix polynomial, with norm at most 2||A||.
All derivatives of B as a function of the six real h coordinates
are bounded. One way to verify this is spectral differentiation:
every divided difference of the scalar logistic function is bounded
by its corresponding bounded real derivative divided by a factorial.
In fixed matrix dimension the finite spectral sums give the required
multilinear bounds. Thus multiplication by B preserves Schwartz space.

The bounded transform is a control device. Convergence of B does
not by itself control q, q^(-1), curvature, or the inverse metric in
Einstein's constraint bracket. Those require additional estimates
near the spectral endpoints.

## 4. Domain estimates that make Galerkin convergence legitimate

Let h=ell sum_a x_a E_a for a fixed ell>0, and let N be the
six-mode harmonic oscillator number on L^2(R^6,dx). Constants below
may depend on ell. Decompose A=S+Omega into symmetric and
antisymmetric parts. Equation (2) becomes

    F_A(h) = g(ad_h) S + [Omega,h],
    g(z) = z coth(z/2),     g(0)=2.                         (7)

Here ad_h acts on all three-by-three matrices. Its eigenvalues are
the real differences lambda_i-lambda_j. Direct differentiation of
the scalar g gives

    |g(z)| <= 2+|z|,   |g'(z)| <= 1,

and bounded real derivatives of every higher order. Differentiating
the finite-dimensional spectral calculus gives bounded derivatives
of F_A of every positive order. For example,

    ||ad_(delta h)||_HS^2
      = 6 tr((delta h)^2)-2(tr delta h)^2
      <= 6 ||delta h||_F^2.

This bounds the first derivative through the divided-difference
bound for g; the same argument iterates at higher orders.
F_A itself grows at most linearly. Therefore D_A preserves
Schwartz space and

    K_A := ||D_A (N+1)^(-1)|| < infinity.                   (8)

To see (8), bound the coefficients of the first derivative in (3)
by C(1+|x|) and its zeroth-order coefficient by a constant.
The oscillator controls partial_a and x_b partial_a relative to
N+1, as follows directly by writing them in creation and
annihilation operators.

For every fixed T, the complete flow and its inverse grow at most
linearly and have bounded positive-order derivatives on |t|<=T.
The determinant half-density and its derivatives are also bounded
on such intervals. These properties follow from the variational
flow equations and the bounded derivatives just proved. They imply
that U_A(t) preserves Schwartz space, with continuous Schwartz
seminorms uniformly on compact time intervals. No invariant
finite-occupation subspace is assumed.

## 5. Exact realization on a finite symmetric spin block

The existing four-spin cell contains the singlet vacuum, a second
singlet and the quintet: seven orthonormal active states in its
sixteen-dimensional Hilbert space. The six excitations can be
identified with the scalar and five shape coordinates of Sym(3).
An orthogonal change to the Cartesian symmetric basis used by the
numerical audit preserves the oscillator number.

This identification intertwines rotations with the original
microscopic spin. If Omega is the antisymmetric vector rotation
matrix and T_ab=tr(E_a[Omega,E_b]), then T is antisymmetric and
the action on the six excitation states is iT. The scalar singlet
is invariant and the five remaining states carry the original
quintet. Equation (3) for this rotation is exactly

    D_Omega = sum_ab (i T_ab) a_a^dagger a_b.

It preserves every P_R and equals the sum of the cell total-spin
generators on the symmetric active block. The audit checks this
both against the sixteen-row microscopic spin matrices and against
the full finite Galerkin matrices. Identifying these internal
rotations with spatial frames is still a model choice.

Take R such cells and their permutation-symmetric active subspace.
Its basis is

    |n_1,...,n_6>,  |n|<=R,  n_0=R-|n|,
    dimension = binomial(R+6,6).

It is exactly isometric to the oscillator projection P_R=1_(N<=R).
The normalized collective transition into state a has coefficient

    B_a^dagger |n>
      = sqrt((n_a+1)(1-|n|/R)) |n+e_a>.

Dressing it on the right by (1-N/R)^(-1/2) below the top face,
and zero on that face, gives the exact truncated creation matrix.
This explains the encoding using the same microscopic transitions
as the preceding one-component repair.

Now define the finite spin operators by exact matrix elements:

    D_(A,R) = P_R D_A P_R,   B_R = P_R B P_R.                (9)

These are compressions of continuum operators; they are not
asserted equal to simply substituting truncated coordinates into
each nonlinear continuum formula. Matrix elements of (9) are
specified by ordinary Gaussian/Hermite integrals.

D_(A,R) is Hermitian. As an operator on C^3 tensor P_R H,
B_R and I-B_R are strictly positive. For any nonzero vector-valued
Hermite function f,

    <f,B_R f> = integral f(h)^* B(h) f(h) dh > 0,

and the same argument applies to I-B_R. Individual entries of B_R
need not commute at finite R.

Every matrix in (9) is an actual finite operator on the selected
spin block, extended by zero on the unused spin space if desired.
Strict metric positivity is claimed on the encoded space only.
An extension with a fixed positive metric on the orthogonal
complement is also possible. Neither extension supplies a stable
phase or bounded-range, bounded-body-order microscopic interactions.
R cells, hence 4R qubits per encoded site, grow with the accuracy.

## 6. Full-output error bounds on a specified input domain

Write P=P_R, Q=I-P_R and fix an input cutoff n<=R. For any
Schwartz-preserving operator X and integer m>=0,

    ||Q X P_n||
      <= (R+1)^(-m) ||(N+1)^m X P_n||.                    (10)

All right-hand constants are finite because P_n has finite
dimension and consists of Schwartz functions.

Using the exact continuum algebra, the finite Lie defect is

    [D_(A,R),D_(C,R)]-i D_([A,C],R)
      = -P D_A Q D_C P + P D_C Q D_A P.                   (11)

Define d_(A,m,n)=||(N+1)^m D_A P_n||. Equations (8)-(11) give

    ||([D_(A,R),D_(C,R)]-i D_([A,C],R)) P_n||
      <= (R+1)^(-m)
          (K_A d_(C,m+1,n)+K_C d_(A,m+1,n)).              (12)

All output rows in P_R are retained. Compressing the output back
to P_n would give a weaker test and is not used.

For metric covariance, extend P, N and D by the auxiliary identity
on C^3 and put b_(m,n)=||(N+1)^m B P_n||. Subtracting the
polynomial in (6), rather than merely its compressed matrix,
gives the exact defect

    i[D_(A,R),B_R]-V_A(B_R)
      = -i P D_A Q B P+i P B Q D_A P
        -P B Q(A+A^T)B P.                                (13)

The last term matters: compression does not preserve products.
Since ||B||<=1, its norm on the input P_n obeys

    ||(i[D_(A,R),B_R]-V_A(B_R))P_n||
      <= (R+1)^(-m)
         (K_A b_(m+1,n)+d_(A,m,n)+2||A|| b_(m,n)).         (14)

Likewise, each component commutator is the difference of two
terms P B_ij Q B_kl P and P B_kl Q B_ij P, so it tends to zero
with a bound of the same form. The direct observable error
||(B_R-B)P_n|| is bounded by (10).

Thus convergence is faster than any fixed inverse power of R
on a fixed P_n. The constants depend on n, m, ell and the
generators; they are graph norms, not a computed universal error
constant. This is not convergence in operator norm on the whole
growing Hilbert space. It also does not place an unknown physical
vacuum within the controlled input domain.

## 7. Finite transformations and several encoded sites

For unit psi in P_n, let psi(t)=U_A(t)psi. Duhamel's formula and
the discarded tail give, for |t|<=T,

    ||exp(-it D_(A,R))psi-psi(t)||
      <= ||Q psi(t)|| + integral_0^|t| ||P D_A Q psi(s)|| ds.

For negative t the integral follows the negative-time orbit.
By (8), (10) and compact-time preservation of Schwartz space,
the bound is at most

    (R+1)^(-m) (M_(m,n,T)+T K_A M_(m+1,n,T)),              (15)
    M_(j,n,T)=sup_(|s|<=T) ||(N+1)^j U_A(s)P_n|| < infinity.

The comparison takes place in the full oscillator Hilbert space.
It includes probability leaving P_R during a finite transformation.
It is not just an infinitesimal or input-to-input matrix identity.
By density of finite Hermite spans and the unitary norm bound,
the embedded finite evolutions converge strongly on every fixed
Hilbert-space state, uniformly on compact time intervals. The
explicit rate in (15) applies to the stated finite input spaces;
there is no uniform rate over all normalized states.

At finitely many encoded sites, operators at distinct sites commute.
For sums sum_x a_x D_(A,R,x) and sum_x c_x D_(C,R,x), the Lie
defect on tensor_x P_n is bounded by the right-hand side of (12)
times sum_x |a_x c_x|. In particular, a bound for extensive sums
can grow linearly with the site count. The local result cannot
silently be promoted to a volume-uniform continuum statement;
one must specify smearings, state domains and a joint cutoff limit.

These independent changes of frame omit the advective term
v^i partial_i h in a spatial diffeomorphism. The full spatial
generator, the metric-dependent Hamiltonian-constraint bracket
and a two-polarization reduced phase are still separate requirements.
The nine local affine generators are not nine gravitational
constraints.

## 8. Reproducible checks and remaining physical gap

Run:

    OPENBLAS_NUM_THREADS=1 python3 -W error::RuntimeWarning scripts/affine_spin_metric_audit.py

The audit checks the noncommuting polynomial vector fields and the
bounded-transform derivative symbolically. It verifies the existing
seven-state cell and every dressed occupation coefficient in its
selected finite blocks. Gaussian quadrature constructs all affine
generators and all metric components, checks positivity and computes
full-output commutator defects on occupation at most one. Quadrature
refinement is reported independently of cutoff changes. A displaced
Gaussian checks finite-time convergence for the central dilation.
An independent nonlinear shear test in SPD(2) uses the exact
log-congruence flow and its half-density Jacobian. The latter is
computed from the congruence determinant exp((d+1)t tr A) on
Sym(d) and the exponential Jacobians at the two endpoints.
The general finite-time conclusion is (15), not an extrapolation
from these numerical subgroups.

There are 20 numerical cases and eight quadrature-refinement pairs,
in addition to the exact symbolic identities. The full SPD(3)
calculation uses R=1,2,3,4 with input occupation at most one.
Its covariance defect is about 0.00473136 at R=2 and 0.000135423
at R=4; the latter block has dimension 210. Its bounded metric
spectrum lies approximately in [0.33368349,0.66631651].
The complete sequence of Lie and covariance defects is in
[the report](data/affine_spin_metric_audit.json); odd and even
cutoffs do not give a monotone sequence. This is compatible with
(12)-(14), whose output space grows with R.

The separate SPD(2) illustration extends to R=8. Its finite-shear
state error decreases from about 0.0582346 at R=2 to 0.000005399
at R=8. The central dilation test reaches about 4.90e-13 at R=16.
The report separates quadrature changes in the generators, the
bounded metric, the evolved finite state and the independent
continuum overlap.

The analytical proof covers the full six-coordinate metric.
Lower-dimensional numerical illustrations are labeled separately.
Neither quadrature differences nor floating-point residuals are
certified integration error bounds, and no new Lean theorem is
claimed.

What changes in the proposed model is precise: use unrestricted
logarithmic coordinates, self-adjoint affine generators and growing
spin blocks for this local positive metric representation. Requiring
global translations of positive metric entries would be the wrong
kinematic target. This does not select the representation from
microscopic dynamics, establish spatial locality, or fix G.

The next gravity test must use this same metric in a spatial
constraint algebra, control the unbounded inverse-metric factors,
and obtain an interacting physical tensor sector and its boundary
energy from a specified microscopic Hamiltonian. The prior
[embedding counterexample](EMBEDDING_VERSUS_GRAVITY.md) still
prevents calling covariance alone a gravitational phase. Einstein
gravity and a physical TOE remain unproved.
