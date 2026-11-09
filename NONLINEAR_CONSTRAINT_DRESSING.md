# Compatible nonlinear constraint vacua and their quantum response

Date: 2026-09-11

The [linear tensor parent](HOLOMORPHIC_TENSOR_PHASE.md) selects two
polarizations, but its vacuum conditions do not produce the nonlinear
conformal and longitudinal responses. Simply subtracting the desired
operator sources from its annihilators does not resolve this: the
sources need not commute. This note constructs a compatible nonlinear
deformation and calculates the Hamiltonian in its normalized kernel.

The result is conditional. With a finite physical regulator it gives
an exact nonempty quantum kernel and the supplied Einstein response
through order two in a coupling parameter, together with an explicit
quantum correction. An independent, untruncated oscillator example
proves that this correction can open a gap even when the transverse
vacuum has exactly zero energy. Uniform microscopic locality, removal
of the physical regulator, and Einstein's clock algebra are not proved.

## 1. A common dressing resolves the compatibility problem

First let the physical Hilbert space have finite dimension d. Let
S_i be arbitrary Hermitian matrices on it, not necessarily commuting.
There are m auxiliary coordinates y in R^m, with
pi_i=-i hbar partial_i. Fix a real symmetric positive matrix M and put

    N=M^(-1),
    Omega(y)=(det M/(pi hbar)^m)^(1/4) exp[-y^T M y/(2hbar)],
    c_i=hbar partial_i+(M y)_i,
    X(y)=sum_i y_i S_i,       T_lambda(y)=exp[lambda X(y)/hbar].

All c_i commute and have common kernel Omega times the physical
space. Define the deformed conditions using the same similarity:

    C_i=T_lambda c_i T_lambda^(-1)
       =hbar partial_i+(M y)_i-A_i(y),
    A_i=hbar (partial_i T_lambda) T_lambda^(-1).          (1)

These are annihilation conditions, not Hermitian first-class
gravitational generators. Their adjoints are not additionally imposed.
On smooth compactly supported functions,

    [C_i,C_j]=0,
    hbar(partial_i A_j-partial_j A_i)-[A_i,A_j]=0.        (2)

Their exact common kernel is

    J_lambda v=Omega(y) T_lambda(y) v,      v in C^d.    (3)

Indeed T^(-1) C psi=c T^(-1)psi locally, so the first-order equations
give T^(-1)psi=Omega v with constant v. Bounded S_i and the Gaussian
make (3) square-integrable for every v. Smooth cutoffs of (3) converge
in the graph norm of all C_i; the only cutoff residual is
hbar (partial_i cutoff) J_lambda v. Thus (3) is also the kernel of
the nonnegative closed quadratic form sum_i ||C_i psi||^2, initially
defined on compactly supported smooth functions. Its dimension is d.
This is a kernel theorem, not a general spectral-gap theorem.

The first nontrivial terms are

    A_i=lambda S_i
        +lambda^2/(2hbar) sum_j y_j [S_j,S_i]
        +lambda^3/(6hbar^2) sum_(j,k) y_j y_k [S_j,[S_k,S_i]]
        + ... .                                        (4)

The coefficients follow by differentiating an exponential:
A_i=lambda integral_0^1 exp[t lambda X/hbar] S_i
exp[-t lambda X/hbar] dt. In contrast, the naive shifts
c_i-lambda S_i have commutator lambda^2[S_i,S_j]. The derivatives
of the second term in (4) cancel precisely this commutator. For
S_1=sigma_x and S_2=sigma_z it is invertible, so the naive conditions
have no nonzero common solution when lambda is nonzero. Equation
(3) supplies two independent solutions for the completed conditions.

Flat-connection extensions of noncommuting constraints are established
methods; see [Batalin and Lavrov](https://arxiv.org/html/1505.03601),
Sections 2-3. The Gaussian kernel and compression below are proved
directly for this particular nonunitary choice. This is not a claim
to a new general quantization method or to an Einstein gauge algebra.

## 2. Normalizing the physical space changes the Hamiltonian

T is not unitary. Define the positive Gram matrix and exact isometry

    G_lambda=J_lambda^dagger J_lambda
            =integral |Omega|^2 exp[2lambda X/hbar] dy,
    I_lambda=J_lambda G_lambda^(-1/2).                   (5)

G is finite, and G>=I by pairing y with -y and using cosh of a
Hermitian matrix. For finite d all the following expansions have
operator-norm remainders on bounded lambda intervals. Gaussian parity
eliminates odd orders for physical observables and even orders for
one y insertion. Set Q=sum_(i,j) N_ij S_i S_j. Gaussian integration gives

    G_lambda=I+lambda^2 Q/hbar+O(lambda^4),

    I_lambda^dagger O I_lambda
       =O-lambda^2/(4hbar) sum_(i,j) N_ij
                         [S_i,[S_j,O]]+O(lambda^4),     (6)

    I_lambda^dagger y_i O I_lambda
       =lambda/2 sum_j N_ij {S_j,O}+O(lambda^3),        (7)

    I_lambda^dagger y_i y_j I_lambda
       =(hbar/2)N_ij I
        +lambda^2/2 sum_(k,l) N_ik N_jl {S_k,S_l}
        +O(lambda^4).                                  (8)

Braces denote anticommutators. O is any physical matrix; it commutes
with y before compression. These formulas do not replace S_i by
commuting labels. For example, before the two factors G^(-1/2) are
included, the order-two term for O is

    (lambda^2/(4hbar)) sum N_ij
       (S_i S_j O+O S_i S_j+2 S_i O S_j).

The normalization subtracts lambda^2 {Q,O}/(2hbar), yielding (6).
Wick's four-point identity gives (8); its term proportional to
N_ij Q cancels against the same normalization. This is why a
nonempty kernel alone is insufficient to identify its dynamics.

The compression in (6) is a unital completely positive map. It need
not preserve products or canonical commutators of the original
physical observables. The abstract physical Hilbert space is preserved
by I; specifying which compressed observables represent the metric
and momentum is additional work.

## 3. Apply the formula to the required gravitational response

Use the already supplied quadratic sources and positive elliptic
inverses from [the quartic calculation](EINSTEIN_QUARTIC_CONSTRAINTS.md):

    B=T+V, A=7T-V, T=|s|^2, V=|partial h|^2/4,
    f_i=-(s:partial_i h+partial_j[s,h]_ij)/2,
    L=-Delta, K=-Delta I-(1/3)grad div.

Here the matrix commutator [s,h] is the spatial tensor commutator;
operator commutators in (4)-(8) are distinct. Symmetric operator
orderings and a finite physical cutoff are required when turning
these sources into matrices. Boundary conditions make L and K
invertible; numerical Fourier tests remove their constant modes.
This is not a solution of the compact homogeneous Einstein constraint.

Choose the auxiliary data

    y=(u,W), M=diag(8L,K), S=(B,f),                     (9)

and use lambda as a coupling-order bookkeeping parameter. Equations
(7)-(8) imply

    I^dagger u I=lambda L^(-1) B/8+O(lambda^3),
    I^dagger W I=lambda K^(-1) f+O(lambda^3).            (10)

Consider the specified slow Hamiltonian

    F_lambda=H_2+lambda H_3+lambda^2 H_local,4
                   -lambda sum_x A_x u_x
                   +2 W^T K W-hbar m_W I,             (11)

where m_W is the number of vector auxiliary coordinates. Its last
constant removes their known vacuum contribution. H_local,4 is
the supplied curvature and matrix-commutator quartic. There is no
scalar saddle multiplier in this quantum construction.

Combining (6)-(8), with all inverse and source indices retained, gives

    I^dagger F_lambda I
       =H_2+lambda H_3+lambda^2(H_target,4+Q_quant)
          +O(lambda^3),                               (12)

    H_target,4=H_local,4
         -(1/16) sum_(x,z) (L^(-1))_xz {A_x,B_z}
         +2 sum_(i,j) (K^(-1))_ij f_i f_j,

    Q_quant=-(1/(4hbar)) sum_(i,j) (M^(-1))_ij
                                  [S_i,[S_j,H_2]].     (13)

In the commuting classical expression the scalar term is exactly
-<A,L^(-1)B>/8 and the vector term is 2<f,K^(-1)f>, including the
positive contribution that independent stable quadratic minimization
could not produce. The sign comes from constrained displacement of
the quantum band and its specified slow energy. No unstable auxiliary
vacuum is minimized. The original source coefficients remain inputs.

Equation (12) is a finite-regulator operator identity to the stated
order. It does not rely on a semiclassical approximation. If S_i and
H_2 are Weyl-ordered quadratics on a canonical finite-mode core,
each commutator is exactly i hbar times its quadratic Poisson bracket.
Consequently Q_quant is an order-hbar quadratic operator. It generally
renormalizes the free propagation at order lambda^2, rather than being
another classical quartic. The finite-cutoff matrices need not obey
exact canonical commutation relations; that last classification is
a separate statement in the untruncated quadratic algebra.

At a fixed regulator one can cancel this known correction by adding
-lambda^2 Q_quant to (11). That is an explicit counterterm choice,
not a derivation of its coefficient by gravity. Its uniform locality,
cutoff dependence and compatibility with masslessness need proof.
Likewise, (10) does not generate the lapse n=lambda L^(-1)A/8 or
arbitrary changes of clock. Agreement of a fixed-gauge Hamiltonian
through fourth field order is weaker than the Einstein constraint
algebra and its universal matter coupling.

The frozen quartic audit already checks the full tensor source and
inverse identities. The new matrix tests check the operator ordering
and normalization in (12); they are not simulations of a full
three-dimensional nonlinear tensor field.

There is also an exact evaluation of Q_quant for genuine restricted
Einstein sources. Normalize spatial averages to one and retain three
canonical pairs, with the following real TT fields depending on z:

    E_0=(e_x e_z^T+e_z e_x^T)/sqrt(2), D=diag(1,-1,0),
    h=q_0 E_0+[q_c cos(kz)+q_s sin(kz)]D,
    s=p_0 E_0+[p_c cos(kz)+p_s sin(kz)]D, k>0.

E_0 is a homogeneous tracefree shear. The two oscillatory profiles
have unit mean Frobenius norm and are transverse to z. The induced
three-pair canonical bracket is a specified Galerkin bracket, not
the bracket of the unrestricted TT field. In this truncation,

    H_2=p_0^2+p_c^2+p_s^2+k^2(q_c^2+q_s^2)/4,

    f_x=k/(2sqrt(2))[(q_0 p_c-p_0 q_c)sin(kz)
                            -(q_0 p_s-p_0 q_s)cos(kz)].

Keep the actual B and f_z as well, and remove constant auxiliary
sources as in the earlier Fourier audits. Direct quadratic Poisson
brackets, or equivalently exact Weyl commutators, then give

    Q_quant=(hbar/256)[4k^2 q_0^2
                 +3k^2(q_c^2+q_s^2)+20(p_c^2+p_s^2)].  (13a)

For verification, the scalar nonconstant source has wave number 2k
and inverse weight 1/(32k^2); f_x has weight 1/k^2; f_z's nonconstant
part has weight 3/(16k^2). The homogeneous shear term comes entirely
from f_x. Formula (13a) is checked both symbolically from the tensor
fields and independently using Fourier inverses of their quadratic
source Hessians. It exposes an explicit order-hbar lambda^2 response
for a coordinate with zero free potential. It is not a prediction of
a physical graviton mass: further tensor modes, the chosen ordering
of other interactions, counterterms and the full clock symmetry have
not been included. In particular these mean-subtracted source tests
are not full periodic Einstein solutions.

## 4. An exact untruncated example: the kernel itself can induce a gap

There is a useful control with one physical coordinate q and one
auxiliary y. Take M=mu>0, S=q^2 and

    C=hbar partial_y+mu y-lambda q^2,
    D=C^dagger C/2,
    H_Lambda=Lambda D+p_q^2/2+omega^2 q^2/2, omega>0.   (14)

The exact normalized kernel embedding, without a physical occupation
cutoff, is

    (I psi)(q,y)=(mu/(pi hbar))^(1/4)
       exp[-mu(y-lambda q^2/mu)^2/(2hbar)] psi(q).       (15)

Here the unnormalized J need not exist on every physical vector;
(15) defines the isometry directly. The transverse energy is exactly
zero for every q. Its gap at fixed q is hbar mu. Nevertheless,

    I^dagger H_Lambda I
       =p_q^2/2+(omega^2/2+hbar lambda^2/mu)q^2,        (16)
    omega_eff=sqrt(omega^2+2hbar lambda^2/mu).

This identity is exact on the physical oscillator form domain.
The real normalized Gaussian has zero Berry connection, while
||partial_q Omega_shifted||_y^2=2lambda^2 q^2/(hbar mu).
The physical kinetic energy therefore adds
(hbar^2/2)||partial_q Omega_shifted||^2. This proves (16).
It is the familiar geometric contribution in quantum confinement;
see [Wachsmuth and Teufel](https://arxiv.org/abs/0907.0351).
Neither a source-dependent fast zero-point energy nor a failure of
the annihilation kernel is needed for this effect.

There is also a spectral limit here, not just a static compression.
For Lambda>=1 the forms in (14) increase with Lambda. Bounded energy
controls p_q^2 and q^2 and gives <D>=O(Lambda^(-1)). Moreover,

    2D=p_y^2+(mu y-lambda q^2)^2-hbar mu,

so p_y^2 and the squared distance to the shifted normal center are
uniformly bounded. A bound on q^2 controls the probability of large
q; on its complement the shifted center is bounded. The latter
distance bound then controls the probability of large y. These tail
bounds, the two derivative bounds and local Rellich compactness
give norm-precompactness of bounded-energy sequences.

Every limit lies in ker D. Finite-energy trial vectors (15) and the
min-max principle give the upper limits of all fixed eigenvalues.
The compactness and the weak eigenvalue equation on kernel test
vectors give their lower limits and multiplicities. Thus each fixed
low eigenvalue converges to (n+1/2)hbar omega_eff, and isolated
spectral projectors converge in norm after the embedding (15).
Kernel trials also give strong finite-time evolution by controlling
the spectral tail. This proof uses omega>0 for compactness. The
formula at omega=0 still exhibits a positive induced oscillator
term, but a uniform spectral theorem at that endpoint is not asserted.

This explicit result strengthens the masslessness warning for a
nonlinear tensor vacuum: even an exactly zero-energy constraint
kernel does not protect a massless slow Hamiltonian. It is not a
calculation of a graviton mass in the proposed tensor model.

## 5. Finite-spin kernels can be dressed, but locality is the frontier

An elementary finite-dimensional counterpart works for actual spin
spaces. Let d_i be any finite-spin annihilation conditions, with
D_0=sum d_i^dagger d_i and kernel projector P. For any Hermitian
spin operator X_R define

    T_R=exp(lambda X_R),
    d_i'=T_R d_i T_R^(-1),
    P'=the orthogonal projector onto T_R ran P.         (17)

The kernel is exactly T_R ran P, its dimension is unchanged, and
its physical isometry is T_R P(P T_R^2 P)^(-1/2). If the first
positive eigenvalue of D_0 is delta_0, the new positive gap obeys

    gap(sum d_i'^dagger d_i')
         >=delta_0/cond(T_R)^2
         >=delta_0 exp[-4|lambda| ||X_R||].             (18)

To prove this, regard all d_i as one stacked matrix. Left
multiplication by block-diagonal T_R and right multiplication by
T_R^(-1) preserve rank. Each nonzero singular value is bounded
below by the old one divided by cond(T_R). This statement concerns
the whole finite-dimensional space; it does not use a small-occupation
approximation. Applied to the previous tensor parent it preserves
the established kernel as a vector space, but need not preserve its
particle-number grading or its occupation estimates.

Equation (18) is not uniform if ||X_R|| grows. Nor does a local
generator give a fixed-support dressed operator for free:

    d_i'=sum_(n>=0) lambda^n ad_(X_R)^n(d_i)/n!          (19)

has successively larger support. At a fixed perturbative order,
local sources on an unreduced canonical lattice give a bounded
range for (4). That observation is insufficient at fixed nonzero
lambda and an amplified R^2 constraint scale: a fixed-order error
does not tend to zero as R grows. Source projection into the physical
TT space and the normalized map (5) additionally contain spatially
nonlocal operators. No uniform decay, bounded interaction order,
or microscopic summed-strength estimate for this nonlinear family
has been established.

The next construction must control that entire dressing, its physical
normalization and its clock response together. Simply declaring the
common kernel, dropping Q_quant, or identifying four new auxiliaries
with the original four normal tensor modes does not do this. Such
an identification must respect canonical brackets and spatial
locality; in the construction above the physical input was supplied.
The nonlinear Einstein phase, finite physical G, continuum limit,
and TOE remain unproved.

## 6. Verification

Run

    OPENBLAS_NUM_THREADS=1 python3 -W error::RuntimeWarning scripts/nonlinear_constraint_dressing_audit.py

The report is
[data/nonlinear_constraint_dressing_audit.json](data/nonlinear_constraint_dressing_audit.json).
It records exact identities, Gaussian quadrature checks with
noncommuting matrix sources, finite-spin similarity spectra and
untruncated-control Galerkin spectra with an increased cutoff check.
There are 32 numerical cases, including an independent Fourier check
of the explicit restricted tensor correction (13a).
The latter numerical spectra corroborate the analytic limit; their
cutoff comparison is not an interval error certificate. No new Lean
theorem, fully nonlinear tensor evolution or uniform regulator
removal is claimed.
