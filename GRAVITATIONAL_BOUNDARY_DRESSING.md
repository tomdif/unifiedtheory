# Boundary energy and the gravitational dressing missing from the spin model

Date: 2026-09-11

The nonlinear Einstein target requires more than the preceding free
wave cone. A localized gravitational excitation changes a long-range
metric field, and its total energy is recorded at spatial infinity.
This note constructs that tail for a smooth localized TT momentum
seed, with an explicit small-amplitude existence bound. A separate
finite-dimensional estimate quantifies why a strictly local spin
observable cannot remain a dynamical physical bulk observable when
the same physical Hamiltonian becomes a boundary operator.

**The model needs a derived gravitational dressing map.** Microscopic
spin locality can remain a hypothesis, but it cannot simply be
identified with exact locality of every physical gravitational
observable. The finite code example below demonstrates how the
distinction can arise through constraints. It is not a graviton phase.
The conformal construction uses supplied Einstein constraints and G;
it does not derive them, their evolution, or a TOE.

The relevant general restrictions are established results.
[Marolf](https://arxiv.org/pdf/1409.2509) treats boundary energy and
compatible microscopic and gravitational locality.
[Donnelly--Giddings](https://arxiv.org/pdf/1607.01025) prove a
perturbative gravitational dressing theorem for operators carrying
Poincare charges. Our additions are the explicit bounds and examples
for the repository's encoding and TT-state program.

## 1. The previously proved propagation bound is insufficient

[Local causal clocks](LOCAL_CAUSAL_CLOCK.md) have a uniform
Lieb--Robinson bound for their constraint's auxiliary flow. Their
conditional gate evolution has a separately supplied calibration.
The [joint spin Hamiltonian](PROJECTED_GEOMETRY_AND_LOCAL_DYNAMICS.md)
has a propagation bound for its actual microscopic evolution.
Neither result establishes a common ground state for H-v.P as v
varies. Neither identifies a gravitational boundary energy.

The [causal vacuum selection theorem](CAUSAL_VACUUM_SELECTION.md)
therefore remains conditional. Its local-field microcausality
interpretation is a free or suitable nongravitational limiting
statement. It must not be promoted to an assertion that all exact
diffeomorphism-invariant observables of interacting gravity commute
at spacelike separation. The dressing construction below explains
the difference without changing the free tensor dispersion.

## 2. A quantitative boundary-energy test on a physical subspace

Let P be an orthogonal projector onto a finite physical space,
Q=I-P, and H=H* preserve it: [H,P]=0. Let B=B* be a microscopic
boundary observable and O=O* a microscopic bulk observable with
disjoint supports, so [B,O]=0. Write H_P=PHP and O_P=POP,
as operators on the range of P, and set

    epsilon = ||(H-B)P||.                                (1)

Then

    ||[H_P,O_P]|| <= 2 epsilon ||O||.                    (2)

Indeed [H_P,O_P]=P[H,O]P=P[H-B,O]P. Hermiticity implies
||P(H-B)||=||(H-B)P||, which bounds both terms. Integrating
the commutator also gives

    ||exp(it H_P) O_P exp(-it H_P)-O_P||
          <= 2 |t| epsilon ||O||.                       (3)

Thus a boundary representation accurate on physical input states
forces these bulk observables to become static if epsilon -> 0.
For physical energy eigenvectors m,n, the stronger directly
observable consequence is

    |E_m-E_n| |<m|O|n>| <= 2 epsilon ||O||.              (4)

A small error in energy units must be compared with the frequency
and transition amplitude one is trying to retain. This is an
operator estimate, not a claim about the actual spin model's
unknown physical projector.

### Compression alone leaves an essential leakage term

Equality PHP=PBP is weaker than (H-B)P=0. Put
delta=||PHP-PBP||, b_leak=||QBP|| and o_leak=||QOP||.
Direct insertion of I=P+Q gives

    [PBP,POP]=POQBP-PBQOP,
    ||[H_P,O_P]|| <= 2 delta ||O_P||
                           +2 b_leak o_leak.             (5)

Compressed disjoint operators need not commute. One must not
discard the leakage terms merely because their supports were
disjoint before projection.

For an exact two-qubit example, use bulk first, boundary second,

    |0_L>=|00>,
    |1_L>=cos(theta)|10>+sin(theta)|01>,
    B=I tensor Z,           O=X tensor I.

Their compressions in this basis are

    B_P=diag(1,cos(2 theta)),       O_P=cos(theta) X,
    ||[B_P,O_P]||=2 sin(theta)^2 cos(theta),
    b_leak=2 sin(theta) cos(theta), o_leak=sin(theta),    (6)

for 0<=theta<=pi/2. Taking H=PBP+8Q makes delta=0, but
generically leaves epsilon=b_leak nonzero. This algebraic
example does not supply a local Hamiltonian for widely separated
qubits. It shows exactly which estimate an encoding must prove.

### A lower bound on the necessary dressing

Let A=A* preserve P and represent a physical excitation. Suppose
O is a bulk approximation commuting with B, and define

    eta=||(A-O)P||,         b=||BP||.

Using P[H,A]P=P[H-B,A]P+P[B,A-O]P gives

    |E_m-E_n| |<m|A|n>|
       <= 2 epsilon ||A||+2 b eta.                      (7)

An arbitrary common scalar shift of H and B can reduce b without
changing the transition energies or epsilon.

For epsilon=0, a nonzero fixed transition cannot have eta=0.
If a finite-spin boundary sum has b_R<=C R^(d-1), and an
encoding claims eta_R<=C' R^s exp(-R/xi), then its permitted
transition strength tends to zero as the boundary recedes.
The same conclusion holds for transitions falling only as a
power of R, after dividing (7) by that power and controlling
epsilon_R on the corresponding scale.

This excludes that combination of boundary representation and
uniformly exponential dressing for the specified bounded
operators. It does not exclude local microscopic spins with
a nonlocal map to physical space, changing boundary norms or
regulator scales, or a relational evolution different from H.
Unbounded continuum fields require separate domain estimates.

## 3. A local finite code illustrates the required distinction

Take N two-state occupation registers n_j=0,1 and N link registers
e_j=0,...,N. Set e_0=0. The diagonal, commuting local constraints

    C_j=e_j-e_(j-1)-n_j=0                               (8)

have exactly one link configuration per occupation string:
e_j=sum_(i<=j) n_i. Their common zero space has dimension 2^N.
A positive local Hamiltonian is

    H_code=Delta sum_j C_j^2 + omega e_N,
    Delta,omega>0.                                     (9)

It preserves the code, and on it the energy is the boundary
operator B=omega e_N=omega sum_j n_j. No approximation is
needed for the equality on code states.

Let S_l^+ increment e_l, annihilating its top state. The physical
creation operator at j is

    D_j=s_j^+ product_(l>=j) S_l^+.                      (10)

On a code state with n_j=0, none of these increments overflows.
Its adjoint also preserves the code. They act as logical raising
and lowering operators and satisfy [B,D_j]P=omega D_j P.
The bare local raising operator instead has P s_j^+ P=0.
The excitation must change every downstream link through the
boundary. A strictly local physical bulk observable cannot have
that energy-changing action.

This supplies a finite constructive example of the distinction
behind (2), using only local constraints and a boundary Hamiltonian.
It has no propagating tensor modes, gravitational metric, or
universal matter coupling. The link dimension N+1 grows; encoding
it uses growing numbers of spins, and a fixed-dimensional
thermodynamic realization is not asserted. The entire code band
is separated from violations if Delta>N omega, also a growing
parameter choice. Without that choice, exact invariance remains
true, but not separation of the entire code band.
The boundary-energy norm and constraint-penalty norms grow with
N; this example does not establish a uniform interaction bound.

## 4. A localized TT seed from the repository's prepotential map

Now consider the asymptotically flat continuum Einstein target in
three spatial dimensions, with zero cosmological constant and
c=1. Retain G explicitly. Lengths below use a fixed reference
unit. This is a different boundary condition from the earlier
[periodic backreaction test](NONLINEAR_TENSOR_BACKREACTION.md).

Apply the cubic Cotton operator of the
[prepotential construction](PREPOTENTIAL_LATTICE_BRIDGE.md) to
Z=diag(-1,-1,2) exp(-r^2/2). With the Fourier derivative convention
partial_j -> i k_j, this gives the following real tensor, up to
an irrelevant overall orientation sign:

    tau=exp(-r^2/2) *
      [[-3xyz,       3z(x^2-y^2)/2,  3y(rho^2-4)/2],
       [3z(x^2-y^2)/2, 3xyz,       -3x(rho^2-4)/2],
       [3y(rho^2-4)/2, -3x(rho^2-4)/2,          0]],
    rho^2=x^2+y^2,       r^2=rho^2+z^2.                 (11)

Exact differentiation verifies symmetry, trace zero and
partial_j tau_ij=0. It is smooth and rapidly decreasing, rather
than compactly supported. Its nonnegative squared norm is

    S=|tau|^2 =
      (9/2) rho^2 [(rho^2-4)^2+rho^2 z^2] exp(-r^2),
    integral S d^3x = 63 pi^(3/2)/2.                    (12)

Thus this is actual localized TT initial momentum data, not a
scalar positive source merely called a tensor.

## 5. A controlled nonlinear completion and its compulsory tail

Use the conformal ansatz

    q_ij=psi^4 delta_ij,
    K_ij=epsilon psi^(-2) tau_ij,       psi -> 1.         (13)

It has tr_q K=0, and conformal covariance of TT divergence
solves the momentum constraint. The vacuum scalar constraint
R(q)-|K|_q^2=0 reduces to

    Delta psi=-(epsilon^2/8) S psi^(-7).                (14)

This is the established conformal initial-data method; see
[Dilts](https://arxiv.org/abs/1507.01913) for the asymptotically
Euclidean constraint problem. Here a direct small-data proof
suffices and supplies explicit constants.

Define the positive Newton potential

    U(x)=(1/(32 pi)) integral S(y)/|x-y| d^3y.

The radial envelope S(x)<=(9/2)r^2(r^4+16)exp(-r^2)
and the spherical Newton formula imply

    0<=U(x)<=U_bar=99/16.                               (15)

Indeed a nonnegative radial source has its largest potential
at the center, where this envelope gives
(1/8) integral_0^infinity r (9/2)r^2(r^4+16)e^(-r^2) dr
=99/16.

Put gamma=epsilon^2 U_bar. On continuous functions 0<=u<=gamma,
the map

    T(u)(x)=(epsilon^2/(32 pi))
        integral S(y)(1+u(y))^(-7)/|x-y| d^3y            (16)

maps this interval into itself and has Lipschitz constant
at most 7 gamma in the uniform norm. Consequently

    7 gamma<1                                          (17)

gives a unique nonnegative fixed point there. It vanishes at
infinity, is smooth by elliptic regularity, and psi=1+u solves
the full vacuum initial-data constraints. The same potential
bound puts any nonnegative decaying solution in this interval.
Also

    ||u-epsilon^2 U||_infinity <= 7 gamma^2.             (18)

This follows from |(1+u)^(-7)-1|<=7u. It is a continuum
existence and error argument, not an inference from numerical
iteration.

The ADM energy is

    E_ADM=-(1/(2 pi G)) lim_(R->infinity)
                       integral_(S_R) partial_r psi dA
         =(epsilon^2/(16 pi G)) integral S psi^(-7)d^3x.
                                                               (19)

In particular, for nonzero epsilon,

    0 < E_bare (1+gamma)^(-7) <= E_ADM <= E_bare,
    E_bare=epsilon^2 (63 sqrt(pi))/(32 G).               (20)

The rapidly decreasing source gives

    psi=1+G E_ADM/(2r)+O(r^(-2)),
    q_ij=[1+2G E_ADM/r+O(r^(-2))] delta_ij.              (21)

The quadratic TT momentum therefore produces a metric tail
at arbitrarily large distances. At leading order its boundary
energy equals the canonical TT kinetic energy. Setting the
metric exactly flat outside the wave packet would violate the
integrated constraint.

At finite R, the conformal flux
-(1/(2 pi G)) integral_(S_R) partial_r psi equals the
source integral inside the sphere. The ADM metric surface
expression instead includes psi^3 partial_r psi; these agree
only in the R->infinity limit. The audit checks that distinction.

The elliptic constraint relates data on one slice. Comparing
two such initial data sets does not describe an instantaneous
signal or establish the causal behavior of their evolution.

This construction supplies smooth initial data, not a microscopic
preparation, a quantum dressing operator, or a derived time
evolution. G and the Einstein scalar constraint were inputs.
The boundary-energy argument is for the stated asymptotically
flat setting. Closed cosmology needs relational evolution and
the homogeneous balance already exhibited on the torus; an
ADM boundary cannot be inserted into it without changing the
problem.

## 6. Consequence for the proposed theory and next construction

The free causal selection result survives. The nonlinear extension
must additionally represent the constraint-required long-range
field of its excitations. A local tensor wave profile, a projector
onto linear gauge constraints, and an independently assigned
boundary energy are not sufficient without estimates such as
(1), (5) and (7).

The proposed model should therefore retain local microscopic
dynamics while requiring an explicitly constructed map to
gravitationally dressed physical observables. Exact locality of
all such observables is not an appropriate completion criterion.
Local curvature propagation in the free limit and controlled
approximate locality of relational measurements remain useful
targets. A nonlocal encoding is not automatically a defect, but
its constraints, energy action, preparation and physical
interpretation must be derived rather than assigned.

The immediate tensor target is an observable/state map whose
second-order response realizes (14) and whose energy is the
corresponding boundary flux on the physical sector, with
controlled cutoff and size errors. The finite prefix code shows
one algebraic mechanism for energy-changing strings, but lacks
the tensor dynamics needed to supply this target.

The microscopic phase, canonical limit, common cone and vacuum
stability, nonlinear constraint algebra, universal coupling,
Standard Model dynamics and TOE remain unproved.

## 7. Reproduction and scope of the audit

    OPENBLAS_NUM_THREADS=1 python3 -W error::RuntimeWarning scripts/gravitational_boundary_dressing_audit.py

The audit verifies the polynomial TT construction and its exact
Gaussian norm, finite operator bounds including leakage,
complete small prefix-code kernels and dressed transitions,
and the nonlinear conformal equation using an axisymmetric
Newton-potential discretization at three resolutions.

The numerical conformal solver truncates radius at 8 and uses
radial midpoint and angular Legendre quadrature. Its reported
fixed-point residual is a discrete residual. Resolution
comparisons are convergence evidence, not certified continuum
discretization error bars. Continuum existence and the mass
enclosure follow from (15)--(20). All 44 numerical cases and
the exact TT, source-norm and potential-bound identities pass.
No Lean source changes.
