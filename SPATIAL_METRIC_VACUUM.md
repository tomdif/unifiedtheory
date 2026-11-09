# Spatial metric covariance requires a compatible quantum representation

Date: 2026-09-11

The [onsite affine construction](AFFINE_SPIN_METRIC.md) supplies
positive metric variables and their local frame generators. It does
not settle how a spatial change of coordinates acts on a quantum
wave vacuum. This note tests that next step and finds a necessary
change to the proposed continuum construction.

Two tempting extensions fail under explicit hypotheses. A centered
lattice transport generator has a nonvanishing commutator defect
density on an independent Gaussian vacuum, even as it converges on
smooth fields. Replacing that vacuum with a free-wave Fock
representation does not generally solve the higher-dimensional
problem: one explicit smooth, volume-preserving shear cannot be
implemented by a unitary within that fixed representation.

A covariance transported with the geometry does transform
consistently. It supplies maps between the corresponding quantum
representations. It does not make the forbidden fixed-representation
unitary exist or supply a microscopic gravitational Hamiltonian.

These issues belong to established quantum field theory. In
particular, Torre and Varadarajan prove related non-implementability
results, including spatial diffeomorphisms, in
[Functional Evolution of Free Quantum Fields](https://arxiv.org/html/hep-th/9811222),
Section III and Appendix B. The present contribution is an explicit
shear lower bound and a diagnostic for the repository's metric
construction. It is not a new general no-go theorem for quantum gravity.

## 1. The metric already contains the transport test

For q=exp(h), let rho=log(det q)=tr h. The exact spatial metric
transformation is

    delta_v q = v^i partial_i q + A q+q A^T,
    A_ij = partial_i v^j

with the corresponding consistent matrix index convention.
Taking the logarithmic determinant removes the convention ambiguity:

    delta_v rho = v^i partial_i rho + 2 partial_i v^i.       (1)

Equivalently, a finite coordinate map chi gives

    rho'(x) = rho(chi(x)) + 2 log|det D chi(x)|.             (2)

The five shape coordinates do not enter this equation. In the
logarithmic affine vector field, they are also independent of an
additive identity component of h. Thus the trace transport is a
closed configuration channel of the proposed full metric.

The canonical lift transforms its momentum as the corresponding
density. A volume-preserving chi makes the inhomogeneous term in
(2) vanish, so rho and its momentum transform just like scalar
canonical data. This gives a necessary test if rho is assigned an
independent scalar Fock representation before gravitational
constraints are imposed. That assignment is a hypothesis being
tested, not a requirement on every quantization of gravity. In GR
the trace is not an independent physical gravitational wave.

## 2. Smooth-field convergence can miss a quantum transport defect

First consider a circle of length 2 pi, n sites and spacing a=2 pi/n.
Let d=(S-S^(-1))/(2a) be the centered difference, with
(S f)_i=f_(i+1). A direct discretization of (1) is the complete
affine configuration vector field

    F_v(rho) = A_v rho+b_v,
    A_v = diag(v) d,       b_v=2 d v.

Its exact finite-dimensional self-adjoint half-density generator is

    G_v = -i[(A_v rho+b_v).partial_rho+(1/2)tr A_v].         (3)

This statement concerns the oscillator configuration space before
the spin cutoff; its vector field is globally affine and complete.
The preceding spin encoding approximates such operators.

Choose v=1 and w=sin(x), and even give the proposed lattice algebra
its own discrete vector bracket z=d w. The constant part of the
commutator defect is then exactly zero. Define

    E = [d,diag(w)]d-diag(d w)d.                            (4)

The sign convention of the preceding affine note gives

    [G_1,G_w]-i G_z = i G_E,
    G_E = -i[(E rho).partial_rho+(1/2)tr E].                (5)

E measures the failed discrete product rule. For every fixed smooth
Fourier input it is O(a^2). On the n-dimensional configuration
space take the normalized product Gaussian whose probability
covariance is sigma^2 I. Acting on this state gives

    G_E psi = i[(rho^T E rho)/(2 sigma^2)-(1/2)tr E] psi,
    ||G_E psi||^2 = (1/2)||sym E||_F^2.                    (6)

Wick's identity proves the second equality. In particular, the
width sigma cancels, even if it depends on a.

For n>=5, direct evaluation of the five nonzero diagonals of
sym E gives the exact result

    ||G_E psi||^2/n
      = [sin(a/2)/a]^4 [3/8+(1/2)cos^2(a/2)]
      -> 7/128.                                         (7)

For clarity, the diagonal coefficients multiplying the appropriately
shifted sine are

    center:       sin^2(a/2)/a^2,
    distance one: -sin(a)sin(a/2)/(2a^2),
    distance two: sin^2(a/2)/(2a^2).

Summing their squares and averaging sin^2 gives (7).
The full commutator error grows as sqrt(n); even its error per
square root of the site count does not vanish. This is distinct
from convergence on a smooth classical configuration.

The state in (6) has zero mean residual, so subtracting a scalar
normal-ordering constant cannot remove its two-excitation component.
For the displayed nearest-neighbor generators, local oscillator
cutoff R>=2 already contains both orders of G_1 G_w acting on the
vacuum, including all output rows. Each factor raises local
occupation by at most one. Thus raising only the spin cutoff does
not repair this particular spatial vacuum defect.

On a product of this trace Gaussian and a shape state, the trace
two-excitation component is orthogonal to errors confined to the
shape factor. It cannot be cancelled merely by appending the five
independent shape channels. Entangled states and modified generators
are outside that product-state conclusion.

There is also a simple finite-algebra warning. Every derivation
of the pointwise function algebra on finitely many sites is zero:
each site idempotent e_i satisfies
d e_i=d(e_i^2)=2 e_i d e_i, forcing every component of d e_i to
vanish. An exact finite-site Leibniz rule with this unchanged
product is therefore not a possible repair. Broader lattice
locality/Leibniz obstructions are established by Kato, Sakamoto
and So in [Taming the Leibniz Rule on the Lattice](https://arxiv.org/abs/0803.3121).
This does not exclude a continuum limit, a changed product or a
different state domain.

## 3. A correlated wave vacuum helps in one dimension

Now change regulator and use continuum Fourier modes on a torus,
with a Fourier cutoff. This is a separate test of a correlated
wave vacuum, not a claim about the centered stencil of Section 2.
Use massless frequencies omega_k=|k| and the standard expansions

    phi(x) = V^(-1/2) sum_k
      [a_k exp(ik.x)+a_k^dagger exp(-ik.x)]/sqrt(2 omega_k),
    pi(x) = -i V^(-1/2) sum_k sqrt(omega_k/2)
      [a_k exp(ik.x)-a_k^dagger exp(-ik.x)].

Set the invariant homogeneous canonical pair aside when the
frequency is zero. It cannot determine ultraviolet convergence.
The quadratic part of the spatial generator is

    G[v] = (1/2) integral {pi,v.partial phi}.

Its vacuum pair norm, restricted to nonzero k,l in the cutoff, is

    ||G[v]|0>||_pair^2
      = (1/8) sum_(k,l)
         |v_hat(k+l).[
             k sqrt(omega_l/omega_k)
            +l sqrt(omega_k/omega_l)]|^2.                 (8)

This follows by symmetrizing the two creation coefficients and
using the bosonic two-particle inner product. The expression
counts both ordered pairs consistently. If (1) is used, its
additional term 2 integral div(v) pi creates one-particle states.
For a smooth, finite Fourier v this only adds finitely many
one-particle channels; it cannot cancel the pair norm.

In one dimension, opposite-sign momenta cancel exactly in (8):

    k sqrt(|l|/|k|)+l sqrt(|k|/|l|)=0,       k l<0.

For a finite Fourier v, the remaining same-sign pairs with
k+l fixed have bounded momenta. The pair norm stabilizes.
For v=cos(3x), the nonzero-mode contribution is exactly one
once the cutoff is at least three. This verifies a cancellation
that the spatial product Gaussian did not possess. It does
not by itself prove a complete one-dimensional gravitational
constraint algebra.

## 4. The same cancellation fails for a transverse spatial shear

In spatial dimension d>=2, use v=cos(y) partial_x. It is
divergence-free, so the trace-density shift in (1) is absent.
For one Fourier component p=e_y and l=p-k, the expression
inside the absolute value in (8) is

    (1/2) k_x (omega_l-omega_k)/sqrt(omega_k omega_l).

Along k=r n, r large, it tends to

    -(1/2) n_x n_y.                                      (9)

It is bounded away from zero on an open angular set.
Consequently, for large Fourier cubes of radius K,

    c K^d <= ||G[v]|0>||_pair^2 <= C K^d,                  (10)

with positive constants independent of K. For the lower bound,
restrict k to an interior radial shell and an angular cone where
|n_x n_y| has a positive lower bound; l remains in the cube,
and the number of such lattice points grows as K^d. For the
upper bound, |omega_l-omega_k|<=|p| and k_x/sqrt(omega_k
omega_l) is bounded outside finitely many low modes.

The cutoff generator therefore does not converge on the Fock
vacuum. This is a domain obstruction for this proposed generator
limit. On its own, divergence on one state would not exclude a
unitary group with that state outside its generator domain.
The next calculation addresses the finite transformation itself.

## 5. An explicit finite shear fails the unitary criterion

On T^3 take the smooth one-parameter family

    chi_tau(x,y,z) = (x+tau sin(y), y, z),                 (11)

with addition understood modulo 2 pi. It is a diffeomorphism for
every real tau, has determinant one, and composes by adding tau.
Let T_tau be scalar pullback by this map. It is unitary on spatial
L^2. The canonical data transform as

    phi -> T_tau phi,       pi -> T_tau pi.

This classical canonical transformation is bounded in the
one-particle Sobolev norm: smooth pullback and its inverse are
bounded on H^1 and L^2, hence on H^(1/2), and on H^(-1/2) by
duality. The constant mode is invariant and can be treated
separately.

Spatial L^2 unitarity is not the Fock implementability condition.
In the fixed massless Fock representation, the relevant
creation/annihilation mixing, after an irrelevant relabeling
k -> -k of the creation index, is

    beta_(l,-k) = (1/2)
      [sqrt(omega_l/omega_k)-sqrt(omega_k/omega_l)] T_(l,k).
                                                               (12)

The necessary and sufficient Hilbert-Schmidt criterion is
sum_(l,k)|beta_(l,k)|^2<infinity. See the primary discussion
and Shale reference in
[Torre and Varadarajan, Section III.2](https://arxiv.org/html/hep-th/9811222).

The Fourier transform of (11) is explicit:

    T_tau exp(i k.x)
      = exp(i k.x) exp(i tau k_x sin y),
    T_(l,k) = J_m(tau k_x),
    l=(k_x,k_y+m,k_z).

Restrict incoming momenta to k=(K,0,0), K positive. With
r_m=sqrt(1+(m/K)^2), the full outgoing column norm is

    sum_l |beta_(l,-k)|^2
      = sum_(m in Z) [(r_m-1)^2/(4r_m)] J_m(tau K)^2.     (13)

No outgoing projection is made in (13).

Here is an elementary uniform lower bound. Put z=tau K
and regard J_m(z)^2 as a probability distribution. Parseval
applied to f(y)=exp(i z sin y), f' and f'' gives

    sum_m J_m(z)^2 = 1,
    E[m^2] = z^2/2,
    E[m^4] = (3z^4+4z^2)/8.                              (14)

For the nonnegative random variable X=m^2, Cauchy-Schwarz
gives the Paley-Zygmund bound

    Pr(X >= E[X]/2)
      >= (E[X])^2/(4 E[X^2])
      = z^2/[2(3z^2+4)] >= 1/14,       |z|>=1.           (15)

On this event |m|>=|z|/2 and
r_m>=r_tau:=sqrt(1+tau^2/4). The positive function
(r-1)^2/(4r) increases for r>=1. Thus, for every
K>=ceil(1/|tau|),

    sum_l |beta_(l,-(K,0,0))|^2
      >= c_tau := (r_tau-1)^2/(56 r_tau) > 0
      whenever tau != 0.                                (16)

Summing just these incoming columns diverges. The finite
shear is therefore not unitarily implementable within the
fixed massless scalar Fock representation for any nonzero
tau. The same proof works on T^2 by dropping z, and in
higher dimensions by fixing the other momenta to zero.

This proof does not infer non-implementability from a divergent
infinitesimal generator; it tests the actual finite map.
It also does not assume that a unitary must leave the vacuum
unchanged. The Hilbert-Schmidt criterion already permits a
different normalizable squeezed vacuum when one exists.

Applied to the proposal, (16) excludes assigning the unrestricted
trace channel this fixed Fock representation and then requiring
all smooth spatial coordinate transformations to be unitaries
within it. It does not exclude a gauge-reduced physical Fock
sector, a different kinematic representation, geometry-dependent
sectors, or a finite physical cutoff.

## 6. Transport the covariance with the geometry

There is a precise compatible kinematic replacement. Label a
semiclassical scalar wave sector by a smooth background metric
qbar and, with an infrared mass mu>0 if needed, set

    Omega_qbar = sqrt(-Delta_qbar+mu^2),
    C_qbar = (1/2) Omega_qbar^(-1).                        (17)

The functions use L^2(dV_qbar). This is a chosen static
Gaussian reference sector, not a state derived from the spin
Hamiltonian. For a geometric fluctuation, its background
log-determinant must also transform; the fluctuation about
that background then transforms as a scalar.

For qbar'=chi^* qbar, scalar pullback T maps these spatial
L^2 spaces unitarily. Naturality of the scalar Laplacian gives

    Omega_qbar' = T Omega_qbar T^(-1),
    C_qbar' = T C_qbar T^(-1).                            (18)

For the volume-preserving shear, this is the ordinary
orthogonal conjugation used in the finite audit. In a finite
real basis, put C=(1/2)Omega^(-1) and P=(1/2)Omega.
Transporting both gives

    C' = T C T^T,       P'=T P T^T,       4 C' P'=I.

The Bogoliubov coefficient between the original and transported
frequency conventions is now exactly

    beta_carried = (1/2)[Omega'^(1/2) T Omega^(-1/2)
                        -Omega'^(-1/2) T Omega^(1/2)] = 0. (19)

The corresponding complex-linear one-particle map lifts to a
unitary between the associated Fock spaces. Composition is
consistent because pullbacks and the covariance transformations
compose. This transports the representation together with the
geometry. It is not a unitary implementing (11) within the
original fixed representation, and therefore does not contradict
(16).

For the two-dimensional part of (11), the pulled-back flat
metric is

    qbar' = [[1, tau cos y],
             [tau cos y, 1+tau^2 cos^2 y]],   det qbar'=1.

Its scalar Laplacian is

    Delta_qbar' = (1+tau^2 cos^2 y) partial_x^2
                 -2tau cos y partial_x partial_y
                 +tau sin y partial_x + partial_y^2.

The audit verifies Delta_qbar' T=T Delta_flat symbolically
on arbitrary Fourier waves. It also discretizes this metric
Laplacian independently and checks the intertwining on smooth
inputs. The exact finite carried cutoff T Omega^2 T^T is
dense; this construction is not a uniform local spin parent.

The metric here is a coordinate transform of a flat metric.
It has no newly generated intrinsic curvature or physical
gravitational degrees of freedom. The
[embedding diagnostic](EMBEDDING_VERSUS_GRAVITY.md) still
applies: covariance and consistent composition alone do not
produce gravity.

## 7. Consequence for the model and reproducible evidence

Keep the positive affine spin variables. Withdraw the shortcut
that an independent free-wave Fock representation for all six
unreduced metric channels can serve as the fixed Hilbert space
for every spatial coordinate transformation.

A compatible next architecture separates the kinematic metric
representation and constraint reduction from the resulting
physical wave sectors. A family of Gaussian sectors whose
covariances transform with their semiclassical geometries
satisfies the tested kinematic covariance requirement. Defining
the complete space of such sectors, its physical inner product,
the microscopic selection mechanism, and the constraint dynamics
is still required. This note does not construct them.

In particular, a phase should supply its own covariance and the
common state domain on which its spatial and clock constraints
act. Testing only the classical smooth-field bracket or the
one-site spin cutoff would miss the failure in (7) and (16).
This is an ultraviolet representation issue, not a refutation
of the infrared tensor pole already constructed.

Run:

    OPENBLAS_NUM_THREADS=1 python3 -W error::RuntimeWarning scripts/spatial_metric_vacuum_audit.py

[The audit](scripts/spatial_metric_vacuum_audit.py) writes
[the report](data/spatial_metric_vacuum_audit.json). It contains:

- Six lattice transport cases and the exact squared vacuum
  defect density 7/128.
- Eighteen Fourier-vacuum pair-norm cases in one, two and
  three spatial dimensions, with two independent real
  Gaussian/Wick checks.
- Eighteen finite-shear columns/cumulative sums with explicit
  positive lower bounds, Bessel normalization, moments and
  summation refinement.
- Nine metric-carried covariance cases, purity and composition
  checks, and an independently discretized metric Laplacian
  comparison on smooth inputs.

These are 51 numerical cases plus the independent checks and
exact symbolic identities. In the three-dimensional pair test,
the squared norm grows to about 1286.45 at Fourier cutoff 32.
The finite carried-covariance tests have relative beta norms
below 2e-13. The infinite-dimensional obstruction follows from
(14)-(16) and the stated implementability criterion, not from
extrapolating those finite numerical results.

The previous 218 frozen files are unchanged. No new Lean
theorem is claimed. A selected microscopic gravitational
phase, the quantum Einstein constraint algebra, physical
interactions and a complete TOE remain unproved.
