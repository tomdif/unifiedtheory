# Positive spectral weight and a resolved metric with two-sided moment control

Date: 2026-09-11

**Lean update (2026-10-15).**
[`KFCausalPositiveMetric.lean`](UnifiedTheory/Audit/KFCausalPositiveMetric.lean)
now proves the finite-dimensional real symmetric matrix construction in
Section 5: strict positive definiteness, the ordinary matrix inverse,
`Q + Q^(-1) = 2 I + g^2 H^2`, and its exact trace identity. For any
probability measure, measurable metric and inverse traces have finite means
when the field has a finite second moment; their sum is exactly
`2 dim + g^2 E sum_ij H_ij^2`. Measurability is an explicit hypothesis of
the probability theorem. The finite-ensemble version is also checked.
These theorems do not yet formalize the unbounded operator extension,
the global smooth-bijection assertion, the L2-to-L1 continuity bound,
the spectral-pole argument, or the gravitational dynamics below.

The [ultraviolet metric test](ULTRAVIOLET_METRIC_CONTROL.md) used a
Gaussian tensor vacuum. Here part of its conclusion extends to
non-Gaussian states under an explicit positive-pole hypothesis. Other
positive spectral contributions cannot cancel the retained massless
pole's variance. For commuting configuration variables this gives a
non-Gaussian obstruction to bounding both moments of exp(g h) and its
inverse by deterministic scalar normalization.

There is also a constructive change. Spacetime resolution tied to a
supplied observer controls positive polynomially growing spectral
measures. A global asinh parametrization of positive metrics then
controls both metric and inverse moments using only second moments
of the resolved field. This avoids assuming exponential tails. It
does not derive the observer, Einstein dynamics, or a microscopic
interacting continuum. Its canonical and locality costs are explicit.

## 1. A positive pole alone supplies a variance lower bound

Use hbar=c=1 in this note. Suppose a positive Hilbert space contains
a vacuum and a nonzero massless helicity-two pole with residue Z>0.
For the displayed spatial TT coordinate field, assume its one-particle
matrix elements give the pole contribution

    <h_ij h_kl>_pole(k)=Z Pi_ij,kl(k)/(2|k|)          (1)

on the full boosted mass shell, with the TT projector and normalization
of the preceding note. Equation (1) is a hypothesis about the chosen
field and its residue, not a deduction from its infrared dispersion
alone. A momentum-dependent detector response is not included in Z.

For any regulated smeared component, insertion of the orthogonal
one-particle projection P_1 gives

    ||(h(f)-<h(f)>)|0>||^2
       >=||P_1 h(f)|0>||^2.                           (2)

All additional states contribute nonnegative squared norms. Applying
(2) to a sharp spatial cutoff, whenever the regulated field is defined,
and using average Pi_11,11=4/15, yields

    Var((h_Lambda)_11)>=Z Lambda^2/(30pi^2).           (3)

An additional regulator for the interacting spectral continuum may
be necessary even at finite spatial cutoff. If that continuum already
has infinite variance, it does not improve the bound. No assumption
of Gaussian higher correlations is used in (2)-(3).

The scalar version is the familiar positive spectral representation

    D_E(x)=integral_0^infinity d rho(s)/(x+s),
    d rho(s)=Z delta_0+ d rho_cont(s), d rho_cont>=0,  (4)

with x a positive Euclidean momentum squared. Spectral methods go
back to [Lehmann's original paper](https://users.physik.fu-berlin.de/~kamecke/ps/Lehmann.pdf).
For an unsubtracted representation (4),

    D_E(x)>=Z/x,       d[x D_E(x)]/dx>=0.              (5)

The second inequality follows by differentiating x/(x+s). The
one-particle norm bound (2) does not depend on a choice of Euclidean
contact terms or on using (4) for the whole tensor potential.

Gauge qualifications matter. A gauge-fixed metric potential need not
be a local Lorentz tensor on a positive physical Hilbert space, and a
TT projection is spatially nonlocal. Nor is a nonzero exact pole
residue automatically assured in an infrared-dressed interacting
theory. We use (1) only when it is supplied for the intended observable.
This is not a proof against all ultraviolet completions of gravity.
The distinction between background and fluctuation graviton spectral
functions is also explicit in
[Bonanno, Denz, Pawlowski and Reichert](https://arxiv.org/abs/2102.02217).

## 2. A distribution-independent exponential moment inequality

Let X be any real random variable with finite variance. With X' an
independent copy, monotone integration of positive functions gives

    E[e^X] E[e^(-X)]
      =E[cosh(X-X')]
      >=cosh(sqrt(2 Var X))
      >=1+Var X.                                      (6)

The first inequality is Jensen's inequality for the convex function
u -> cosh(sqrt(u)) on u>=0. Its power series has nonnegative
coefficients, and every second derivative term is nonnegative.
The assertion also holds when an exponential moment is infinite.

Now assume the equal-time regulated configuration matrices have a
joint classical spectral measure, as commuting canonical coordinates
do. The finite-dimensional matrix Jensen inequality implies

    e_1^T exp(+-g h)e_1>=exp(+-g h_11).

For q_Lambda=a_Lambda exp(g h_Lambda), with a_Lambda>0 deterministic,
(3) and (6) give

    E[(q_Lambda)_11] E[(q_Lambda^(-1))_11]
      >=cosh(g sqrt(2 Var((h_Lambda)_11)))
      >=cosh[g sqrt(Z) Lambda/(sqrt(15) pi)].          (7)

This extends the failure of simultaneous first-moment bounds beyond
Gaussian states, under the specified configuration and pole hypotheses.
It does not extend the previous stronger Gaussian condition-number
or uniform-collapse statements without additional distribution control.

For example, X_n=0 with probability 1-1/n^2 and X_n=+-n^2 with
probability 1/(2n^2) each has Var X_n=n^2 but converges in probability
to zero. Its exponentials converge in probability to one while their
means diverge. This is a probability counterexample to an invalid
inference, not a construction of a Lorentzian quantum field theory.

Even finite moments of every polynomial are not enough to define an
exponential metric mean. If Y is a standard Gaussian and X=Y^3,
then Var X=15 and all polynomial moments exist, but E exp(g X) is
infinite for every nonzero real g. On [L,L+1], for g>0, its defining
integral is at least

    (2pi)^(-1/2) exp[g L^3-(L+1)^2/2],

which tends to infinity. Thus removing the variance divergence by
smearing does not by itself prove exponential integrability in a
non-Gaussian interacting state.

## 3. Invariant propagator damping is not observer resolution

A scalar linear filter F(p^2) acts on the massless pole by F(0).
Preserving that pole leaves its arbitrarily boosted spatial momenta
unsuppressed. Such a filter does not implement finite spatial
resolution for the pole. Requiring F(0)=0 instead removes it.

The frequently considered Euclidean function exp(-ell^2 x)/x has
xD_E(x)=exp(-ell^2 x), decreasing to zero. It therefore cannot be
the unsubtracted positive spectral covariance (4) with a retained
nonzero massless pole. This can be checked without extrapolating its
large-momentum behavior. At a fixed nonzero spatial momentum k, its
Euclidean time covariance for t>=0 is

    C_(ell,k)(t)=1/(4k) [
      exp(-kt) erfc(k ell-t/(2ell))
      +exp(kt) erfc(k ell+t/(2ell))].                 (8)

It follows either by Fourier integration or from the heat integral
integral_(ell^2)^infinity ds exp(-s k^2-t^2/(4s))/sqrt(4pi s).
The two-by-two reflected Gram matrix C(t_i+t_j), t_i>0, has a
negative eigenvalue in the explicit tests. For example ell=1,
k=0.7, (t_1,t_2)=(0.1,0.3) gives about -0.00115674.

Similarly, 1/x-1/(x+M^2) damps the ultraviolet through a negative
massive spectral contribution. Its reflected Gram determinant is

    -ab(v_1 w_2-v_2 w_1)^2<0,

where a,b>0 and v,w are the unequal-mass exponential time vectors.
Changing the minus to a plus restores positivity and loses this
cancellation. The audit includes that positive control.

These claims test the stated Euclidean functions as ordinary field
covariances. Some nonlocal theories distinguish their diagrammatic
propagator from the positive time-ordered field correlation; see
[Briscese, Calcagni, Modesto and Nardelli](https://link.springer.com/article/10.1007/JHEP08(2024)204).
No conclusion about every such theory or its scattering unitarity
follows from (8). The on-shell norm statement (2) remains the relevant
test for whichever physical field is proposed as the metric seed.

## 4. A Lorentz-covariant family of resolved linear observables

Supply a future unit timelike observer u, proper spatial resolution
ell>0 and proper sampling duration tau>0. With signature (+---), use
the real Gaussian spacetime test function whose Fourier transform is

    f_tilde_(ell,tau,u)(p)
      =exp[-tau^2(p.u)^2/2
            -ell^2((p.u)^2-p^2)/2].                  (9)

In the observer's rest frame this is exp[-(tau^2 E^2+ell^2 k^2)/2].
Under a simultaneous Lorentz transformation of p and u, (9) is
unchanged. This is a covariant family of measurements. It does not
select a preferred observer or alter the underlying dispersion.
The observer and its resolution have not been derived from the
microscopic partial order.

For a scalar positive spectral measure define a=ell^2+tau^2. The
variance of the resolved field is

    V=1/(4pi^2) integral d rho(s) exp(-tau^2 s)
                    integral_0^infinity
                      k^2 exp(-a k^2)/sqrt(k^2+s) dk.

Since k^2/sqrt(k^2+s)<=k,

    Z/(8pi^2 a)<=V
       <=[integral exp(-tau^2 s)d rho(s)]/(8pi^2 a).   (10)

The upper bound is finite for a positive spectral measure of at most
polynomial growth. Sampling over time is important: a spatial filter
alone need not control large invariant masses in an interacting
continuum. For a tensor channel the relevant positive matrix spectral
measure must be used. Its massless TT component gives the lower bound
Z/(30pi^2 a) in the observer frame, with the preceding angular factor.

For the positive scalar example d rho=Z delta_0+lambda s^p ds,
integer p>=0, the continuum contribution can be computed as

    lambda Gamma(p+1)/(8pi^2)
       integral_0^infinity du
       (a+u^2)^(-3/2)(tau^2+u^2)^(-p-1).             (11)

The Laplace representation of 1/sqrt(k^2+s) proves (11). This gives
explicit tests beyond a finite list of spectral poles.

Gaussian profiles are not compactly supported observables. For a
local free massless scalar, two identical measurements (9) have

    i[phi_f(t,r),phi_f(0,0)]
      =[exp(-(r-t)^2/(4a))-exp(-(r+t)^2/(4a))]
                                  /(8pi^(3/2) r sqrt(a)). (12)

It is exponentially small but nonzero for r>t>0. This is the overlap
of the noncompact measurement profiles, not acausal propagation of
the unsmeared field. It prevents treating (9) as a new strictly local
fundamental field. Compactly supported smooth measurements can instead
be used when disjoint causal supports are required. Equation (12) is
a scalar control, not a microcausality claim for a TT-projected
gravitational potential, which is already spatially nonlocal.

## 5. A global metric chart requiring only second moments

Let H be a resolved real symmetric configuration matrix. More generally
let it be a self-adjoint operator on C^3 tensor a quantum Hilbert
space, with the domains needed for the following functional calculus.
Define

    X=gH/2,
    Q(H)=[sqrt(I+X^2)+X]^2
        =exp[2 asinh(gH/2)].                          (13)

It is positive and has positive inverse

    Q(H)^(-1)=[sqrt(I+X^2)-X]^2.

For an unbounded H, positivity is a strict quadratic-form statement;
there is no uniform lower spectral bound. Crucially,

    Q(H)+Q(H)^(-1)=2I+g^2 H^2.                        (14)

Consequently, in every vector in the domain of H, the sum of the
metric and inverse quadratic-form expectations is exactly controlled
by its second moment. For a classical random three-by-three matrix,

    E tr[Q+Q^(-1)]=6+g^2 E||H||_F^2.                 (15)

No Gaussian assumption or exponential moment is needed. The example
H=Y^3 has infinite exponential moments but finite Q and inverse means:
in one dimension their sum is exactly 2+15g^2.

The map (13) is a global smooth bijection Sym(3)->SPD(3). Its inverse is

    H=[Q^(1/2)-Q^(-1/2)]/g.                           (16)

Unlike a bounded-range clipping, it covers every positive metric.
It respects orthogonal changes of spatial frame by matrix functional
calculus. The operator version also respects unitary conjugation,
but positivity of an operator-valued matrix alone does not imply
that its individual metric entries commute or have an Einstein
constraint algebra.

There is a useful regulator convergence estimate for commuting
configuration matrices. Put A(H)=sqrt(I+(gH/2)^2)+gH/2. The scalar
derivative of sqrt(1+x^2) is bounded by one. Divided differences give
the same derivative bound in the finite matrix Frobenius norm, so

    ||A(H)-A(K)||_F<=g||H-K||_F,
    ||A(H)||<=1+g||H||_F.

Cauchy-Schwarz then proves

    E||Q(H)-Q(K)||_F
      <=g||H-K||_(L2,F)
           [2+g(||H||_(L2,F)+||K||_(L2,F))],           (17)

with the same bound for Q^(-1). Thus L^2 convergence of the resolved
field implies L^1 convergence of both metric and inverse. Higher
polynomial moments control their higher moments. This is a concrete
resolved-observable theorem; proving the required field convergence
from the interacting spin model remains necessary.

If a unit-determinant shape is required for commuting configuration
matrices, Gamma=Q/(det Q)^(1/3) is positive. Both its norm and inverse
norm are at most ||Q|| ||Q^(-1)||<=(2+g^2||H||_F^2)^2. Uniform fourth
moments then suffice for the corresponding first-moment bounds.
This determinant construction is not asserted for noncommuting
operator entries. It also does not impose spatial transversality.

## 6. Changing the chart does not supply a new gravitational law

Near H=0,

    Q=I+gH+(g^2/2)H^2+(g^3/8)H^3+O(g^5),
    h_log:=log Q=2 asinh(gH/2)=gH-g^3 H^3/24+O(g^5). (18)

It agrees with the exponential chart through quadratic order but
differs at cubic order. The change cannot be inserted into the
previous quartic Hamiltonian without transforming that Hamiltonian
and its momenta.

For the full six-coordinate metric, let J_H=D_H h_log. In the
eigenbasis of H, J_H multiplies each variation by a positive divided
difference of 2asinh(gx/2), so it is invertible. The exact cotangent
map is

    P_H=J_H^* p_log,
    p_log=(J_H^*)^(-1)P_H.                            (19)

It preserves tr(p_log delta h_log)=tr(P_H delta H). The audit checks
the full twelve-dimensional symplectic Jacobian. To retain the
conditional Einstein dynamics from
[the canonical reconstruction](CANONICAL_METRIC_RECONSTRUCTION.md)
and [reduced tensor Hamiltonian](REDUCED_TENSOR_HAMILTONIAN.md), their
complete constraints and Hamiltonian must be pulled back by (19).

In one dimension, p_log=sqrt(1+g^2 H^2/4)P_H/g. Even a free old
kinetic energy becomes (1+g^2H^2/4)P_H^2/(2g^2) classically. Quantum
transport with the half-density coordinate change gives the momentum
operator (a P_H+P_H a)/2, a=sqrt(1+g^2H^2/4)/g, including its ordering.
Keeping a bare P_H^2 instead changes the theory. A unitarily transported
free theory still has its free spectrum.

Likewise, this is not a coordinate cure for the preceding unsmeared
Gaussian vacuum. If h_log has Gaussian variance v, (16) gives

    E H^2=2[exp(v/2)-1]/g^2

in one dimension, and (14) reproduces the original diverging metric
moments. The improvement requires an actually controlled resolved H
and a specified state, not merely renaming the old random variable.

The chart acts on all six local metric coordinates. Applying it to
linearly TT H does not make h_log transverse and traceless at nonlinear
order. A scalar determinant normalization fixes neither the full
gauge condition nor its canonical reduction. The earlier linear TT
space and its nonlinear Einstein embedding must still be treated
together. The chart alone fixes no gravitational coupling.

## 7. What the model can now claim

A positive massless pole forbids cancelling its variance by adding
positive spectral states. Under the stated coordinate assumptions,
the exponential metric's simultaneous moment obstruction survives
beyond Gaussian vacua. Its stronger probability conclusions do not
follow just from that variance bound.

The current candidate geometry observable can instead use a resolved
field in the asinh chart, with observer-covariant spacetime sampling.
The resulting metric and inverse have the exact moment identity (14)
and convergence criterion (17). The observer, resolutions, field
definition and metric identification remain explicit inputs.

Lorentz covariance of this family on a supplied flat background is
weaker than gravitational diffeomorphism invariance or independence
of slicing. A relational observer construction, its backreaction,
the interacting microscopic field limit, local physical observables,
Einstein's clock algebra and physical G remain unproved. None of
these observable constructions completes the TOE.

Run

    OPENBLAS_NUM_THREADS=1 python3 -W error::RuntimeWarning scripts/positive_spectral_metric_audit.py

Exact identities and 77 numerical cases pass. The report is
[data/positive_spectral_metric_audit.json](data/positive_spectral_metric_audit.json).
It checks non-Gaussian moments and their counterexamples, positive
spectral channels, explicit reflection-positivity failures, observer
boost covariance, a polynomial spectral continuum, measurement
commutators, the global metric chart and its canonical pullback.
Finite numerical checks support the scoped analytical arguments;
they do not certify an interacting field theory or formal Lean proof.
