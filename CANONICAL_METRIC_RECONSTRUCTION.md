# A canonical nonlinear reconstruction of the tensor initial data

Date: 2026-09-11

The [two-packet energy](TENSOR_PACKET_SELF_GRAVITY.md) was computed on
a family with a conformally flat metric and freely varied TT momentum.
The gravitational canonical one-form vanishes on that whole family.
Its energy dependence on separation therefore does not, by itself,
give a dynamical force between canonical packet positions.

There is a classical extension with both tensor coordinates and
momenta. A logarithmic conformal metric, an elliptic momentum
correction, and a scalar constraint solve give nonlinear Einstein
initial data while preserving the TT canonical one-form exactly.
A small-field estimate below proves that the momentum correction
exists uniquely; a separate explicit contraction condition suffices
for the scalar solve.

This is a canonical reconstruction under supplied Einstein constraints,
not a derivation of those constraints or a microscopic phase. It
adapts the established York/conformal reduction rather than proposing
a new classical gravitational theory.

## 1. Why the momentum-only packet family has no dynamics of its own

Write kappa=16 pi G. At maximal slicing, tr_q K=0, the ADM momentum is

    pi^ij=sqrt(det q) K^ij/kappa.

For q=psi^4 delta and K_ij=psi^(-2) sigma_ij with delta-traceless
sigma, it follows that pi^ij=psi^(-4) sigma^ij/kappa. Hence

    Theta=integral pi^ij delta q_ij
         =(4/kappa) integral psi^(-1) tr_delta(sigma) delta psi
         =0.                                           (1)

Its exterior derivative is zero too, even when psi depends
nonlocally on every packet parameter. This is an isotropic
momentum-data submanifold of the larger gravitational phase space;
it does not imply that the packets have no gravitational curvature.
It explains why the previous note did not identify minus the
separation derivative of its energy with a force.

## 2. A local positive metric and its exact cotangent map

On R^3 choose smooth compactly supported symmetric tensors h,s
that are trace-free and divergence-free with respect to the flat
reference metric. They supply the two TT tensor coordinates and
their two momenta. A noncompact extension needs its own asymptotic
conditions and boundary terms; those are not silently assumed.

Set gamma=exp(h), so gamma is positive and det gamma=1. Its
pointwise differential on symmetric matrices is

    J_h(B)=d exp_h(B)
          =integral_0^1 exp(t h) B exp((1-t)h) dt.       (2)

This map is self-adjoint for the Frobenius pairing and positive.
In an eigenbasis of h its component multipliers are

    J_ab=(exp(lambda_a)-exp(lambda_b))/(lambda_a-lambda_b),
    J_aa=exp(lambda_a),

with the continuous value at repeated eigenvalues. All are
strictly positive. If ||h||_op<=H, both ||J_h|| and ||J_h^(-1)||
are at most exp(H), in the Frobenius operator norm.

For a flat-traceless momentum density p define

    t=J_h^(-1)(p).

Then t:delta gamma=p:delta h and gamma:t=tr p=0, since
J_h(I)=gamma. Density components are written in the fixed flat
coordinates; det gamma=1 makes its volume element d^3x.

For any positive conformal factor psi, define

    q=psi^4 gamma,
    pi=psi^(-4) t/kappa,
    K_ij=psi^(-2) gamma_ik gamma_jl t^kl.               (3)

These satisfy tr_q K=0. Direct contraction, without differentiating
the equation for psi, gives the exact identity

    integral pi:delta q
       =(1/kappa) integral t:delta gamma
       =(1/kappa) integral p:delta h.                  (4)

Thus the sourced scalar metric can be restored without adding a
physical scalar canonical pair or changing the shape one-form.
The remaining task is to make t covariantly transverse.

## 3. Solve the nonlinear momentum constraint in a canonical chart

Define the flat longitudinal operator

    (L_0 W)_ij=partial_i W_j+partial_j W_i
                              -(2/3)delta_ij partial_k W_k,
    p=s+L_0 W.                                         (5)

Because every allowed variation delta h is flat TT, integration
by parts gives integral (L_0 W):delta h=0. If W solves the
momentum constraint, (4) therefore becomes exactly

    Theta=(1/kappa) integral s:delta h.                 (6)

To prove that such W exists, first write the infinitesimal spatial
action in logarithmic coordinates. With A_i^j=partial_i v^j,

    F_h(v)=v^k partial_k h
             +J_h^(-1)(A gamma+gamma A^T)
             -(2/3)(partial_k v^k) I.                  (7)

The last term preserves det gamma=1. The corresponding action on
gamma is its spatial Lie derivative with the determinant rescaling
removed; it is the normalized conformal representative, not an
ordinary unit-determinant metric held fixed under arbitrary coordinate
changes. The trace-free t annihilates that rescaling in the pairing.

The momentum constraint is

    integral p:F_h(v)=0 for all compactly supported v.

Indeed this equals integral t:L_v gamma, whose integration by
parts is -2 integral v^i gamma_ij nabla_k t^jk. It is exactly
covariant transversality of t, not just flat transversality of p.
Let D_h=F_h^*. An explicit expression is

    (D_h p)_i=p:partial_i h-2 partial_j (t gamma)_ji.   (8)

At h=0, F_0=L_0 and D_0 p=-2 div p. For W the weak equation is

    integral F_h(v):L_0 W=-integral F_h(v):s.           (9)

It is linear in W for each fixed h, including all orders in h.

### An explicit sufficient smallness condition

Use the homogeneous Sobolev space dot H^1(R^3), the completion
of compactly supported vector fields in the gradient norm. It
excludes nondecaying translations and conformal Killing fields.
Let C_S be a Sobolev constant in ||v||_6<=C_S||grad v||_2.
Set H=||h||_op,infinity and

    k=[2(exp(2H)-1)+C_S ||grad h||_3]/sqrt(2).          (10)

If k<1, (9) has one unique solution in dot H^1, with

    ||L_0 W||_2 <= k ||s||_2/(1-k).                    (11)

Here is a direct proof. Spectral bounds on (2) imply

    ||J_h^(-1)(A gamma+gamma A^T)-(A+A^T)||_F
                       <=2(exp(2H)-1)||A||_F.

Together with Holder and Sobolev, this bounds
||(F_h-L_0)v||_2 by the numerator of (10) times ||grad v||_2.
The flat identity

    ||L_0 v||_2^2=2||grad v||_2^2+(2/3)||div v||_2^2

then gives ||(F_h-L_0)v||_2<=k||L_0 v||_2.
The bilinear form on the left of (9) is bounded and coercive:
its value at v=W is at least (1-k)||L_0 W||_2^2.
The right side has norm at most k||s||_2 because L_0^*s=0.
Lax--Milgram gives existence, uniqueness and (11).

For fixed smooth compact seed profiles scaled to zero, k tends
to zero. Elliptic regularity gives a smooth W; outside their
support it solves the flat vector elliptic equation and has the
decaying multipole behavior W=O(1/r), L_0 W=O(1/r^2).
No volume-dependent Fourier cutoff is used in this argument.

### The first correction is already nonzero

Expanding J_h^(-1)p=p-(hp+ph)/2+O(h^2 p), for flat TT h,s,

    (D_h s)_i=s:partial_i h+partial_j[s,h]_ij+O(h^2 s),
    [s,h]=s h-h s.                                     (12)

The leading longitudinal correction consequently solves

    [Delta W_i+(1/3)partial_i div W]
       =(1/2)[s:partial_i h+partial_j[s,h]_ij].         (13)

This is an inverse vector elliptic operator. Assigning t=s
independently of h would miss the nonlinear momentum constraint.
Equation (11) controls the full correction, not only (13).

## 4. Restore the scalar constraint with a separate bound

For the metric gamma and momentum t just constructed, let
S=gamma_ik gamma_jl t^ij t^kl>=0 and R_gamma be its scalar curvature.
The maximal vacuum scalar constraint for (3) is

    -8 Delta_gamma psi+R_gamma psi-S psi^(-7)=0,
    psi -> 1.                                         (14)

Let G_gamma=(-Delta_gamma)^(-1) with decaying boundary condition.
For the smooth uniformly positive gamma equal to delta outside a
compact set this inverse has a positive Green kernel. Define

    a=||G_gamma(S/8)||_infinity,
    b=||G_gamma(|R_gamma|/8)||_infinity.

A sufficient explicit condition, for some 0<r<1, is

    a(1-r)^(-7)+b(1+r)<=r,
    ell=7a(1-r)^(-8)+b<1.                              (15)

On ||u||_infinity<=r the map

    u -> G_gamma[(S/8)(1+u)^(-7)-(R_gamma/8)(1+u)]

is then invariant and contractive with constant ell.
Its fixed point gives positive psi=1+u and solves (14).
This is uniqueness in the specified ball, not a global theorem
for arbitrary conformal classes or large data.
For example a,b<=1/256 satisfy both conditions with r=1/4.

For a fixed pair of smooth compact TT profiles (h_0,s_0), set
h=epsilon h_0 and s=epsilon s_0. The linear scalar curvature
of h_0 vanishes, so R_gamma=O(epsilon^2) with compact support.
The momentum solve has L_0 W=O(epsilon^2), and t has an
O(epsilon^2/r^2) tail outside the seed region. Uniform elliptic
Green estimates near gamma=delta give a,b=O(epsilon^2).
Consequently (10) and (15) hold for sufficiently small epsilon.
This proves reconstruction near the flat initial data, without claiming
an explicit amplitude threshold for every chosen profile.

General conformal constraint solvability is established literature;
see [Pfeiffer--York](https://arxiv.org/abs/gr-qc/0207095) and
[Dilts](https://arxiv.org/abs/1507.01913). The relevant canonical
precedent is
[Isenberg--Marsden, "The York map is a canonical transformation"](https://doi.org/10.1016/0393-0440(84)90015-9).
The calculation here makes the logarithmic chart,
longitudinal correction and their bounds explicit for this program.

## 5. What has been repaired in the classical tensor benchmark

Equations (2)--(15) define constraint-satisfying asymptotically flat
initial data on an open small-data region of the specified TT
profile space. Their pulled-back symplectic form is exactly

    Omega=(1/kappa) integral delta s wedge delta h.     (16)

Both physical tensor canonical pairs survive. The map is a
symplectic embedding on this chart, not a proof that it covers
all gravitational data or all gauge orbits. The inverse elliptic
operators and the flat reference used for the TT chart are
explicit; no strictly local finite-spin encoding follows.
The map is injective: q determines psi=(det q)^(1/12),
gamma=q/(det q)^(1/3), and h=log gamma. Then
t=kappa psi^4 pi, p=J_h(t), and s=Pi_TT,flat p recover the input
momentum, since the TT projector removes L_0 W.

For h=0 this reduces to the conformal TT packet construction.
Allowing variations of h supplies the missing canonical partners
while retaining the same energy on the old momentum slice.
For gamma-delta of compact support, the ADM energy is

    E=(1/kappa) integral [S psi^(-7)-R_gamma psi].       (17)

This follows from (14), det gamma=1 and the asymptotic flux.
Its role as an ADM-time Hamiltonian uses the usual canonical
Einstein evolution and gauge-preserving lapse and shift.
Those equations have not been derived from microscopic clocks.

## 6. One exact check of the resulting initial metric velocity

At h=0, t=s and the flat conformal equation applies. Let w solve

    [-8 Delta+7 |s|^2 psi^(-8)] w=0,       w -> 1.

Green's identity gives, for TT momentum variations,

    delta E=(2/kappa) integral w psi^(-7) s:delta s,
    dot h=2 Pi_TT[w psi^(-7) s].                        (18)

The maximum principle gives 0<w<=1. The lapse N=w/psi solves
the maximal-slicing lapse equation

    Delta_q N=N |K|_q^2,       N -> 1.

The TT part of dot q=2N K+L_shift q, after removing its conformal
factor, is exactly the second line of (18). Thus the boundary
energy gradient and the canonical metric velocity agree on this
slice, including its nonlinear conformal dressing. This is an
initial-velocity identity, not a constructed finite-time flow or
a packet-center force law.
The TT projection can make this velocity noncompact, so the compact
seed class used in the existence proof is not claimed to be
invariant under evolution. Extending the phase space to suitable
asymptotic function spaces and proving a flow remains necessary.

## 7. Reproduction and remaining microscopic work

    OPENBLAS_NUM_THREADS=1 python3 -W error::RuntimeWarning scripts/canonical_metric_reconstruction_audit.py

The audit tests the pointwise cotangent lift and pulled-back
symplectic form, a spectral discretization of the nonlinear
momentum solve, its first correction and TT one-form, and the
boundary-energy gradient at conformal packet data.

The momentum benchmark is periodic and tests only that part of
the construction. Its even seed profiles have zero total
translation source, and its vector solves use mean-zero fields.
No maximal nontrivial vacuum scalar solution on a flat torus is
asserted. The analytical full reconstruction above is on R^3;
its nonconformal scalar solve is covered by (15), not by a
periodic numerical example. Discrete momentum constraints are
not an anomaly-free quantum deformation algebra.

All 30 numerical cases and the exact symbolic checks pass.
The pointwise symplectic finite difference error is below 3e-10;
the tested momentum constraints have root-mean-square residuals
below 2e-13. The energy-gradient check differs by less than
4e-11 in the chosen G=1 packet units. These are numerical
checks of the stated parts, not certified discretization bounds
for the full nonconformal R^3 reconstruction. No Lean source changes.

The classical reconstruction gap is repaired on the stated
small-data domain under supplied Einstein constraints. The
remaining task is to obtain this phase space, energy, constraint
action and physical identification from one controlled spin/clock
model. Its finite-spin phase, locality after refinement, universal
matter coupling, quantum Einstein dynamics and TOE remain unproved.
