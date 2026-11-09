# The reduced tensor Hamiltonian and its first gravitational interactions

Date: 2026-09-11

The [canonical reconstruction](CANONICAL_METRIC_RECONSTRUCTION.md)
can now be expanded into an explicit nonlinear Hamiltonian for
its surviving TT pairs. In the logarithmic chart, the quadratic
scalar constraint is sourced by the positive free-wave energy
density. The momentum-dependent cubic term cancels; a nonzero
cubic curvature interaction remains. At fourth order, the
longitudinal momentum correction, a logarithmic commutator term
and a Newton-kernel term all contribute with fixed coefficients.

These results use the supplied asymptotically flat Einstein
constraints and the preceding canonical map. They derive the
interaction target within that conditional construction, not
Einstein gravity from the microscopic spin Hamiltonian.

The motivation for reducing first is the
[spatial vacuum obstruction](SPATIAL_METRIC_VACUUM.md). A physical
TT wave sector need not implement every spatial gauge transformation
as a unitary on an unreduced fixed Fock space. Here the spatial
reduction preserves both tensor canonical pairs before any
prospective wave quantization. A complete quantum reduction,
physical inner product and microscopic phase remain unconstructed.

The general use of a reduced boundary Hamiltonian is established
ADM theory; see Arnowitt, Deser and Misner,
[The Dynamics of General Relativity](https://arxiv.org/abs/gr-qc/0405109).
The formulas below specialize it to the repository's logarithmic
canonical reconstruction.

## 1. Precise input and expansion

Let h,s be compactly supported, symmetric, flat-transverse
and traceless tensors on R^3, with at least C^5 regularity.
Smooth compact profiles are also allowed. Use kappa=16 pi G>0
and the prior map

    gamma=exp(h),             p=s+L_0 W,
    t=J_h^(-1)p,              q=psi^4 gamma,
    pi=psi^(-4)t/kappa,
    (L_0 W)_ij=partial_i W_j+partial_j W_i
                  -(2/3)delta_ij div W.

J_h is the Frechet derivative of the exponential. The nonlinear
momentum constraint determines W, and the maximal scalar
constraint is

    -8 Delta_gamma psi+R_gamma psi-S psi^(-7)=0,
    S=tr(gamma t gamma t),             psi -> 1.

The pulled-back one-form and ADM energy are exactly

    Theta=(1/kappa) integral s:delta h,
    E=(1/kappa) integral [S psi^(-7)-R_gamma psi].            (1)

The preceding small-data coercivity and contraction bounds apply.
For fixed seed profiles replace (h,s) by (epsilon h,epsilon s).
For clarity about differentiability, use weighted Holder spaces
C^(4,alpha)_delta for W and psi-1, with -1<delta<-1/2;
a j-th derivative is bounded by a constant times
(1+r)^(delta-j). Their equations take values in
C^(2,alpha)_(delta-2). At the flat zero data the two
linearizations are -2[Delta+(1/3)grad div] and -8 Delta.
The decaying Newton and vector Newton kernels give bounded
inverses at these weights, with derivatives controlled by local
elliptic estimates. In particular, the inverse kernel of
-[Delta+(1/3)grad div] is
(7 delta_ij+n_i n_j)/(32 pi r), where n=x/r.
The nonlinear maps are analytic near zero.
The implicit-function theorem therefore gives analytic dependence
on epsilon. This solution agrees with the prior unique small-data
solve. The choice delta<-1/2 also makes squared momentum tails
integrable, allowing differentiation of the energy integral.
The asymptotically decaying vector tails are retained.
In particular,

    W=epsilon^2 W_2+epsilon^3 W_3+...,
    psi=1+epsilon^2 u_2+epsilon^3 u_3+...,
    R_(exp(epsilon h))=epsilon^2 R_2+
                       epsilon^3 R_3+epsilon^4 R_4+....

The expansion of E through degree four has an O(epsilon^5)
remainder for each such fixed sufficiently regular profile pair.
The remainder constant depends on the profiles and the
small-data bounds; no universal amplitude threshold is asserted.

For a compact seed gamma=delta outside its support, integration
by parts in (1) has no seed boundary term. The noncompact tail
of W contributes to S and must not be dropped.

## 2. The quadratic scalar curvature is a negative gradient square

For a unit-determinant gamma, the contracted connection obeys
Gamma^k_(ki)=0. Define

    B=gamma^ij Gamma^k_(il) Gamma^l_(jk),
    V^k=gamma^ij Gamma^k_(ij).

Metric compatibility and the Ricci formula give the exact identity

    R_gamma=B+partial_k V^k.                               (2)

Write C=Gamma_1, where

    C^k_(ij)=(partial_i h_kj+partial_j h_ki-partial_k h_ij)/2.

The quadratic term of B is

    B_2=-(1/4)|partial h|^2
         +(1/2)(partial_l h_ik)(partial_k h_il).

Using flat transversality and tr h=0 in the exponential metric
expansion gives

    V_1=0,
    V_2^k=-(1/2)h_ij partial_i h_jk,
    partial_k V_2^k
      =-(1/2)(partial_k h_ij)(partial_i h_jk).

The two crossed derivative terms cancel after relabeling indices.
Thus the pointwise identity in this logarithmic TT chart is

    R_2=-(1/4)|partial h|^2.                               (3)

This is stronger than just an integrated gradient identity. It
determines the leading conformal source, including the gradient
energy of a metric wave.

## 3. Free-wave energy sources the leading metric tail

Set

    T=|s|^2,             V=(1/4)|partial h|^2,
    rho_2=(T+V)/kappa,   N=(-Delta)^(-1),
    (N f)(x)=(1/(4 pi)) integral f(y)/|x-y| dy.

At quadratic order the scalar constraint becomes

    -8 Delta u_2=T+V,
    u_2=(1/8)N(T+V)
       =(G/2) integral rho_2(y)/|x-y| dy.                  (4)

Both canonical parts of the tensor wave source the conformal
metric with the same coefficient. The quadratic energy is

    E_2=(1/kappa) integral (T+V)>0

for a nonzero compact seed. Outside the seed,

    u_2(x)=G E_2/(2|x|)+O(|x|^(-2)).

Consequently the leading exterior spatial metric contains
2 G E_2 delta_ij/|x|. The free tensor wave's canonical energy
and its leading asymptotic gravitational charge agree here.
G is still an input to (1).

Hamilton's equations from E_2 and Theta are

    dot h=2s,              dot s=(1/2)Delta h,
    ddot h=Delta h.

They preserve the TT conditions at linear order and retain two
polarizations. Their local energy balance is

    partial_t rho_2+partial_i j_i=0,
    j_i=-(1/kappa)s:partial_i h.

Here rho_2 is the canonical free-field density in the chosen
TT chart, not a gauge-invariant local gravitational stress
tensor. Its role does not contradict the boundary-dressing
requirements of the full theory.

The canonical normalization h=sqrt(2kappa) Q,
s=sqrt(kappa/2) P gives

    Theta=integral P:delta Q,
    E_2=(1/2) integral [|P|^2+|partial Q|^2].

This is the physical free-wave target. A pole or a vacuum with
this normalization alone would not establish its nonlinear
Hamiltonian or its microscopic origin.

## 4. Exact logarithmic kinetic factor and the cubic cancellation

Put m=gamma^(1/2) t gamma^(1/2). In an eigenbasis of h,

    m_ij=f(lambda_i-lambda_j) p_ij,
    f(z)=z/[2 sinh(z/2)],             f(0)=1,
    S=|m|^2.                                               (5)

Indeed J_h(t) is m multiplied entrywise by 1/f. The function
f is real and even. Its square expands as

    f(z)^2=1-z^2/12+z^4/240+....

Therefore

    S=|p|^2-(1/12)|[h,p]|_F^2+O(h^4 p^2).                (6)

The commutator is antisymmetric; the norm in (6) is its
positive Frobenius norm, not tr([h,p]^2).
For ||h||_op<=H, the exact useful bounds are

    [H/sinh(H)]^2 |p|^2 <= S <= |p|^2,

with continuous value one at H=0.

Flat transversality and the decaying W imply

    integral s:L_0 W=0,
    integral |p|^2=integral |s|^2+integral |L_0 W|^2.        (7)

Since W starts at degree two, (6)-(7) show that integral S
has no degree-three correction. Also psi-1 starts at degree
two, so neither scalar factor in (1) can supply a cubic
correction. The entire cubic Hamiltonian is consequently

    E_3=-(1/kappa) integral R_3.                            (8)

This is a cancellation in these canonical logarithmic variables.
It is not the absence of graviton self-interaction or a
coordinate-independent statement that every description lacks
a cubic momentum vertex.

## 5. Explicit cubic and quartic curvature vertices

For any symmetric matrix field X, define

    C(X)^k_(ij)
      =(partial_i X_kj+partial_j X_ki-partial_k X_ij)/2.

All indices in these coefficients are moved with delta. The
first three connection coefficients of gamma=exp(h) are

    G_1=C(h),
    G_2=(1/2)C(h^2)-h G_1,
    G_3=(1/6)C(h^3)-(1/2)h C(h^2)+(1/2)h^2 G_1.           (9)

Matrix multiplication in h G acts on the upper connection index.
For a symmetric matrix a, abbreviate

    B_a(X,Y)=a^ij X^k_(il) Y^l_(jk).

It is symmetric in X,Y. By (2), the integrated curvature
coefficients can be computed with first derivatives alone:

    integral R_3
      =integral [2 B_I(G_1,G_2)-B_h(G_1,G_1)],

    integral R_4
      =integral [2 B_I(G_1,G_3)+B_I(G_2,G_2)
                  -2 B_h(G_1,G_2)+(1/2)B_(h^2)(G_1,G_1)].
                                                               (10)

Exact polynomial integration proves that the compact example
below has a positive, nonzero cubic energy coefficient.
Quadrature refinement and the full exponential-metric curvature
integral reproduce it independently. The explicit formulas
specify the vertex without a fit to the nonlinear energy.

## 6. The complete fourth-order reduced energy

The leading momentum correction is the decaying solution of

    [Delta W_2+(1/3)grad div W_2]_i
      =(1/2)[s:partial_i h+partial_j[s,h]_ij].              (11)

Using (6)-(7), the degree-four integrated kinetic correction is

    integral [|L_0 W_2|^2-(1/12)|[h,s]|_F^2].

The term 2 integral s:L_0 W_3 vanishes exactly. Expanding the
remaining factors of (1) uses only u_2:

    S psi^(-7)=S-7 T u_2+O(degree five),
    R_gamma psi=R_gamma+R_2 u_2+O(degree five).

Together with (3)-(4), this yields

    kappa E_4 =
      integral [|L_0 W_2|^2-(1/12)|[h,s]|_F^2-R_4]
      -(1/8) integral (7T-V) N(T+V).                      (12)

Equations (8), (10)-(12), with E_2, give the reduced Hamiltonian
through fourth order. No nonlinear vector solve beyond W_2
and no scalar solve beyond u_2 is needed for these coefficients.
The full prior solves are still required for the untruncated
energy and its higher terms.

The Newton kernel in (12) is not just a freely tunable
pair potential added to a wave model. It is correlated with
the momentum correction and local curvature terms by the
supplied constraints. Nor is its coefficient alone the
physically calibrated two-body Newtonian energy: changing
the coordinate seeds can change the packets, as shown by
[the tensor-packet calculation](TENSOR_PACKET_SELF_GRAVITY.md).

## 7. A compact canonical pair with explicit interaction coefficients

For a reproducible nonzero example, take the Cotton TT tensor
tau generated by diag(-1,-1,2)(1-r^2)^10 inside the unit ball,
zero outside. Let eta be its symmetrized curl, normalized by
integral |eta|^2=1. It is still symmetric, traceless and
divergence-free; its boundary zero has order six.
The audit proves these polynomial identities and obtains

    (1/4) integral |partial eta|^2=105/4

exactly. Its exact cubic energy coefficient is

    c_3=172125 sqrt(33426748355)/(1051588951 sqrt(pi)) > 0.

Restrict the energy to h=a eta, s=b eta. Its
pulled-back one-form is b da/kappa, so a and b are canonical
amplitudes with the stated factor. This restriction supplies
energy coefficients and projected forces; it is not an
invariant single-mode subspace of full Einstein evolution.

Write F=|eta|^2, V_eta=|partial eta|^2/4. Since h and s
commute pointwise, (11) reduces to

    W_2=(3ab/16) grad Delta^(-1)F,
    L_0 W_2=(3ab/8)[partial_i partial_j Delta^(-1)
                                  -delta_ij/3]F.

The Fourier tensor n_i n_j-delta_ij/3 has squared norm 2/3,
so Parseval gives the exact whole-space identity

    integral |L_0 W_2|^2=(3a^2 b^2/32) integral F^2.        (13)

It includes the exterior momentum tail. Numerically the
resulting energy restriction is

    kappa E(a,b) =
      b^2 + 26.25 a^2
      +16.8837949274 a^3
      +25.8932880910 a^4
      -3.87153688481 a^2 b^2
      -0.201448575369 b^4
      +O((|a|+|b|)^5).                                   (14)

The underlying Newton integrals are approximately

    integral F N F       = 0.230226943279,
    integral F N V_eta   = 5.630442918251,
    integral V_eta N V_eta = 142.064976564.

Their calculation splits the radial Green integral at its
diagonal before quadrature. For axisymmetric Legendre
coefficients f_l,g_l, it uses

    integral f N g =
      4pi sum_l (2l+1)^(-2)
      integral_0^1 dr integral_0^1 dt r^4 t^(l+2)
        [f_l(r)g_l(rt)+g_l(r)f_l(rt)].                    (15)

All sources here are compact polynomials. Orders 36,44,52
agree on the printed coefficients; this is distinct from
the unsplit Green quadrature used for the nonlinear scalar
iteration. Floating-point agreement is not an interval
certificate for every printed digit.

The cubic term in (14) gives a quadratic contribution to
the force conjugate to a. Thus the extended family has both
a canonical partner and a nonzero nonlinear interaction,
which the earlier momentum-only energy family lacked.
The complete field vector field will generally excite other
TT profiles.

The Taylor polynomial is a small-amplitude expansion.
Its negative b^4 coefficient is not a globally stable
standalone Hamiltonian and is not a proof of a negative-energy
state in the full constrained theory.

## 8. Verification and the next microscopic requirement

Run:

    OPENBLAS_NUM_THREADS=1 python3 -W error::RuntimeWarning scripts/reduced_tensor_hamiltonian_audit.py

[The audit](scripts/reduced_tensor_hamiltonian_audit.py) writes
[the report](data/reduced_tensor_hamiltonian_audit.json).
Its 51 numerical cases cover distinct parts of the derivation:

- Twelve compact curvature evaluations compare the full
  exponential metric with the cubic and quartic coefficients.
- Six independent Ricci-jet evaluations verify the pointwise
  quadratic source. They use matrix-exponential Frechet
  derivatives and block exponentials for second derivatives.
- Twelve pointwise kinetic cases verify (5) and its spectral
  bounds.
- Nine periodic nonlinear momentum solves check the
  fourth-order kinetic term, keeping noncommuting h,s.
  Opposite h signs isolate the even correction.
- Three split-domain Newton quadratures determine (14).
- Nine full conformal scalar solves on h=0 check its b^4
  coefficient against the nonlinear ADM energy.

The periodic test covers the vector solve only; it does not
assert a nontrivial maximal vacuum scalar solution on a torus.
The nonconformal, asymptotically flat result is the analytical
small-data expansion of (1). The numerical checks of its
parts are not a full nonconformal evolution calculation.
No new Lean theorem is claimed.

The physical target has become more restrictive. A microscopic
spin/clock phase must reproduce the canonical wave normalization,
its sourced metric (4), and the coupled coefficients (8)-(12)
after a specified canonical identification. Choosing a positive
pole or transporting a covariance alone does not establish those
interactions.

The Einstein constraints and ADM-time interpretation remain
supplied. A spatially local microscopic parent, its selected
two-polarization phase, an invariant asymptotic phase space with
finite-time evolution, a quantum constraint representation and
the physical TOE remain unproved.
