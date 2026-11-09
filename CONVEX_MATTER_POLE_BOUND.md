# Convex matter bounds tensor fluctuations but does not supply a metric

Date: 2026-09-11

The positive tapered quartic has an exact, nonperturbative bound on
connected quadratic fluctuations. At fixed proper cutoff, its local
derivative tensor channels have a bound independent of volume, coupling,
and matrix sizes, including at eight species. Consequently a massless
field with nonzero fixed pole residue cannot be identified with these
quadratic composites using bounded source normalization.

This closes a specific ambiguity in the proposed matter-to-gravity bridge.
An induced curvature coefficient for an external geometry is not a
propagating metric degree of freedom. The result does not exclude
nonlocal collective variables, derivative-suppressed overlap with a
massless gauge field, or a distinct dynamical geometry sector. It does
not complete Einstein gravity or the TOE, and is not a locality theorem.

## 1. The exact interacting measure

Use the real harmonic mode space on the supplied product geometry
S²(r1) × S²(r2), with ell_i < N_i and

    r_i = N_i/kappa,       P = N1² N2²,
    V = 16 pi² r1² r2²,    P/V = kappa⁴/(16 pi²).

The positive scalar Laplacian is Delta_N. Fix m0 > 0, kappa > 0,
an integer species count q >= 1, and g >= 0. On q real mode vectors set

    A = Delta_N + m0² I,       C = A^(-1),
    F = (I - Delta_1/kappa²)(I - Delta_2/kappa²),
    psi_a = F phi_a,
    S(phi) = (1/2) sum_a phi_a^T A phi_a
             + (g/(4q)) integral (sum_a psi_a(x)²)² dV,
    dmu = Z^(-1) exp(-S) product_a dphi_a.                 (1)

This is the revised interaction of
[the spectral-edge calculation](SPECTRAL_EDGE_LOCALITY.md).
Here F includes the isometric harmonic evaluation map when used as a
map to functions. Its mode eigenvalues lie in (0,1]. The free fermion
determinant on a fixed geometry is independent of phi and cancels from
this normalized scalar measure. The theorem below does not bound
fermionic observables or a joint measure over geometries.

For z in R^q and s = z^T z, the pointwise quartic obeys

    Hess_z [(g/(4q)) s²] = (g/q)(s I + 2 z z^T) >= 0.     (2)

Composition with a linear map and integration preserve convexity.
Thus S is even under phi -> -phi and

    Hess S >= I_q tensor A > 0.                           (3)

No perturbative expansion, Gaussian replacement, or large-q limit is
used in (3). The same argument applies to any even convex addition to
this positive quadratic action.

## 2. Every quadratic source is bounded by twice its free covariance

We use the Brascamp--Lieb variance inequality, Eq. (1.3) in
[Carlen, Cordero-Erausquin and Lieb](https://arxiv.org/pdf/1106.0709).
For the smooth strictly convex measure (1) it states

    Var_mu f <= E_mu [grad f^T (Hess S)^(-1) grad f]
             <= E_mu [grad f^T (I_q tensor C) grad f].    (4)

The polynomial observables below have finite moments; cutoff
approximation extends the inequality to them using the Gaussian tails.
Applied to linear f, (4) gives

    Cov_mu(phi) <= I_q tensor C.                          (5)

Evenness makes E_mu phi = 0. This matters when bounding uncentered
quadratic moments in the next step.

Let B be any real symmetric P-by-P matrix, of either sign, and define

    Q_B = (1/q) sum_a phi_a^T B phi_a.

Its a-th gradient is 2 B phi_a/q. Applying (4) and then (5),
using B C B >= 0, gives

    Var_mu Q_B
       <= (4/q²) sum_a E_mu [phi_a^T B C B phi_a]
       <= (4/q) Tr(C B C B).                              (6)

For the free measure with covariance C, Wick contraction gives

    Var_0 Q_B = (2/q) Tr(C B C B).                         (7)

For source matrices B_i, let chi_mu,ij = Cov_mu(Q_Bi,Q_Bj).
Applying (6) to every real linear combination of the B_i proves the
matrix inequality

    0 <= chi_mu <= 2 chi_0.                               (8)

This is a quadratic-form ordering, not an entrywise comparison.
The factor two is sufficient here; no optimality claim is needed.
The theorem is about the complete measure (1) at zero applied source.

## 3. Uniform normalization for local density sources

For a real source f(x), write B_f = F* M_f F, where M_f denotes
multiplication. With K = F C F*,

    Tr(C B_f C B_f) = Tr(M_f K M_f K)
                   <= ||K||_op Tr(M_f K M_f)
                   = ||K||_op integral f(x)² K(x,x) dV.   (9)

The inequality follows by applying K <= ||K|| I inside
the Hilbert--Schmidt norm. It holds for signed f.
Because F² <= I, ||K|| <= m0^(-2). Homogeneity gives

    K(x,x) = Tr(C F²)/V <= P/(V m0²).

Combining this with (6),

    Var_mu [(1/q) sum_a integral f psi_a² dV]
       <= kappa⁴/(4 pi² q m0⁴) ||f||_L2².                (10)

The bound is uniform in volume, sizes, and g at fixed positive mass and
proper cutoff. It is deliberately loose and does not estimate spatial
decay or derivatives with respect to momentum.

## 4. A mass-independent bound for derivative tensor sources

Use the three real infinitesimal rotation derivatives on each sphere,
scaled by its inverse radius. These six globally smooth vector fields
form a redundant frame for the four tangent directions. They obey

    sum_A D_A* D_A = Delta_N,       A = 1,...,6.

Six frame components are not six physical gravitational polarizations.
The rotation fields commute with the two Casimirs and with F. Define

    T_A = D_A F,       T = (T_A)_A,
    T* T = F² Delta_N.

For a real symmetric matrix field h_AB(x), set

    Q_h = (1/q) sum_a integral
          sum_AB (T_A phi_a) h_AB(x) (T_B phi_a) dV,
    B_h = T* M_h T,
    ||h||² = integral Tr[h(x)^T h(x)] dV.                 (11)

Intrinsic symmetric tensor sources can be represented in this frame;
the inequality also covers all ambient symmetric h and therefore any
specified tracefree or transverse subspace. No constraint algebra or
Lorentzian transverse-traceless decomposition is derived by using such
a subspace.

Let R = T C T*, a positive finite-rank operator on six-component
functions. Its nonzero eigenvalues are those of
C^(1/2) T* T C^(1/2), so

    ||R||_op = ||C F² Delta_N||_op <= 1.                  (12)

The fiber trace of its diagonal kernel is invariant under the
transitive product rotation group. Consequently

    tr R(x,x) = Tr(C F² Delta_N)/V <= P/V.                (13)

For any symmetric multiplication operator M_h,

    Tr(C B_h C B_h)
      = ||R^(1/2) M_h R^(1/2)||_HS²
      <= ||R||_op Tr(M_h R M_h)
      = ||R||_op integral tr[h(x) R(x,x) h(x)] dV
      <= (P/V) ||h||².                                  (14)

In the last step, the positive fiber matrix obeys
R(x,x) <= tr R(x,x) I. Equations (6) and (14) yield

    Var_mu Q_h <= B_T ||h||²,
    B_T = kappa⁴/(4 pi² q).                              (15)

This holds for every finite q and every g >= 0. It survives arbitrary
growth of the radii at fixed kappa. The constant has no m0 dependence,
although the proof and measure here assume m0 > 0. We do not infer a
massless-field construction at m0 = 0.

For an L2-orthonormal set of h_i, (15) is the matrix bound

    0 <= chi_mu <= B_T I.                                (16)

It remains true after projection onto a chosen source subspace.

## 5. What this says about a proposed composite graviton

For finitely many source channels define, near J = 0,

    W(J) = log E_mu exp(sum_i J_i Q_hi).

Then W''(0) = chi_mu. On independent channels with nonzero covariance,
the local Legendre transform with respect to these composite
expectation values satisfies, at their unforced mean,

    Gamma_comp'' = chi_mu^(-1) >= B_T^(-1) I.             (17)

Source directions whose observables vanish identically are removed
before taking this inverse. Equation (17) is not a statement about the
Legendre Hessian at arbitrary sources: a large quadratic tilt can
destroy the original convexity lower bound.

Suppose a sequence of normalized tensor source modes with p_N -> 0
is claimed to see a positive pole contribution Z_N/p_N². If the full
susceptibility is at least that contribution, (16) forces

    0 <= Z_N <= B_T p_N² -> 0.                            (18)

A positive residue approaching a nonzero constant is therefore
impossible in this identification. A decomposition into positive
physical spectral contributions requires additional reconstruction
assumptions; it is not established by this Euclidean calculation.
The conclusion also holds for a fixed positive leading 1/p²
asymptotic whose remaining terms stay bounded.

Uniformly bounded field redefinitions preserve the covariance bound
up to their squared operator norm. Inverse derivatives or
normalizations diverging with size are outside this argument.
For example, if a microscopic operator overlaps with a derivative of
a massless field, the derivatives can suppress its pole. A bound on
that operator does not rule out the field itself. Local curvature
observables need not share a metric potential's pole.

Thus this is a no-pole result for the specified quadratic matter
channels, not a theorem excluding all emergent gravity.

## 6. Three different objects in the gravity proposal

| Object | Meaning | What is established here |
| --- | --- | --- |
| Connected covariance of Q_h | Matter fluctuations in a fixed geometry | The exact bounds (8) and (15) |
| Second metric variation of the matter effective action | Response to a supplied external metric, including contact terms | Not equal to the connected covariance alone |
| Physical metric propagator | Inverse of the complete dynamical metric operator after constraints and gauge reduction | No such construction follows from (15) |

For a parameter h entering the microscopic action,

    d²[-log Z(h)]/dh²
       = E[S''(h)] - Var[S'(h)].                          (19)

Any h-dependent measure factor must first be included in that action.
Even for a Gaussian matrix A(h), this gives

    (1/2) Tr[C A''] - (1/2) Tr[C A' C A'].                (20)

The first term is the contact term; the second is the negative connected
quadratic response. The exact cancellation for isospectral metric
relabelings was checked in
[the microscopic metric Ward analysis](MICROSCOPIC_METRIC_WARD.md).
An external-metric derivative expansion can have an Einstein curvature
coefficient while all the covariances in (15) remain bounded.

The earlier [induced tensor calculation](INDUCED_TENSOR_DYNAMICS.md)
explicitly promoted strain to a collective field and tuned its
quadratic mass before finding conditional Gaussian poles. It did not
derive that promotion from the scalar measure. Equations (17)--(18)
show why it cannot be justified simply by identifying strain with the
present bounded quadratic order parameter.

Integrating over a new h with a specified action and measure changes
the microscopic model. Conditional convexity in phi at fixed h does
not imply a joint convexity bound on (phi,h): mixed derivatives and
the geometry action matter. This provides room for new dynamics but
does not supply it.

## 7. Model decision and remaining constructive target

Retain the tapered convex sector as a controlled matter benchmark.
Its induced homogeneous curvature coefficients and interaction bounds
remain useful. Increasing its positive quartic coupling cannot by
itself produce the proposed fixed-residue quadratic tensor pole.
The sign zero of a Gaussian external-metric curvature coefficient in
the preceding note is therefore not evidence of this composite
criticality.

The next construction must identify a genuine geometric variable and
its microscopic dynamics. A successful continuation needs to show:

1. Where that variable resides in the microscopic state space and how
   its dynamics or measure arise, rather than obtain a new degree of
   freedom by inverting a response to an external parameter.
2. Which mechanism escapes this bound if the variable is built from
   matter: a different observable, justified scaling, changed convexity,
   or an explicitly constructed additional sector.
3. Why the resulting geometry has the gravitational constraints and
   two physical tensor polarizations, a common matter cone, and universal
   coupling. A massless tensor pole alone would not establish these.

This sharpens the earlier
[Einstein model decision](EINSTEIN_MODEL_DECISION.md). It does not
invalidate every spin construction in the repository: finite spin
variables and their interacting phases are not the measure (1).
The broad principle is that a uniformly convex matter sector supplies
controlled response; identifying a critical geometric order parameter
requires a separate mechanism that overcomes the relevant response
bound.

Uniform susceptibility does not imply uniform momentum derivatives.
In particular, (15) does not bound chi(0)-chi(p) divided by p²,
and it does not close the fixed-eight-species shape dependence of the
nonlinear action remainder. Uniform physical locality, local geometry
refinement, arbitrary-metric dynamics, Lorentzian reconstruction,
Einstein constraints, Standard Model dynamics, and the TOE remain open.

## 8. Executable checks and their scope

Run:

    OPENBLAS_NUM_THREADS=1 python3 -W error::RuntimeWarning scripts/convex_matter_pole_bound_audit.py

[The audit](scripts/convex_matter_pole_bound_audit.py) records
[its report](data/convex_matter_pole_bound_audit.json), with:

- Symbolic quartic Hessian and exact low-mode interaction identities.
- Twelve product-sphere cases checking real rotation matrices, the
  filtered Casimir identity, kernel diagonal homogeneity, orthonormal
  constant and varying tensor sources, and the free-covariance upper
  bound used to control the complete interacting theory.
- Sixteen full radial quartic integrations at q = 8 and 32, including
  tracefree indefinite quadratic observables and composite Legendre
  Hessians. These are independent tests of the general theorem; the
  multimode radial quartic is not the pointwise sphere interaction.
- Four direct nonlinear integrations of the actual tapered model at
  q = 1 and (N1,N2) = (2,1). There is a constant mode a and a real
  three-vector b of ell = 1 coefficients. Exact angular integration
  gives

      integral psi⁴ dV = [a⁴ + (3/2)a²|b|² + (9/80)|b|⁴]/V.

  The four-dimensional integral reduces to two Gamma-weighted
  integrals. Orders 100 and 180 check numerical convergence of the
  connected density and tracefree covariances. This is a finite
  nonconstant-mode test, not a large-volume calculation.

The general result is the analytical argument (2)--(16); numerical
examples check identities, conventions, and normalization. Quadrature
is not interval-certified. No new Lean theorem is claimed.
