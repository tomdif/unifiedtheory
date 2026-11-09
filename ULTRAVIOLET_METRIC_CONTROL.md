# Ultraviolet control of the exponential tensor metric

Date: 2026-09-11

The local [affine spin metric](AFFINE_SPIN_METRIC.md) controls bounded
functions of a positive metric. Einstein's spatial and clock algebra
also needs its inverse and derivatives. This note tests that missing
requirement on the proposed Gaussian tensor-wave continuation.

At fixed nonzero wave-to-metric normalization, the exponential of a
free three-dimensional TT field does not have a nondegenerate
pointwise metric limit as its ultraviolet cutoff is removed. Its
eigenvalue ratio diverges in probability. No scalar conformal factor
can change that ratio. Deterministic scalar normalization cannot keep
both metric and inverse-metric first moments bounded.

This is a result about a specified Gaussian ultraviolet ansatz in a
regular background frame. It is not a no-go theorem for quantum
gravity, renormalized composite operators, distributional geometry,
or non-Gaussian gravitational states. It explains why the earlier
fixed-regulator constructions cannot alone justify this continuum
metric. Two controlled alternatives are tested below: resolving the
metric at a finite length, and modifying its high-frequency spectrum.
The latter has an explicit cost in the ordinary clock algebra.

## 1. Use the physical tensor shape, rather than an independent trace

Let h_ij be a canonically normalized real, symmetric, transverse and
traceless free field on R^3. Use an isotropic Fourier cutoff |k|<=Lambda
and vacuum covariance

    <h_ij(x) h_kl(x)>=hbar integral_(|k|<=Lambda)
                  [d^3k/(2pi)^3] Pi_ij,kl(k)/(2 omega_k),
    P_ij=delta_ij-k_i k_j/|k|^2,
    Pi_ij,kl=(P_ik P_jl+P_il P_jk-P_ij P_kl)/2.       (1)

Pi has rank two. The ultraviolet estimates do not require an
independent scalar wave or discarding any nonzero tensor mode.
The homogeneous sector may be regulated separately.

Define the shape metric gamma_Lambda=exp(g h_Lambda), g>0. Here g
is the normalization between the canonical wave and the dimensionless
logarithmic metric. It is not the parameter named kappa=16piG in
[the classical reduced Hamiltonian](REDUCED_TENSOR_HAMILTONIAN.md).
That note uses q=psi^4 gamma. Its scalar conformal factor will not
alter the condition-number test below. No value of G is derived here.

At equal time the configuration fields commute, so their vacuum
matrix-exponential observables have an ordinary joint Gaussian
spectral measure. Matrix multiplication in the spatial tensor indices
is retained; exponentiating each entry separately would be incorrect.
This exponential parametrization is also studied in other gravity
programs, for example [Nink](https://arxiv.org/abs/1410.7816).

Put

    C_Lambda=hbar/(4pi^2) integral_0^Lambda k^2/omega_k dk.

Angular averaging gives

    average Pi=(2/5) I_STF,
    average Pi_11,11=4/15,
    Var(h_11)=(4/15) C_Lambda.                         (2)

The second identity follows directly from
Pi_11,11=(1-n_1^2)^2/2 and averaging n_1 uniformly on [-1,1].
For the first, the rotational average is scalar on the five-dimensional
traceless symmetric representation and has trace two. Equivalently,
the isotropic fourth-moment identity verifies every component.

For omega_k=c|k| these formulas become

    C_Lambda=hbar Lambda^2/(8pi^2 c),
    v_Lambda:=Var(h_11)=hbar Lambda^2/(30pi^2 c).       (3)

At one point h_Lambda has the exact law

    h_Lambda=sigma_Lambda sum_(a=1)^5 Z_a E_a,
    sigma_Lambda^2=(2/5)C_Lambda, Z_a independent N(0,1), (4)

where the E_a are Frobenius-orthonormal traceless symmetric matrices.
These statements concern the continuum spherical regulator. The
separate torus audit computes its discrete angular covariance directly.

## 2. A conformal factor cannot repair the diverging anisotropy

For a positive matrix, cond(gamma)=||gamma|| ||gamma^(-1)||. Since
the matrix exponential preserves eigenvectors,

    log cond(gamma_Lambda)
       =g[lambda_max(h_Lambda)-lambda_min(h_Lambda)].   (5)

For a traceless symmetric three-by-three matrix H, its eigenvalue
range is at least sqrt(3/2)||H||_F. To verify the coefficient, fix
the range d and zero sum. The sum of squared eigenvalues is at most
2d^2/3, attained when two eigenvalues coincide. Thus, for K>1,

    Pr(cond(gamma_Lambda)<=K)
       <=Pr(chi_5<=log(K)/(sqrt(3/2) g sigma_Lambda))
       ->0.                                           (6)

Here chi_5 is the Euclidean norm of five independent standard
Gaussians. This proves divergence in probability, not merely a
divergent expectation caused by rare states.

Any scalar factor a_Lambda(x)>0, including a field-dependent conformal
solution psi_Lambda^4, leaves cond(a_Lambda gamma_Lambda) unchanged.
A change of frame A obeys

    cond(A gamma A^T)>=cond(gamma)/cond(A)^2.           (7)

Consequently uniformly conditioned frame changes also cannot repair
(6). The frame is measured relative to the supplied regular background
chart. A singular cutoff-dependent coordinate description is outside
that regular-chart conclusion.

If both a positive metric and its inverse were tight as finite
matrices, their condition number would be tight. Equation (6) rules
this out under the displayed Gaussian assumptions. In particular,
solving only the scalar conformal constraint cannot provide a
nondegenerate pointwise limit for this tensor shape. This does not
assume the full interacting Einstein vacuum is Gaussian.

The bounded affine observable B=gamma(1+gamma)^(-1) does not exclude
this failure. Gaussian sign symmetry gives E[B]=I/2 at every cutoff.
Nevertheless its eigenvalues approach zero or one in the one-point
law as sigma_Lambda grows: B approaches a random spectral projection,
and tr[B(1-B)] tends to zero in mean. Reconstructing gamma=B(1-B)^(-1)
then reaches the singular endpoints. Controlled bounded observables
alone do not provide the missing inverse-metric bound.

## 3. Scalar normalization cannot bound both first moments

The spectral theorem and scalar Jensen inequality give, for any
unit vector e,

    e^T exp(+-g h)e >= exp(+-g e^T h e).

For e=e_1 the Gaussian moment formula therefore implies

    E[(gamma_Lambda)_11]>=exp(g^2 v_Lambda/2),
    E[(gamma_Lambda^(-1))_11]>=exp(g^2 v_Lambda/2).

For every deterministic scalar Z_Lambda>0, put q_Lambda=Z_Lambda gamma_Lambda.
Then

    E[(q_Lambda)_11] E[(q_Lambda^(-1))_11]
                              >=exp(g^2 v_Lambda).     (8)

The normalization cancels exactly in the product. No deterministic
scalar multiplicative renormalization bounds both first moments.
The statement does not extend that particular moment inequality to
arbitrary random conformal factors; (6) already handles their
pointwise condition number without a moment assumption.

There is also a useful distinction between a bounded mean and a
typical metric. On a fixed torus use the TT trigonometric field with
nonzero modes |k|<=K. It has component variances at most C K^2 and
Var(h_11)>=c K^2 for large K. The latter follows by retaining a cone
and shell of lattice momenta where Pi_11,11 is bounded below.

A trigonometric polynomial of degree at most K in each coordinate
satisfies ||partial_i f||_infinity<=K||f||_infinity. A grid of spacing
at most 1/(3K) consequently bounds its supremum by twice its grid
maximum. There are O(K^3) grid points. A union bound on their Gaussian
tails, with the six symmetric matrix entries, gives

    ||h_K||_(uniform,F)=O_P(K sqrt(log K)).             (9)

For sufficiently large constants the failure probabilities are
summable on dyadic K, so the same upper bound holds almost surely
eventually along that sequence. Spatial samples need not be independent.

If a deterministic scalar normalization has E[(Z_K exp(g h_K))_11]
bounded by a constant, Jensen forces Z_K<=C exp(-c g^2 K^2/2).
Equation (9) then gives

    ||Z_K exp(g h_K)||_uniform ->0 in probability,     (10)

and almost surely along the controlled dyadic sequence. Its inverse
cannot converge to a finite nondegenerate metric. A mean-one scalar
normalization is thus dominated by rare configurations, rather than
producing an ordinary positive metric. The finite numerical samples
below are used for quantiles, not to estimate those rare-event means.

This power-divergent free-wave field is not a log-correlated field.
Results constructing Gaussian multiplicative chaos for logarithmic
covariances, such as [Robert and Vargas](https://arxiv.org/abs/0807.1030),
do not supply a nontrivial limit for (10). Different renormalizations
or generalized random geometric objects require separate definitions.

## 4. Running the common amplitude to zero loses the fixed wave residue

Within the same Gaussian family, replacing g by g_Lambda can make
the pointwise condition number tight only if g_Lambda sigma_Lambda
stays bounded. For the free dispersion this requires

    g_Lambda Lambda=O(1), hence g_Lambda->0.            (11)

For any fixed nonzero Fourier momentum, the covariance of g_Lambda h
is proportional to g_Lambda^2 hbar/(2c|k|), which then vanishes.
Thus a single scale-independent field normalization cannot both
repair the local metric and retain a nonzero fixed-momentum tensor
residue in this ansatz. When that same residue is used to normalize
the gravitational coupling, (11) also removes that coupling. This
does not exclude a nontrivial renormalization-group flow with distinct
bare and physical quantities; it shows why that flow must be derived.

Multiplying a Hamiltonian by an overall slower energy scale does not
change its vacuum eigenvectors. The earlier spin and auxiliary clock
scale hierarchies alone therefore do not change (3)-(8).

## 5. A sufficient Gaussian spectral repair and its regularity

For a Gaussian TT field with the same canonical kinetic normalization,
local metric and inverse moments are uniformly controlled if

    integral^infinity k^2/omega(k) dk < infinity.       (12)

Indeed the five-component covariance is then uniformly bounded.
Writing the point field in independent Gaussian coordinates bounds
every E exp(t||h||_F), uniformly in cutoff. Since
||exp(+-g h)||<=exp(g||h||_F), this bounds every fixed positive moment
of the metric and its inverse. Convergence of the Gaussian field at
a point and uniform higher exponential moments give convergence of
these matrix observables in every finite L^p at that point.

If omega(k) grows as k^z, (12) holds precisely for z>3. At z=3 it
has a logarithmic divergence. This criterion is for a pointwise
exponential metric; it is not a universal condition on quantization
or renormalizability of gravity.

The following specific family keeps the low-momentum wave pole:

    omega_z(k)=c k sqrt[1+(k/M)^(2(z-1))], z>1.       (13)

For z>3,

    integral_0^infinity k^2/omega_z(k) dk
      =M^2/[2c(z-1)]
         B(1/(z-1),1/2-1/(z-1)),                     (14)

where B is Euler's beta function. At k<<M the relative frequency
change is at most (k/M)^(2(z-1))/2. Thus suppression of the ultraviolet
variance does not, by itself, require losing the low-frequency pole.
Both M and the changed spectrum are supplied model parameters.

There is a spatial, not just one-point, result on a fixed torus.
A dyadic Fourier shell of radius K has component variance
O(K^(3-z)). The same grid and Gaussian-tail argument as for (9)
bounds its uniform norm almost surely eventually by

    C K^((3-z)/2) sqrt(log K).

For z>3 these dyadic bounds are summable. The Fourier series converges
uniformly almost surely to a continuous matrix field. The limiting
exponential metric and inverse converge uniformly as well and are
bounded on that compact slice for each realization. Applying r spatial
derivatives gives the sufficient condition z>3+2r. Hence z=4 provides
a continuous positive metric, while z=8 provides two continuous
spatial derivatives by this estimate. This is not yet an Einstein
constraint solution or a quantum interacting phase.

This also controls intermediate spherical cutoffs: a shell has only
O(K^3) distinct partial sums, each with no larger variance and the
same bandwidth. Including them in the Gaussian union bound changes
only the constant multiplying sqrt(log K), so convergence is not
restricted to the dyadic endpoints.

The canonical momentum becomes rougher under this change. With the
same angular normalization its one-point variance is

    w_Lambda=Var(p_11)=hbar/(15pi^2)
                              integral_0^Lambda k^2 omega(k) dk.

For the free wave w_Lambda=hbar c Lambda^4/(60pi^2). For the z=4
repair it grows as hbar c Lambda^7/(105pi^2 M^3). Cauchy-Schwarz
also gives the regulator-dependent uncertainty bound

    Var(h_11) Var(p_11)>=hbar^2 Lambda^6/(2025pi^4).   (14a)

Subtracting the mean from p_11^2 leaves Gaussian variance
2 w_Lambda^2. Thus metric control alone does not remove the cutoff
from the quadratic momentum sources appearing in the earlier Einstein
response calculation. Composite source operators and their domains
still need a construction. This does not deny their possible meaning
as appropriately smeared or renormalized observables.

Anisotropic ultraviolet scaling is an established possible model
choice; [Horava's original proposal](https://arxiv.org/abs/0901.3775)
uses z=3. Its physical and renormalization claims are not assumed
here. Equation (12) asks a different, stronger question about this
pointwise Gaussian metric representation.

## 6. The simple smoother seed fails the ordinary clock test

For z=4 a local canonical scalar example on a circle has

    H[N]=(1/2) integral N[p^2+c^2(phi')^2
                                  +(c^2/M^6)(phi'''' )^2]. (15)

Its unweighted dispersion is exactly (13). This is a diagnostic for
the proposed ultraviolet mechanism, not the full TT Einstein system.
Let A[N]=-c^2 partial N partial+(c^2/M^6)partial^4 N partial^4.
The canonical bracket is integral p K[N,L] phi, where

    K[N,L]=L A[N]-N A[L].                              (16)

With N=1, L=exp(i l x), and phi=exp(i k x), its output coefficient is

    -c^2 k l+(c^2/M^6)[k^8-k^4(k+l)^4].               (17)

The ordinary constant-metric spatial action would give only
-c^2 k l. The second term depends on the field momentum k and has
higher powers of the lapse momentum l. At small l, the inferred
metric coefficient becomes c^2[1+4(k/M)^6], rather than one common
metric acting on all Fourier probes. The audit retains the complete
Fourier output when checking this term.

In this canonical scalar ansatz, merely changing the spatial
stiffness does not preserve the ordinary hypersurface-deformation
algebra. More general covariant higher-derivative theories can have
additional fields and momenta; (17) is not a no-go result for them.
For the proposed Gaussian repair, restoring the full gravitational
algebra in the infrared and controlling extra modes remain tasks.
Improved ultraviolet metric moments do not establish either one.

## 7. A finite-resolution metric is a distinct, controlled alternative

Keep the free dispersion but first smooth the logarithmic field:
h_ell=exp(ell^2 Delta/2)h on the supplied flat background, then define
gamma_ell=exp(g h_ell). At every fixed ell>0,

    Var((h_ell)_11)=hbar/(30pi^2 c ell^2)               (18)

after removal of the Fourier cutoff. All derivative variances are
finite. Gaussian shell estimates give a smooth field on compact sets,
with positive metric and inverse. The size of the metric fluctuations
is controlled by g sqrt(hbar/c)/ell. A weakly fluctuating metric
therefore needs resolution large compared with that supplied scale.
There is no claim here that this calibrates a physical Planck length.

Smoothing the logarithm and exponentiating is not equivalent to
smoothing the microscopic exponential metric. For example, let
h(x)=t cos(x) diag(1,-1,0). Its averaged logarithm is zero, whereas
the spatial average of exp(h) is diag(I_0(t),I_0(t),1), with I_0(t)>1
for t!=0. This difference is exact, not a discretization error.

The flat heat filter and logarithmic chart are specified. A fully
spatially covariant or relational definition of resolution must be
derived before gamma_ell can serve as the complete gravitational
observable. The earlier [geometry-carried covariance](SPATIAL_METRIC_VACUUM.md)
is relevant to that problem; it does not automatically supply this
nonlinear metric definition or its clock dynamics.

## 8. Consequence for the model and verification

The earlier affine construction remains valid at fixed encoded
sites and on its stated oscillator domains. The
[clock-mediated construction](CLOCK_MEDIATED_CONSTRAINTS.md) also
retains its exact finite-regulator kernel. Neither result establishes
the ultraviolet metric and inverse bounds now shown to fail for a
Gaussian TT field with free dispersion extended to arbitrarily short
distances at fixed g.

The model therefore cannot use that extension as its pointwise
continuum geometry. It must specify a resolved or renormalized
geometric observable, or derive ultraviolet state and spectral
behavior that changes the hypothesis. The fixed-resolution definition
and the z>3 Gaussian construction are controlled options, not selected
laws of nature. Their dynamics, Einstein refoliation symmetry,
nonzero physical G and a complete TOE remain unproved.

Run

    OPENBLAS_NUM_THREADS=1 python3 -W error::RuntimeWarning scripts/ultraviolet_metric_control_audit.py

Exact identities and 72 numerical cases pass. The report is
[data/ultraviolet_metric_control_audit.json](data/ultraviolet_metric_control_audit.json).
It checks exact angular and clock identities, Gaussian radial
covariances, full matrix eigenvalues and frame changes, TT Fourier
realizations, resolution dependence, and the higher-derivative clock
defect. Sample quantiles and numerical quadrature differences are not
interval certificates or estimates of the exponentially rare tails.
No new Lean theorem is claimed.
