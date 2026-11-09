# A deformation algebra can describe slicing without gravity

Date: 2026-09-11

The next step after [quantum energy dressing](QUANTUM_ENERGY_DRESSING.md)
was to construct metric-dependent normal and spatial deformations.
There is a precise false positive for that test. Four embedding
coordinates in fixed flat spacetime have the required classical
hypersurface-deformation algebra, including the correct spatial action
on their induced metric. They have no local gravitational degrees of
freedom. Their induced initial data even satisfy the vacuum Einstein
constraints, while their spacetime Weyl curvature vanishes.

This note constructs that counterexample and a test that rejects it.
It rules out deriving gravitational waves by identifying the metric
solely with the geometry of clock slices in a fixed four-dimensional
flat spacetime. It does not rule out emergent independent metric
variables, higher-dimensional embedding theories, or correlated spin
phases. No microscopic Einstein phase or TOE is established.

## 1. Four commuting constraints yield the geometric algebra

Supply a flat ambient metric eta=diag(-1,1,1,1) and a smooth spacelike
embedding X^mu(x) of a three-dimensional slice. Work locally, or use
compactly supported smearings to avoid boundary terms. Let

    e_i^mu=partial_i X^mu,
    q_ij=eta_mu,nu e_i^mu e_j^nu,
    eta(n,n)=-1,          eta(n,e_i)=0,

with q positive and n future directed. Introduce the canonical
embedding momentum density P_mu:

    {X^mu(x),P_nu(y)}=delta^mu_nu delta(x-y).

The four constraints C_mu=P_mu commute strongly. Resolve them in the
normal/tangential frame:

    H[N]=integral N n^mu P_mu,
    D[xi]=integral xi^i e_i^mu P_mu.                    (1)

Since the frame is invertible, H=0 and D_i=0 are exactly P_mu=0.
Their Hamiltonian actions on X are N n and xi^i e_i, respectively.
Differentiating normalization and orthogonality under delta_N X=N n
gives

    delta_N n^mu=e_i^mu q^ij partial_j N.               (2)

No field equation or Einstein action is used. Consequently

    {D[xi],D[zeta]}=D[[xi,zeta]],
    {D[xi],H[N]}=H[xi^i partial_i N],
    {H[N],H[M]}=D[q^ij(N partial_j M-M partial_j N)].   (3)

For clarity about the last sign: with delta_N F={F,H[N]}, the
commutator delta_N delta_M-delta_M delta_N acts on X as
e_i q^ij(M partial_j N-N partial_j M). Hamiltonian vector fields
in this convention reverse the Poisson-bracket order, giving (3).
The generators are linear in P, so their vector-field brackets fix
the full generators, with no momentum-independent remainder.

The spatial transformation is also correct:

    {q_ij,D[xi]}=L_xi q_ij.                             (4)

Thus repairing the missing spatial action diagnosed in
[the spin bracket](SPIN_CLOCK_BRACKET.md) is necessary but, even
together with (3), insufficient to derive propagating gravity.

The geometry behind these brackets is established, not a new
discovery: see [Bojowald--Duque--Shah](https://arxiv.org/abs/2410.18807).
Their distinction between hypersurface deformations and on-shell
spacetime covariance is relevant here. Representations in flat
discrete sectors are also studied by
[Bonzom--Dittrich](https://arxiv.org/abs/1304.5983).
We do not infer an anomaly-free quantum algebra from the classical
calculation or from finite differences.

## 2. A change of constraint basis cannot add a graviton

The embedding phase space has eight local phase-space components.
Four independent first-class constraints remove eight. Equivalently,
the pullback of its symplectic form integral delta P_mu wedge delta
X^mu to P=0 is zero, and the gauge directions span variations of X.
The reduced local gravitational phase space is a point.

This remains true under an invertible change of the four constraint
generators or a canonical transformation of the extended phase space.
If a canonical transformation fixes X, it also fixes q(X), and carries
(3) into another representation with the same structure functions.
It preserves the reduced phase-space dimension. Extra matter can
survive the reduction, but a re-encoding alone does not manufacture
independent geometric degrees of freedom.

At a regulated quantum level, an actual common unitary conjugation
likewise preserves the physical-space dimension and operator algebra.
The finite quantum clock construction proves that statement for its
own finite constraints. It does not prove a continuum quantum version
of (3). A general dressing also need not make matter transform as a
local scalar under D: that is a separate condition to test.

## 3. Nonzero spatial curvature can still be pure slicing

Choose the graph embedding X^0=T(x), X^a=x^a with |grad T|<1.
Writing v_i=partial_i T and s=sqrt(1-|v|^2), direct differentiation
gives

    q_ij=delta_ij-v_i v_j,
    q^ij=delta^ij+v_i v_j/s^2,
    n=(1,v)/s,
    K_ij=e_i . partial_j n=(partial_i partial_j T)/s.   (5)

We use K=(1/2)L_n q, as in the previous nonlinear benchmark.
The intrinsic connection is

    Gamma^k_ij=-v_k (partial_i partial_j T)/s^2.

Substitution in the intrinsic Riemann tensor, or the Gauss equation
for a timelike unit normal in flat spacetime, gives

    R_ijkl=-(K_ik K_jl-K_il K_jk),
    R_ij=(K q^(-1) K)_ij-(tr_q K) K_ij,
    nabla_i K_jk=nabla_j K_ik.                          (6)

The Riemann convention in (6) contracts R_ij=q^kl R_kilj.
Equations (6) imply exactly

    R+(tr_q K)^2-K_ij K^ij=0,
    nabla^j K_ij-nabla_i tr_q K=0.                      (7)

These are the supplied vacuum Einstein initial-data constraints.
Nevertheless the electric and magnetic spacetime Weyl tensors are

    E_ij=R_ij+(tr_q K) K_ij-(K q^(-1) K)_ij=0,
    B_ij=epsilon_i^kl nabla_k K_lj=0.                   (8)

The ambient spacetime is flat for every allowed T. Equation (8)
shows explicitly why intrinsic curvature or a scalar-constraint
residual is not an adequate gravitational-wave diagnostic.

For example T=a|x|^2/2 in the region |a x|<1 has

    R=-2a^2(3-a^2|x|^2)/(1-a^2|x|^2)^2,

which is nonzero when a is nonzero, although (8) still vanishes.
A globally asymptotically flat example is

    T=epsilon exp(-|x|^2/2),        |epsilon|<sqrt(e).

Here max |grad T|=|epsilon|/sqrt(e), so the slice is everywhere
spacelike. The metric correction is
-epsilon^2 x_i x_j exp(-|x|^2), and its derivatives decay
exponentially. Its ADM energy is zero. This clock deformation
cannot supply the positive-energy, inverse-distance metric tail of
[the TT boundary construction](GRAVITATIONAL_BOUNDARY_DRESSING.md).
It has a varying trace curvature as well as shear; it is not the
trace-free momentum seed used in that construction.

## 4. The tensor sector is absent already at first order

Linearize about X^0=0, X^a=x^a, K=0. Write delta X^0=tau and
delta X^a=u^a. Then

    delta q_ij=partial_i u_j+partial_j u_i,
    delta K_ij=partial_i partial_j tau.                 (9)

For every nonzero Fourier momentum, the transverse-traceless
projection of both tensors is zero. The same holds for
delta pi^ij proportional to delta K^ij-delta^ij tr(delta K).
Thus both members of a gravitational tensor canonical pair are
missing. In a TT coordinate representation, the embedding-to-
physical-tensor map has rank zero.

This linear diagnostic is used about the stated flat slice.
At nonlinear order a coordinate TT projection can contain gauge
artifacts; the exact zero-Weyl result (8) is the stronger test.
There is no statement here that every zero-Weyl configuration in
every theory has no degrees of freedom.

For a positive control, the existing periodic data

    q=delta,   K=Sigma+(tau/3)delta,
    Sigma=A [[cos(kz),sin(kz),0],[sin(kz),-cos(kz),0],[0,0,0]],
    tau=+sqrt(3)A,

satisfy (7), but B=-k Sigma has squared norm 2A^2 k^2>0.
They therefore cannot be produced by a graph in flat spacetime.
This benchmark is from [nonlinear tensor backreaction](NONLINEAR_TENSOR_BACKREACTION.md)
and still assumes Einstein initial-data equations.

## 5. The structure function must include the physical tensor

Adding a spectator tensor oscillator is also insufficient. Suppose
the proposed physical metric near the flat slice is q_phys=I+h_TT,
but the deformation generators still use q_emb=I from (1).
The difference in the normal-normal bracket's shift coefficient is

    [q_emb^(-1)-q_phys^(-1)] w
      =h_TT w+O(||h_TT||^2 |w|),
    w_j=N partial_j M-M partial_j N.                    (10)

For example h_TT=diag(a,-a,0), with wavevector along z, and w along
x gives a mismatch a/(1+a) in that shift component. There is no
small-parameter cancellation beyond its explicit linear size.

The lapse-gradient covector w can be chosen arbitrarily at a point.
Consequently the structure function has to respond to the independent
physical metric perturbation itself. A deformation algebra whose
metric depends only on the embedding clocks fails that test.
This compares the specified generators before imposing constraints;
setting D=0 first would hide the mismatch and would not verify (3).

## 6. Consequence for the microscopic model

The candidate identification tested here,
q_ij=eta_mu,nu partial_i X^mu partial_j X^nu in fixed
four-dimensional Minkowski spacetime, must be rejected
as the source of the gravitational tensor phase. Clocks can describe
relational evolution and energy dressing. Independent geometric
degrees of freedom still have to emerge from the spin sector.

The next joint test is therefore:

1. Exhibit two nondegenerate tensor canonical pairs after reduction,
   with a physical curvature response that survives refinement.
2. Derive the normal and spatial actions on that same metric and on
   matter. In particular verify the tensor variation of the inverse
   metric in the normal-normal bracket, as tested in (10).
3. Recover the nonlinear constraint balance, positive-energy boundary
   tail in the asymptotically flat sector, and the corresponding
   dynamics, with the required locality and error control.

These are necessary tests for the intended Einstein limit, not a
sufficient general definition of quantum gravity. The two-derivative
metric uniqueness calculation in
[gravity from clock constraints](GRAVITY_FROM_CLOCK_CONSTRAINTS.md)
remains conditional on an independent canonical metric and its
specified local Hamiltonian ansatz. The pure embedding counterexample
violates that premise and does not contradict the calculation.

The local prepotential wave action supplies a classical benchmark for
the first test, but its stable finite-spin realization and nonlinear
completion are unproved. A field-dependent change of basis in the
clock constraints cannot substitute for those missing results.

## 7. Reproduction

    OPENBLAS_NUM_THREADS=1 python3 -W error::RuntimeWarning scripts/embedding_gravity_audit.py

The audit checks exact one-dimensional normal and metric variation
identities; normal variations on general three-dimensional embedding
tangents; graph curvature from metric derivatives; the zero-Weyl
and vacuum-constraint identities; the linear TT map; the nonflat
positive control; and the physical-metric structure-function mismatch.
It also computes the canonical bracket with a centered lattice
derivative. The functional derivatives used there are

    delta H[N]/delta P_mu=N n^mu,
    delta H[N]/delta X^mu
      =partial_i [N q^ij (e_j^nu P_nu) n_mu].

The audit independently differentiates the discrete Hamiltonian
under both temporal and spatial embedding perturbations to check
the second formula with centered differences. Its bracket convergence
check is not an exact lattice algebra
or an operator-norm continuum theorem. No Lean source is changed.

All 61 numerical cases and the exact symbolic identities pass.
Graph curvature and constraint residuals are below 1e-15; the
normal-commutator finite difference residual is below 1.6e-10.
The lattice bracket's observed convergence orders are 1.95, 1.99
and 1.99, with relative error about 0.00764 on the finest 32^3 grid.
The counterexample and its limitations are analytical statements;
the floating point checks are supporting evidence.
