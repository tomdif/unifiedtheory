# Tensor-packet self-gravity with fixed physical normalization

Date: 2026-09-11

Two separated packets of transverse-traceless gravitational momentum
can be completed to vacuum Einstein initial data with energy

    E_ADM(R)=m_A+m_B-G m_A m_B/R+O(R^(-2)).              (1)

Here m_A,m_B are their isolated ADM energies in units c=1. The
construction holds their local physical packet geometry fixed to
the accuracy of the separation expansion. It supplies an explicit
remainder bound, rather than identifying a positive source with a
Newtonian mass by assumption.

Holding the coordinate TT seeds fixed gives a different comparison:
its weak-amplitude coefficient is seven instead of one. The
difference comes from changing physical packet size and strength
when the background conformal factor changes. An exact rescaling
identity resolves that apparent mismatch.

**This is a conditional nonlinear self-gravity benchmark.** The
Einstein constraint, its geometric variables, asymptotically flat
boundary conditions, and G are supplied. The calculation does not
derive them from the spins, establish packet equations of motion,
or close the quantum deformation algebra. No TOE is proved.

## 1. Use actual compact TT data

The [boundary dressing calculation](GRAVITATIONAL_BOUNDARY_DRESSING.md)
already supplied a Gaussian Cotton seed and a small-data conformal
existence argument. Compact support now makes the two source regions
exactly disjoint. Apply the same local Cotton operator to
Z=diag(-1,-1,2) f(r^2), where

    f(s)=(1-s)^8 for s<1,      f(s)=0 for s>=1.

For rho^2=x^2+y^2, write b=f''(r^2), d=f'''(r^2). Up to an overall
orientation sign the tensor is

    tau =
      [[24xyz d,       -12z(x^2-y^2)d, -12y(2b+rho^2 d)],
       [-12z(x^2-y^2)d,-24xyz d,        12x(2b+rho^2 d)],
       [-12y(2b+rho^2 d),12x(2b+rho^2 d),             0]].

Exact differentiation gives tr tau=0 and partial_j tau_ij=0. The
prepotential is C^7 across r=1, its Cotton tensor is C^4, and its
components vanish to at least fifth order at that boundary. Thus
extending it by zero introduces no distributional surface charge.
This is a compact finite-regularity seed, not a C-infinity bump.

Its squared norm and normalization are

    |tau|^2=288 rho^2 [(2b+rho^2 d)^2+rho^2 z^2 d^2],
    M=integral |tau|^2=3367254360064 pi/770201575.

Set sigma=epsilon tau/sqrt(M), so integral |sigma|^2=epsilon^2.
The conformal data are

    q=psi^4 delta,       K=psi^(-2) sigma,
    Delta psi=-|sigma|^2 psi^(-7)/8,       psi -> 1.    (2)

The momentum constraint is solved by conformal TT covariance.
This is the established conformal constraint method; see
[Dilts](https://arxiv.org/abs/1507.01913). The prepotential origin
is the linear construction of
[Henneaux--Teitelboim](https://arxiv.org/abs/gr-qc/0408101), as
implemented in the repository's local lattice benchmark.

For N[S](x)=(32 pi)^(-1) integral S(y)/|x-y|, the normalized
seed has the continuum bound

    ||N[|tau|^2/M]||_infinity
       <= U_bar=1502700975/(1879048192 pi)
       < 0.255.                                        (3)

To obtain it, use rho^2<=r^2, rho^2 z^2<=r^4 and
|2b+rho^2 d|<=2b-r^2 d inside the unit ball. The resulting
nonnegative radial envelope has Newton potential bounded by
its central value, (8M)^(-1) integral_0^1 r envelope(r) dr.
Its exact polynomial integral gives (3).

More generally take two compact TT seeds sigma_i supported in balls
of radii a_i, each with gamma_i=||N[|sigma_i|^2]||_infinity.
If 7 gamma_i<1, the contraction argument gives an isolated solution
u_i>=1 and a positive isolated energy

    m_i=(16 pi G)^(-1) integral |sigma_i|^2 u_i^(-7),
    u_i=1+G m_i/(2r)+O(r^(-2)).                         (4)

The symbol u_i denotes the full isolated conformal factor here.

## 2. Why fixed coordinate amplitudes give the wrong comparison

For a weak seed sigma=epsilon tau, expansion of (2) gives

    psi=1+epsilon^2 N[|tau|^2]+O(epsilon^4),
    E=(epsilon^2/(16 pi G)) integral |tau|^2
      -(7 epsilon^4/(16 pi G))
                       integral |tau|^2 N[|tau|^2]+O(epsilon^6).

For two disjoint coordinate seeds, the cross term is

    Delta E_fixed
      =-7 G m_A,bare m_B,bare/R
         +O(epsilon^4/R^2)+O(epsilon^6).                (5)

Here m_i,bare=epsilon^2 integral |tau_i|^2/(16 pi G).
Equation (5) identifies the coefficient at fourth order in the
common amplitude; its displayed amplitude remainder must not be
dropped while sending R to infinity at fixed epsilon.

A precise fixed-amplitude version uses the isolated coordinate
flux charge F_i(c) when the boundary value in (2) is c rather than
one, with the coordinate seed held fixed. Let chi_i=-F_i'(1).
Differentiating the contraction equation gives

    w_i=1-7 N[|sigma_i|^2 u_i^(-8) w_i],
    chi_i=(7/(16 pi G)) integral |sigma_i|^2 u_i^(-8) w_i.

The separation expansion then has leading binding
-G(chi_A m_B+chi_B m_A)/(2R). In the weak-amplitude limit,
chi_i/m_i tends to seven. F_i(c) is a coordinate flux charge,
not an ADM energy in coordinates normalized to a unit asymptotic
metric when c differs from one.

The explanation is physical normalization. Near a packet with
approximately constant external conformal factor c, proper
coordinate lengths scale as c^2. Keeping its coordinate tensor
fixed changes its local metric and extrinsic curvature.

## 3. An exact rescaling keeps the physical packet fixed

Start with any isolated solution (u,sigma) of (2). For a constant
c>=1 and packet center x_A define

    y=c^2(x-x_A),
    sigma_c(x)=c^6 sigma(y),
    psi_c(x)=c u(y).                                    (6)

The seed stays TT. The equation is exactly covariant:

    Delta_x psi_c=c^5 Delta_y u,
    |sigma_c|^2 psi_c^(-7)=c^5 |sigma|^2 u^(-7).

In the y coordinates the physical fields are exactly

    q_ab(y)=u(y)^4 delta_ab,
    K_ab(y)=u(y)^(-2) sigma_ab(y).                       (7)

In particular, the c^(-4) from the two covariant tensor coordinate
indices cancels the remaining c^4 in psi_c^(-2) sigma_c.
Both physical fields, including the isolated self-dressing, are
the original packet's fields.

Its contribution to the far conformal factor is instead

    psi_c=c+G m/(2c |x-x_A|)+O(|x-x_A|^(-2)).

Equivalently, the coordinate flux charge is exactly

    alpha(c)=(16 pi G)^(-1)
                    integral |sigma_c|^2 psi_c^(-7)=m/c. (8)

The scaling powers in the integral are c^12 from the squared seed,
c^(-6) from volume, and c^(-7) from the conformal factor.
This gives c^(-1), rather than the c^(-7) obtained by fixing the
coordinate seed and neglecting its self-response.

Distinguishing local masses from asymptotic conformal coefficients
has established precedent in
[Brill--Lindquist interaction energy](https://doi.org/10.1103/PhysRev.131.471).
The present calculation uses regular compact TT packets, not
punctures or stationary black holes.

## 4. Construct the two packets and bound the error

Place the centers a coordinate distance R apart. Choose positive
alpha_A,alpha_B and constants c_A,c_B solving

    c_A=1+G alpha_B/(2R),       c_B=1+G alpha_A/(2R),
    alpha_A=m_A/c_A,           alpha_B=m_B/c_B.          (9)

This algebraic system has a unique positive solution. Subtracting
the two equations m_i=alpha_i c_i gives alpha_A-alpha_B=m_A-m_B;
the positive root for their sum fixes both. In particular

    alpha_A+alpha_B=m_A+m_B-G alpha_A alpha_B/R.         (10)

Scale and translate each seed by (6), then add them. Put
b_i=a_i/c_i^2, b=b_A+b_B and require R>b. Their supports are
disjoint, so the squared total TT seed is exactly S_A,c+S_B,c.
There is no discarded tensor interference term.

The transformed linear Newton potentials satisfy
||N[S_i,c]||<=c_i^8 gamma_i. Define

    Gamma=c_A^8 gamma_A+c_B^8 gamma_B,       7 Gamma<1.  (11)

The positive conformal fixed-point map is a contraction with
constant 7 Gamma on 1<=psi<=1+Gamma. It gives an exact two-packet
solution of the vacuum Einstein constraints.

To control its energy, let

    f_i(x)=c_i[u_i(c_i^2(x-x_i))-1],
    Psi_app(x)=1+f_A(x)+f_B(x).

On packet i, its exact isolated constant-background reference is
c_i+f_i. The other packet's potential differs from c_i-1 by at most

    delta=max(G alpha_A/2,G alpha_B/2)
                              b/[R(R-b)].              (12)

Indeed f_j is the Newton potential of a positive effective source
inside the radius b_j, with monopole G alpha_j/2. For x in packet i
and y in packet j,
|1/|x-y|-1/R|<=b/[R(R-b)]. Integrating this inequality proves (12)
without spherical symmetry or a truncated multipole expansion.

Both the exact solution and Psi_app lie in [1,1+Gamma].
Using |a^(-7)-b^(-7)|<=7|a-b| for a,b>=1, the fixed-point
residual of Psi_app is at most 7 Gamma delta. Hence

    ||psi-Psi_app||_infinity
                 <= 7 Gamma delta/(1-7 Gamma).         (13)

On each packet, its difference from c_i+f_i is at most
delta/(1-7 Gamma). In the local y coordinates this also controls
the C^0 errors in both q and K relative to the isolated packet.
Thus holding the physical packet fixed is justified to order R^(-2),
rather than asserted exactly in a spatially varying external field.

Let

    E_bare,R=(16 pi G)^(-1) integral (S_A,c+S_B,c).

Comparing the exact energy integrals with (8) gives the explicit bound

    |E_ADM-(alpha_A+alpha_B)|
             <= 7 E_bare,R delta/(1-7 Gamma).           (14)

This includes nonlinear self-gravity inside each packet. No weak
amplitude expansion inside m_i was used; the smallness assumption
is the sufficient existence/control condition (11).

## 5. The coefficient is the product of physical energies

From (9), m_A-alpha_A=m_B-alpha_B=G alpha_A alpha_B/(2R).
Therefore

    0<=m_A m_B-alpha_A alpha_B
                  <=G m_A m_B(m_A+m_B)/(2R).

Combining this with (10) and (14) proves

    |E_ADM-(m_A+m_B-G m_A m_B/R)|
      <= 7 E_bare,R delta/(1-7 Gamma)
                      +G^2 m_A m_B(m_A+m_B)/(2R^2).    (15)

For fixed packets with 7(gamma_A+gamma_B)<1, condition (11)
holds with a uniform margin for all sufficiently large R.
Their radii and rescaled bare energies remain bounded, and
delta=O(R^(-2)). This proves (1), including the sign of the
leading interaction. Its coefficient does not depend on the
packets' detailed TT profiles or orientations.

The bound is conservative and need not prove attraction at each
finite separation tested numerically. It does establish attraction
for sufficiently large separation. R is the specified conformal
coordinate separation. No exact finite-separation formula in terms
of a chosen proper-distance prescription is asserted.

For the unit-radius compact packet, the audit obtains the following
dimensionless ratio with G=1:

    (m_A+m_B-E_ADM)/(m_A m_B/R).

At amplitudes (0.2,0.32), it is approximately 0.98631, 0.99650,
0.99908 and 0.99975 at R=4,8,16,32. Holding the coordinate seeds
fixed gives about 6.90237 at R=32, consistent with their charge
susceptibilities. At the weaker pair (0.12,0.12), that control
approaches 6.98010 rather than one.

## 6. What this supplies to the microscopic program

There is a necessary change in the free reconstruction itself.
On the pure TT momentum slice, write sigma=epsilon tau and
q=delta+epsilon^2 h_2+O(epsilon^4). Equations (2) give

    h_2=4 N[|tau|^2] delta,
    partial_i partial_j h_2,ij-Delta tr h_2=|tau|^2.   (16)

But the linear prepotential reconstruction h=S(Phi), including
its original spatial gauge shifts, identically lies in the kernel
of the scalar operator on the left. No choice of a second-order
Phi in that unchanged map can produce (16). A new interaction
Hamiltonian with the old linear reconstruction alone would miss
this nonlinear constraint.

The required extension must supply a sourced metric component and
the corresponding nonlinear constraint reduction. Its eliminated
form contains an inverse Laplacian. For the compact seeds above its
nonzero integrated source requires a long-range tail; a finite-range
local function of only compact seed data cannot supply that tail.
Keeping a local auxiliary constraint equation is a distinct option,
but its brackets and physical energy still need to be derived
together, as the prior mediator test emphasized.

The independent tensor's nonlinear metric dressing now has a
specific energy test: reproduce (15) for physically calibrated
packets, with the same G that fixes the single-packet boundary tail.
The physical fields must change with the external geometry through
the normalization in (6)--(8). A microscopic tensor amplitude held
fixed without a physical calibration is insufficient for this test.

This is more information than a free-wave pole, a nonzero Weyl
tensor, or a successful embedding algebra. It remains a benchmark
computed from supplied Einstein constraints. The spin Hamiltonian
and clock constraints have not been shown to generate (2), (6),
or the energy (15).

In particular, the packets are gravitational initial data, not
stationary particles. A derivative of this energy along the
constructed family has not been shown to be their dynamical force.
That requires collective canonical variables and an evolution
calculation. Universal coupling to other matter, the independent
metric's quantum phase, the tensor-dependent deformation algebra,
nonlinear causal evolution and a physical TOE remain open.

## 7. Reproduction

    OPENBLAS_NUM_THREADS=1 python3 -W error::RuntimeWarning scripts/tensor_packet_self_gravity_audit.py

The exact checks cover the compact TT tensor, its norm and
potential envelope, its Cotton origin, the failure of the unchanged
linear reconstruction, conformal scaling identities and the
algebraic mass expansion. Fifty numerical cases check isolated
packets, finite differences of their charge susceptibility,
constant-background rescaling, coupled nonlinear packets at
three resolutions, the comparison bounds, and the fixed-coordinate
control.

The solver works on each compact source region, using all even
and odd Legendre modes retained by its angular resolution. It
couples the regions through exterior multipoles and computes the
mass from their effective sources. The finest grid has 96 radial
points and 18 angular points per packet. Nonlinear residuals
are below 3e-16; these are discrete residuals, not certified
continuum error estimates. Refinement changes in the normalized
binding coefficient decrease, but the numerical discretization
error is not bounded by (15). That equation is a separate
continuum comparison bound. No Lean source is changed.
