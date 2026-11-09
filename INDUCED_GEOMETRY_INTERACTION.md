# Field-mediated geometry interactions and an exact Gaussian influence

Date: 2026-09-10

The neutral field does mediate interactions between the switches. The
leading acoustic calculation gives an anisotropic two-phonon potential
proportional to inverse distance to the seventh power, with continuous
spectral weight. It supplies neither a Newtonian potential nor a graviton.

There is also a stronger control result: expanding the field operator
around the midpoint of the two local graphs gives a uniform relative
bound `1/sqrt(3)<1`. Consequently the Gaussian field can be integrated
out for every switch history, with an absolutely convergent determinant
expansion at finite spatial volume and finite Euclidean duration. No
oscillator occupation cutoff is needed. The spatial regulator and the
large-spin extension are still inputs, and summing the resulting
interacting switch histories remains an unsolved problem.

## 1. Reorganize the existing Hamiltonian without changing it

Use the large-spin Hamiltonian of
[the finite-gap calculation](FINITE_GAP_GEOMETRY_FEEDBACK.md). For any
reference number theta between zero and one, write the exact identity

```
A_Lambda = Lambda G + pi^T pi/(2 chi)
             + (1/2)q^T A_theta q + sum_s (n_s-theta) F_s(q),
chi=1/(6 kappa),
A_theta=kappa[L_0+theta sum_s B_s],
V_s=kappa B_s,  F_s=(1/2)q^T V_s q
    =kappa(q_a-q_d)(q_b-q_c).                        (1)
```

Here B_s is the local switched-minus-reference Laplacian. The geometry
operator G, its parameters, and the physical model have not changed.
The earlier fast-limit reference was theta=p=(1-d/Omega)/2. Choosing
theta=1/2 below is an auxiliary expansion choice, not a claim that
the physical switch occupancy equals one half. Linear terms in
`n_s-theta` must be retained; they include the field's vacuum force.

Every F_s annihilates the constant spatial coordinate. Separate the
free center-of-mass canonical pair and work on the relative field
space, orthogonal to the spatial constant. This removes its common
divergent partition factor, not a geometry-dependent interaction.
All connected finite carriers then have a strictly positive A_theta
on the remaining coordinates.

## 2. A uniform midpoint bound for all configurations and histories

For one switched path, put x=q_a-q_b, y=q_b-q_c, z=q_c-q_d. The
two path energies, before their common kappa/2 factor, are

```
E_old=x^2+y^2+z^2,
E_new=(x+y)^2+y^2+(y+z)^2.
```

The matrix of E_new relative to E_old has eigenvalues
`1, 2-sqrt(3), 2+sqrt(3)`. Set
`m=(E_old+E_new)/2`, `h=(E_new-E_old)/2`, u=x+z, v=x-z.
The exact sum-of-squares identity

```
4(m^2-3h^2) = (u^2+2uy-2y^2)^2
                +2v^2(u+y)^2+6v^2y^2+v^4 >= 0      (2)
```

proves `|h|<=m/sqrt(3)`. For any z_s in [0,1], the deviation
from the midpoint is `(2z_s-1)h`, so it obeys the same bound.
The switch paths in this carrier have disjoint reference edges;
sum (2), and include the untouched positive bond energies. With
A_*=A_(1/2) this proves the quadratic-form inequality

```
-r A_* <= sum_s (z_s-1/2)V_s <= r A_*,
r=1/sqrt(3)<1.                                     (3)
```

The constant is independent of volume, switch count, Lambda, rho,
and J. Equation (3) also holds pointwise in Euclidean time for any
measurable switch history. The bound is sharp for the isolated path;
untouched bonds can improve the full-carrier constant.

For comparison, expanding around theta=p gives the sufficient radius

```
r_theta=max_(z=0,1; l=1+sqrt(3),1-sqrt(3))
                      |(z-theta)l/(1+theta l)|.      (4)
```

It is below one precisely when
`(3-sqrt(3))/4 < theta < (1+sqrt(3))/4`.
For the previous p=0.3193394661..., r_p=0.9931360123....
The midpoint reduces the universal sufficient radius to 0.5773502692....
This is a bound on the field operator; it is not a geometry spectral
gap bound or a proof that the final switch measure has short correlations.

## 3. Exact influence of the Gaussian field

At finite Euclidean duration beta with periodic boundary conditions,
define, on relative field coordinates,

```
M_0=-chi partial_tau^2+A_*,
delta A(tau)=sum_s (z_s(tau)-1/2)V_s,
S=M_0^(-1/2) delta A M_0^(-1/2).
```

The positive time kinetic form and (3) imply `||S||<=r`.
At finite spatial volume, M_0^(-1) is trace class: its eigenvalues
are `(chi(2 pi n/beta)^2+a_j)^(-1)`, with finitely many positive
spatial a_j. Since delta A is bounded, S is trace class as well.
The normalized Gaussian integral is therefore well defined, and its
contribution to the switch action is the exact Fredholm determinant

```
Gamma[z] = (1/2) Tr log(I+S)
         = (1/2) sum_(n>=1) (-1)^(n+1) Tr(S^n)/n.    (5)
```

One may first use a finite time-mode cutoff, evaluate the ordinary
Gaussian integral, and take the trace-class limit. For K>=2,

```
|Gamma-Gamma_(through K)|
 <= r^(K-1) Tr(S^2)/[2(K+1)(1-r)].                  (6)
```

Proof: for n>=2, self-adjointness gives
`|Tr(S^n)|<=r^(n-2)Tr(S^2)`. Bound 1/n by 1/(K+1) in the
tail and sum the geometric series. Thus the convergence ratio is
uniform across all physical histories, with no small source or
oscillator occupation assumption. The total trace factor may grow
with beta and volume; (6) is not an absolute error independent of
system size or a spatial continuum limit.

The transverse-field geometry has its usual Trotter representation
as a sum over piecewise constant switch histories. In that finite-volume
Euclidean representation, multiplying the geometry weight by
`exp(-Gamma[z])` exactly integrates the relative Gaussian field of
(1). This retains all field-induced many-switch and time-dependent
interactions. It does not evaluate the remaining history sum or prove
its phase, nor is it a local-in-time Hamiltonian for the switches.

## 4. The induced pair kernel and its finite-volume error

For any fixed positive reference A=A_theta on relative coordinates,
let omega_j=sqrt(a_j/chi) and u_j be its normal modes. The zero-temperature
Euclidean covariance of the full oscillator field is

```
C(tau)=sum_j u_j u_j^T exp(-omega_j |tau|)/(2 chi omega_j).
```

Center each source operator by its vacuum mean. Wick contraction gives
the exact Gaussian connected correlation

```
Pi_sr(tau)=<F_s(tau)F_r(0)>_connected
         =(1/2)Tr[V_s C(tau) V_r C(tau)].            (7)
```

The determinant's quadratic contribution is
`-(1/2)sum_sr integral x_s(tau)Pi_sr(tau-tau')x_r(tau')d tau d tau'`.
It includes nonzero interactions between different switches. For static
sources x_s, their ground-energy expansion is

```
E(eta x)-E(0)=eta sum_s x_s mu_s
               -(eta^2/2)sum_sr x_s W_sr x_r+R_3,
mu_s=Tr[V_s A^(-1/2)]/(4 sqrt(chi)),
W_sr=integral Pi_sr(tau)d tau
 =(1/(4chi^2))sum_ij (V_s)_ij(V_r)_ji
                          /[omega_i omega_j(omega_i+omega_j)]. (8)
```

Matrix elements in the sum use the normal-mode basis. W is positive
semidefinite, so the exact Gaussian ground energy is concave in the
external static sources. This also follows from its variational
characterization. Individual off-diagonal W_sr need not have a fixed
sign for arbitrary source operators.

Put `V_x=sum_s x_s V_s`, `w_x=x^T W x`, and
`r_x=|eta| ||A^(-1/2)V_x A^(-1/2)||<1`. The zero-temperature
version of (6) at K=2 gives the explicit bound

```
|R_3| <= eta^2 r_x w_x/[3(1-r_x)].                  (9)
```

For clarity, use `G_nu=(chi nu^2+A)^(-1)`. Then
`w_x=(1/2)integral Tr[(G_nu V_x)^2]d nu/(2pi)` and the exact
energy shift is `(1/2)integral log det(I+eta G_nu V_x)d nu/(2pi)`.
These convergent finite-spatial-volume integrals prove (9) without
truncating oscillator occupation. They also let the audit reduce a
3,456-vertex carrier to four source columns and small determinants.

For the midpoint reference on the periodic 24 by 12 by 12 carrier,
the two switches are twelve sites apart. The audit finds
`W_11=W_22=0.04514811991...` and `W_12=1.20372446...e-8`.
This is a nonzero finite-volume pair response, with periodic images
included. It is not an infinite-space estimate of (12).

Equations (7)-(9) concern the Gaussian field at the chosen reference
and the expansion of its exact influence. They are not a solution
of the interacting geometry spectrum. In particular the linear vacuum
force in (8) cannot be omitted when inferring the physical switch bias.

## 5. Match the source to the periodic acoustic field

The source coefficient is affected by the same cell relaxation that
determines the acoustic stiffness. It should not be set to 3 kappa
using a rigid affine field when the reference has nonzero switch weight.
Let h_x(v)=v_x+w(v) be the harmonic coordinate of A_theta, with w
periodic and mean zero. For our x-oriented switch, its leading
low-band source is

```
F_s -> gamma_theta (partial_x phi)^2,
gamma_theta=kappa[h_x(a)-h_x(d)][h_x(b)-h_x(c)].      (10)
```

The transverse harmonic coordinates have no corrector because only
x bonds change. Differentiating the minimized cell energy gives an
independent check of this vertex:

```
d D_theta,x/d theta = 2 gamma_theta/ell^3.           (11)
```

Stationarity of the cell minimizer removes its derivative from (11).
The audit solves that cell problem, checks (11) by finite differences,
and reports both theta=p and theta=1/2. At theta=p the matched vertex
is 0.4808429765..., and at the midpoint it is 0.3575627337...;
the uncorrected affine value is 0.75.
The midpoint coefficient and acoustic speeds refer to an auxiliary
Gaussian reference, not new predictions for the full interacting model.

## 6. Exact acoustic pair interaction: an inverse seventh power

For the Gaussian acoustic action at that reference, let
`c_i=sqrt(D_theta,i/chi)`, `c_prod=c_x c_y c_z`, and use acoustic
coordinates `y_i=x_i/c_i`, `R=|y|`, `mu=y_x/R`. At separated points
the Euclidean propagator is

```
G_E(tau,x)=1/[4pi^2 chi c_prod (tau^2+R^2)].
```

For `O=gamma_theta :(partial_x phi)^2:`, differentiate the propagator
twice and use Wick's two cross contractions. Its static kernel is

```
W_ac(x)=gamma_theta^2
  *[5-35mu^2+63mu^4]/[32pi^3 chi^2 c_prod^2 c_x^4 R^7]. (12)
```

The time integral is elementary. On putting t=tau/R, its three
terms use
`integral(1+t^2)^(-4)dt=5pi/16`,
`integral(1+t^2)^(-5)dt=35pi/128`, and
`integral(1+t^2)^(-6)dt=63pi/256` over the real line.
The angular factor is strictly positive:

```
5-35mu^2+63mu^4=63(mu^2-5/18)^2+5/36.              (13)
```

For source positions r_s,r_r, the leading pair energy
`-eta^2 x_s x_r W_ac(r_s-r_r)` is
attractive for identical aligned sources of the same sign. Opposite
source signs reverse it. In isotropic coordinates with speed c,
(12) becomes `gamma^2[5-35mu^2+63mu^4]/(32pi^3 chi^2 c^3 r^7)`.
The inverse seventh power describes energy; its radial force has an
inverse eighth power, together with an angular component.

This is the exact separated-point result in the Gaussian acoustic
theory. Equation (10) matches its leading vertex to the periodic cell.
A uniform remainder taking the full interacting lattice correlations
to (12) has not been proved. The finite periodic audit checks (7)-(9),
not an infinite-volume power-law fit. Contact terms and local bias
renormalizations are regulator dependent and do not change this
separated-point acoustic calculation.

The two-phonon inverse-seventh-power mechanism is already known in
other systems: [Fujii, Hongo and Enss (2022)](https://arxiv.org/abs/2206.01048)
derive it for heavy impurities in superfluids. Their model differs from
this graph model. The midpoint bound, the exact switch source, and its
cell matching above are the repository-specific results; the power
law is not presented as new general physics.

## 7. Continuous two-phonon weight is not a graviton pole

At finite volume, a centered quadratic field operator acting on the
Gaussian vacuum creates exactly two oscillator quanta. Its excitation
energies in (7) are omega_i+omega_j. It has no one-phonon matrix
element. In the acoustic continuum, the positive-frequency spectral
function is the two-particle phase-space integral. With the convention

```
S_O(omega,k)=integral exp(i omega t-i k.x)<O(t,x)O(0,0)>dt d^3x,
```

it has support `omega>=sqrt(sum_i c_i^2 k_i^2)`. At k=0 the
angular average of the fourth power of one direction cosine is 1/5,
giving the exact expression

```
S_O(omega,0)=gamma_theta^2 omega^4 theta(omega)
               /[320 pi chi^2 c_prod c_x^4].        (14)
```

The two-particle measure is continuous in energy; the collinear
threshold set carries no isolated delta-function mass shell in three
spatial dimensions. These are gapless composite fluctuations of the
existing field, not a new massless one-particle pole at this order.

There is also an exact selection rule in the full large-spin Hamiltonian:
field parity `q->-q, pi->-pi` commutes with the Hamiltonian and every
n_s. A geometry observable therefore has zero matrix element between
opposite parity eigenstates. In a parity-even vacuum it cannot create
an odd one-phonon state. This does not forbid an even composite bound
state, a new collective phase, or spontaneous symmetry breaking in a
thermodynamic limit; those require a calculation beyond the Gaussian
pair response. Angular tensor dependence in (12) alone does not imply
spin-two particles or gravitational gauge constraints.

## 8. What this closes and what it leaves open

The field-mediated interaction is now explicit. The midpoint bound
supplies an exact convergent representation of all Gaussian-field
feedback at finite spatial volume, rather than only a formal first
diagram or a finite-occupation matrix truncation. It preserves the
original finite-gap geometry dynamics inside a remaining history sum.

The unresolved dynamical problem is to control that history sum and
its collective spectral function, including the vacuum-force shift,
then take its spatial and physical spin limits. The leading two-phonon
answer gives no gravitational pole or Newtonian potential. A successful
composite proposal must demonstrate an isolated tensor excitation,
the necessary constraints, and universal matter coupling. Adding a
new constrained geometry sector would instead be a model change.
Neither outcome follows from the determinant identity alone.

The audit checks the local form bound and sum of squares, finite-time
determinant remainders, a 3,456-vertex Gaussian carrier, independent
normal-mode/Fock/trace-square-root identities, the cell source vertex,
and the angular/time integrals. Twelve supporting Lean results cover algebra,
positivity, and the scalar parity selection rule. The trace-class,
Gaussian, and spectral arguments above remain analytic proofs.
