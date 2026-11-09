# Scalar-induced tensor dynamics: linear shear poles and a failed Einstein cone

Date: 2026-09-10

Scalar fluctuations do induce positive temporal and spatial derivative
terms for transverse tensor strain in a local extension of the spin-field
model. If that strain is promoted to a collective field and its quadratic
mass is tuned away, the resulting Gaussian effective model has linear
poles below the two-scalar threshold. This is a concrete dynamical
mechanism beyond the earlier purely static induced interaction.

It fails the Einstein matching test as constructed. The two shear
polarizations have unequal speeds, both strictly below the scalar acoustic
speed. The complete temporal strain response has rank six and supplies
no gravitational constraints. The mass tuning and the interacting spin
phase are not proved. These are exact Gaussian source-response results
and a conditional collective model, not a derived graviton or TOE.

## 1. Why a new clock alone cannot fix the previous spectrum

The [nonlinear initial-data benchmark](NONLINEAR_TENSOR_BACKREACTION.md)
identified a volume--mean-curvature clock pair. A regular common clock
change has a finite, nonzero Jacobian dT/dt on the reference background.
It rescales all local characteristic frequencies by the same factor.
Consequently it preserves the momentum power in a dispersion relation
and preserves ratios of tensor and matter speeds. On a slowly varying
background this statement concerns local characteristics, not a global
Fourier frequency.

Nor is replacing an energy by a singular function of energy automatically
a common clock change. Near a stationary reference state with
H=E_0+H_2+O(amplitude^3), a regular F gives
F(H)=F(E_0)+F'(E_0)H_2+O(amplitude^3), so the quadratic frequencies
again receive a common factor. A singular F requires a separate
physical interpretation and does not supply a regular repair. The
calculation below instead changes the effective tensor dynamics through
its coupling to scalar fluctuations.

## 2. A specified local regulator for the existing spin stiffness

Retain the spin tensor of [the clock-bracket model](SPIN_CLOCK_BRACKET.md),
setting kappa=1:

```
C_s^ij=delta^ij I+gamma sum_alpha E_alpha^ij X_s,alpha,
u_i C_s^ij u_j >= (1-|gamma|)|u|^2 I,       |gamma|<1.    (1)
```

The six E_alpha form the symmetric Frobenius basis and the X_alpha are
the existing singlet-to-excited-state transitions in a four-spin cell.
Use centered differences D_i=(T_i-T_i^(-1))/2 and additionally the
positive local term with B_i=I-(T_i+T_i^(-1))/2. The scalar energy is

```
H_phi=(1/2) sum_s [P_s^2+m^2 Q_s^2
                   +(D_i Q)_s C_s^ij (D_j Q)_s
                   +sum_i (B_i Q)_s^2].                 (2)
```

The last term is a new, explicitly chosen ultraviolet regulator. It is
independent of C and removes the extra zeros of the centered difference.
All terms have fixed finite spatial support. The old positivity bound
and the nonnegative B terms make this spin-field Hamiltonian bounded
below at finite volume. For m>0 the field coordinates are confined.
This gives neither a many-body gap nor a critical-phase theorem, and
the canonical scalar operators remain unbounded. A bounded microscopic
operator-norm locality theorem is not inferred from this form bound.

At C=I, in lattice units,

```
omega_q^2=m^2+sum_i [sin^2 q_i+(1-cos q_i)^2]
         =m^2+2 sum_i (1-cos q_i).                       (3)
```

There is one zero at q=0 when m=0, and the scalar acoustic speed is
one. The massless response coefficients below can be obtained as
m decreases to zero. The free constant-coordinate partition factor
is source independent for these derivative couplings; no arbitrary
local-lapse invariant reduction is claimed.

## 3. Integrating the scalar for a commuting strain history

For this response calculation replace C by the commuting source
C=I+gamma h T, near h=0. Take propagation along z and either

```
T_+=diag(1,-1,0),
(T_cross)_xy=(T_cross)_yx=1,       other entries zero.
```

Both have Frobenius norm squared two and are transverse-traceless
relative to the supplied z direction. For |gamma h|<1 the scalar
quadratic form is positive. These source histories are not a proof
that noncommuting spin histories can be replaced by classical h.
The reference C=I is chosen; it has not been proved to be the
self-consistent ground-state stiffness of the coupled spin model.

The scalar is Gaussian, so its normalized influence is
Gamma[h]=(1/2)Tr log(M[h] M[0]^(-1)), with
M[0]=-partial_tau^2+omega^2. The exact second variation follows from

```
Gamma^(2)=-(gamma^2/4) Tr(G h V G h V),       G=M[0]^(-1).
```

The kernels below are zero-temperature response densities. The trace
log can first be defined at finite spatial volume and Euclidean duration
before taking those density limits.

For external momentum along z, h commutes with the transverse
derivatives, and the vertices are independent of q_z:

```
v_+(q)=sin^2 q_y-sin^2 q_x,
v_cross(q)=-2 sin q_x sin q_y.                            (4)
```

The overall vertex signs do not affect the diagonal response. Write
Gamma^(2)=(1/2) integral h(-p) Pi(p) h(p), and use the normalized
Brillouin-zone integral integral_BZ d^3q/(2pi)^3. The frequency integral
can be done exactly:

```
integral dnu/(2pi) 1/[(nu^2+a^2)((nu+Omega)^2+b^2)]
             =(a+b)/[2ab((a+b)^2+Omega^2)] = J_E.        (5)
```

Here a=omega_(q-p e_z/2), b=omega_(q+p e_z/2), and

```
Pi(Omega,p)=-(gamma^2/2) integral_BZ v(q)^2 J_E.          (6)
```

The mixed +/cross kernel vanishes by transverse reflection and exchange
symmetry. The action in (2) is linear in the source C, so there is no
second-order source contact vertex in this convention. A nonlinear
metric parameterization can add such vertices; it must be specified
and cannot be silently substituted for (2).

## 4. Positive induced derivatives and a strict speed inequality

Expansion of (6) gives

```
Pi(Omega,p)=r_ind+Z_tau Omega^2+Z_z p^2+o(Omega^2+p^2),
r_ind=-(gamma^2/8) integral_BZ v^2/omega^3,
Z_tau=(gamma^2/32) integral_BZ v^2/omega^5,
Z_z=(5 gamma^2/32) integral_BZ v^2 sin^2 q_z/omega^7.    (7)
```

The temporal formula follows immediately from (5). For the spatial
coefficient, differentiate the bubble at p=0 and integrate by parts
in periodic q_z. Since v is independent of q_z, the second derivative
of the bubble is minus the integral of v^2 (partial_qz G)^2. This
gives the positive expression for Z_z after integrating frequency.
Both derivative coefficients are strictly positive.

A second periodic integration by parts yields the decisive relation:

```
partial_qz [sin q_z/omega^5]
           =cos q_z/omega^5-5 sin^2 q_z/omega^7,
Z_z=(gamma^2/32) integral_BZ v^2 cos q_z/omega^5,
Z_tau-Z_z=(gamma^2/32) integral_BZ v^2(1-cos q_z)/omega^5>0.
```

Therefore

```
0 < c_ind^2=Z_z/Z_tau < 1.                              (8)
```

This is an analytical inequality for this regulator, not just a
numerical speed fit. The massless limits of the integrals are finite:
v=O(|q|^2), and their possible infrared singularities are integrable
in three dimensions. The integration-by-parts boundary around q=0
also vanishes. A regular common clock rescaling cannot remove (8)
relative to the scalar acoustic speed.

## 5. An independent infinite-volume evaluation

The three-dimensional integrals reduce to one-dimensional integrals.
Let I_n be modified Bessel functions and define

```
A_0(t)=exp(-2t) I_0(2t),
A_c(t)=exp(-2t) I_1(2t),
A_2(t)=exp(-2t) I_1(2t)/(2t),
A_4(t)=3 exp(-2t) I_2(2t)/(4t^2).
```

These are respectively the weighted angular averages of 1, cos q,
sin^2 q, and sin^4 q, with weight exp[-2t(1-cos q)]. The continuous
values at zero are 1,0,1/2,3/8. Define

```
W_+(t)=2[A_4 A_0-A_2^2],          W_cross(t)=4 A_2^2.
```

For either polarization,

```
integral_BZ v^2/omega^r
 =1/Gamma(r/2) integral_0^infinity dt
       t^(r/2-1) exp(-m^2 t) W(t) A_0(t).               (9)
```

For the cosine-weighted integral in Z_z replace A_0 by A_c. This
supplies an independent adaptive quadrature rather than a finite-grid
extrapolation. The audit checks it against three-dimensional midpoint
quadrature through 96^3 points. At m=0, gamma^2=1, one real scalar,
the resulting coefficients are:

| Shear | r_ind | Z_tau | Z_z | c_ind / c_scalar |
| --- | ---: | ---: | ---: | ---: |
| + | -0.0036945320 | 0.00047040549 | 0.00034219674 | 0.85290712 |
| cross | -0.0117819259 | 0.00097685472 | 0.00060093666 | 0.78433096 |

The unit coupling here specifies coefficient normalization; it is not
a claim that the strict positivity assumption |gamma|<1 has been
replaced by equality. At smaller nonzero gamma, multiply r and Z by
gamma^2; the loop-only speeds are unchanged. Additional identical
scalar species likewise multiply the coefficients, leaving those
speeds unchanged. Quadrature error estimates are not interval proofs.

## 6. What the linear poles actually establish

Promote one source h to a collective field and explicitly choose its
bare local quadratic coefficient r_0=-r_ind, with no added derivative
terms for the moment. This defines a mass-tuned Gaussian effective
model with inverse propagator K=Pi-Pi(0,0). It is an additional model
choice, not a conclusion about the original spin ground state.
At leading derivative order, after analytic continuation,

```
K_R(omega,p)=Z_z p^2-Z_tau omega^2+o(p^2+omega^2),
omega=c_ind |p|+o(|p|).                                  (10)
```

For the massless scalar, the exact two-particle threshold at momentum
p e_z is 2|sin(p/2)|. This follows from the triangle inequality for
the chord-distance form of (3); either scalar can carry zero momentum
at the infimum. By (8), the small-p root of (10) lies strictly below
that threshold.

This also follows from the unexpanded kernel. Below threshold,
replace +Omega^2 in (5) by -omega^2. K_R is strictly decreasing in
omega^2. At omega=0 its spatial difference is positive by the
autocorrelation inequality for G. The small-p expansion changes sign
at some fixed speed between c_ind and one. Consequently there is
a unique root in that interval, with -partial_(omega^2)K_R>0. The
infrared expansion is justified inside any cone omega/|p|<=1-eta:
the region |q| of order |p| contributes at order p^4, and away from
it the convergent second-derivative integrals give (7).

Eight root calculations with the unexpanded response verify the poles
and their positive kinetic residues. There is no scalar-pair damping
below threshold in this Gaussian construction. That statement does
not include interactions or decay channels of a dynamical tensor
sector that has not been constructed.

The scalar response itself has a two-particle continuum; the new poles
belong to the deliberately promoted and mass-tuned h propagator.
Thus there is no contradiction with the earlier
[two-phonon interaction calculation](INDUCED_GEOMETRY_INTERACTION.md),
which did not construct this critical collective denominator. Higher
terms in the effective potential, and fluctuations of the spin sector,
can change or preempt the proposed critical point. A continuous critical
phase and its poles in the complete microscopic model remain unproved.

For comparison, normalize h as an isolated spin transition expectation,
absorbing its polarization normalization into gamma. Its exact
uncoupled susceptibility is chi_0(Omega)=2mu/(Omega^2+mu^2) for gap mu.
A Gaussian susceptibility matching approximation would give

```
K(Omega,p)=(Omega^2+mu^2)/(2mu)+Pi(Omega,p),
mu/2+r_ind=0,
c_reference^2=Z_z/[1/(2mu)+Z_tau].                       (11)
```

This further reduces the speed. It is a reference approximation, not
a controlled proof at the critical spin coupling. Since the two
r_ind values in the table differ, one common bare spin gap cannot
make both shear channels critical in this approximation. Tuning the
smaller shift after the larger one has crossed zero would already
give a negative quadratic mass in the other channel.

## 7. Why this is not yet induced Einstein gravity

The two transverse shear projections are useful tests of a tensor
response. They are not proof that only two physical modes propagate.
For a general symmetric strain T, the complete temporal coefficient is
the Gram form

```
Z_tau(T,T)=(gamma^2/32) integral_BZ
                          [(sin q)^T T (sin q)]^2/omega^5. (12)
```

It is strictly positive for every nonzero T: a nonzero quadratic
polynomial cannot vanish for all sin q in an open cube. The six-dimensional
form has rank six, as independently checked in the audit. No first-class
constraints, lapse/shift equations, or gauge null directions have been
derived by integrating out this scalar. Additional constraint fields
could alter the physical reduction, but they would need to be supplied
and verified.

The unequal masses and speeds also matter. The regulator has cubic
spatial symmetry; it does not require the two inequivalent shear
representations to have identical response. The bare scalar recovers
speed one at long wavelength, while the induced derivative coefficients
integrate over the whole Brillouin zone. Their infrared contribution
below an internal cutoff q_* scales as q_*^2; ultraviolet structure
therefore affects the leading p^2 coefficients even as external p
tends to zero. An irrelevant correction to the free scalar dispersion
need not be irrelevant to the induced tensor kinetic coefficients.

Sakharov-style induction is an established possible mechanism; see
[Visser](https://arxiv.org/abs/gr-qc/0204062) and the explicit scalar/fermion
calculation of [Chaichian, Oksanen, and Tureanu](https://arxiv.org/abs/1805.03148).
Covariant heat-kernel calculations organize matter determinants into
geometric terms, as described by [Vassilevich](https://arxiv.org/abs/hep-th/0306138).
Applying that conclusion here would require a covariant metric coupling,
measure, and regulator that have not been established. The positive
local action (2) and the existence of an acoustic cone do not establish
those assumptions.

One could add independent gradient and mass counterterms to match the
two speeds to the scalar speed. That would be an additional tuning,
and it would still not derive gravitational constraints or universal
coupling. The exact strict inequality (8) rules out automatic common-cone
matching by this scalar-only induction prescription with no such terms.

## 8. Consequence for the TOE construction

This provides a concrete source of temporal and spatial tensor response,
and a sharply specified collective-wave candidate after mass tuning.
It is a different, unconstrained strain model from the fixed compact
tensor code, so it does not evade the earlier cubic-wave theorem while
keeping that theorem's hypotheses intact. Imposing the old checks on
these new interactions would require another calculation.

The next induced-gravity candidate must demonstrate the missing
covariance and constraint structure at the microscopic level or in a
controlled limit. It must explain the mass protection, the common
matter/tensor cone, the removal of extra strain modes, and the nonlinear
volume/trace balance identified in the preceding benchmark. The current
calculation establishes none of those by assumption or by relabeling
shear waves as gravitons. Einstein emergence, quantum state selection,
spacetime emergence, and the full TOE remain open.

## 9. Reproduction and scope

```sh
OPENBLAS_NUM_THREADS=1 python3 -W error::RuntimeWarning scripts/induced_tensor_dynamics_audit.py
```

The [script](scripts/induced_tensor_dynamics_audit.py) writes
[the source-hashed report](data/induced_tensor_dynamics_audit.json).
Checks include exact stencil and integration-by-parts identities,
six-component Gram nondegeneracy, sixteen independent frequency
integrals, two independent methods for the loop coefficients, static
vacuum-energy and temporal-response differences, and eight tuned
Gaussian pole calculations. No new Lean theorem, thermodynamic spin
phase proof, or microscopic graviton pole is claimed.
