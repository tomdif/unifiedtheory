# Finite-gap geometry feedback and its gravitational limit

Date: 2026-09-10

The geometry can now be allowed to respond instead of being projected
onto a fixed state. In the large-spin branch, its response is exactly
solvable for prescribed field configurations. It produces a stable
nonlinear elastic potential, with a negative quartic correction at
leading inverse gap. A finite oscillator cutoff also admits an explicit
quantum effective operator with a spectral error bound through second
inverse-gap order. Neither calculation supplies a graviton: the bare
geometry response is spatially independent and has a nonzero gap.

This closes the finite-gap response calculation within the stated
regulators. It does not close the derivation of Einstein gravity or
prove the original spin-1/2 phase. The distinctions between static
minimization, quantum compression, and quantum elimination matter here.

## 1. Exact strain coupling in the existing extension

Start with equation (3) of [the collective-wave note](COLLECTIVE_WAVE_SPACETIME.md):

```
A_Lambda = Lambda G + H_ref + sum_s n_s F_s(q),
H_ref = 3 kappa pi^T pi + V_ref(q),
V_ref = (kappa/2) q^T L_0 q,
G_s = -b X_s + d n_s + (Omega-d)/2,
b=4rho>0, d=62J>=0, Omega=sqrt(d^2+4b^2),
p=(1-d/Omega)/2, alpha^2=p(1-p)=b^2/Omega^2,
Delta=Lambda Omega, Lambda>0.
```

For a switch replacing edges ab,cd by ac,bd and retaining bc,

```
F_s = (kappa/2)[(q_a-q_c)^2+(q_b-q_d)^2
                         -(q_a-q_b)^2-(q_c-q_d)^2]
    = kappa (q_a-q_d)(q_b-q_c).                       (1)
||grad F_s||^2 = 2 kappa^2[(q_a-q_d)^2+(q_b-q_c)^2].
```

The switch senses a quadratic relative-field strain. It has no coupling
linear in q, and a constant shift of every q leaves the interaction
unchanged. The carrier, chosen ordered orientation, and large-spin
limit are inherited hypotheses, not derived spacetime inputs.

## 2. Exact static response, a remainder bound, and stability

Fix real field coordinates q. The geometry matrices factorize over
switches. The lower eigenvalue of `Lambda G_s+F n_s` and its gap are

```
e_Lambda(F) = [Lambda Omega+F-R(F)]/2,
R(F) = sqrt((Lambda d+F)^2+4 Lambda^2 b^2)
     >= 2 Lambda b > 0.                              (2)
```

Thus no prescribed static strain closes the individual switch gap.
The exact active probability, by differentiation or its eigenvector, is

```
p_Lambda(F) = e_Lambda'(F)
 = [1-(Lambda d+F)/R(F)]/2,
e_Lambda''(F) = -2 Lambda^2 b^2/R(F)^3 < 0.           (3)
```

Positive strain reduces occupancy of the more costly switched graph.
At zero strain the expansion is

```
e_Lambda(F) = p F - alpha^2 F^2/Delta + r_3(F),
p_Lambda(F) = p - 2 alpha^2 F/Delta + r_2(F).         (4)
```

For `|F|<=eta Lambda Omega`, `0<=eta<1`, the reverse triangle
inequality gives `R(tF)>=(1-eta)Lambda Omega` for `0<=t<=1`.
Since `e'''(F)=6 Lambda^2 b^2(Lambda d+F)/R(F)^5`, Taylor's
integral remainder proves

```
|r_3(F)| <= b^2 |F|^3/[(1-eta)^4 Lambda^2 Omega^4],
|r_2(F)| <= 3 b^2 F^2/[(1-eta)^4 Lambda^2 Omega^4].  (5)
```

The leading feedback in the potential is therefore
`-alpha^2 sum_s F_s(q)^2/Delta`: a quartic field interaction.
It is not a new quadratic metric mode.

The exact static potential is globally stable:

```
V_ad(q) = V_ref(q)+sum_s e_Lambda(F_s(q))
        >= V_ref(q)/4 >= 0.                          (6)
```

Proof: `Lambda G>=0` and every graph in this carrier satisfies
`L_z>=L_0/4`. Apply the resulting matrix inequality at fixed q and
take its lowest eigenvalue. In contrast, the negative quartic
truncation is unbounded below along a direction with nonzero F_s.
It must only be used inside its small-strain regime. This is a
limitation of the truncation, not an instability of (2) or A_Lambda.

## 3. Quantum derivative terms cannot be discarded

Static minimization does not diagonalize the quantum kinetic energy.
Let `g_s(F)=(cos(theta_s/2),sin(theta_s/2))` be its real normalized
ground vector, with

```
theta_s=atan2(2 Lambda b,Lambda d+F_s),
d theta_s/d F_s = -2 Lambda b/R(F_s)^2.
```

Use the q-dependent isometry
`(W psi)(q)=[tensor_s g_s(F_s(q))] psi(q)`.
For smooth compactly supported psi, direct differentiation proves
the exact compressed quadratic form

```
W^* A_Lambda W = 3 kappa pi^T pi + V_ad(q) + U_BH(q),
U_BH = 3 kappa sum_s
          Lambda^2 b^2 ||grad F_s||^2/R(F_s)^4 >= 0. (7)
```

Here the real ground vectors have zero diagonal Berry connection;
their derivative norms give the displayed Born-Huang potential.
There are still off-diagonal derivative couplings to excited geometry.
The range of W is generally not invariant under A_Lambda. Equation
(7) is an exact compression and a variational construction, not the
exact reduced quantum evolution.

Near q=0, U_BH has the quadratic contribution

```
3 kappa b^2/(Lambda^2 Omega^4) sum_s ||grad F_s||^2.  (8)
```

Consequently the statement about a quartic *leading* correction is
an inverse-gap statement. It does not exclude quantum corrections to
the field stiffness at higher order. Quantum zero-point fluctuations
and their thermodynamic/continuum limits require additional control.

## 4. A bounded quantum elimination with explicit errors

To make the quantum approximation rigorous without asserting a norm
bound on unbounded oscillator operators, fix finite volume and a
finite total-occupation cutoff. Compress the polynomial field
operators to that space; denote them H_ref and F_s again. All products
in this section are products of these compressed matrices. In
particular `(P_m F P_m)^2` need not equal `P_m F^2 P_m`.

Write `H=Lambda G+V`, `v=||V||`, P for all geometry switches in their
unperturbed ground state, Q=1-P, and

```
A=PVP, B=PVQ, C=QVQ, D=Lambda QGQ >= Delta Q,
Dinv=D^(-1), beta=||B||, w=v+E_star.
```

Assume `Delta>w` and consider an exact eigenvalue `|E|<=E_star`.
The Q equation is invertible, P psi is nonzero, and the exact
Schur complement on P is

```
T(E) = A-B(D+C-E)^(-1)B^*,    T(E)u=E u.            (9)
```

Two resolvent identities give

```
||(D+C-E)^(-1)-Dinv|| <= w/[Delta(Delta-w)],
||(D+C-E)^(-1)-Dinv+Dinv(C-E)Dinv||
 <= w^2/[Delta^2(Delta-w)].                         (10)
```

For example the second remainder is
`Dinv(C-E)Dinv(C-E)(D+C-E)^(-1)`; bounding each factor proves
(10). Thus the first corrected operator is

```
H_1 = A-B Dinv B^*
    = H_ref+p sum_s F_s-alpha^2/Delta sum_s F_s^2,
dist(E,spec H_1) <= beta^2 w/[Delta(Delta-w)].       (11)
```

Only single-switch excitations connect P and Q, so the cross terms
in (11) vanish and each intermediate denominator is Delta.

A further energy-independent, self-adjoint operator improves the
spectral error by another inverse gap:

```
Z = I+B Dinv^2 B^* >= I,
K = A-B Dinv B^*+B Dinv C Dinv B^*,
H_2 = Z^(-1/2) K Z^(-1/2),
dist(E,spec H_2) <= beta^2 w^2/[Delta^2(Delta-w)].   (12)
```

Indeed the approximate eigenvalue equation is `(K-E Z)u=r` with
`||r||<=error ||u||`. Set `y=Z^(1/2)u`, use
`||Z^(-1/2)||<=1`, and apply the spectral residual bound. These
are spectral-distance estimates, not time-evolution bounds or a
claimed one-to-one eigenvalue matching theorem. For the positive
cutoff V inherited from the graph, its lowest dim(P) eigenvalues lie
in [0,v] by min-max; one can choose E_star=v and require Delta>2v.
The constants depend on the cutoff and volume. No removal of those
regulators follows from (10).

For one switch, expanding (12) at a fixed cutoff gives

```
H_2 = H_ref+pF-alpha^2 F^2/Delta
 + alpha^2/Delta^2 [(1-2p)F^3
                     +(1/2)[F,[H_ref,F]]] + O(Delta^(-3)). (13)
```

In the uncompressed differential algebra on smooth compactly
supported functions, `[F,[H_ref,F]]=6 kappa ||grad F||^2`.
Its coefficient in (13) agrees with (8); the cubic term agrees with
the next Taylor coefficient of (2). This is an algebraic agreement,
not a uniform remainder theorem for the unbounded field theory.
The general use of a gapped sector to construct effective quantum
Hamiltonians is developed rigorously by
[Bravyi, DiVincenzo and Loss](https://arxiv.org/abs/1105.0675).
The elementary estimates (9)-(12) are proved here with their own
finite-matrix hypotheses rather than importing a spin-system theorem
as an unbounded-boson bound.

## 5. Exact bare dynamical response: local, gapped, and retarded

Apply a prescribed small classical source `+sum_s f_s(t)n_s` to
the independent geometry in its product ground state. Use the
convention `delta<n_s(t)>=sum_r integral K_sr(t-t')f_r(t')dt'`.
The Kubo commutator can be evaluated in the two-level basis:

```
K_sr(t) = -i theta(t)<[n_s(t),n_r(0)]>
        = -2 delta_sr alpha^2 theta(t) sin(Delta t),
K_sr(omega) = -delta_sr 2 Delta alpha^2
                            /[Delta^2-(omega+i0)^2]. (14)
```

The static value is `-2 alpha^2/Delta`, exactly (4).
For a constant source switched on at zero,
`delta<n(t)>=-2 alpha^2 f(1-cos(Delta t))/Delta+O(f^2)`.
The audit compares this expression with exact two-level evolution.

Spatial Fourier transformation leaves (14) unchanged: its bare poles
are at +/-Delta for every wave vector, with no spatial propagation.
About classical q=0, F(q) is second order in the wave amplitude;
the switch response is second order and its force back on q is third
order. The classical linearized branches are therefore the existing
acoustic field and independent gapped switch oscillations.

These observations exclude a new *bare or classical linearized*
massless tensor branch in this model. They do not rule out every
possible interacting quantum phase: field-mediated correlations,
two-phonon continua, or composite bound states are not evaluated by
the independent-switch susceptibility. A gapless continuum in a
geometry correlator would also not by itself establish an isolated
spin-two pole with gravitational constraints and coupling.

## 6. What survives the smooth classical continuum test

Retain the previous normalization `q_v=a phi(av)`, linear clock
`t=a t_micro`, and fixed reference cell size ell. For a smooth affine
field along a switch, with slope u=partial_x phi,

```
F_s = 3 kappa a^4 u^2,
F_s^2 = 9 kappa^2 a^8 u^4.                           (15)
```

There are O(a^(-3)) switches in a fixed macroscopic volume, and
the macroscopic Hamiltonian is A_Lambda/a. Accordingly the leading
static nonlinear correction is of order `a^4/Lambda`. For a smooth
field with bounded gradients, the same bound follows from (1);
bounded periodic cell correctors preserve that power counting.

For affine test data the quartic density before a nonlinear cell
relaxation is explicitly

```
-9 alpha^2 kappa^2 a^4/(Lambda Omega ell^3) u^4.       (16)
```

It vanishes whenever the switch is fast in macroscopic units,
`Delta/a -> infinity`. Keeping (16) finite would require
`Lambda` of order `a^4`; then `Delta/a` tends to zero and F/Delta
is generally order one. Both fast elimination and a parametrically
small-strain quartic expansion would lose their justification.

This is a smooth classical power-counting test, not a quantum
renormalization theorem. In particular it cannot erase (8): the
Born-Huang compression evaluated on the same affine coordinates has
a quadratic density of order Lambda^(-2), whose leading value is
`60 kappa^3 b^2/(Lambda^2 Omega^4 ell^3) u^2`. That expression is
neither a homogenized stiffness nor the exact finite-gap quantum
continuum coefficient. The full coupled quantum limit remains open.

## 7. Consequence for the model

Restoring finite-gap switches gives calculable backreaction and quantum
corrections. The principle realized here is ordinary energy response:
strain changes the locally favored geometry, whose delayed response
feeds back into the field. It yields nonlinear elasticity. It does
not produce independent massless metric dynamics merely by keeping
Lambda finite.

A gravitational completion must supply a collective geometry sector
with spatial propagation, the appropriate tensor degrees of freedom
and constraints, and a common coupling to matter. An isolated spin-two
pole and its consistency conditions must be demonstrated in that
sector. Tuning local switch costs or declaring the acoustic stiffness
to be a metric does not supply those results. Additional geometry
interactions/constraints would be a model change; a proposed composite
route in the existing Hamiltonian instead needs a calculation of its
interacting spectrum. The present work establishes neither route.

The executable audit checks static eigenvalues and remainder bounds,
global stability versus failure of the quartic truncation, derivative
compression, retarded response, continuum power counting, and the
finite-matrix estimates (11)-(12) on two disjoint switch motifs with
eight oscillator coordinates. These motifs test the elimination
mechanism and are not a simulation of the entire cubic carrier.
Twelve supporting Lean results check scalar algebra and inequalities; the
operator and continuum arguments above are analytic proofs.
