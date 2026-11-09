# Uniform field response and the collective-geometry stability test

Date: 2026-09-10

The field-induced geometry response can now be bounded independently of
spatial volume, including the full nonlinear Gaussian influence. This
turns the earlier determinant expansion into a uniform approximation
of free energy per switch. It also proves that, at the repository's
parameters, the optimal state without geometry-field entanglement has
a unique stable occupancy profile. Its self-consistent occupancy
response has no zero-frequency instability in this sector.

These are different scopes. The influence and free-energy error bounds
apply to the full geometry history sum of the large-spin model. The
stability theorem applies to its factorized variational sector. An
explicit finite-time-grid calculation below sums interacting histories
without factorizing them, but does not establish their zero-temperature
thermodynamic phase. No graviton or Einstein equation is derived.

## 1. A local certificate controls the global field differences

Keep the model and notation of
[the induced-interaction calculation](INDUCED_GEOMETRY_INTERACTION.md).
For each switch define the two source columns
`u_s=e_a-e_d`, `v_s=e_b-e_c`, and collect them into U. Their
supports are disjoint between switches, so `U^T U=2I`. With
`J_x` block diagonal, having blocks `[[0,x_s],[x_s,0]]`,

```
V_x=sum_s x_s V_s=kappa U J_x U^T.                  (1)
```

Surround each switch by a 4 by 3 by 3 box: the switched path runs
along its central x line. These 36-vertex boxes fit disjointly inside
the existing cells of side at least twelve. Use only internal edges;
the omitted boundary edges have nonnegative energy.

For the old and switched box Laplacians L_0,L_1, solve the rational
network equations `L_z Phi_z=[u,v]`, fixing one potential to zero.
The audit supplies all 36 rows of each exact rational solution and
checks both equations and the energy identity. The resulting matrices are

```
R_0=Phi_0^T L_0 Phi_0 = (1/713)[[495,117],[117,261]],
R_1=Phi_1^T L_1 Phi_1 = (1/785)[[495,-45],[-45,261]]. (2)
```

Both are at most I. For example their complementary quadratic forms
have numerators

```
713 w^T(I-R_0)w=117(w_1-w_2)^2+101w_1^2+335w_2^2,
785 w^T(I-R_1)w=45(w_1+w_2)^2+245w_1^2+479w_2^2.
```

Cauchy-Schwarz in the edge-energy inner product therefore gives
`||[u,v]^T q||^2<=q^T L_z q`. Convex interpolation preserves this
inequality for every occupancy m_s in [0,1]. Sum the disjoint boxes
and restore the omitted positive bonds to obtain the global form bound

```
U U^T <= L(m),    A(m)=kappa L(m),
for every m in [0,1]^M and every carrier volume.     (3)
```

This certificate does not impose a gap on the acoustic field. It
controls the relative field coordinates actually coupled to geometry.

## 2. Uniform static response, with all source amplitudes retained

On the relative field space, define
`G_nu(m)=(chi nu^2+A(m))^(-1)`, with chi=1/(6 kappa).
Using (3), inverse order, and U^T U=2I gives

```
0 <= U^T G_nu(m) U <= 2/(chi nu^2+2kappa) I.        (4)
```

At zero frequency, add a positive scalar to both comparison operators
and take it to zero after compression onto U. This avoids inverting
the constant mode or the null space of U U^T.

The exact Gaussian field ground energy at this static occupancy is
`E_phi(m)=(1/2)Tr sqrt(A(m)/chi)`. Its gradient is the vacuum force
mu_s(m), and its negative Hessian is the positive matrix W(m) from
the preceding note. For a real source vector x,

```
x^T W(m)x=(1/(2pi)) integral_0^infinity
          Tr[(V_x G_nu(m))^2]d nu.
```

The Hilbert-Schmidt norm inequality and `Tr J_x^2=2||x||^2` bound
this expression by
`(kappa^2/pi)||x||^2 integral_0^infinity [2/(chi nu^2+2kappa)]^2 d nu`.
Evaluating this elementary integral proves

```
0 <= W(m) <= C_infinity I,
C_infinity=(sqrt(3)/2)kappa.                        (5)
```

The same compressed resolvent bound, now on the first derivative,
gives `|mu_s(m)|<=sqrt(3)kappa`. These estimates hold uniformly in
volume and throughout the full occupancy cube, not only at the
midpoint or to quadratic order in a small source. At kappa=0.25,
`C_infinity=0.2165063509...`.

## 3. The full time-dependent influence has a bounded curvature

Let beta be finite Euclidean duration and let m_s(tau) be any
measurable functions in [0,1]. For
`M_m=-chi partial_tau^2+A(m(tau))`, the time version of (4) is

```
0 <= U^T M_m^(-1) U <= R_beta tensor I,
R_beta=2(-chi partial_tau^2+2kappa)^(-1).            (6)
```

The source map U acts at each time. Let Gamma[m] be the exact
Gaussian determinant influence of the previous note. For an allowed
real variation eta_s(tau), differentiating that determinant gives

```
-D^2 Gamma[m](eta,eta)
 =(1/2)Tr[M_m^(-1) V_eta M_m^(-1) V_eta] >= 0.
```

This Hessian is uniformly bounded on the entire history domain:

```
0 <= -D^2 Gamma[m](eta,eta)
  <= C_beta integral_0^beta sum_s eta_s(tau)^2 d tau,
C_beta=(kappa^2/beta)sum_(n in Z)
                 4/[chi(2pi n/beta)^2+2kappa]^2
 = C_infinity [coth x+x csch^2 x],
x=beta sqrt(12)kappa/2.                            (7)
```

To justify the noncommuting step, if 0<=K<=R then
`||K^(1/2) J K^(1/2)||_HS<=||R^(1/2) J R^(1/2)||_HS`:
factor the left side through the contraction K^(1/2)R^(-1/2).
Regularization handles its domain before taking the limit. In (6),
R is scalar in the source indices. The remaining trace is a convolution
of eta_s with the nonnegative square of its time kernel. Young's
inequality bounds it by its time integral, which is the Matsubara sum
in (7). The identity for that sum follows by differentiating
the scalar periodic oscillator sum. As beta increases, C_beta tends
to C_infinity; as beta tends to zero, its leading behavior is 1/beta.

Equation (7) is a bound on the full nonlinear influence, with no
oscillator occupation cutoff. It is not, by itself, a uniqueness or
mixing theorem for the discrete switch-history measure.

## 4. Controlled intensive errors in the interacting partition function

Use the previous midpoint operator S and r=1/sqrt(3). Applying (7)
at the midpoint with eta_s=z_s-1/2 gives, for every physical history,

```
Tr(S^2) <= C_beta beta M/2.                        (8)
```

Indeed the determinant Hessian is Tr(S^2)/2 and every eta_s^2=1/4
almost everywhere. Insert (8) into the earlier series-tail estimate.
If Gamma_K retains powers through K>=2, then

```
|Gamma-Gamma_K| <= beta M epsilon_K(beta),
epsilon_K(beta)=C_beta r^(K-1)/[4(K+1)(1-r)].        (9)
```

The original geometry path weights are positive. Multiplying each
weight by exp(-Gamma) or exp(-Gamma_K), then summing, yields

```
exp(-beta M epsilon_K) Z_K <= Z <= exp(beta M epsilon_K) Z_K,
|f-f_K| <= epsilon_K,
f=-(1/(beta M))log Z.                              (10)
```

Common reference-field factors can be included or canceled in both
partition functions. This bound is uniform in spatial volume. It
controls the *full interacting* geometry free energy per switch even
though the remaining history sum is not generally evaluated here.
At kappa=0.25 the limiting beta->infinity error at order twelve is
about 2.34e-5 energy units per switch; higher orders decrease geometrically.
The limiting bound is a statement about the limsup of the free-energy
error. It does not presuppose a separate time-pressure limit for every
truncated nonlocal history model or prove a spatial thermodynamic limit.

A small intensive free-energy error does not bound the gap or identify
a phase transition. Different long-distance spectra can have close
energy densities. Thus (10) makes subsequent computations controllable
without certifying gravitational dynamics.

## 5. Solve the optimal geometry-field factorized sector

Consider states with no entanglement between geometry and field, while
allowing arbitrary correlations within the field. At fixed occupancies
m_s, each spin minimizes its transverse energy with
`<X_s>=2sqrt(m_s(1-m_s))`. At fixed geometry expectations the field
Hamiltonian is quadratic, and its optimal state is its full Gaussian
vacuum. Minimizing over this sector is therefore exactly equivalent to
minimizing

```
F_var(m)=Lambda sum_s [-2b sqrt(m_s(1-m_s))+d m_s+(Omega-d)/2]
           +E_phi(m).                             (11)
```

No oscillator occupation truncation enters (11). Entangling geometry
spins with each other cannot improve the optimum while the entire
geometry remains factorized from the field: at fixed field state the
spin Hamiltonian is a sum of independent on-site terms.

The on-site spin curvature is

```
Lambda b/[2(m_s(1-m_s))^(3/2)] >= 4 Lambda b.
```

Together with (5), this proves the global Hessian bound

```
D^2 F_var >= delta I,
delta=4 Lambda b-C_infinity.                       (12)
```

When delta>0, the continuous energy has a unique minimum. Its divergent
inward spin derivative and bounded mu_s put that minimum in the
interior. Translation symmetry then forces equal occupancies on
equivalent periodic cells. There is no first-order multiplicity or
vanishing occupancy curvature anywhere in this variational problem.
The sufficient condition at b=0.4,kappa=0.25 is
`Lambda>0.1353164693...`; at Lambda=1, delta=1.3834936491....
Failure of this sufficient condition is not evidence of a transition.

The minimum obeys the self-consistent equations

```
B_s=Lambda d+mu_s(m),
R_s=sqrt(B_s^2+4 Lambda^2 b^2),
m_s=(1-B_s/R_s)/2.                                (13)
```

The right side is a contraction in Euclidean norm with constant
`q=C_infinity/(4 Lambda b)<1`: its scalar response to B_s is
at most 1/(4 Lambda b), and the derivative of mu is -W. Thus
iteration converges from any occupancy vector, with the a posteriori
distance bound `||m-m_*||<=||m-T(m)||/(1-q)`.
The audit evaluates mu and W with the same finite-carrier resolvents
used for the exact Gaussian determinant, retaining the vacuum-force
shift. On the 3,456-vertex two-cell carrier at Lambda=1, the optimized
occupancy is approximately 0.3138181734, compared with the uncoupled
value 0.3193394661. Its vacuum-force shift is about 0.01097308966 and
the smallest variational Hessian eigenvalue is about 1.955650819.
Reported numerical residuals are floating-point checks, not
interval-certified real-number values.

## 6. The corresponding collective fluctuation test

Linearizing time-dependent factorized evolution gives the independent
biased-spin susceptibility

```
C_spin,s(i nu)=2 R_s m_s(1-m_s)/(R_s^2+nu^2).
```

The field response in the optimized Gaussian vacuum has
`0<=Pi_m(i nu)<=W(m)`: each two-phonon spectral term has a
positive matrix weight multiplied by
`2E/(E^2+nu^2)<=2/E`. The inverse self-consistent response is

```
K_var(i nu)=C_spin(i nu)^(-1)-Pi_m(i nu)
           >= delta I.                            (14)
```

The zero-frequency spin inverse equals its curvature in (11), and
increasing nu only raises it. This rules out a zero-frequency
collective occupancy instability in this factorized fluctuation test,
uniformly in volume. It does not give a spectral gap of the full
Hamiltonian. In particular the two-phonon continuum can give geometry
observables arbitrarily low-energy weight in an infinite system;
a finite inverse static susceptibility is compatible with that fact.

## 7. Sum interacting histories as an independent finite test

The audit also sums every two-switch history on time grids with
four, six, and eight time slices: 256, 4,096, and 65,536 histories.
The spatial carrier has 3,456 vertices and the Gaussian field is
integrated without an occupation cutoff. Each history uses the exact
two-level transfer matrix `exp(-Delta tau G_s)` and the full Gaussian
determinant of the specified discrete-time field action. Low-rank
source reduction keeps its determinant at dimension 4 times the
number of time slices.

For each grid the audit computes the complete partition sum, average
occupancy, and covariance of time-averaged occupations. It compares
orders two, four, eight, and twelve with the full determinant sum.
The grid analogue of (7), using the discrete kinetic frequencies,
supplies a rigorous scalar truncation bound of the form (10), checked
against all enumerated histories and partition functions.

This calculation retains correlations between geometry and field in
that time-grid model. It is distinct from (11). It runs at finite
inverse temperature beta=2, so its occupations should not be confused
with the zero-temperature variational minimum. No numerical error rate
for removing the time grid, zero-temperature extrapolation, or large
spatial-volume phase is claimed. These small history sums cannot settle
the existence of an interacting tensor mode.

## 8. Implication for the proposed theory

The midpoint expansion now has an explicit intensive error bound,
and the nonlinear field response has a local supplier of uniform
control. The simplest self-consistent collective sector is stable at
the current parameters after including its vacuum-force shift. It
does not provide the desired massless geometry mode.

The remaining possibility in this Hamiltonian is an entangled
collective phase beyond factorization. Proving or excluding it requires
control of the interacting history correlations or spectrum; it cannot
be inferred solely from determinant convergence, convexity of (11), or
a finite-volume partition sum. A gravitational completion would still
need an isolated tensor mode, its constraints, universal matter coupling,
the physical spin-1/2 phase, and a controlled spacetime limit.

The executable audit contains the exact rational local certificates,
nonlinear response and fixed-point checks, periodic-oscillator sums,
and exhaustive finite-time-grid history sums. Twelve supporting Lean results
check the certificate inequalities, curvature bounds, contraction
estimate, and scalar error algebra. The operator, Gaussian, and
variational arguments above remain analytic proofs.
