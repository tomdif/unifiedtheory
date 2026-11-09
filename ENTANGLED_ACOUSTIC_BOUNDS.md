# Acoustic spectral weight in the entangled geometry–field model

Date: 2026-09-10

The large-spin Hamiltonian has a robust acoustic energy scale even when
geometry and the field are fully entangled and the geometry gap is finite.
This follows directly from a bound valid for every geometry history. No
factorization, small interaction expansion, oscillator occupation cutoff,
or fast-geometry limit is needed for the analytical result.

For a normalized nonconstant Fourier mode with reference Laplacian
eigenvalue lambda, put `omega_0=sqrt(kappa lambda/chi)`, where
`chi=1/(6 kappa)`. At least half of its **energy-weighted** field spectral
measure lies in `[omega_0/4,4 omega_0]`. Thus a fixed fraction of this
response has energy of order wave number. This is a spectral-weight
theorem, not by itself a proof of a sharp phonon pole or a wave equation.
A separate exact invariant-subspace argument below does prove sharp free
waves for momenta transverse to the switch direction.

The finite-volume relative-field ground state is also unique, even under
field parity, and necessarily entangled across geometry and field for a
nontrivial switch and positive transverse mixing. None of these statements
settles uniqueness of the infinite-volume geometry phase. The carrier,
dimension, large-spin extension, and clock calibration remain supplied;
Einstein gravity and a physical TOE are not established.

## 1. Hamiltonian and finite-volume ground state

Use exactly the Hamiltonian of the
[preceding calculation](COLLECTIVE_GEOMETRY_STABILITY.md):

```
H = Lambda G + pi^T pi/(2 chi) + q^T A(n) q/2,
A(z)=kappa L(z),  chi=1/(6 kappa),
G=sum_s[-b X_s+d n_s+(Omega-d)/2],
Omega=sqrt(d^2+4b^2),  Lambda>0, b>0, kappa>0.
```

Remove the free spatial center-of-mass canonical pair throughout. All
switches annihilate the constant spatial vector. On this relative space
the previously proved graph comparison is

```
(kappa/4) L_0 <= A(z) <= 4 kappa L_0.              (1)
```

It holds for every configuration, and for all convex interpolations of
the occupancies. The constants do not grow with spatial volume.

At any fixed connected finite carrier, L_0 is positive on the relative
space. The diagonal matrix potential therefore confines all relative
coordinates quadratically. The off-diagonal spin operator is bounded
at fixed volume. The resulting self-adjoint matrix Schrodinger operator
has compact resolvent and a ground state.

Its heat kernel is positivity improving. Indeed, expand in spin flips:
any two switch configurations are joined by a sequence of flips, every
flip has positive weight Lambda b, and each intervening scalar confining
heat kernel is strictly positive. The positive sum has a strictly
positive kernel between every pair of configurations. The usual
Perron–Frobenius argument for the compact heat semigroup gives a unique
ground state whose components are strictly positive. Field parity
`(q,pi)->(-q,-pi)` commutes with H. Uniqueness and positivity force its
ground-state eigenvalue to be +1.

This ground state cannot factor as `psi_z(q)=c_z phi(q)` when some
`V_s=A(z+s)-A(z)` is nonzero. Positivity makes every c_z and phi positive.
Divide the eigenvalue equations by c_z phi and subtract equations for
configurations differing only at s. The common kinetic term cancels,
leaving `q^T V_s q/2 + constant = 0` for every relative q. A nonzero
quadratic form cannot be constant. This contradiction proves entanglement;
it supplies no volume-uniform lower bound on its amount.

## 2. Exact Gaussian conditioning, without factorizing the quantum state

At finite inverse temperature beta the spin-flip path representation
has positive weights. Conditional on the **entire** periodic geometry
history z(tau), the relative field is centered Gaussian with precision

```
M_z=-chi partial_tau^2+A(z(tau)).
```

The marginal geometry weight includes the complete Gaussian determinant.
It is the interacting history measure, denoted P_beta. Consequently the
exact Euclidean field covariance, as a quadratic form on time-dependent
relative-field sources, is

```
C_beta = E_(P_beta)[M_z^(-1)].                     (2)
```

This is conditioning in a positive path integral, not a separability
claim about the quantum density matrix. Define

```
M_-=-chi partial_tau^2+(kappa/4)L_0,
M_+=-chi partial_tau^2+4 kappa L_0.
```

Equation (1) holds at every time. Inverse order followed by averaging
over the exact, correlated history law proves

```
M_+^(-1) <= C_beta <= M_-^(-1).                   (3)
```

No geometry correlation estimate is required. These are quadratic-form
bounds; they do not assert entrywise bounds for signed position-space
correlations. They also do not bound the geometry-occupation covariance.

For a real source j let `X_j=integral j(tau)^T q(tau) d tau`. The same
argument controls the whole moment-generating function:

```
exp(<j,M_+^(-1)j>/2) <= <exp X_j>
                         <= exp(<j,M_-^(-1)j>/2). (4)
```

In particular linear field observables have uniform Gaussian upper
tails with the comparison variance. For
`v_z=<j,M_z^(-1)j>`, exact Gaussian conditioning also gives

```
<X_j^4>-3<X_j^2>^2 = 3 Var_(P_beta)(v_z) >= 0.    (5)
```

Thus the covariance bounds do not license replacing the interacting
field measure by one Gaussian. Equation (5) identifies precisely one
contribution that such a replacement would discard.

## 3. Ground-state covariance and spectral sum rule

Let f be real, orthogonal to spatial constants, and normalized, with
`L_0 f=lambda f`, lambda>0. Set Q_f=f^T q. The averaged history measure
is stationary in Euclidean time. Evaluating (3) on a Matsubara source
and then taking beta to infinity at **fixed finite volume** gives

```
1/[chi(nu^2+4 omega_0^2)] <= C_f(i nu)
              <= 1/[chi(nu^2+omega_0^2/4)],
omega_0^2=kappa lambda/chi.                       (6)
```

Compact resolvent, a unique ground state, and quadratic confinement
justify this finite-volume ground-state limit, including the unbounded
linear coordinate insertions. One can equivalently use the ground-state
Lehmann representation below. No uniform thermodynamic convergence is
asserted by taking this limit.

Integrating (6) over real nu gives the equal-time bounds

```
1/(4 chi omega_0) <= <Q_f^2> <= 1/(chi omega_0).   (7)
```

For excitation energies E_a=E_a(total)-E_0>0 define
`dS_f(E)=sum_a |<a|Q_f|0>|^2 delta_(E_a)(dE)`.
Parity makes <Q_f>=0. The Lehmann formula and canonical double commutator
are

```
C_f(i nu)=integral 2E/(nu^2+E^2) dS_f(E),
integral 2E dS_f(E)=<[Q_f,[H,Q_f]]>=1/chi.         (8)
```

Indeed `[H,Q_f]=-i P_f/chi`; all coordinate potentials and geometry
operators commute with Q_f. The canonical pair is normalized because
f is a unit vector in the relative space. Confinement permits these
identities on the ground state by coordinate cutoffs and closure.

The measure `dmu_f(E)=2 chi E dS_f(E)` is therefore a probability measure.
Two consequences of (6) are

```
integral E^(-2) dmu_f <= 4/omega_0^2,
integral E^2 dmu_f <= 4 omega_0^2.                 (9)
```

The first is (6) at nu=0. For the second, write t=nu^2 and use the
**lower** covariance bound:

```
integral t E^2/(t+E^2) dmu_f
 =t[1-t chi C_f(i sqrt(t))]
 <=4 omega_0^2 t/(t+4 omega_0^2).
```

Monotone convergence as t increases proves the second inequality in
(9), without assuming a finite third spectral moment in advance.

## 4. A finite fraction of the response must be acoustic

Markov's inequality applied to the two moments in (9) gives, for
0<alpha<R,

```
mu_f(E<alpha omega_0) <= 4 alpha^2,
mu_f(E>R omega_0) <= 4/R^2,
mu_f([alpha omega_0,R omega_0])
                         >=1-4 alpha^2-4/R^2.    (10)
```

In particular

```
mu_f([omega_0/4,4 omega_0]) >= 1/2.               (11)
```

The corresponding unweighted spectral measure in this interval is at
least `1/(16 chi omega_0)`. Equation (7) then shows that the interval
carries at least **1/16 of the total unweighted field spectral weight**.
The constants are conservative.

There is also a variational excitation bound. The trial vector Q_f|0>
is orthogonal to |0>, and (7)–(8) give

```
gap(H) <= <Q_f(H-E_0)Q_f>/<Q_f^2>
        =1/[2 chi <Q_f^2>] <= 2 omega_0.           (12)
```

For a cubic reference torus,
`lambda(k)=4 sum_i sin^2(k_i/2)` and hence
`omega_0(k)~sqrt(6) kappa |k|`. The constants in (6)–(12) are independent
of volume, Lambda, b, and d (positivity of Lambda b is used for the
unique finite-volume ground state). Along growing carriers the field
response has a fixed fraction of its spectral weight on a linear energy
scale; the total spectral gap has an upper bound of order inverse size.
There may be still lower-energy geometry excitations. No matching lower
bound for the full gap is proved.

At kappa=1/4 the reference slope is `sqrt(6)/4=0.612372...`.
The interval in (11) has slopes 0.153093... and 2.449490... at small k.
These are response bounds, not measured sound speeds or light cones.

## 5. An exact transverse wave sector at finite geometry gap

The full-carrier audit revealed an exact exception to the generic pole
question. Every switch changes only x-directed bonds, with all four
vertices at the same y,z. For any field profile independent of x,
`u_s^T f=v_s^T f=0`, so `V_s f=0` for every switch. The reference
Laplacian preserves this subspace.

More explicitly, on a torus of size L_x by L_y by L_z define the isometry

```
(T h)(x,y,z)=h(y,z)/sqrt(L_x).
```

It obeys `T^T T=I`, `U^T T=0`, and

```
A(z) T = kappa T L_yz,  for every z,              (13)
```

where L_yz is the two-dimensional square-torus Laplacian. Because A(z)
is symmetric, the orthogonal complement is invariant too. The canonical
kinetic form respects this orthogonal splitting. After removing the
single spatial constant, the **full quantum Hamiltonian** therefore
splits as a tensor sum

```
H = H_transverse tensor I + I tensor H_coupled,
H_transverse=P^T P/(2 chi)+(kappa/2)Q^T L_yz Q.    (14)
```

The geometry operators belong to H_coupled. This tensor splitting does
not factorize geometry from the coupled part of the field, whose ground
state remains entangled by Section 1. It extracts a free field factor
that the switches cannot see.

For a transverse Fourier eigenmode with nonzero k=(0,k_y,k_z), the exact
Heisenberg equations close:

```
dQ_f/dt=P_f/chi,  dP_f/dt=-kappa lambda(k) Q_f,
d^2 Q_f/dt^2+omega_0(k)^2 Q_f=0.                  (15)
```

The exact ground-state response and spectral measure are accordingly

```
C_f(i nu)=1/[chi(nu^2+omega_0(k)^2)],
dS_f(E)=delta_(omega_0(k))(dE)/(2 chi omega_0(k)).  (16)
```

These are sharp free scalar wave poles for arbitrary positive finite
Lambda b, including the repository parameters. Mixed correlations with
the coupled factor vanish in the finite-volume ground state and Gibbs
state; the transverse field's connected higher Gaussian cumulants vanish.

There is a controlled transverse long-wavelength limit. Put
`c_0=sqrt(6) kappa`. The elementary sine remainder and the reverse
triangle inequality give, for p in the y,z plane,

```
|omega_0(a p)/a-c_0 |p|| <= c_0 a^2 |p|^3/24.     (17)
```

At bounded momenta this proves uniform convergence of the frequencies
and of the free wave propagators on bounded time intervals. The scalar
cosine propagator error is at most |t| times the right side of (17).
It supplies a two-dimensional transverse wave equation for the
normalized x-average field in the linear time scaling already used in
the [collective wave construction](COLLECTIVE_WAVE_SPACETIME.md).

The protected modes are spatially delocalized along x. They comprise
L_y L_z-1 of the L_x L_y L_z-1 relative oscillators, and occupy a
measure-zero plane in three-dimensional momentum space as all sizes
grow. This does not provide local propagation in all three spatial
directions, a universal Lorentzian cone, or gravitational tensor modes.
The dependence on the supplied orientation of the switches also makes
the limitation concrete.

## 6. Can the poles, or an underlying spin, generate gravity?

The exact factorization (14) answers one version of this question
negatively for the present Hamiltonian. For any protected occupation n,
`|n>_transverse tensor |ground>_coupled` has the same reduced geometry
state. Adding protected-wave energy cannot change any geometry
expectation. Equivalently,

```
Z[z] = Z_transverse Z_coupled[z],
delta log Z_transverse / delta z_s(tau) = 0.       (18)
```

Every higher geometry derivative also vanishes. Integrating out this
free factor cannot induce a geometry action. This is a precise failure
of universal backreaction for these excitations if the existing switch
variables are meant to encode the entire gravitational geometry.
It is not a theorem excluding gravity after the Hamiltonian is extended.

Making a tensor out of two protected waves does not cure that problem.
For instance `O=:partial_y phi partial_z phi:` has two transverse scalar
quanta in its vacuum spectral measure. In the transverse continuum,
with `c=c_0`, the Fourier convention
`integral dt d^2x exp(i omega t-ik.x)<O(t,x)O(0)>` gives

```
S_O(omega,0)=omega^3 theta(omega)/(256 chi^2 c^6). (19)
```

Wick contraction contributes
`2 p_y^2 p_z^2/(4 chi^2 c^2 |p|^2)` under the two-particle phase-space
integral. The angular integral is pi/4 and the energy delta function
sets |p|=omega/(2c), giving (19). An independent Euclidean calculation
gives the spatial integral `3/(256 pi chi^2 c^6 tau^4)`, equal to the
Laplace transform of (19) with measure d omega/(2pi).

At nonzero total momentum, the two-particle threshold is omega=c|k|.
The collinear pairs attaining it have zero two-dimensional momentum
measure, so the derivative-bilinear spectral measure has no isolated
atom there. Threshold singularities of the density do not change this.
The tensor indices describe the operator; they do not turn its free
two-particle continuum into a bound graviton. The whole free factor
continues to decouple from the switch variables at every order.

**A collective spin-2 mode is nevertheless a meaningful research target
for a modified coupled sector.** Spin-2 here refers to the transformation
of an excitation under physical spatial rotations; helicity +/-2 refers
to its two massless polarizations about the direction of propagation.
The geometry's two-level switch label, and the XY model's internal
spin variables, are not by themselves a demonstrated representation of
those emergent spatial rotations.

There are useful exact algebraic checks. For a single spin-1/2,
`S_i=sigma_i/2` and

```
(S_i S_j+S_j S_i)/2-delta_ij S(S+1)I/3=0.         (20)
```

There is no nonzero on-site traceless quadrupole to identify as the
missing tensor. A four-spin block does have an internal spin-2 multiplet:

```
(1/2) tensor (1/2) tensor (1/2) tensor (1/2)
      = 2 copies of spin 0 + 3 copies of spin 1 + spin 2.
```

The audit verifies the exact total-spin-squared eigenvalue
multiplicities `0:2, 2:9, 6:5`. This shows that collective tensor
representation content can exist. It does not select such a low-energy
phase, identify internal spin with spatial helicity, or remove the
unwanted massless polarizations. A traceless transverse tensor
`[[a,b],[b,-a]]` transforms its two components by angle 2 theta under
rotation theta; this double-angle algebra is also checked.

For perspective, [Gu and Wen](https://arxiv.org/abs/0907.1203) give a
controlled semiclassical construction of helicity +/-2 modes with
cubic dispersion and a less controlled proposed model with linear
dispersion. Their result is not a proof of a realistic nonlinear
gravitational completion, and its constraints are not already present
in this repository's XY Hamiltonian.

The model-building target suggested by this diagnostic is a collective
**spatial** tensor made from correlated bond variables, with constraints
that leave the two transverse traceless polarizations, a linear
low-energy pole, and nonzero universal coupling to the energy and
momentum of all matter modes. The constraints and pole must be derived
from a concrete modified Hamiltonian; adding tensor indices is
insufficient. Allowing switches in all spatial directions would break
the exact transverse decoupling, but alone does not supply these
constraints or prove a tensor phase. No such modification is silently
made in this calculation.

For a Lorentz-invariant massless spin-2 S-matrix with the relevant pole
structure, [Weinberg's soft-particle argument](https://journals.aps.org/pr/abstract/10.1103/PhysRev.135.B1049)
requires universal coupling. [Deser's construction](https://arxiv.org/abs/gr-qc/0411023)
explains the consistent nonlinear self-coupling once the suitable
linear spin-2 gauge theory is supplied. These are criteria and routes
for a candidate to satisfy, not derivations of the missing candidate
from our current microscopic model.

## 7. What the general bounds leave open

There is a direct counterexample to inferring a sharp pole from the new
bounds. Let the probability law of y=E^2 be uniform on
`[a,b]=[omega_0^2/4,4 omega_0^2]`. Its response is

```
C_cont(i nu)=log[(nu^2+b)/(nu^2+a)]/[chi(b-a)].    (21)
```

It obeys (6), the normalized sum rule, and the moment bounds, but has
no spectral atom at all. This is a counterexample to the inference from
the general estimates, not a claimed solution of the repository
Hamiltonian or its exactly protected transverse sector.
Mixtures with a continuum of slopes can also remain scale invariant.

For generic three-dimensional momenta, the next physical question is
whether the actual averaged inverse operator in (2) homogenizes to one
deterministic local wave operator with a nonzero pole residue. Its
two-point function must obey the bounds above, but the required
convergence and residue have not been supplied outside the protected
sector.
Independently, geometry-occupation mixing and possible even composite
collective modes remain open. The earlier Hessian bound on a smooth
history extension cannot simply be substituted for a theorem controlling
those discrete path correlations.

The useful general principle is **uniform stiffness protects an acoustic
energy scale through quantum geometry fluctuations**. Its hypotheses
are a positive geometry-history representation, a canonical quadratic
kinetic term, and configuration-wise ellipticity. Deriving these
hypotheses from the causal-order law is still separate work. They do not
generate the tensor degrees of freedom, gauge constraints, universal
coupling, or Einstein dynamics required for gravity.

## 8. Verification and relationship to established methods

The new audit checks the graph form bounds and all-history covariance
inequalities on the actual 3,456-vertex two-switch carrier. It sums the
correlated history weights on finite Euclidean grids and evaluates field
responses and the fourth-cumulant identity. The Gaussian field is
integrated without an occupation cutoff on these grids. Their finite
time discretization has not been assigned a continuum error rate.

An independent canonical three-relative-mode, one-switch path-motif
calculation diagonalizes increasing Fock compressions, checks the
Lehmann response, sum rule, spectral moments, and geometry-field purity.
This is a finite spectral cross-check, not an occupation-cutoff proof
or a simulation of the full carrier spectrum. A continuous spectral
example checks the limitation in (21). A full-carrier isometry check
verifies (13), and all enumerated histories have the same protected
transverse response. Exact spin matrices check (20) and the four-spin
decomposition; phase-space and Euclidean integrals independently check
the free composite spectrum (19). Fourteen Lean results check finite weighted-average,
cumulant, sum-rule, spectral-tail, invariant-mode, and closed-wave algebra; the
functional analysis and path-integral suppliers above are not formalized.

Positive spin-flip path representations and spectral moment bounds are
established tools. See [Hirokawa, Hiroshima and Lorinczi's spin-boson
path construction](https://arxiv.org/abs/1209.5521) and
[Boronat et al.'s spectral sum-rule analysis](https://arxiv.org/abs/cond-mat/9503129).
Those papers concern different Hamiltonians. The configuration-wise
comparison, conditioning argument, and constants used here are derived
for the specified repository model, rather than imported as theorems
about it.
