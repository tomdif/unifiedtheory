# Deriving the actual continuum before calling it spacetime

Date: 2026-09-10

The regulated quantum-geometry model now has an actual controlled
long-wavelength continuum in its low one-probe band. Quantum geometry
remains active in the calculation. Its continuum equation is

```
i partial_t psi = -D_x partial_x^2 psi
                  -kappa(partial_y^2+partial_z^2) psi,
```

with a positive coefficient D_x determined by a joint geometry/probe
resolvent. This is a **Schroedinger continuum**, not yet Lorentzian
spacetime. Linear time scaling makes this shifted band freeze; quadratic
time scaling gives nontrivial evolution. A common finite microscopic
propagation bound was therefore insufficient to identify the clock
scaling or a relativistic light cone.

The result recovers the supplied spatial dimension in the low-energy
counting law. It does not select dimension, remove the reference lattice,
derive internal time, or rule out relativistic collective modes in
other sectors. In particular, quadratic dispersion near a particle-band
minimum is compatible with a massive particle's nonrelativistic regime.
The missing task is a derivation of the physical collective spacetime
sector, not a relabeling of this continuum as GR.

## 1. Keep the actual fluctuating Hamiltonian

Use the separated-switch carrier of
[the previous construction](PROJECTED_GEOMETRY_AND_LOCAL_DYNAMICS.md),
with one straight x-directed switch in every cell of side ell>=12.
Take a periodic array of K_x K_y K_z=M cells, N=M ell^3 vertices,
rho>0, J>=0, and kappa>0. Let

```
b=4rho, d=62J, Omega=sqrt(d^2+4b^2),
e_g=b+d/2-Omega/2,
p=(1-d/Omega)/2,
H_g=sum_s [b(I-X_s)+d n_s].
```

The graph-only ground state |g_M> is a product of positive one-switch
ground states with active probability p, energy M e_g, and excitation
gap Omega. Let L_z=6I-A_Gz. After subtracting the exact ground energy
of the one-probe Hamiltonian, the operator to analyze is

```
K_M = (H_g-M e_g) tensor I
      + kappa sum_z |z><z| tensor L_z.                   (1)
```

No replacement of the quantum switches by their mean occupancy has
been made. Since every G_z is connected and degree six, every L_z
annihilates the same normalized constant probe vector |1_N>.
Both terms of (1) are nonnegative. It follows that

```
|G_M> = |g_M> tensor |1_N>
```

is its unique zero-energy state. Uniqueness follows by first using the
kernel of H_g-M e_g, then the common constant kernel of the graph
Laplacians. The original one-probe ground energy is M e_g-6kappa, up
to the already displayed graph-compression constant.

## 2. A uniform energy-form comparison

For a selected path a-b-c-d, write
`x=f(a)-f(b), y=f(b)-f(c), z=f(c)-f(d)`. The old and new path energies are

```
E_old=|x|^2+|y|^2+|z|^2,
E_new=|x+y|^2+|y|^2+|y+z|^2.
```

The three-by-three comparison matrix has eigenvalues 1 and 2+-sqrt(3).
A simpler rational bound has the exact real-component certificate

```
3(4E_old-E_new)=(3x-y)^2+(3z-y)^2+y^2 >= 0.
```

Apply it separately to real and imaginary parts. The transformation
`(x,y,z)->(x+y,-y,y+z)` is an involution, so the reverse inequality
holds as well. Selected path supports are disjoint and all other edges
are unchanged. Therefore, as quadratic-form inequalities on the whole
probe space,

```
(1/4)L_0 <= L_z <= 4L_0,       for every z, every M.      (2)
```

The sharper constants are possible but unnecessary here. Equation (2)
is stronger than a comparison of shortest-path lengths: it controls
the energy of every complex field, and hence the joint quantum operator
in (1).

## 3. Spectral dimension and time scaling

Let lambda_j be the ordered eigenvalues of L_0, including lambda_0=0.
The min-max principle, (1), and (2) give, for the first N joint levels,

```
min(Omega,kappa lambda_j/4) <= E_j(K_M) <= 4kappa lambda_j.
```

For the lower bound, compare with the commuting sum
`H_g-M e_g+(kappa/4)L_0`. Geometry excitations in that comparison cost
at least Omega. For the upper bound use the trial space formed by the
geometry ground state tensored with the first reference probe modes.
Thus the first excitation satisfies

```
min(Omega,kappa lambda_1/4) <= gap(K_M) <= 4kappa lambda_1. (3)
```

On a cubic reference torus of side L,
`lambda_1=4 sin^2(pi/L)` lies between 16/L^2 and 4pi^2/L^2.
At fixed couplings the actual joint gap is consequently of order L^-2,
even though the geometry itself fluctuates and has a fixed gap.

For 0<E<Omega, eigenvalue counting gives

```
N_L0(E/(4kappa)) <= N_KM(E) <= N_L0(4E/kappa).            (4)
```

The reference eigenvalues are `2 sum_j(1-cos q_j)`. In increasing cubic
volumes, their count divided by N has low-energy leading term
`E^(3/2)/(6pi^2)`. Equation (4) therefore gives a three-dimensional
spatial counting exponent for this low joint band. This is an
operational recovery of the input dimension, not dimension selection.
It is also not a claim about the unrestricted trace of the full
exponentially large geometry Hilbert space: the energy window below
Omega is essential.

## 4. A joint Bloch band, including geometry excitations

The simultaneous translation of probe and geometry by a cell commutes
with (1). Decompose by this total cell momentum. Equivalently, place
the probe's cell at the origin, retain its ell^3 internal positions,
and express all switch bits relative to that cell. A probe hop across
a cell boundary translates the relative bit register. Dropping that
translation would give the wrong quantum model.

Use microscopic momentum k, so cell momentum is ell k. An internal
gauge transformation puts phase exp(i k dot displacement) on each hop.
Call the resulting fiber K_M(k). Its finite dimension is 2^M ell^3.
At k=0 the ground vector is the geometry product ground state times the
constant internal probe vector. The other fiber states have gap at least

```
delta=min(Omega,kappa sin^2(pi/ell)) > 0,                 (5)
```

independent of M. To prove (5), use (2): in the geometry ground sector,
zero total cell momentum leaves only the ell-cell internal reference
modes, whose first nonzero eigenvalue is 4sin^2(pi/ell). All other
geometry sectors cost at least Omega. The detour proof also applies
with the hop phases, since phases add along each two-step detour.

Every hop has reference length at most two and degree is six. For
complex k,

```
||K_M(k)-K_M(0)|| <= 6kappa(exp(2|k|_1)-1).
```

Choose the conservative analytic radius

```
r=(1/2)log(1+delta/(24kappa)).
```

On |k|_1<=r, the perturbation is at most delta/4. The resolvent contour
of radius delta/2 around zero therefore defines a unique analytic
eigenvalue epsilon_M(k), uniformly in volume. Real matrix coefficients
give epsilon_M(-k)=epsilon_M(k). Resolvent perturbation and Cauchy bounds
on each complex direction yield

```
epsilon_M(k)=k^T D_M k+R_M(k),
|R_M(k)| <= C |k|_1^4,   |k|_1<=r/2,
C=delta/r^4,
(kappa/4)I <= D_M <= 4kappa I.                           (6)
```

For the remainder, the contour bounds |epsilon_M| by delta/2. Odd Taylor
coefficients vanish; bounding the tail from degree four by the geometric
series at |k|_1/r<=1/2 gives exactly the displayed C. These constants
are deliberately conservative. The band argument uses standard
resolvent perturbation; periodic-graph effective-mass methods provide
related background in [Korotyaev and Saburova](https://arxiv.org/abs/1502.02989).
That paper is not invoked as a theorem for this interacting quantum
geometry fiber: equations (1)-(6) provide the needed suppliers here.

## 5. The effective spatial coefficient is not a mean-graph guess

All switches change only x-directed edges. For transverse momentum,
the same ground vector is an exact eigenvector:

```
epsilon_M(0,k_y,k_z)=2kappa(2-cos k_y-cos k_z)
```

near zero. The y and z first derivatives of K_M annihilate its ground
vector, and mixed second hop derivatives vanish. Consequently

```
D_M=diag(D_x,M,kappa,kappa).
```

Let g denote the normalized zero-momentum fiber ground vector, Q its
orthogonal complement, and

```
f=partial_kx K_M(0) g,
S_M=(K_M(0)|_Q)^(-1) Q.
```

Second-order perturbation gives the exact expression

```
D_x,M=kappa(1+6p/ell^3)-<f,S_M f>,
||f||^2=20kappa^2 p/ell^3.                              (7)
```

The first term counts the two removed length-one edges and two added
length-two edges per active switch. The second term includes virtual
probe and geometry excitations. In the relative-cell description f is
supported at the four internal path vertices and the origin switch.
Its vertex coefficients have squared sum 1+9+9+1=20. In the switch
excitation basis, n_0 acting on the vacuum creates only a vacuum part
and one excitation at the origin. This locality of f is also useful
for the volume limit.

At ell=12, rho=0.1, J=0.005, and kappa=0.25, the audited one-cell fiber
gives D_x approximately 0.25017127773, whereas D_y=D_z=0.25. The
resolvent correction is approximately 0.00010592667. A two-cell quantum
fiber gives the same displayed digits. Agreement at these volumes is
numerical evidence; the following separate argument supplies convergence.

## 6. Why the volume limit of D_M exists

Take periodic cell boxes growing in all three directions. Rotate each
switch into its ground/excited eigenbasis. The geometry energy after
its ground subtraction is exactly `Omega N_exc`. Use the infinite
tensor-product Hilbert space with product ground vacuum, whose dense
core consists of finitely many switch excitations, tensored with the
ell^3 internal probe positions.

In this relative-cell representation a probe hop either acts within
the internal cell or translates the switch register by one cell. Its
local controlled part reads the origin switch. Thus

```
K_infinity(0)=Omega N_exc+B_infinity,
0<=B_infinity,   ||B_infinity||<=12kappa.
```

This defines a self-adjoint operator on the number-operator domain by
bounded perturbation. Embed each finite box's excitation states into
this common space, extend its hopping by the identity on outside
switch factors, and keep `Omega N_exc` on all cells. On every finite
excitation vector, sufficiently large boxes agree with the infinite
hopping action: none of its finitely many excitations wraps around the
boundary in one step. Uniform boundedness then gives strong convergence
of B_M to B_infinity.

For a>12kappa, the Neumann expansion of
`(Omega N_exc+B_M+a)^(-1)` converges geometrically, uniformly in M.
Termwise strong convergence proves strong convergence of these shifted
resolvents. The same ground vector g and gap delta apply to all extended
operators and the limit. Write R_M=(K_M+a)^(-1). On Q,

```
S_M=sum_{n>=0} a^n R_M^(n+1) Q,
||tail after n=m|| <= (a/(a+delta))^(m+1)/delta.
```

This tail bound is uniform in volume, so S_M converges strongly to S_infinity.
The source f in (7) is the same finite-excitation vector at every size.
Hence

```
D_x,M -> D_x,infinity
 = kappa(1+6p/ell^3)-<f,S_infinity f>,
kappa/4 <= D_x,infinity <= 4kappa.                       (8)
```

This proves a unique coefficient for growing boxes, rather than choosing
a convergent subsequence of unrelated metrics. The construction retains
the reference cell, the geometry ground state, and the gapped-switch
Hamiltonian as inputs. No continuum geometry measure is inferred from it.

## 7. A controlled continuum propagator

Fix a physical spatial torus and let lattice spacing a tend to zero
while the number of cells grows. Allowed physical momenta p correspond
to microscopic k=a p. Identify a continuum Fourier mode with the
normalized lowest joint fiber eigenvector at that momentum. This is
an explicit low-band identification, including its geometry dressing.

For any fixed momentum cutoff |p|_1<=P, equations (6) and (8) imply

```
|epsilon_M(a p)/a^2-p^T D_infinity p|
 <= C a^2 P^4 + P^2 |D_x,M-D_x,infinity|.
```

The elementary bound on the difference of two real-frequency phases
therefore gives the propagator error on that band,

```
||U_a(t) J_a - J_a U_cont(t)||
 <= |t|[C a^2 P^4 + P^2 |D_x,M-D_x,infinity|] -> 0,       (9)
```

where `U_a(t)=exp(-it K_M/a^2)` and J_a is the stated Fourier-band
identification. The continuum generator is `-div(D_infinity grad)`.
The eigenprojection also approaches the product ground/internal constant
vector at order aP by its resolvent contour, but that simpler product
is not substituted for the exact dressed band in (9).

By contrast, using the linear time scaling `exp(-it K_M/a)` gives
`epsilon_M(a p)/a=O(a |p|^2)`. Its shifted low-band propagator tends
to the identity. Thus the nontrivial scaling of this band is z=2,
not the z=1 scaling of a massless relativistic mode. This is a statement
about this actual joint band, not about every excitation of the full
neutral many-body Hamiltonian or a possible massive relativistic completion.

## 8. The remaining spacetime requirement

The calculation has reconstructed a positive spatial propagation tensor
and a nontrivial continuum time scaling from the specified microscopic
Hamiltonian. It has also shown why calling that result spacetime would
be premature. Spatial dimension and the reference interaction structure
were supplied; the evolution parameter was external; the resulting
field equation is first order in time with quadratic dispersion.

For a possible **collective** spacetime sector, a precise next target is
a stable phase whose long-wavelength phase and density variables have
finite positive susceptibility chi and stiffness K_ij. If their actual
effective action is

```
S_eff=(1/2) integral [chi (partial_t theta)^2
                    -K_ij partial_i theta partial_j theta] dt d^3x,
```

its characteristic equation is
`chi omega^2=K_ij k_i k_j`. This would define a Lorentzian effective cone
when K is positive definite. It is a test criterion, not an action
derived in this note. The microscopic ordered phase, coefficients,
universality across matter species, and a dynamical metric still have
to be demonstrated. A common Lieb-Robinson envelope does not provide
those properties.

The earlier [free Weyl update](WEYL_WALK_CONTINUUM.md) already shows that
an explicitly different microscopic carrier can have a controlled
relativistic wave limit. It supplies its lattice and spinor structure
and has additional cones; simply importing it would not derive this
model's spacetime or physical chiral matter. Einstein dynamics also
cannot be inferred from the positive tensor D or from a cone alone.

## 9. Verification and scope

- [The audit](scripts/collective_spacetime_audit.py) checks the exact
  form identity and comparison spectrum, the ground vector, the
  zero-momentum gap, the virtual-excitation coefficient, and the
  transverse eigenvector identity.
- Numerical Bloch bands in dimensions 3,456 and 6,912 show the quadratic
  dispersion and quartic remainder. The smallest tested momentum lies
  within the deliberately conservative analytic radius; larger momenta
  are finite diagnostics rather than uses of that radius theorem.
- An explicit isometric cell-translation quotient is checked against
  the complete 13,824-dimensional two-cell joint Hamiltonian. The
  finite benchmarks grow only the x cell count; the growing-box proof
  above, not those samples, supplies the three-dimensional volume limit.
- Reference spectral counts and finite-size gaps are checked through
  side 128. They support the exact joint min-max comparison, not a
  separate claim about the full many-body spectral dimension.
- [Eight supporting Lean results](UnifiedTheory/Audit/KFCausalCollectiveSpacetime.lean)
  verify the energy-form certificate, uniform adjacency action, positivity,
  inverse-square scaling, the rescaled band error, and the scalar limits.
  Min-max, the fiber and infinite-volume constructions, resolvent
  perturbation, and the propagator assembly remain analytic suppliers.
- [The report](data/collective_spacetime_audit.json) records checks and
  source hashes. Earlier hashed research artifacts are unchanged.

Run `OPENBLAS_NUM_THREADS=1 python3 -W error::RuntimeWarning scripts/collective_spacetime_audit.py`
and `lake build`.
