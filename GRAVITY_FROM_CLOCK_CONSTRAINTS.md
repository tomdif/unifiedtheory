# What would turn the microscopic spin seed into gravity?

Date: 2026-09-10

The calculation below gives a **conditional gravitational completion**
and a sharper microscopic target. It does not prove that the repository's
spin Hamiltonian reaches that target. There are three separate results:
an exact six-component extension inside the existing four-spin cell;
a diagnosis of the dynamics needed for linear waves; and a continuum
constraint calculation that recovers Einstein gravity under stated
metric, locality, and clock-consistency assumptions.

The proposed organizing principle is **independence of the local choice
of time slices**. Advancing neighboring local clocks in different orders
must differ only by a spatial relabeling, with the same rule acting on
geometry and matter. This is substantially stronger than having a partial
order or a local Hamiltonian. It is the missing dynamical principle to
test in the microscopic model, not a consequence already obtained from
the causal order.

## 1. The same four spins contain the missing scalar channel

Keep the notation of [the microscopic seed](MICROSCOPIC_SPIN_TWO_SEED.md).
In addition to the triplet-pair singlet Omega and the quintet, there is
the product of the two pair singlets,

```
|eta>=|singlet_12> tensor |singlet_34>,
P_s=(I-A^2/2)(I-B^2/2)=|eta><eta|.
```

This is a second total-spin-zero state, orthogonal to Omega. For the
microscopic exchange R=s_1.s_3, exact sixteen-state algebra gives

```
<eta|R|Omega>=-sqrt(3)/4,
b_0^dagger=-(4/sqrt(3)) P_s R P_0=|eta><Omega|.       (1)
```

Together with the old five quintet transitions b_alpha, this gives six
channels on a seven-dimensional active space. Define E_0=I/sqrt(3)
and retain the five orthonormal traceless E_alpha. These six matrices
are an orthonormal basis of all real symmetric three-by-three tensors.
The transition algebra is the old one with six flavors and
`N=P_s+P_2`. The remaining nine local states are inactive if projected
out of the transition operators. Promoting eta to a low local level
is an explicit change of the onsite Hamiltonian; it needs no new qubits.

For X_ij=sum_(alpha=0,...,5) E_alpha,ij (b_alpha+b_alpha^dagger),

```
||d_i X_ij d_j||^2=sum_alpha(d^T E_alpha d)^2=|d|^4.  (2)
```

Consequently the old direct scalar-strain stability estimate remains
valid with sufficient condition `|gamma|<kappa/4`. This is a kinematic
and stability extension, not a gravitational scalar degree of freedom:
in a successful gravitational theory the constraints must remove the
unphysical components, including the trace channel.

## 2. Linear dispersion requires a change of dynamics

There is a general obstruction to repairing the old positive hopping
band just by adjusting its short-range coefficients. Suppose K(k) is
a finite-dimensional Hermitian, twice continuously differentiable
one-particle Bloch Hamiltonian, K(k)>=0 near k=0, and P projects onto
ker K(0). For every v in that kernel and every momentum direction e,
`v^dagger K(t e)v` has a nonnegative minimum at t=0. Its first derivative
vanishes. Polarization therefore gives `P (partial_e K)(0) P=0` and

```
||P K(k) P||=O(|k|^2).
```

If the kernel has dimension m, the min-max principle using its fixed
m-dimensional trial subspace bounds the lowest m eigenvalues by
`0<=epsilon_j(k)<=C|k|^2`. Thus a positive analytic number-conserving
vacuum band cannot acquire a nonzero linear slope at that minimum.
Finite-range hopping satisfies the differentiability hypothesis. This
does not exclude interacting phases, particle-hole descriptions about
filled states, or long-range/nonanalytic Hamiltonians.

For canonical collective coordinates h,p, a possible wave Hamiltonian
is instead

```
H_wave(k)=J p^2/2+(r+g ell(k))h^2/2,
ell(k)=4 sum_i sin^2(k_i/2),       J,g>0.            (3)
```

At r=0, its frequency is sqrt(Jg ell(k)), linear at small k. With
`h=(b+b^dagger)/sqrt(2)` and `p=(b-b^dagger)/(i sqrt(2))`, its number
and pairing coefficients are

```
A(k)=(J+r+g ell(k))/2,
B(k)=(r+g ell(k)-J)/2,
omega(k)^2=A(k)^2-B(k)^2=J(r+g ell(k)).             (4)
```

Here the Hamiltonian contains `(B/2)(b_k b_-k+h.c.)`, as well as
`A b_k^dagger b_k`. Pairing breaks conservation of the old excitation
number. The mass r must be zero, or a symmetry must protect that value.
The zero momentum massless coordinate requires separate treatment.
Equation (3) initially produces six waves; gravitational constraints
are still needed to select two.

It would be incorrect to insert the single-cell hard-core b matrices
into (3) and claim that this canonical spectrum follows. For six flavors,

```
sum_alpha p_alpha^2=sum_alpha h_alpha^2=(6 P_0+N)/2. (5)
```

The proposed onsite p-squared energy is *higher* in Omega than in an
active excited state. For a positive sum of onsite p-squares and bond
h-difference squares, a product of active states has lower energy
expectation than the product of Omega states. The old vacuum expansion
is therefore not justified for that naive spin substitution.

A controlled kinematic alternative is a block of R copies of the
seven-state active cell in its permutation-symmetric sector. Collective
transitions have the exact occupation-basis action

```
B_alpha^dagger |n>=sqrt((n_alpha+1)(1-|n|/R)) |n+e_alpha>.
```

Compared with canonical creation, the norm error on |n|<=n_* is at most
`sqrt(n_*+1) n_*/R`. The commutator error is at most `2n_*/R` there.
This supplies a controlled finite-occupation canonical limit as R grows.
It does not prove the block-symmetric ground phase, finite-density
control, joint spatial locality in that limit, or a constrained quantum
gravity phase. Those cannot be inferred from a commutator estimate.

## 3. The nonlinear clock-consistency target

Now make the continuum assumptions explicit. Suppose coarse variables
include a positive spatial metric q_ij and its canonical momentum
pi^ij in three spatial dimensions. Suppose a generator D[xi] acts by
spatial Lie derivatives on all fields, and H[N] generates normal clock
advances with arbitrary lapse N. On a compact slice without boundary,
or with appropriate falloff, require

```
{D[xi],D[zeta]}=D[[xi,zeta]],
{D[xi],H[N]}=H[xi^i partial_i N],
{H[N],H[M]}=D[V],
V^i=q^ij(N partial_j M-M partial_j N).             (6)
```

The sign in the last equation is the Lorentzian convention. Its
field-dependent q^ij is essential. Mere closure with some coefficients,
or pairwise commuting linear constraints, is a weaker requirement.
Equation (6) is the hypersurface-deformation algebra: see
[Teitelboim's original derivation](https://doi.org/10.1016/0003-4916(73)90096-1)
and [Hojman, Kuchar, and Teitelboim](https://doi.org/10.1016/0003-4916(76)90112-3).
The present calculation applies this established principle to a narrow,
explicit ansatz; it is not a new discovery of the GR uniqueness program.

The microscopic task would be to derive (6), with vanishing anomalies,
as an operator or effective Poisson-bracket limit of the actual local
spin and clock generators. The previously constructed causal clock
does not supply arbitrary lapse gauge symmetry, a metric-dependent
commutator, or this representation of spatial relabelings.

## 4. Computing the constraint bracket fixes the gravity coefficients

Assume a local, time-reversal-even Hamiltonian, quadratic and ultralocal
in pi, with at most two spatial derivatives of the metric, and no
additional gravitational fields. Within the following ansatz let

```
H_g[N]=integral N [a/sqrt(q) (pi^ij pi_ij-lambda pi^2)
                         -b sqrt(q) (R^(3)-2 Lambda)],
D_g[xi]=-2 integral xi_j nabla_i pi^ij,
pi=q_ij pi^ij,          a,b>0.                    (7)
```

The supplied spatial covariance motivates the curvature term and
momentum generator. It does not derive the metric itself from spins.
Higher derivatives, extra fields, different constraint algebras, and
other phases are outside this ansatz.

All ultralocal contributions to {H_g[N],H_g[M]} cancel by antisymmetry
in N,M. The derivative part of the curvature variation is
`b sqrt(q)(q^ij nabla^2 N-nabla^i nabla^j N)`. Contracting with
`delta H_g[M]/delta pi^ij=2a M(pi_ij-lambda pi q_ij)/sqrt(q)` gives

```
{H_g[N],H_g[M]}
 =2ab integral [pi^ij(N nabla_i nabla_j M-M nabla_i nabla_j N)
          +(2lambda-1)pi(N nabla^2 M-M nabla^2 N)]
 =ab D_g[V]+2ab(1-2lambda) integral sqrt(q) V^i
                                        partial_i(pi/sqrt(q)). (8)
```

The second line follows by integration by parts, remembering that pi
is a density. Matching (6) for unrestricted phase-space data forces

```
lambda=1/2,                  ab=1.               (9)
```

The trace-gradient term is an actual obstruction. On a flat periodic
slice, take pi_xx=cos(y) and all other components zero, N=1, M=cos(y).
Then D_g[V]=0, but the integral multiplying 1-2lambda is positive.
It cannot be absorbed into the specified momentum generator. Imposing
an additional constant-trace constraint or restricting lapse functions
changes the problem and is not a realization of (6) on the stated phase
space. A common rescaling of time changes the normalization ab=1;
it does not remove the trace condition.

## 5. The same algebra forces a common scalar wave speed

For scalar species A, allow positive independent kinetic coefficients
u_A,v_A and an ultralocal potential U_A:

```
H_A[N]=integral N [u_A p_A^2/(2sqrt(q))
       +v_A sqrt(q) q^ij partial_i phi_A partial_j phi_A/2
       +sqrt(q) U_A(phi_A)],
D_A[xi]=integral p_A xi^i partial_i phi_A.          (10)
```

Direct functional differentiation yields

```
{H_A[N],H_A[M]}=u_A v_A D_A[V].                  (11)
```

The derivative on N or M supplies V; potential terms and terms
proportional to NM cancel. Mixed metric-scalar brackets likewise
cancel after antisymmetrization, since the scalar dependence on q
in (10) has no metric derivatives. Thus a *single* total algebra (6)
requires `u_A v_A=ab=1` for every species in this ansatz. All scalar
wave speeds then agree with the gravitational one. Separate positive
Hamiltonians with different speeds do not satisfy the same total
normal-deformation rule.

The individual u_A are field normalizations: with phi_A=sqrt(u_A) psi_A,
the kinetic action of psi_A is the usual scalar action for the same
metric. Potentials, particle masses, and interaction strengths are not
fixed. The shared spatial tensor transformation and the matter ansatz
are hypotheses. This calculation is not a proof that every possible
matter theory or nonminimal interaction is uniquely determined.

## 6. The resulting nonlinear dynamics is Einstein gravity

Write a=16 pi G and b=1/(16 pi G), with G>0. The ratio of the two
coefficients, and hence Newton's constant, remains undetermined by
the closure condition. Lambda also remains free.

Use the canonical action with lapse N and shift N^i. Defining
`K_ij=(dot q_ij-L_N q_ij)/(2N)`, the momentum equation from (7),(9) gives

```
pi^ij=sqrt(q)/(16 pi G) (K^ij-q^ij K).
```

Eliminating pi gives

```
S_g=(1/(16 pi G)) integral dt d^3x N sqrt(q)
                   [K_ij K^ij-K^2+R^(3)-2 Lambda]. (12)
```

This is the Einstein-Hilbert action up to the usual boundary term for

```
ds^2=-N^2 dt^2+q_ij(dx^i+N^i dt)(dx^j+N^j dt).
```

Together with the common-metric matter action, variation gives

```
G_mu nu+Lambda g_mu nu=8 pi G T_mu nu.             (13)
```

Four first-class constraints and their gauge transformations reduce
six metric canonical pairs to two propagating polarizations. Around
flat space with Lambda=0, their constrained quadratic Hamiltonian is
the positive transverse-traceless wave Hamiltonian, with linear
dispersion. The negative trace coefficient in (7) is removed from the
physical propagating sector by the constraints; it is not a stable
unconstrained oscillator energy to impose on every microscopic state.

This supplies a nonlinear gravitational theory **if the continuum
variables and exact deformation algebra are obtained**. It does not
establish a finite-spin microscopic realization of them, nor a quantum
continuum limit. The established self-coupling route of
[Deser](https://arxiv.org/abs/gr-qc/0411023) reaches the same Einstein
completion from a supplied interacting massless spin-2 gauge theory.

## 7. Static attraction needs the clock constraint, not only TT waves

For weak, static sources, set Lambda=0,
`N=1+Phi`, `q_ij=(1-2Psi)delta_ij`, and shift zero. At linear order,

```
R^(3)=4 nabla^2 Psi,
G_00=2 nabla^2 Psi,
G_ij=(partial_i partial_j-delta_ij nabla^2)(Psi-Phi).
```

The normal constraint therefore gives
`nabla^2 Psi=4 pi G rho`. Negligible spatial stress, with decaying
boundary conditions, sets Phi=Psi. For a point mass,

```
Phi(r)=-Gm/r,       F=-m_test grad Phi.            (14)
```

The sign is attractive. The spatial TT vertex alone couples to T_ij;
stationary nonrelativistic matter has leading source T_00 instead.
This explains concretely why merely obtaining two tensor waves, or
coupling the old spin tensor to scalar gradients, is insufficient.
The energy and momentum source terms of the normal and spatial
constraints are indispensable.

There is a separate scattering diagnostic for universal strength.
If a common Lorentzian continuum, a massless helicity-two pole, soft
factorization, and nonzero generic scattering amplitudes are supplied,
soft gauge invariance requires `sum_a eta_a g_a p_a^nu=0`. For elastic
A+B scattering, momentum conservation reduces this to
`(g_A-g_B) Delta p_A^nu=0`. Nonzero momentum exchange forces g_A=g_B.
This is [Weinberg's soft-graviton argument](https://journals.aps.org/pr/abstract/10.1103/PhysRev.135.B1049),
and includes self-coupling when gravitons participate. It does not
follow from conservation of separately free stress tensors or relate
completely disconnected sectors without those scattering assumptions.

## 8. The precise microscopic task left by this derivation

The second singlet supplies six microscopic transition channels.
Canonical pairing describes the required linear dynamics, but its
validity about a spin ground state must be established. The nonlinear
target is now more restrictive than a spin label or a two-mode spectrum:
local spin and clock generators must approach (6), acting on geometry
and matter together, with the source terms intact.

A successful construction needs a stable physical sector and a
controlled limit in which commutator defects vanish while the two
gravitational poles and a nonzero common coupling survive. Large finite
derivative penalties, the dilute commutator estimate alone, and tuning
a hopping gap to zero do not prove this. No such microscopic sector is
claimed here. The causal carrier, spatial dimension, metric
interpretation, clock normalization, and matter content are still inputs.

One concrete diagnostic is to compute the coarse commutator in the form
`{H[N],H[M]}=D[C^ij(N partial_j M-M partial_j N)]+remainder`.
If C is a positive, rank-three, state-dependent field and the remainder
vanishes in a controlled limit, its inverse is a candidate operational
spatial metric. Canonical conjugacy, the other brackets, and matter
coupling must also be verified. A fixed C would supply a background
propagation geometry, not by itself a dynamical gravitational field.

The free dispersion already diagnoses part of this requirement. For
locally weighted one-particle evolution with symbol N(x) epsilon(p),
the leading commutator symbol contains
`epsilon partial_p epsilon = (1/2)partial_p(epsilon^2)`. A relativistic
dispersion gives c^2 p; the quadratic seed gives
`2 t_h(mu+t_h |p|^2) p`, a momentum-dependent coefficient. At mu=0
this fails to give a nonzero constant low-momentum clock-deformation
coefficient. This is a principal-symbol diagnostic, not an exact
microscopic constraint algebra. The exact canonical scalar bracket
(11) shows why free waves can supply the background version of the
clock rule while leaving dynamical gravity unresolved.

## 9. Verification and reproducibility

The [audit](scripts/gravity_constraint_audit.py) and its
[report](data/gravity_constraint_audit.json) check the microscopic scalar
transition, all six-channel identities, block occupation algebra,
pairing coefficients, and the failed single-cell canonical substitution.
They independently evaluate the metric and scalar functional brackets
on periodic data, verify the trace anomaly witness, and check the
Legendre transform, weak-field Einstein tensor, and soft-source identity.
These are local algebra and finite functional tests alongside the
analytical derivation; no numerical experiment establishes the missing
microscopic gravitational phase.

The fifteen results in the [Lean module](UnifiedTheory/Audit/KFCausalGravityConstraint.lean)
contain supporting scalar algebra and a zero-slope minimum lemma, not
a formalization of continuum functional geometry or a microscopic
quantum-gravity theorem. Their axiom reports contain only the standard
`propext`, `Classical.choice`, and `Quot.sound` axioms.

The audit passes all 36 local transition checks and 144 collective
commutator checks in occupation matrices of dimension 210, with an
84-dimensional input sector. Eighty positive-band comparisons satisfy
the min-max bound. Twelve metric and twelve scalar bracket checks on
4,096-point periodic grids have maximum residuals below 3.6e-15 and
3.7e-16, respectively. These finite checks use a flat spatial metric;
the curved-metric identity in (8) is supplied by the analytical
functional-variation calculation.

```sh
OPENBLAS_NUM_THREADS=1 python3 -W error::RuntimeWarning scripts/gravity_constraint_audit.py
lake env lean UnifiedTheory/Audit/KFCausalGravityConstraint.lean
```
