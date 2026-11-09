# A finite-spin parent that selects two tensor polarizations

Date: 2026-09-11

The previous [quartic construction](EINSTEIN_QUARTIC_CONSTRAINTS.md)
assumed a TT input space. The parent below instead selects that space
from the six-channel spin blocks. Its exact low-occupation kernel is
large enough to carry both tensor polarizations. A separation of energy
scales then gives their quantum Hamiltonian, including a nonvanishing
supplied cubic when that interaction is included.

This is an explicitly engineered modification of the microscopic model.
The local constraint stencil, scale hierarchy and interaction coefficients
are inputs. The theorem is at fixed finite carrier volume. It does not
derive Einstein's nonlinear constraints, a physical Newton constant,
a joint continuum limit, or the TOE. In the interacting version the
sextic stabilizer is an additional model input, and a protected massless
interacting spectrum is not proved.

## 1. A local annihilation constraint on the original spin channels

Use the seven active states of each four-spin cell and R cells per
block. The six transitions from an excited state to Omega are b_alpha.
Define the collective annihilators

    B_(x,alpha)=R^(-1/2) sum_(j in block x) b_(j,alpha).

An orthogonal change of the six excited states puts these in Cartesian
Frobenius coordinates xx,yy,zz,xy,yz,zx; off-diagonal tensor entries
are the corresponding coordinate divided by sqrt(2). This changes
neither the cell dimension nor its symmetric-block occupation formula.
The original trace singlet and spin-two quintet remain the same space.

On a periodic cubic carrier of side L>=2, take the real integer maps G,B_0 from
[the compact constraint complex](COMPACT_TENSOR_CONSTRAINTS.md):

    f_i=T_i-1, b_i=1-T_i^(-1), ell_i=T_i+T_i^(-1)-2,
    (G xi)_ii=2 f_i xi_i,
    (G xi)_ij=f_i xi_j+f_j xi_i,
    B_0 h=sum_i T_i^(-1) sum_(j!=i) ell_j h_ii
                         -2 sum_(i<j) b_i b_j h_ij.

They satisfy B_0 G=0 exactly. With
W=diag(1,1,1,sqrt(2),sqrt(2),sqrt(2)), put

    G_F=W G,             B_F=B_0 W^(-1),
    C=[G_F^T; B_F],      K=C^T C,
    D_R=sum_mu (C B)_mu^dagger (C B)_mu.                  (1)

Transposes here are real-space adjoints, including the reversed lattice
translations. D_R is positive and preserves total occupation. Every
collective annihilator commutes with every other one, so these are
compatible annihilation conditions. We do not impose their adjoints
as additional conditions on a state.

On the periodic cubic carrier, at k!=0 set
v_i=2sin(k_i/2), ell=|v|^2. The same component staggering as in the
constraint complex transforms G_F to xi -> i(v xi^T+xi v^T), and B_F
to contraction with vv^T-ell I. Their ranges are orthogonal. Therefore

    spectrum K(k)={0,0,2ell,2ell,4ell,2ell^2}.             (2)

The kernel is exactly the staggered TT tensor space. There are two
polarizations at every nonzero momentum and no extra zero at a corner
of the Brillouin zone. At k=0 all six channels remain. For V=L^3,

    m:=dim ker C=2(V-1)+6.                               (3)

These six homogeneous coordinates are retained explicitly. Their
nonlinear Einstein constraint and volume-clock role remain open.
The smallest positive eigenvalue delta_C of K scales as L^(-4) on
large periodic boxes; it is not a volume-independent constraint gap.

The maps in (1) are deliberately supplied. What is new in this parent
is the annihilation constraint and its finite-spin kernel, not the
previous integer stencil or the linear TT counting.

## 2. An exact finite-spin kernel, not an approximate substitution

In the active symmetric block, use the normalized occupation basis
with N_x=sum_alpha n_(x,alpha)<=R. Canonical bosonic annihilation a
and the actual collective spin operator obey

    B_alpha|n>=sqrt[n_alpha(1-(N_x-1)/R)] |n-e_alpha>.

Define a positive diagonal map on this finite occupation chart:

    S_R|n>=product_x s_R(N_x)|n>,
    s_R(N)=product_(j=0)^(N-1)(1-j/R)^(-1/2).

The empty product is one. Directly comparing adjacent coefficients gives

    B_alpha=S_R a_alpha S_R^(-1),                       (4)

where a is restricted to the allowed local occupation chart. This
similarity is not unitary; ignoring its change of inner product would
give incorrect finite-R states. The associated polynomial realization
is part of the standard coherent-state representation framework;
see [Perelomov](https://arxiv.org/abs/math-ph/0203002). Equation (4)
and the estimates here follow directly from the displayed coefficients.

On total occupation n<=R the local cutoffs exclude no n-particle
configuration. Let P_n project onto Sym^n(ker C) in canonical Fock
space. Equation (4) then proves exactly

    ker(D_R restricted to total n)=S_R ran P_n,
    dim ker(D_R|_n)=binomial(m+n-1,n).                    (5)

Indeed CB=S_R(Ca)S_R^(-1), with S_R on the output n-1 sector.
The kernel of sum_mu(Ca)_mu^dagger(Ca)_mu=dGamma(K) is exactly
the Fock space of ker C. In polynomial language, its states depend
only on the m unconstrained linear coordinates.

For n>R the correct statement is the same polynomial kernel intersected
with all local degree caps. The dimension in (5) is not asserted there.

There is also a quantitative bound on the excluded n-particle sector.
For 1<=n<=R,

    1<=S_R<=exp[n(n-1)/(4(R-n+1))],
    gap(D_R|_n)>=delta_C exp[-n(n-1)/(2(R-n+1))].          (6)

To prove the first inequality, use -log(1-j/R)<=j/(R-n+1)
and sum over cells; sum_x N_x(N_x-1)<=n(n-1). For the second,
the annihilation map is S_(n-1)(Ca)S_n^(-1). Multiplying a matrix
on either side by invertible matrices bounds each nonzero singular
value below by the corresponding least singular factors. The
canonical n-particle map has least nonzero squared singular value
delta_C. Squaring the bound proves (6).

An isometric physical embedding on this sector is

    I_(R,n)=S_R P_n(P_n S_R^2 P_n)^(-1/2).                (7)

It tends to the identity on each fixed particle sector and satisfies
D_R I_(R,n)=0 exactly. This exact cancellation is important when the
constraint energy is later divided by a small parameter.

## 3. A bounded-strength microscopic family

Choose epsilon_R=R^(-2) and Gamma>0. On the collective chart set

    H_R=Gamma D_R+epsilon_R F_R.                          (8)

Add the previous guarded exchange and inactive-state penalties on the
full sixteen-state cells. Two useful choices of F_R are as follows.

For the free reference, take the positive six-component wave energy
H_w with U,r>0,g>=0 and the vanishing three-cell guard

    F_R,free=H_w+sum_x [c(d-1)N_x/(2R)+c N_x^3/R^2],
    c=min(U,r),                 d=6.

The prior occupation identity gives F_R,free>=3c sum_x N_x/4+dcV/2.
Its fixed-particle limit is H_w in canonical Fock space.

For an interacting construction use

    F_R,int=H_w+chi sum_(abc)c_abc :Q_a Q_b Q_c:_R
                      +nu sum_x N_x(N_x-1)(N_x-2),       (9)
    Q=(B+B^dagger)/sqrt(2),             nu>0.

The cubic uses the actual supplied 93-monomial tensor coefficient
table and a bounded finite-difference stencil. The subscript R means
expand the classical monomial into its eight creation/annihilation
terms and place all B^dagger to the left. It does not mean commute
finite-spin operators as if their commutators were canonical.
The result is Hermitian. This normal-ordering prescription is an
explicit quantum-model choice; it differs from the previous Weyl lift
by lower-order terms. Its classical cubic polynomial is unchanged.

Let c_star be the absolute coefficient incidence per block, counting
each of the three occurrences. The same full-row estimate as in the
tensor-vertex note gives, now without a factor R^(-1/2),

    |<V_3>|<=a_3 sum_x<N_x^(3/2)>+b_3 V,
    a_3=4sqrt(3)|chi|c_star, b_3=36|chi|c_star.

For all integer N>=0,

    N(N-1)(N-2)>=N^3/4-2.

Completing a square with x=N^(3/2) therefore proves

    F_R,int >= (nu/8)sum_x N_x^3-K_0 V,
    K_0=2nu+2a_3^2/nu+b_3.                              (10)

This estimate is uniform in R and also permits r=0. It does not
prove a massless interacting spectrum. The Omega trial state has zero
D_R, cubic and sextic expectation and wave energy at most
dV(U+a_max)/4. Thus bounded physical ground energy implies a uniform
occupation bound; high occupations cannot evade the constraint limit.

All terms in the microscopic (8) act on at most three four-spin cells.
The sextic is particularly simple:

    N_x(N_x-1)(N_x-2)=6 sum_(i<j<k in x) n_i n_j n_k.

Multiplication by epsilon_R makes its per-cell norm sum at most 3nu.
Using the eight ordered summands bounds the cubic's per-cell sum by
2sqrt(2)epsilon_R sqrt(R)|chi|c_star, hence bounded. This conservative
bound also covers coincident microscopic cell indices; a normal-ordered
local product need not have the same norm as a product of X=b+b^dagger.
The wave part has at most its previous per-cell budget.

For completeness, the Frobenius constraint rows have absolute sums

    r_G=4+4sqrt(2),         r_B=24+12sqrt(2),
    B_C=3r_G^2+r_B^2=1008+672sqrt(2).

Expanding D_R into two-cell terms gives per-cell norm sum at most
2Gamma B_C. These bounds hold before any small-box periodic aliasing,
which cannot increase them. The block range is at most four lattice
steps. With

    B_parent=2Gamma B_C+B_wave+3nu+2sqrt(2)|chi|c_star

for (9), the [sign-independent selection theorem](TENSOR_VERTEX_SELECTION.md)
applies with q=7,k=3. Choose J=2[120B_parent+Delta] and
delta>=J+2B_parent+Delta. The full four-spin Hamiltonian has all its
ground states in the active symmetric blocks and a ground-energy gap
at least Delta to the excluded sectors, uniformly in R,V. The free
choice has an analogous bound using its guard budget.

The constants are conservative, and exchange still has growing
connectivity inside each block. These are bounded summed strengths
and bounded block ranges, not a proved fixed Euclidean range between
individual microscopic spins. The carrier and its stencils are supplied.

## 4. The quantum constraint limit

Fix a finite carrier and Gamma>0. Embed the active symmetric spaces
in the common bosonic occupation Hilbert space. Let P be the Fock
projector associated with ker C, including the six homogeneous modes.
The physical Hamiltonian is H_R/epsilon_R. Then every fixed low
eigenvalue converges, with multiplicities, to that of

    H_eff=P F_infinity P on ran P.                       (11)

For isolated eigenvalue clusters the embedded spectral projectors
converge in norm. Ground vectors converge in norm when the limiting
ground state is simple; otherwise the statement is about their space.
Here F_infinity is the fixed-particle canonical limit of the chosen
free or interacting F_R.

A proof is needed because the spin spaces and their kernels change
with R. It does not follow just by citing a fixed-space strong-coupling
limit. The argument is:

1. On every finite-particle input F_R converges with all output rows
   retained. The cubic changes total number by at most three and
   the number guard is diagonal. Formula (7) supplies exact zero-energy
   trial embeddings for the fast constraint term. Therefore the
   min-max upper bounds converge to those of (11), regardless of how
   rapidly epsilon_R tends to zero.
2. The free number bound or (10), together with D_R>=0, bounds total
   occupation on every bounded-energy sequence. At fixed volume the
   number operator has finite-rank spectral projections, so these
   sequences are norm-precompact. In the interacting case use
   sum_x N_x^3>=N_total^3/V^2.
3. A bounded-energy eigenvector has <D_R>=O(epsilon_R). D_R preserves
   total number. On any fixed particle cutoff, (5)-(6) force its limit
   into ran P. The occupation bound controls the discarded tail.
4. Test its eigenvalue equation against I_(R,n)phi. The amplified
   constraint term vanishes exactly, while F_R I_(R,n)phi converges
   to F_infinity phi. Thus every limiting eigenvector solves (11).
   Orthogonality, compactness and the min-max upper bounds exclude
   missing low levels or extra bounded-energy eigenvectors.

The finite-particle core defines a unique self-adjoint, lower-bounded
operator in (11). For (9), its number-preserving sextic compression
has a lower bound growing as N_total^3 at fixed V, while the wave and
cubic have relatively vanishing operator bounds. The finite-number
blocks and this bound give compact resolvent and the required core.
For the free choice the positive finite-volume oscillator is standard.

The same spectral argument gives strong finite-time quantum evolution
on physical inputs, uniformly on compact time intervals. Use (7) on
each particle sector up to R and zero above R to define I_R. For a
finite-particle physical input, its fast energy is zero and its slow
energy expectation stays bounded. This controls the spectral tail;
convergence on finitely many low eigenspaces then proves

    exp[-it H_R/epsilon_R] I_R phi
                  -> exp[-it H_eff] phi.                 (12)

Density extends the result to every fixed physical input. The full
microscopic evolution agrees on these symmetric-block inputs; the
exchange and inactive penalties vanish there. This is a finite-volume
quantum limit, not a theorem about interacting continuum gravity.
Strong-coupling subspace dynamics has established precedent in
[Facchi and Pascazio](https://arxiv.org/html/quant-ph/0201115); the
exact finite-spin kernel and compactness estimates above supply the
changing-space argument used here.

## 5. The two waves and the surviving cubic

For the free choice, K commutes with the scalar lattice wave stiffness.
After a real orthogonal mode change, (11) has two wave oscillators at
each k!=0 and six at k=0. The nonzero-momentum wave frequencies are

    omega(k)=sqrt[U(r+g ell(k))].                         (13)

Four eliminated oscillator vacua contribute a known additive constant,
(U+r+g ell)/4 per normal oscillator. For a normal K eigenvalue lambda,
the canonical comparison before the limit has frequency

    sqrt[(Gamma lambda/epsilon_R+U)
                  (Gamma lambda/epsilon_R+r+g ell)].

It diverges in physical energy while the two frequencies (13) stay
finite. At r=0 and k!=0 the latter are linear at small k. The massless
homogeneous coordinates require separate treatment and have no
normalizable free Gaussian ground state. The interacting version of
(9) is confining but has no proved symmetry protecting zero mass.

For any normally ordered polynomial, compression to the normal-mode
vacuum replaces every a by its projection into ker C. There are no
normal-vacuum contractions left over. Thus the cubic in (9) survives
in (11) with its fixed coefficient chi, as a normally ordered polynomial
of the physical tensor operators. The guard similarly remains a
normal-ordered sextic; it introduces no bare normal-ordered quartic.

This is a change of scaling from the earlier regular block limit.
The microscopic slow energy has been tuned to R^(-2), and physical
time is measured in its units. A finite cubic can therefore remain
without making the summed microscopic interaction strength diverge.
The construction is not covered by a fixed nonzero quadratic-scale
Gaussian argument. It does not derive this hierarchy dynamically.

The supplied cubic is not identically zero after projection: the audit
evaluates it on actual nonzero-momentum lattice-kernel profiles. For
a normalized real one-particle profile f in ker C, its vacuum-to-three-
particle matrix element is

    <3_f|V_3|0>=(sqrt(3)/2)chi C_3(f),                    (14)

where C_3 is the supplied discrete classical cubic polynomial. The
exact finite-spin kernel vector S_R|3_f>/||S_R|3_f>|| has the same
matrix element divided by ||S_R|3_f>||, for R>=3. This follows by
using B^dagger=S_R^(-1)a^dagger S_R on its three creation factors.
In particular the vertex is already nonzero in those finite-spin
states. If p_x=sum_alpha|f_(x,alpha)|^2, its normalization obeys

    ||S_R|3_f>||^2
      =1+3(sum p_x^2-sum p_x^3)[R/(R-1)-1]
         +sum p_x^3[R^2/((R-1)(R-2))-1].                 (15)

This just separates three draws into distinct-block, one-pair and
one-triple occupancies. The audit checks it against complete
three-particle occupation vectors before applying it to larger profiles.
Equation (14) uses the reference annihilation vacuum, not the generally
squeezed or interacting ground state. It is an operator matrix element,
not an on-shell scattering amplitude or an invariant Einstein test.
The earlier nonzero compact continuum TT example also persists under
consistent sufficiently fine sampling and staggered projection.
The finite tests evaluate the specified tracefree extension; they do
not establish exact finite-lattice diffeomorphism covariance.

A nonzero operator vertex is not a derived physical Newton constant.
The earlier fixed mean-metric normalization still gives G_match tending
to zero with R. Keeping a finite physical gravitational normalization
would require a tested change to that metric map as well as the clock
scaling here. No such identification is silently assumed.

## 6. What this closes and what is still missing

The construction now selects the two-polarization quantum state space
from actual finite-spin blocks and gives its finite-volume dynamics.
It can retain the supplied cubic. These were previously assumed in
the classical quartic realization. It does not yet make the resulting
interacting tensor theory Einstein gravity.

The annihilation constraints put four normal modes in their vacuum.
Their real and imaginary parts still fluctuate. They are not four
first-class generators of metric-dependent spatial and normal clock
deformations. In particular they do not supply the nonlinear scalar
and longitudinal response, the correlated Newton quartic, or the
lapse derived in the preceding target calculation. Those must be
obtained from a further tested constraint construction, not from
declaring every two-polarization interaction to be gravitational.

At finite R the slow Hamiltonian need not preserve the exact kernel;
decoupling is a scale-limit theorem. The fixed finite-Weyl-code
normalizer obstruction therefore does not apply to this new family.
No claim is made to have repaired propagation inside that old code.

Neither (11) nor (12) is uniform in spatial volume. Already the free
normal gap gives the necessary separation R^2 delta_C -> infinity,
or R/L^2 -> infinity on large cubic boxes. This one-particle condition
is not sufficient for a joint interacting limit; the many-particle
estimates have additional volume dependence. Continuum locality,
nonlinear clock closure, protected interacting masslessness, correct
Einstein higher vertices and universal matter coupling remain open.

## 7. Verification

Run

    OPENBLAS_NUM_THREADS=1 python3 -W error::RuntimeWarning scripts/holomorphic_tensor_phase_audit.py

The report is
[data/holomorphic_tensor_phase_audit.json](data/holomorphic_tensor_phase_audit.json).
It contains exact identities and 24 numerical cases. It checks finite-spin kernels
with all lower-sector outputs retained, the complete two-particle
spectrum on a three-dimensional carrier, normal-mode separation, and
the projected supplied cubic. A separate small nonlinear model tests
the changing-kernel spectral limit with explicit occupation-cutoff
control. Each test's scope is recorded in the report. That original audit
does not supply a Lean proof or a full three-dimensional interacting diagonalization.

## 8. 2026-10-15 formal symbol dynamics and the nonlinear clock test

[`KFCausalTensorModeDynamics.lean`](UnifiedTheory/Audit/KFCausalTensorModeDynamics.lean)
now proves the real-symbol two-dimensional transverse-tracefree kernel
for every nonzero wavevector, preservation by the specified quadratic wave
generator, and its oscillator frequency-squared identity. It also proves
the six-component homogeneous exception. The exact staggered change of
basis relating the existing lattice stencil to this real symbol is checked
by [`diagonal_clock_dynamics_audit.py`](scripts/diagonal_clock_dynamics_audit.py).
This bridge is symbolic verification, not yet a Lean lattice theorem.

[`KFCausalDiagonalClockDynamics.lean`](UnifiedTheory/Audit/KFCausalDiagonalClockDynamics.lean)
adds a genuine variational-jet calculation for a proposed continuum clock
with diagonal metric fields depending on one spatial coordinate. The
normal bracket has the required inverse-metric current at the DeWitt
trace coefficient 1/2. A positive-kinetic curvature extension with
coefficient zero fails that test. The all-orders result is restricted to
this ansatz and sector; it is not derived from H_R. The actual parent has
not acquired nonlinear Einstein constraints through this calculation.

Simply substituting the corrected kinetic term also fails as an unreduced
quadratic energy: its homogeneous trace value is -3 t^2/2, unaffected by
any strength of this parent's zero-momentum constraint penalty. This
obstruction is checked in Lean. A viable revision needs a justified
constraint reduction and controlled microscopic dynamics, not just a
different trace coefficient. See the [completion plan](TOE_COMPLETION_PLAN.md)
for the exact Hamiltonian, boundary term, periodic counterexample and
remaining proof obligations.

The subsequent [constraint-algebra module](UnifiedTheory/Audit/KFCausalDiagonalConstraintAlgebra.lean)
checks all three bracket types in that same diagonal target. The
[areal-clock reduction](UnifiedTheory/Audit/KFCausalArealTensorDynamics.lean)
then produces a positive inhomogeneous polarized wave Hamiltonian,
compatible longitudinal metric reconstruction, and a finite-time energy
estimate independent of Fourier cutoff. These are continuum target results.
They neither modify H_R nor establish its encoding, clock, constraint
reduction or microscopic residual bounds. The exact audit now independently
checks all six original Hamilton equations after the proposed gauge solve.

## 9. Constructive finite-time penalty estimate and the clock bridge

The new [fast-penalty module](UnifiedTheory/Audit/KFCausalFastPenaltyDynamics.lean)
constructs the leakage correction E rather than assuming a small residual.
For a kernel encoding J, K=J* F_R J and E=D_R^+ F_R J, it gives

    ||exp[-it(Lambda D_R+F_R)]J-J exp[-itK]||
      <= [2||E||+t||E K-F_R E||]/Lambda.

The finite [spectral-inverse module](UnifiedTheory/Audit/KFCausalFinitePenaltyInverse.lean)
constructs the kernel projector and inverse from a symmetric matrix and
proves their identities. The exponential estimate is proved for bounded
skew-adjoint generators, with their flow equations and norm bounds derived.
It is quantitative at fixed finite dimension. Uniform control as R and
volume increase still requires bounds on the displayed numerator and gap.

The [new audit](scripts/fast_penalty_dynamics_audit.py) checks the original
six-flavor collective operators and stencils on a periodic 1 x 2 x 1
carrier. All 49 (R=1) and 784 (R=2) collective states are retained, including
dense-occupation dark states. Thirty finite-time evolution comparisons
obey the bound. The comparison is with the actual finite-R kernel
compression; no occupation cutoff or gravitational target is substituted.

The [areal bridge module](UnifiedTheory/Audit/KFCausalArealMicroscopicBridge.lean)
also identifies why the free parent is not yet the areal-clock system.
A scalar time change with the same canonical fields cannot match the
time-dependent ratio of the two areal coefficients. A canonical rescaling
does give a positive fixed-speed wave with mass squared 1/(4t^2), and Lean
proves a decreasing rescaled mode energy. The clock and this field map are
still continuum inputs. The bare tensor symbol also penalizes the
nonlinear longitudinal metric response required by the areal constraint.
Composite or dressed metric observables remain possible and require a
separate construction. See the [completion plan](TOE_COMPLETION_PLAN.md)
for formulas, numerical results, scope and the remaining microscopic task.

## 10. Internal clock and the boundary of the free-parent route

The [internal-clock proof](UnifiedTheory/Audit/KFCausalInternalClock.lean)
uses a retained homogeneous free coordinate of the massless canonical
comparison. A positive-momentum, fixed-total-energy branch gives the
exact relational generator K_E(h)=2[E-sqrt(E(E-h))], with evolution error
at most |t| e^2/E on a system-energy band [0,e]. Generalized stationary
clock states and finite-spin packet preparations are distinct here.
The new [audit](scripts/internal_clock_metric_audit.py) independently
checks full six-flavor block packets through R=16 (74613 collective
states) and derives their exact initial rate. Finite-R clock corrections
remain substantial; the earlier r>0 spectral argument does not supply
the massless clock limit.

The [periodic reconstruction](UnifiedTheory/Audit/KFCausalPeriodicMetricReconstruction.lean)
constructs the reduced longitudinal metric globally, retaining its mean
datum and total-momentum compatibility condition. Exact lattice currents
give its time evolution and an energy bound without an extra volume
factor. This constructs a composite for the supplied reduced constraint;
it does not identify a microscopic metric operator.

The [local-map obstruction](UnifiedTheory/Audit/KFCausalLocalClockObstruction.lean)
proves that a positive time change and any time-dependent linear
symplectic point map cannot convert the free massless wave into the
rescaled areal target with mass squared 1/(4t^2). This strengthens the
earlier scalar-time-change test. Interacting phases and spatially nonlocal
or derivative-dependent transformations are not excluded.

A [revised autonomous canonical model](UnifiedTheory/Audit/KFCausalAutonomousArealClock.lean)
adds the positive interaction u^2/(8T^2) and includes its clock force.
Lean proves energy conservation along solutions and an explicit bound
on relational clock feedback. This term is a proposed modification of
the slow dynamics, not a derived term of (8) or (9). Its bounded local
spin implementation and joint regulator limits remain open. The
[completion plan](TOE_COMPLETION_PLAN.md) records the exact formulas,
proof boundaries and audit results; the full microscopic gap is not closed.

## 11. Finite-spin clock amplitude repair

The clock-block drift can be reduced constructively. For the actual
collective spin annihilator B_a, set x=(N-1)/R and

    A_a=B_a[1+x/2+3x^2/8],
    Q_a=(A_a+A_a*)/sqrt(2),  P_a=(A_a-A_a*)/(i sqrt(2)),
    H_clock=U sum_a P_a^2/2.

The [repair module](UnifiedTheory/Audit/KFCausalSpinClockRepair.lean)
proves that the relative annihilation-amplitude defect is at most x^3,
instead of the original linear defect. A first-degree correction gives
x^2; both have dimension-independent squared weighted-shift norm bounds.
The second correction has at most six spin cells per Hamiltonian term
when expanded, but this does not imply bounded geometric range.

The [audit](scripts/spin_clock_repair_audit.py) retains all six flavors
and all collective states through R=16. At R=16 and t=0.5, the absolute
position error falls from 0.114615 to 0.003238. Exact inverse-square-root
compensation, together with the canonical compression boundary term
U(R+6) projector(N=R)/4, reduces the error to 2.10e-7. That benchmark
generally requires growing microscopic interaction order. The rate and
force defects then live in the top two occupation sectors; their support
identities are numerically checked, while Lean proves the general
boundary-probability expectation bound and the obstruction to exact
finite-dimensional canonical commutators.

This changes both the clock Hamiltonian and its readout. It is a proposed
clock-block repair, not a theorem that the original H_R already had this
dynamics. Its insertion into the constrained spatial parent, finite-energy
relational errors, areal clock coupling and joint limits remain separate.
The [completion plan](TOE_COMPLETION_PLAN.md) and
[source-hashed report](data/spin_clock_repair_audit.json) give the full
comparisons and formal/numerical scope.

## 12. What the clock repair does not resolve: the matter constraints

The current free-parent route requires a dynamics revision to reproduce
the gravitational target. A new [two-mode theorem](UnifiedTheory/Audit/KFCausalTwoModeObstruction.lean)
shows that the inverse-square areal mass cannot be obtained by a common
linear symplectic point map and positive clock change even for frequency
squared zero and one. Other phases and transformation classes remain open.

The [coupled scalar target](UnifiedTheory/Audit/KFCausalMatterConstraintAlgebra.lean)
now has all three local bracket identities checked in Lean. Closure
requires a common scalar/gravity principal coefficient and the corrected
DeWitt trace term. A scalar potential must carry its metric volume factor
to pass the spatial covariance test; its numerical mass and self-coupling
are not selected by these identities.

There is a further clock change: the [matter reduction](UnifiedTheory/Audit/KFCausalMatterArealReduction.lean)
proves that nonzero potential drives the longitudinal momentum. The old
constant-c reduction cannot simply accept a massive scalar. Retaining
c=-P_L as a dynamical positive field gives a positive reduced Hamiltonian
and nondecreasing c for nonnegative potential, along supplied solutions.
An independent [symbolic audit](scripts/matter_clock_revision_audit.py)
checks the revised reduction against all eight unreduced Hamilton equations.
These are proposed continuum target dynamics. None has been derived from
the spin H_R of this note. The [model decision](EINSTEIN_MODEL_DECISION.md)
and [completion plan](TOE_COMPLETION_PLAN.md) record the exact revision and
the remaining microscopic, three-dimensional and quantum obligations.

## 13. An executable finite quantum candidate for the revised target

The [new model](scripts/quantum_areal_spin_model.py) quantizes the supplied
reduced areal Hamiltonian with three active spin flavors. It keeps the
positive geometry variable c dynamical through c=exp(s), p_s=c L, and
specifies clock/matter ordering by sums of adjoint squares. A fixed-degree
version replaces half exponentials by I+X/2+X^2/8. The
[Lean proof](UnifiedTheory/Audit/KFCausalQuantumArealCandidate.lean) establishes
Hamiltonian positivity, the polynomial clock floor C>=I/4, unitary
exponential steps and a finite-clock obstruction: a nonzero Hermitian
commutator force cannot be nonnegative in every state.

The [audit](scripts/quantum_areal_spin_audit.py) tests the expected clock
response on coherent packets in complete finite occupation spaces, checks
the invariant embedding into all six flavors at R=4, and separates
capacity, polynomial, time-step and semiclassical diagnostics. A supplied
two-site graph also evolves with nonzero gravity/scalar gradient terms.
The [report](data/quantum_areal_spin_audit.json) contains source hashes;
the [completion plan](TOE_COMPLETION_PLAN.md) gives formulas and numbers.

This is an explicitly specified replacement Hamiltonian. The original
parent's selected phase has not been shown to survive these interactions.
The graph discretization does not enforce the remaining spatial constraint,
and no controlled quantum/continuum limit or TOE follows from these checks.

## 14. Spatial-constraint preservation requires a different reduction

The revised continuum target preserves
P Q_x+pi phi_x-c L_x+2c_x exactly along smooth solutions. The previous
nearest-neighbor graph candidate does not preserve the corresponding
central-difference expression: initially admissible four-site data acquire
constraint derivative (1/4,0,-1/4,0). Both statements are checked in the
[propagation module](UnifiedTheory/Audit/KFCausalArealConstraintPropagation.lean).

The [new reduced model](scripts/constraint_reduced_spin_model.py) uses all
six excitation flavors for a homogeneous geometry clock, one Q harmonic
pair, one scalar harmonic pair and a scalar zero mode. A positive-clock
Jordan inverse reconstructs the longitudinal operator. Translation-charge
averaging preserves Hamiltonian positivity and the remaining zero-charge
constraint. The [Lean construction](UnifiedTheory/Audit/KFCausalQuantumConstraintReduction.lean)
proves local reconstruction and preservation by exponential steps.
The [concrete source theorem](UnifiedTheory/Audit/KFCausalSpinSourceIdentity.lean)
now proves the spin-source identity for arbitrary finite capacity and
real radial weights, including the top boundary. It derives source
annihilation on the zero-charge sector and connects it to preservation,
also after a supplied charge-preserving clock basis change. The
[correspondence audit](scripts/spin_source_identity_audit.py) checks these
definitions against the executable matrices through R=6, dimension 924.

This replaces the graph discretization with a nonlocal Fourier reduction.
The physical sector is imposed, not selected by the original parent law.
The [completion plan](TOE_COMPLETION_PLAN.md) records the necessary classical
shift and the remaining quantum correspondence, spatial continuum and
microscopic locality gaps. The source identity does not eliminate the
finite-clock commutator defect.

A further [basis-independent reconstruction](UnifiedTheory/Audit/KFCausalConcreteClockConstraint.lean)
now removes the supplied clock spectral basis and proves the actual
polynomial clock positive and translation neutral. The
[specified Hamiltonian theorem](UnifiedTheory/Audit/KFCausalReducedSpinHamiltonian.lean)
uses the full ordered finite Hamiltonian and proves preservation along
exact continuous-time Schrodinger flows, rather than only frozen steps.
The subsequent
[global construction](UnifiedTheory/Audit/KFCausalGlobalSpinDynamics.lean)
discharges the propagator-existence premise: the specified finite model
has a unique global unitary evolution preserving the reconstructed
constraint on the imposed zero-charge sector. The proof uses bounded
auxiliary ODEs, Gram conservation and uniqueness on overlapping intervals.
This does not remove the finite-clock defect or establish a continuum limit.
The [new audit](scripts/positive_clock_continuous_audit.py) checks the
operator transcription and six full-space time-dependent propagators.

The subsequent [clock audit](scripts/clock_limit_exponential_audit.py)
separates the finite boundary from the functional approximation. Lean
derives state-moment bounds for the actual canonical commutator and an
exact classical counterexample to the fixed quadratic clock law. The
[exponential variant](UnifiedTheory/Audit/KFCausalExponentialClockDynamics.lean)
retains positive operators, exact reconstructed constraints and unique
global unitary dynamics while removing that fixed polynomial truncation.
Uniform evolved moment/domain bounds and the nonlinear clock-response
limit remain open; the finite theorem does not establish the continuum.
