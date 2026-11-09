# Collective interactions and the scale of a possible gravitational coupling

Date: 2026-09-11

The [selected spin-block parent](SPIN_BLOCK_WAVE_PARENT.md) has a
controlled Gaussian limit and an explicit parity mismatch with the
[reduced Einstein target](REDUCED_TENSOR_HAMILTONIAN.md). This note
tests two proposed repairs: add microscopic odd interactions, or
change the metric coordinates nonlinearly.

An explicit odd interaction preserves the selected vacuum but still
vanishes in the regular block limit. More generally, bounded-strength
interactions of fixed order have cubic coefficients of order R^(-1/2)
and quartic coefficients of order R^(-1). This is the expected
collective fluctuation hierarchy, not a universal prohibition of spin
gravity. The Einstein cubic can in fact be lifted to explicit
three-cell interactions with exactly this scaling.

The interpretation of the limit matters. If a dimensionless metric is
identified with a mean cell observable, matching the supplied canonical
Einstein normalization requires

    G_match = sigma^2 a^2/(32 pi R).                       (1)

Here a is physical coarse spacing and sigma is the specified coefficient
in that observable map after a fixed canonical wave normalization.
Equation (1) is a conditional matching relation,
not a derived Newton constant or an area-entropy law. At fixed a the
regular R->infinity limit loses the interaction. Keeping G_match fixed
instead requires coordinated scaling or a finite cutoff. The actual
Einstein vertex still lacks a proved selected two-helicity phase.

## 1. Which collective Hamiltonians have a Gaussian block limit?

Work on the active symmetric blocks from the preceding note. Fix the
number V of blocks, the cell dimension d+1=7, a maximum interaction
order k, and a finite list of interaction patterns. A p-cell pattern
is summed over distinct cells inside each block it visits and has the
form

    R^(1-p) sum_(j_1,...,j_p distinct within blocks)
                       K_(j_1,...,j_p),       p<=k.       (2)

The kernel is independent of R and has bounded norm. There may be
finitely many such patterns per block on a supplied bounded-degree
graph. This is a specified class of complete block averages; it does
not include every bounded local spin model, arbitrary growing-body
operators, singular changes of variables, or an uncontrolled critical
joint limit. Bounded R-dependent kernels can be included when their
limits and the stationary expansion below are controlled uniformly.

There are O(R^(p-1)) terms incident on a given cell. Thus (2) has a
bounded summed norm per cell, just like the preceding wave parent.
In the collective occupation basis the matrix-unit sums are exactly

    T_00 = R-N,
    T_(alpha,0) = sqrt(R) a_alpha^dagger sqrt(1-N/R),
    T_(0,alpha) = sqrt(R) sqrt(1-N/R) a_alpha,
    T_(alpha,beta) = a_alpha^dagger a_beta.                (3)

The a's in (3) are oscillator ladder operators on the embedded chart
N<=R. They are used with the displayed square roots and endpoint
restriction, not as exact finite-dimensional canonical operators.

Expand each kernel into products of local matrix units. The sum over
distinct cell labels is the unrestricted product of T's minus its
coincident-label terms. These latter terms have fewer distinct factors
and are obtained by the finite inclusion-exclusion formula over
partitions of the p labels. Products of matrix units at one cell reduce
to matrix units again. This reduction is exact for fixed p.

A vacuum diagonal factor in (3) supplies R, an off-diagonal vacuum
transition supplies sqrt(R) and one fluctuation variable, and an
excitation-to-excitation factor supplies two fluctuation variables
with no power of R. Replacing an R by -N adds two fluctuation variables
and removes one power of R. Each square-root correction does the same.
Normal ordering can reduce polynomial degree through contractions but
cannot increase the power of R. A coincident-label correction has an
extra inverse power of R relative to the corresponding lower-order
complete average. Consequently every normal-ordered term of degree m
has coefficient at most

    O(R^(1-m/2)).                                        (4)

On inputs with total occupation at most M, retain all output rows
through occupation M+k. For R>=2(M+k), the square roots have uniform
Taylor bounds on that finite set. After the constant and linear terms,
the quadratic truncation therefore has an operator error on these
inputs bounded by C_(M,V,k)/sqrt(R). In particular,

    H_R = E_R + sqrt(R) L_1 + H_2 + O_(M,V,k)(R^(-1/2)), (5)

with possible vanishing corrections to the displayed lower-degree
coefficients. L_1 is the tangent of the coherent product-state energy
at the chosen vacuum. A stationary vacuum has L_1=0. Its stability and
occupation control must be established separately; they are not
consequences of power counting. If H_2 is strictly positive and an
R-uniform occupation coercivity estimate holds at fixed V, the
compactness/core argument in the preceding note yields the Gaussian
ground-state limit. Without those hypotheses (5) is only a controlled
fixed-input expansion.

For a simple sharp example, take p raising operators of one excitation
species on distinct cells, plus their adjoints, normalized as (2).
Its vacuum-to-p matrix element is exactly

    sqrt(p!) R^(1-p/2)
                     sqrt(product_(j=0)^(p-1)(1-j/R)).   (6)

The summed per-cell norm is at most p. Thus a bounded cubic coefficient
does vanish like 1/sqrt(R), whereas a fixed nonzero collective cubic
coefficient would require an increasing microscopic coefficient in
this class and these units. Tuning a Hessian to zero and rescaling time
or fluctuations can change the conclusion; so can a coordinated spatial
limit. None is covered by simply taking the regular limit (5).

Quasifree collective fluctuation dynamics is established prior work;
see [Goderis, Verbeure and Vets](https://doi.org/10.1007/BF02096872).
Their general lattice hypotheses differ from this explicit finite-block
calculation. Equations (3)-(6) provide the argument for the class used
here, rather than invoking a general central-limit theorem outside
its assumptions.

## 2. Breaking parity while preserving the selected vacuum

Use the previous positive wave parent with its occupation penalty
lambda sum N_x^2/R. Let Q_(x,eta) be the extra singlet coordinate.
For beta>=0 add

    V_beta = -beta/sqrt(2R) sum_x {N_x,Q_(x,eta)}.         (7)

It is a scalar under the original internal spin rotations. With
S_X=sum_j X_(j,eta), its exact cell expansion is

    V_(beta,x) = -beta/(2R) sum_j X_(j,eta)
                -beta/R sum_(j!=l) n_j X_(l,eta).        (8)

This uses {n,X_eta}=X_eta. Equation (8) acts on at most two cells,
and adds at most 2 beta to the per-cell interaction budget. It breaks
the global excitation parity of the even parent.

Every new off-diagonal entry in the active occupation basis is
nonpositive. Thus the previous permutation-averaging proof for H_0
still applies with the same exchange threshold J_0. The added
Delta C_x/R still gives a gap Delta above the ground energy to
excluded active symmetry sectors. Replacing an inactive cell by
Omega changes the expectation of (7) by zero: every newly incident
term contains either the zero occupation or a zero X mean of that
vacuum. The same inactive repair bound therefore applies as well.

Stability of the occupation chart is also explicit. For r>0,
the contribution of the singlet Q coordinate can be completed as

    (r/2)Q^2 - beta/sqrt(2R){N,Q} + lambda N^2/R
      = (r/4)Q^2
        + (r/4)[Q-2sqrt(2) beta N/(r sqrt(R))]^2
        + [lambda-2 beta^2/r]N^2/R.                     (9)

This is an operator identity retaining the anticommutator. Put
c=min(U,r/2). If

    lambda-2 beta^2/r >= c(d+1)/2,

the same number identity as before proves

    H_R+V_beta restricted to the collective space
                          >= c sum_x N_x + dcV/2.        (10)

Hence the selected ground state still converges to the same Gaussian
at fixed V and r>0. This time parity is not protecting the limit:
the odd interaction itself goes to zero on the relevant input core.

Subtracting the linear term in (8), the one-species oscillator form
of the remaining odd interaction is

    -beta/sqrt(R) [a^dagger a^dagger a+a^dagger a a]
                                             + O_M(R^(-3/2)). (11)

Other excitation species contribute the corresponding N_other Q_eta
terms. An exact matrix element in the one-species chart extracts the
coefficient beta/sqrt(R), including its finite-R square-root factor.
For inputs of occupation at most M, the audit's full-output estimate is

    ||[sqrt(R)V_beta + beta{N,Q_infinity}/sqrt(2)] P_M||
      <= beta/(2R) [(2M+1)sqrt(M+1)M
                              +(2M-1)sqrt(M)(M-1)].      (12)

The proof uses 1-sqrt(1-x)<=x on the raising and lowering matrix
elements and the triangle inequality. Equation (7) is a diagnostic
odd scalar interaction, not the gravitational tensor vertex.

The numerical audit checks complete microscopic spaces, including
inactive cells, and a separate O(5) radial reduction. In that reduction
m is the singlet occupation and n is the total quintet occupation in
angular sector ell, with n=ell,ell+2,... and N=m+n<=R. The diagonal is
the previous d=6 wave diagonal plus lambda N^2/R. The three independent
off-diagonals are

    (m,n)->(m+2,n):
      (r-U)/(4R) sqrt((R-N)(R-N-1)(m+1)(m+2)),
    (m,n)->(m,n+2):
      (r-U)/(4R) sqrt((R-N)(R-N-1)(n-ell+2)(n+ell+5)),
    (m,n)->(m+1,n):
      -beta/(2sqrt(R))(2N+1)sqrt((m+1)(1-N/R)).           (13)

Every O(5) angular sector is included when identifying each tested
ground state. The full infinite Gaussian tail is included in reported
state distances. The proof, not the small set of block sizes, supplies
the asymptotic convergence claim.

## 3. An explicit microscopic lift of the Einstein cubic

The preceding result does not prevent an Einstein-sized interaction
at finite R. Let H be a traceless symmetric matrix of five real
coordinates and let D_i H denote a supplied coarse finite difference.
Discretize the continuum first-derivative polynomial

    G_1=C(DH),
    G_2=(1/2)C((DH)H+H(DH))-H G_1,
    B_A(X,Y)=A^ij X^k_(il)Y^l_(jk),
    C_3(H,DH)=-2[2B_I(G_1,G_2)-B_H(G_1,G_1)].           (14)

C has the connection index arrangement defined in the reduced
Hamiltonian note. Equation (14) is a polynomial discretization of
its integrated cubic density. It does not assert a discrete product
rule, an exact finite-lattice curvature identity, or gravitational
constraint closure. The tracefree extension away from TT inputs is
chosen; only its value on TT inputs is the Einstein target.

Use the Frobenius-orthonormal basis
diag(1,-1,0)/sqrt(2), diag(1,1,-2)/sqrt(6), and the three normalized
symmetric off-diagonal matrices. This differs from the prior quintet
basis by a real orthogonal transformation, so the corresponding cell
X operators still have norm one. Exact expansion of (14) has 93
nonzero monomials, each linear in H and quadratic in DH. In this
basis the sum of absolute jet-polynomial coefficients is

    14sqrt(6)/3 + 23sqrt(2)/2.

The machine-readable report contains all coefficients. Independent
exponential-metric Frechet derivatives check the cubic extraction at
TT first jets. These pointwise bulk tests do not solve the nonlinear
constraints or replace the existing compact integrated TT benchmark.

After expanding the finite-difference stencils, write the spatial sum
as C_3(Q)=sum_(abc)c_abc Q_a Q_b Q_c. Each label includes block and
component. At finite R components in one block need not commute.
Define W(A,B,C) as the average of the six operator orderings and set

    H_(3,R) = chi/sqrt(R) sum_(abc)c_abc W(Q_a,Q_b,Q_c).

Since Q_a=(2R)^(-1/2)sum_j X_(a,j), its exact microscopic lift is

    H_(3,R) = chi/(2sqrt(2)R^2)
       sum_(abc)c_abc sum_(j,l,m)
                        W(X_(a,j),X_(b,l),X_(c,m)).      (15)

All coincident-cell terms are retained. They are necessary for exact
equality; they simply act on fewer than three cells. Every term is
Hermitian and has support on at most three four-spin cells, or twelve
qubits. It commutes with block permutations and preserves every
cell's active subspace. Thus it has an exact action on the collective
encoding, with no leakage caused by this lift.

Define the finite stencil coefficient bound

    c_star = sup_x sum_(abc)|c_abc|
                 [1_(x_a=x)+1_(x_b=x)+1_(x_c=x)].

For one cell in block x, at most the displayed multiplicity times
R^2 microscopic triples are incident on it. Because each Weyl average
has norm at most one, the new per-cell interaction budget is at most

    |chi| c_star/(2sqrt(2)),                              (16)

independent of R,V for fixed bounded stencils. This is still locality
on the supplied block graph, with growing internal connectivity.

On fixed occupation inputs the rescaled cubic sqrt(R)H_(3,R)
approaches chi C_3(q) with full-output error O_M(1/R). The operator
itself vanishes as (4) requires. Its value on the prior normalized
compact TT direction is 2c_3 times the cube of that canonical field
amplitude, where c_3=16.8837949274... is the exact coefficient in the
reduced Hamiltonian note. This uses C_3=-2 integral R_3 and checks
the normalization without changing that prior result.

Equations (14)-(16) encode a supplied Einstein vertex. The lifting
formula imposes no nonpositive-off-diagonal condition like that of
Section 2, so it does not supply that selection proof. Permutation
invariance alone proves preservation of a
sector, not energetic selection of that sector. No uniform ground
selection or physical two-helicity reduction is claimed for the
Einstein lift. Those remain the immediate dynamical tasks.

## 4. Stabilizing the chart without fixing a wrong leading quartic

The earlier lambda N^2/R guard is useful for selection, but its
normal-ordered quartic is of order 1/R, the same order as the target
Einstein quartic. Keeping it arbitrarily would contaminate an
interaction match. There is a controlled alternative for the even
wave parent: with c=min(U,r)>0 choose

    alpha=c(d-1)/2,       lambda>=c,
    H_guard = sum_x [alpha N_x/R + lambda N_x^3/R^2].      (17)

The earlier number identity gives

    H_w+H_guard >= dcV/2
       + c sum_x N_x[1-N_x/R+(lambda/c)(N_x/R)^2]
      >= dcV/2+(3c/4)sum_x N_x.                         (18)

The first term in (17) cancels the linear finite-R deficit in that
identity; 1-x+(lambda/c)x^2>=3/4 follows from lambda>=c. Thus this
alternative still gives fixed-volume vacuum convergence. It is
diagonal in the active occupation basis, so the same exchange and
inactive-state selection proofs apply to this even parent.

For commuting cell excitation projectors,

    N^3=sum_i n_i + 6sum_(i<j)n_i n_j
                         +6sum_(i<j<k)n_i n_j n_k.       (19)

The guard acts on at most three cells and has per-cell summed norm
at most alpha+3lambda. In normal-ordered oscillator variables,

    N^3 = :N^3: + 3:N^2: + N.

Consequently the guard's quartic coefficient is 3lambda/R^2 rather
than lambda/R. Its leading order-1/R contribution is the known
quadratic counterterm alpha N/R. The finite-block wave operators
still have their own quartic corrections, which must be matched or
removed. This guard does not magically supply Einstein's quartic.
At higher orders it also adds non-Einstein vertices unless the full
microscopic construction compensates or renders them irrelevant.

This is a separately proved guard for the even parent. Equations
(18),(19) are not a proof of a selected vacuum for the combined
Einstein cubic, gravitational constraints and guard. In particular,
one cannot silently reuse the sign argument after (15) is added.

## 5. Can a nonlinear metric coordinate turn the free limit into gravity?

A configuration-only change with its canonical cotangent lift already
fails at cubic order in the specified logarithmic target. At a finite
spatial/TT mode regulator normalize the free Hamiltonian as

    H_free=(1/2)p^T p+(1/2)q^T Kq,
    h=phi(q)=q+F_2(q)+O(q^3),       s=(Dphi)^(-T)p,

where F_2 is homogeneous quadratic. The transformed cubic is

    H_3=s^T sym(DF_2(h))s-h^T K F_2(h).                 (20)

The logarithmic Einstein target has zero momentum-dependent cubic
as a functional identity for all TT canonical pairs. Matching it
therefore requires DF_2+(DF_2)^T=0. Put
S_ij=partial_i F_j+partial_j F_i. Then

    2partial_j partial_k F_i
              =partial_j S_ik+partial_k S_ij-partial_i S_jk=0.

A homogeneous quadratic F_2 with zero second derivatives vanishes.
Equation (20) then cannot produce the nonzero potential cubic.
This proof applies even if a regulated configuration map mixes spatial
modes; it assumes an invertible map on the same canonical degrees of
freedom. It does not impose the missing constraints or remove four
degrees of freedom from the six-component parent.

The restriction to a cotangent lift matters. A momentum-dependent
canonical transformation can manufacture a pure cubic from a free
oscillator. For H_2=(p^2+omega^2 q^2)/2 use

    F_3=c q^2 p/omega^2 + 2c p^3/(3omega^4),
    {H_2,F_3}=c q^3,
    (1/2){{H_2,F_3},F_3}
           =3c^2 q^4/(2omega^2)+3c^2 q^2 p^2/omega^4.   (21)

The Lie-transformed Hamiltonian has these vertices and is still
canonically equivalent to the free oscillator. The inverse transform
removes them through quartic order exactly. This is an independent
oscillator example: the compact Einstein profile in the earlier note
is not an invariant one-mode truncation and is not used as one here.

Thus an isolated nonzero cubic is not a coordinate-invariant proof
of gravitational interaction. An admissible invertible local field
redefinition preserves on-shell scattering under the usual equivalence
theorem hypotheses; see
[Kamefuchi, O'Raifeartaigh and Salam](https://doi.org/10.1016/0029-5582(61)90056-6).
Momentum-dependent or nonlocal constructions require their own domain,
asymptotic-state and locality checks. The existing
[Einstein four-graviton amplitudes](https://arxiv.org/abs/2002.12374)
offer an eventual physical comparison. This note does not compute a
microscopic scattering amplitude or assert equivalence for singular
or asymptotically nontrivial transformations.

## 6. Physical units and the required coordinated scaling

This section makes an additional conditional identification; it is not
part of the selection theorem. In three spatial dimensions set the
physical light speed and hbar to one. Use the oscillator variables in
the established block limit, and write its massless wave expression as

    H_lat=(1/2)sum_x [U P_x^2+g sum_i(Q_(x+e_i)-Q_x)^2],
    v=sqrt(Ug),       b=(U/g)^(1/4),
    Qhat=Q/b,         Phat=bP,
    H_phys=H_lat/(av)
          =(1/(2a))sum_x [Phat_x^2+sum_i(D_i Qhat_x)^2].

This is a fixed canonical rescaling, not a choice U=g that would
violate the previous exchange sign threshold on a cubic graph.
It assumes g>0 and that the required massless sector is obtained.
For r>0 the same rescaling gives mass squared r/(g a^2); the finite-R
critical tuning has not been established.

The continuum normalization is Qhat_x=a phi(x), Phat_x=a^2 Pi(x):
the canonical one-form sum Phat delta Qhat approaches integral
Pi delta phi, and H_phys approaches the usual continuum wave
Hamiltonian. Applying this normalization to a physical TT tensor
assumes the appropriate two-helicity reduction has been obtained.

Now postulate a dimensionless log metric represented by a cell mean,

    h_x=s Q_x/sqrt(R)=sigma Qhat_x/sqrt(R),   sigma=s b,
    h_x=s sum_j X_(x,j)/(sqrt(2)R).                      (22)

The supplied Einstein normalization is
h=sqrt(2kappa)phi=sqrt(32 pi G)phi, with kappa=16 pi G.
Comparing with (22) proves (1), or equivalently

    G_match=s^2 sqrt(U/g) a^2/(32 pi R).

There is a separate interaction check of the same factors. In the
continuum Einstein normalization, E_3=sqrt(32 pi G) C_3(phi).
Since Q=b a phi and D_lat Q=b a^2 partial phi+O(a^4) on smooth
fields, the spatial lattice cubic sum in (14) approaches
b^3 a^2 C_3(phi). Hence the physical coefficient of (15) is

    chi b^3 a/(v sqrt(R)).

Matching it to sigma a/sqrt(R)=sqrt(32 pi G_match) requires

    chi=s g.                                            (23)

Thus the microscopic vertex coefficient and the mean-metric
coefficient are linked; they cannot be chosen independently and then
called a gravitational match. In normalized variables (23) is exactly
the coefficient sigma/sqrt(R) for C_3(Qhat).

The error estimate for the difference stencil is a smooth-field
statement in its long-wavelength regime. It is not a uniform quantum
continuum limit. Equations (22),(23) agree kinematically and at the
supplied cubic vertex; they do not derive the remaining Einstein
coefficients, universal coupling, or a measured Newton constant.

For fixed sigma and a, R->infinity sends G_match to zero. Sending
a->0 simultaneously does not fix that problem. Keeping G_match>0
with sigma bounded requires a^2 proportional to R, or retaining
finite R,a. If R grows along that relation, a grows: this is a
coarsening or infrared sequence, not a finer ultraviolet lattice.
Wavelengths must grow faster than a for a long-wavelength description.

This gives the hierarchy (4) a possible gravitational interpretation:
at fixed physical G, a packet of size a has dimensionless coupling
sqrt(G)/a of order 1/sqrt(R), while its physical dimensionful G stays
constant. In that interpretation the regular Gaussian limit describes
progressively weaker long-wavelength interactions. It is not itself
the full interacting continuum theory.

There is a further domain requirement. Holding a nonzero classical
metric strain h fixed in (22) requires Q of order sqrt(R), and hence
occupation of order R. Such coherent states are outside the fixed-M
estimates of Section 1. Their small-occupation-fraction dynamics must
be controlled separately. The prior unrestricted onsite affine
representation does not by itself provide that control in this
rescaled mean-metric chart.

Equation (1) motivates testing blocks whose number of contributing
cells scales with coarse area. It does not derive a coarse-graining
map, the number of physical boundary degrees of freedom, black-hole
entropy, a causal-order geometry or holography. Those would be new
dynamical claims and require independent evidence.

## 7. Consequences for the proposed model

The strict regular block limit at fixed physical spacing should no
longer be presented as an interacting gravitational endpoint. Within
the tested class it is a Gaussian approximation. There is now a
concrete finite-R alternative to test: the supplied cubic has a
bounded-strength three-cell lift, and a three-cell occupation guard
can preserve the even reference vacuum without fixing an arbitrary
leading quartic.

The unresolved construction must establish selection and number
control with the actual tensor interaction and its constraints,
remove the four extra canonical pairs, reproduce the coupled
Einstein quartic including its constraint-generated Newton kernel,
and control a physical scaling with nonzero G. The constraint map
and metric dressing must use the same canonical normalization.
An invariant interaction test must distinguish real scattering
from the coordinate-induced vertices illustrated by (21).

The new results do not provide that combined construction, a joint
critical limit, matter/gauge dynamics, or a physical TOE. They rule
out two shortcuts within explicit scopes and provide a microscopic
vertex and scaling relation for a more direct attempt.

## 8. Reproduction

    OPENBLAS_NUM_THREADS=1 python3 -W error::RuntimeWarning scripts/collective_gravity_coupling_audit.py

The report is
[data/collective_gravity_coupling_audit.json](data/collective_gravity_coupling_audit.json).
It contains exact identities and 64 numerical cases: point-map ranks,
full-output odd-vertex convergence, sharp creation-interaction powers,
complete microscopic spectra, independent radial spectra and ground
states, a noncommuting Weyl lift, independent exponential-metric jet
checks, and the higher-order occupation guard. The 93 exact cubic
monomial coefficients are included separately. No new Lean theorem
or general central-limit theorem is claimed. Earlier completed source
files remain unchanged.
