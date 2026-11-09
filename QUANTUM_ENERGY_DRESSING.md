# Quantum clocks repair the noncommuting energy-dressing problem

Date: 2026-09-11

The [boundary prefix code](GRAVITATIONAL_BOUNDARY_DRESSING.md) records
commuting occupation energies. Replacing them by overlapping quantum
energy terms can leave no physical states at all. This note proves a
uniform lower bound on that failure and constructs a clock-dependent
repair for arbitrary supplied finite quantum Hamiltonians.

The repair has exactly commuting constraints, retains the full supplied
matter Hilbert space, and represents its total Hamiltonian on the last
clock. For a nearest-neighbor chain, the local source terms have a
uniform exponential locality estimate on a sufficiently small clock
coordinate chart. An explicit finite-register example preserves
noncommuting quantum dynamics and its boundary energy exactly.
Spectral rounding extends this to every finite Hamiltonian, with
an explicit evolution error and register-size cost.

**This constructs an energy-dressing mechanism, not Einstein gravity.**
The microscopic matter Hamiltonian, spatial chain, clocks and ordering
are inputs. The small-chart bound does not establish a uniformly local
finite-spin parent on its whole Hilbert space. No gravitational tensor
phase, nonlinear Einstein algebra, or TOE follows from this encoding.

## 1. Why commuting energy registers fail

Let A,B be Hermitian involutions with AB=-BA. They can be neighboring
spin interactions, for example

    A=X_1 X_2,             B=Z_2 Z_3.

Both a=(I+A)/2 and b=(I+B)/2 are positive local energy terms.
Suppose two commuting self-adjoint flux registers F,G act on
separate ancillary variables, hence commute with A,B. Propose
the two constraints

    C_a=F-a,                C_b=G-b.

On a joint flux spectral fiber (f,g), put
x=f-1/2, y=g-1/2, r=sqrt(x^2+y^2). Then

    C_a^2+C_b^2=(r^2+1/2)I-x A-y B,
    (x A+y B)^2=r^2 I.

Its smallest eigenvalue is

    r^2+1/2-r=(r-1/2)^2+1/4 >= 1/4.                    (1)

The joint spectral theorem therefore proves the operator bound
C_a^2+C_b^2>=I/4, independently of register dimension or range.
There is no common zero vector. Increasing the constraint penalty
cannot produce the intended zero space. Equivalently, their
commutator contains [a,b], which is invertible in this example.

This rules out the stated commuting-register substitution. It
does not rule out energy constraints with clock-dependent sources,
noncommuting geometry, or a different physical encoding.

## 2. A consistent connection made from prefix Hamiltonians

Take a finite matter Hilbert space and any bounded Hermitian terms
h_1,...,h_N. Define their prefix sums and a multiplication unitary
depending on real link-clock coordinates theta:

    H_j=sum_(i<=j) h_i,       H_0=0,
    U_j(theta_j)=exp(-i theta_j H_j),
    W(theta)=U_1 U_2 ... U_N.                            (2)

Order matters. The last factor contains the total Hamiltonian.
On L2(R^N) tensor H_matter let E_j=i partial_(theta_j),
E_0=0. The sign makes E_j exp(-i e theta_j)=e exp(-i e theta_j).
Define

    C_j=W(E_j-E_(j-1))W^dagger.                          (3)

These are self-adjoint, strongly commuting operators: they are
one common unitary conjugation of the commuting derivatives.
At fixed N, bounded derivatives of W give their usual Sobolev
domains. Define

    V_(j-1)=U_1 ... U_(j-1),
    F_j=i(partial_j W) W^dagger
       =V_(j-1) H_j V_(j-1)^dagger.

The prefix difference simplifies exactly:

    F_j-F_(j-1)=V_(j-1) h_j V_(j-1)^dagger=:h_tilde_j,
    C_j=E_j-E_(j-1)-h_tilde_j(theta),
    ||h_tilde_j(theta)||=||h_j||.                        (4)

In particular, the source need not be a sum of large prefix
energies: their extensive parts cancel. Its spatial support
and clock dependence still need separate control below.

The generalized zero solutions are exactly

    Psi(theta)=W(theta) psi_0.                           (5)

They are not normalizable vectors in L2(R^N). A physical Hilbert
space is defined by the rigging identification with psi_0 and
the inner product <psi_0,phi_0>. This is not a bounded projector
or an already prepared infinite clock state.

Most usefully, the final clock energy satisfies

    E_N Psi=W H_N psi_0,
    [E_N,C_j]=0.                                        (6)

Indeed W^dagger E_N W=E_N+H_N. Thus the boundary clock
implements the full supplied matter Hamiltonian, including its
noncommuting interactions. Its physical positivity follows if
H_N is positive after a chosen vacuum-energy shift; positivity
is not derived from clock consistency.

For any matter observable O, its physical dressed representative

    O_D(theta)=W(theta) O W(theta)^dagger                (7)

commutes with all C_j. On physical states,
[E_N,O_D] is the encoded [H_N,O]. An energy-changing observable
therefore depends on the final clock. The intermediate bare
fluxes E_j generally do not preserve the physical space.
They are not simultaneous nondisturbing records of the original
h_j; the construction does not evade (1) while retaining its
assumptions.

Put t_j=sum_(ell>=j) theta_ell. Then E_j-E_(j-1)=i partial_(t_j).
Equal site-clock readings t_j=t set theta_1=...=theta_(N-1)=0,
theta_N=t, and (5) becomes exp(-it H_N)psi_0. This is an exact
relational representation of the supplied dynamics.

## 3. Energy currents supply the first clock correction

For two terms, (4) reads

    C_1=E_1-h_1,
    C_2=E_2-E_1-exp(-i theta_1 h_1)h_2 exp(i theta_1 h_1).

The identity

    i partial_(theta_1) h_tilde_2=[h_1,h_tilde_2]         (8)

cancels the noncommuting source bracket in [C_1,C_2].
Keeping h_2 fixed would miss precisely this term.

For nearest-neighbor energy terms h_j supported on sites j,j+1,
define the Hermitian energy current

    J_j=i[h_j,h_(j+1)].

Ordinary Heisenberg evolution gives dH_j/dt=-J_j at an
interior cut. Expanding (4) at theta=0 gives

    h_tilde_j=h_j-theta_(j-1) J_(j-1)+O(theta^2),        (9)

with no linear contributions from more distant clocks.
The repair therefore uses the microscopic energy current;
it does not assume that overlapping local energies commute.

Flatness/consistency of multiple Schrödinger equations is
established mathematics; see
[Petrat--Tumulka, section 2](https://arxiv.org/pdf/1308.1065).
Their relativistic particle-position hypotheses and no-interaction
results are not being claimed for the clock construction here.
The repository's [diamond equation](CAUSAL_ORDER_CLOCK_BRIDGE.md)
is another finite consistency formulation. Equations (2)--(9)
supply an explicit connection and boundary action for this
energy-prefix application.

## 4. A uniform locality estimate on a small clock chart

Assume an open nearest-neighbor chain and ||h_j||<=J. Fix
mu>0. A conservative Lieb--Robinson rate valid also for
piecewise time-dependent signed prefix Hamiltonians is

    alpha=8 J exp(mu).

It gives, for an evolved two-site source A and a bond h_i,

    ||[A(T),h_i]|| <= 4 J ||A||
                         exp(alpha T-mu d(supp A,supp h_i)).
                                                               (10)

The local interaction norm load is at most 2J, supports have
size two and diameter one. The usual interaction-chain estimate
gives the displayed conservative constants. Time-dependent
quasi-local dynamics and comparison estimates are treated in
[Nachtergaele--Sims--Young](https://arxiv.org/abs/1810.02428).

Suppose |theta_i|<=delta for i<N and

    beta=mu-alpha delta>0.                              (11)

For 1<=r<j, approximate h_tilde_j using only clocks
theta_(j-r),...,theta_(j-1). In each retained U_k replace H_k
by sum_(ell=j-r)^k h_ell. Call the result h_tilde_j^[r].
It is supported on matter sites j-r,...,j+1 and depends on
only those r clocks. The following all-size bound holds:

    ||h_tilde_j-h_tilde_j^[r]||
      <= 4 J ||h_j|| delta exp(-beta r)
          [1/((1-exp(-mu))(1-exp(-beta)))+r exp(mu)].     (12)

One may also use the trivial upper bound 2||h_j||.

Here is a proof with both truncations included. Let
A_k=Ad_(U_k ... U_(j-1))(h_j). For an omitted k,

    ||A_k-A_(k+1)|| <= |theta_k| ||[H_k,A_(k+1)]||.

Its future evolution lasts at most delta(j-k-1).
Summing (10) over bonds i<=k gives a geometric spatial factor
1/(1-exp(-mu)), with distance at least j-k-1. Summing over
omitted k<=j-r-1 gives the first term in (12).

There remain r retained evolutions, of total absolute duration
at most r delta. Restricting their Hamiltonians to the stated
matter interval only introduces one crossing bond at its left
edge; the other removed bonds commute with every operator on
the interval. Duhamel's formula and (10) bound the resulting
error by 4 J ||h_j|| r delta exp(alpha r delta-mu r).
The slightly looser exp(mu) factor in (12) also covers a
one-site change of boundary-distance convention.

The constants do not grow with total chain length or j.
At mu=1, delta<1/(8eJ) suffices. This is a useful chart
condition on differences of neighboring site times, not
a derivation of a Lorentz metric or an observer cone.

The qualification is essential: (12) holds on the restricted
clock-coordinate chart. The generalized solutions (5) range
over all clock coordinates. Their global quantum constraint
theory is not thereby a uniformly local, bounded finite-spin
Hamiltonian. Nor has a corresponding three-dimensional
geometric ordering and bound been constructed.

## 5. A finite-register realization with noncommuting energies

The three-spin terms A=X_1X_2 and B=Z_2Z_3 above satisfy
A^2=B^2=I and (A+B)^2=2I. Their two prefix spectra are
therefore commensurate individually. Use two odd-dimensional
clock registers D=2M+1, angles theta_n=2 pi n/D, and Fourier
basis exp(-i m theta_n)/sqrt(D), -M<=m<=M.

Let E be the Hermitian clock operator with those eigenvalues m,
and set

    E_1=E tensor I,          E_2=sqrt(2) I tensor E,
    W(theta_1,theta_2)=exp(-i theta_1 A)
                  exp[-i theta_2(A+B)/sqrt(2)],
    C_1=W E_1 W^dagger,
    C_2=W(E_2-E_1)W^dagger.                             (13)

Matter identities are implicit. W is an actual finite
block-diagonal unitary, not a formal differential expression.
The C's commute exactly. Their common zero space has dimension
eight: in the untransformed Fourier basis E_1=0 first forces
m_1=0, and E_2-E_1=0 then forces m_2=0.

The isometry is

    V psi=(1/D) sum_(n_1,n_2) |n_1,n_2>
                                      W(theta_n1,theta_n2)psi.

Each dependence on a clock contains frequencies only +/-1.
For D>=3 this implies exactly

    E_2 V=V(A+B),       C_j V=0,
    exp(-it E_2)V=V exp[-it(A+B)].                       (14)

The encoded dynamics are thus preserved, rather than reduced
to classical energy labels. For D=3,5,7, the positive parent

    H_parent=10(C_1^2+C_2^2)+E_2+sqrt(2)I                (15)

has the physical energies 0 and 2sqrt(2), each fourfold.
Off the code, C_1^2+C_2^2>=I: on any nonzero Fourier pair
the first nonzero flux contributes at least one to the
sum of difference squares. The excluded energies are therefore
at least 10-(M-1)sqrt(2)>2sqrt(2) for these three D's.
This proves full-band separation in this finite example.

### The finite-clock derivative has a cutoff boundary

The continuum-looking forms would be

    C_1,form=E_1-A,
    C_2,form=E_2-E_1-exp(-i theta_1 A)B exp(i theta_1 A).
                                                               (16)

They agree with (13) on input clock Fourier modes
|m_1|,|m_2|<=M-1, and annihilate the code exactly.
The margin prevents wrapping when W^dagger shifts a clock
frequency by one. On the full clock Hilbert space they differ
from (13). The omitted cutoff terms restore exact commutation;
the naive forms do not commute globally.

Agreement on an input band does not imply equality of products
on that band: a first operator can leave it. The audit therefore
tests the exact constraints, the restricted forms, and their
full-space failures separately.

This is a finite patch of two clocks and three matter spins,
with total dimensions 72, 200 and 392 in the audit. It is not
a spatial thermodynamic phase. Generic prefix spectra need not
be commensurate; simply sampling (2) on finite cyclic clocks
would not reproduce (14). The next section supplies a controlled
finite approximation. The global support
of the conjugated parent and the unrestricted clock angles
also prevent inferring uniform locality from this finite test.

## 6. Finite clocks for arbitrary prefix spectra

Fix an energy spacing Delta>0. By spectral functional calculus set

    R_j=Delta round(H_j/Delta),       R_0=0.

Rounding each eigenvalue to a nearest integer gives

    ||R_j-H_j|| <= Delta/2.                             (17)

This does not require the different H_j to commute. Choose an
integer M>=max_j ||R_j||/Delta, M>=1, and D=2M+1. Each clock has
energies Delta m, -M<=m<=M, and coordinate samples
theta_n=2 pi n/(D Delta). Put

    W_R(theta)=exp(-i theta_1 R_1) ... exp(-i theta_N R_N),
    V_R psi=D^(-N/2) sum_n |n> W_R(theta_n)psi,
    C_j^R=W_R(E_j-E_(j-1))W_R^dagger.                   (18)

Here W_R in the last line is a finite block-diagonal unitary.
The C_j^R commute exactly, and their joint kernel is the range
of the isometry V_R, with the complete matter dimension.
Every clock dependence of W_R lies inside its resolved Fourier
band. In particular, differentiating its rightmost factor is
represented exactly by the final finite clock:

    E_N V_R=V_R R_N,
    exp(-it E_N)V_R=V_R exp(-it R_N).

Duhamel's unitary comparison identity and (17) now give

    ||exp(-it E_N)V_R-V_R exp(-it H_N)||
          <= min(2, |t| Delta/2).                       (19)

This is an operator-norm estimate for all matter states, not an
estimate for a selected eigenstate. It compares a common energy
zero. Subtracting the two separate ground energies instead
gives the bound min(2, |t| Delta), by the same eigenvalue estimate.
The map uses full prefix spectral decompositions; no efficient
local algorithm for preparing it is claimed.

### Exact code separation and its cost

The master constraint K_R=sum_j (C_j^R)^2 is unitarily equivalent
to Delta^2 sum_j (m_j-m_(j-1))^2, with m_0=0. Each nonzero
integer tuple has at least one nonzero difference, and the tuple
m_j=1 for every j attains the bound. Hence its spectral gap is
exactly Delta^2, independently of N, on these growing registers.

E_N preserves the code by (18); self-adjointness then makes the
orthogonal complement invariant too. If r_min and r_max are the
extreme eigenvalues of R_N, the parent

    H_parent=lambda K_R+E_N-r_min I                     (20)

has the physical band R_N-r_min. On its orthogonal complement
it is bounded below by lambda Delta^2-M Delta-r_min.
Thus lambda Delta^2>M Delta+r_max separates the whole code
band. For any chosen positive energy margin g, the sufficient
choice

    lambda=(2M Delta+g)/Delta^2

provides a gap of at least g above that band. The audit sets
g=1 in its chosen energy units. This is an algebraic gap
statement, not a locality statement about K_R or its square terms.

When ||h_j||<=J, one can take M=ceil(NJ/Delta+1/2), giving
D=O(1+NJ/Delta). The full clock Hilbert space has dimension
D^N, before matter. The corresponding sufficient penalty
coefficient is O((NJ+Delta+g)/Delta^2). Both resources matter:
there is no fixed local Hilbert dimension or uniform bounded
interaction strength in this construction.

### Compatibility with the small-chart estimate

There is also a norm comparison of the rounded continuous
source with the unrounded source in (4). Write

    V_(j-1)^R=product_(i<j) exp(-i theta_i R_i),
    k_j^R=V_(j-1)^R (R_j-R_(j-1)) (V_(j-1)^R)^dagger.

The difference of two rounding errors is at most Delta, while
unitary telescoping gives
||V_(j-1)^R-V_(j-1)||<=Delta sum_(i<j)|theta_i|/2.
Therefore

    ||k_j^R-h_tilde_j||
        <= Delta [1+J sum_(i<j)|theta_i|]
        <= Delta [1+J(j-1)delta]                        (21)

on the chart of section 4. Adding (12) bounds the distance
from k_j^R to the same strictly local unrounded approximation.
Spectral rounding itself can be spatially nonlocal; (21)
controls that error in norm, not in exact support.

At fixed J and delta, Delta_N N -> 0 is sufficient to make
this extra source error vanish uniformly in j<=N. For example
Delta_N=N^(-1-epsilon) with epsilon>0 permits D=O(N^(2+epsilon)).
This is a sufficient construction cost, not a lower bound
on all possible encodings. A fixed Delta leaves an extensive
upper bound; the estimate then supplies no thermodynamic
locality conclusion.

As in section 5, exact finite constraints require the Fourier
cutoff corrections. Equation (21) compares continuous
clock-coordinate source functions. It does not turn the
finite conjugated constraints into the bare derivative-minus-
source expressions on the whole clock Hilbert space.

The coordinate chart also does not capture most of the encoded
history's norm. For every normalized matter state, unitarity of
each W_R(theta_n) gives exactly uniform joint clock probabilities
D^(-N). Take principal coordinate values in (-pi/Delta,pi/Delta)
and 0<=delta<pi/Delta. The probability that all first N-1 clocks
lie in the small chart is exactly

    Pr(chart)=[(2 floor(D delta Delta/(2 pi))+1)/D]^(N-1)
             <= [delta Delta/pi+1/D]^(N-1).            (22)

In the fine-energy sequences just described this tends to zero.
Projecting the history into that chart therefore removes nearly
all its norm. Conditional clock descriptions remain possible,
but (12) and (21) cannot be promoted to full-code locality by
assuming the histories are already concentrated in the chart.

Relational descriptions using clock correlations and history
states are established constructions; see
[Giovannetti--Lloyd--Maccone](https://arxiv.org/abs/1504.04215)
and the discrete multiple-clock setting of
[Baumann et al.](https://arxiv.org/abs/2105.02304).
The bounds here address the stated prefix energy encoding.
They are not a claim to have derived time or gravity from it.

## 7. What this changes, and what still selects gravity

The commuting energy-register obstacle is repaired by a
constructed clock-dependent connection. Its first correction
is the energy current; its final clock generates the complete
supplied dynamics. This extends the previous diagonal prefix
example to noncommuting quantum energies, and (17)--(21) remove
the commensurate-spectrum restriction on a finite approximation.

It does not derive the gravitational constraint algebra.
The C_j in (3) form an Abelian flat connection for any supplied
Hamiltonian, including ones with the wrong gravitational
dispersion. A field-dependent reconstruction of physical normal
and spatial deformations would be needed to obtain the
[Einstein hypersurface algebra](GRAVITY_FROM_CLOCK_CONSTRAINTS.md).
There is no such reconstruction in this note.

The next construction must connect the clock dressing to
geometric fluxes and the nonlinear metric tail derived in
[the boundary calculation](GRAVITATIONAL_BOUNDARY_DRESSING.md).
It must also control a spatially local finite-spin realization
on the relevant physical domain, a common causal cone and
vacuum stability, and universal matter coupling. Preparation,
three-dimensional refinement, nonlinear Einstein evolution,
Standard Model dynamics and a physical TOE remain open.

## 8. Reproduction

    OPENBLAS_NUM_THREADS=1 python3 -W error::RuntimeWarning scripts/quantum_energy_dressing_audit.py

The audit checks the exact Pauli and two-clock cancellation
identities, the commuting-register residual floor, continuous
connection consistency, the small-chart locality estimate
against full spin-chain matrices, and complete finite-clock
constraint and parent spectra in the two-clock example.
For generic rounded spectra it checks the entire encoding map,
boundary dynamics, constraint action on the code, source errors,
the reference master gap, and the clock-chart probability for
every encoded matter state. It does not materialize the full
parent matrix for those larger systems.

All 60 numerical cases and the exact algebraic identities pass.
The largest generic example has full dimension 148176, with a
16-dimensional code and three 21-dimensional clocks. Boundary
intertwining residuals are below 1.4e-14; the evolution error
against the supplied Hamiltonian obeys (19). These numerical
residuals support the stated algebra and do not certify floating
point arithmetic or a continuum limit. No Lean source changes.
