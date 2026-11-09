# Transporting the nonlinear quantum sector without a spurious kinetic correction

Date: 2026-09-11

The [nonlinear dressing](NONLINEAR_CONSTRAINT_DRESSING.md) exposed a
double-commutator correction to the physical Hamiltonian. This note
constructs a covariant transport that cancels that correction through
the gravitational response order already calculated. In a commuting
source model the cancellation is exact, including at zero free mass.

There is a microscopic cost. An explicit unitary spin dressing has a
diverging summed-strength requirement at fixed normal energy scale.
A slower normal scale repairs the strength bound and gives an exact
nonlinear spin-sector limit, but its interaction order grows with the
block size. The exact repair is therefore not a finite-body local
Einstein parent. Its physical spectrum is still the supplied one.

## 1. A unitary realization of the previously normalized kernel, to order two

Use the bounded physical Hermitian matrices S_i, positive real matrix
M, N=M^(-1), and auxiliary Gaussian Omega from the preceding note.
Set pi=-i hbar partial_y and

    c_i=(M y)_i+i pi_i,
    D_0=(1/2)sum_i c_i^dagger c_i,
    K=sum_(i,j) pi_i N_ij S_j,
    U_lambda=exp[-i lambda K/hbar].                     (1)

K is self-adjoint: in auxiliary momentum representation it is
multiplication by the finite Hermitian matrix sum p_i N_ij S_j.
The unitary is defined for every real lambda, including when the
S_j do not commute. Define

    c_i^U=U_lambda c_i U_lambda^dagger,
    D_lambda=U_lambda D_0 U_lambda^dagger,
    V_lambda v=U_lambda(Omega v).                       (2)

The kernel of D_lambda is exactly ran V_lambda. Its dimension equals
the physical dimension, V_lambda is an isometry, and its normal gap
is hbar times the smallest eigenvalue of M, independent of lambda.
The conditions c_i^U commute. They are not Hermitian gravitational
gauge generators, and their adjoints are not separately imposed.

There is a precise connection to the previous nonunitary construction.
On the Gaussian,

    pi_i Omega=i(M y)_i Omega,
    pi_i pi_j Omega=[hbar M_ij-(M y)_i(M y)_j]Omega.

Consequently, with X=sum y_i S_i and Q=sum N_ij S_i S_j,

    V_lambda v=Omega[1+lambda X/hbar
                     +lambda^2 X^2/(2hbar^2)
                     -lambda^2 Q/(2hbar)]v+O(lambda^3). (3)

This is exactly the order-two expansion of the normalized isometry
I_lambda=J_lambda(J_lambda^dagger J_lambda)^(-1/2) in the preceding
note. For bounded S and fixed M the remainder is in Hilbert norm,
also with the fixed polynomial auxiliary weights used below. Gaussian
moments bound the required derivatives. The two embeddings need not
agree at higher orders. We change the parent to (2), rather than
asserting an all-order equivalence with the earlier nonunitary parent.

In particular their order-two compression formulas coincide:

    V_lambda^dagger O V_lambda
      =O-lambda^2/(4hbar) sum N_ij[S_i,[S_j,O]]
        +O(lambda^4).                                  (4)

Gaussian parity removes odd orders here. Thus making the dressing
unitary does not alone remove the correction to a bare Hamiltonian.

## 2. Covariant observables remove it without changing the physical algebra

Transport a physical observable together with the states:

    O_lambda=U_lambda O U_lambda^dagger.                 (5)

Then, exactly,

    V_lambda^dagger O_lambda V_lambda=O,
    [O_lambda,c_i^U]=[O_lambda,(c_i^U)^dagger]=0,
    (O_1 O_2)_lambda=(O_1)_lambda (O_2)_lambda.          (6)

All physical commutators are preserved. These statements use the
unitary domains when the observables are unbounded; for the bounded
physical regulator they are straightforward operator identities.
They repair the earlier compression map's failure to preserve products.

Apply this to the free physical Hamiltonian H_2. Its transported
extension has the expansion

    (H_2)_lambda=H_2-(i lambda/hbar)[K,H_2]
                      -lambda^2[K,[K,H_2]]/(2hbar^2)
                      +O(lambda^3).                    (7)

The term linear in auxiliary momentum is essential. Compressing the
entire expression to the moved kernel cancels exactly the earlier
quantum correction Q_quant. This prescribes an off-constraint
extension of the kinetic energy; it is not a cancellation obtained
by discarding the normalization or treating the sources as commuting.
The extension is not unique: operators vanishing on the physical
sector can be added. The requirement to use (5) is a model choice,
not a consequence of an already-derived Einstein symmetry.

For the supplied sources S=(B,f), M=diag(8L,K_vector), retain the
same bare auxiliary response terms as in the preceding note and use

    F_lambda=(H_2)_lambda+lambda(H_3)_lambda
              +lambda^2 H_local,4
              -lambda sum_x A_x u_x
              +2 W^T K_vector W-hbar m_W.              (8)

Equations (3)-(6) and the previous Gaussian moment formulas give

    V_lambda^dagger F_lambda V_lambda
       =H_2+lambda H_3+lambda^2 H_target,4+O(lambda^3),   (9)

with the same explicitly ordered scalar and vector quartic as before.
In particular the known homogeneous-shear term in Q_quant is cancelled
at this order. This is a finite-regulator statement with the Einstein
source coefficients, H_3 and H_local,4 supplied. It does not prove
an all-order cancellation, a protected interacting graviton spectrum,
or Einstein's lapse and clock algebra.

At fixed physical regulator, fixed positive M and fixed lambda this
also defines a quantum band limit, not only a compression formula.
For H_Lambda=Lambda D_lambda+F_lambda, the lowest d eigenvalues and
their spectral projectors converge as Lambda grows to those of the
exact matrix V_lambda^dagger F_lambda V_lambda. All other levels
diverge. Quantum evolution on that physical band converges strongly,
uniformly on compact time intervals.

Here is a direct proof. In the momentum representation of (1),
U^dagger y_i U-y_i is a bounded matrix-valued multiplier, of norm
at most |lambda| ||sum_j N_ij S_j||; U leaves pi unchanged.
Thus the dressed oscillator form controls both normal momenta and
coordinates, up to constants. The terms involving only regulated
physical matrices are bounded. The vector quadratic in (8) is
positive, and the remaining term is at most linear in u. For any
eta>0 it follows that F_lambda>=-eta D_lambda-C_eta. Consequently

    H_Lambda>=(Lambda-eta)D_lambda-C_eta.

The fixed normal gap forces every bounded-energy sequence into
ker D_lambda. Compact resolvent of D_lambda gives norm compactness.
Kernel trial vectors have finite slow energy. Min-max upper bounds,
compactness and the weak eigenvalue equation on kernel test vectors
identify all d limiting levels and their multiplicities; the displayed
inequality sends level d+1 to infinity. The same bounded trial energy
controls the spectral tail for time evolution. This proof removes the
earlier general nonlinear kernel's missing band estimate at this
finite-regulator scope. Its constants are not uniform as M becomes
massless or as the physical matrix cutoff is removed.

If every term of a free Hamiltonian is transported by (5), the result
is exactly unitarily equivalent to that free theory. Its spectrum and
observables' dynamics are identical under the identification (6).
A nonlinear-looking constraint or metric response is consequently
not, by itself, gravitational self-interaction. In (8) the additional
response terms and prescribed physical interactions carry the
nontrivial dynamical input. Nothing in (1)-(6) fixes their coefficients.

## 3. Exact covariant momentum and the location of the inverse operator

For commuting coordinate sources S_i(q), put F=lambda N S(q).
The unitary translates the normal Gaussian by F. Its exact physical
momenta are

    Pi_a=p_a+sum_i (partial_a F_i) pi_i.                 (10)

They obey [q_a,Pi_b]=i hbar delta_ab and [Pi_a,Pi_b]=0.
They preserve the shifted conditions c_i^U=(M(y-F))_i+i pi_i.
For the previous untruncated example S=q^2, M=mu,

    Pi=p_q+(2lambda q/mu)pi_y,
    H_cov=Lambda D+Pi^2/2+omega^2 q^2/2.                (11)

This Hamiltonian is exactly U[Lambda D_0+p_q^2/2+omega^2 q^2/2]U^dagger.
Its restriction to the physical band is p_q^2/2+omega^2 q^2/2 for
every Lambda>0. There is no induced hbar lambda^2 q^2/mu term.
At omega=0 this is the free-particle continuum, with no normalizable
oscillator ground state; the statement is an exact unitary equivalence,
not an inference from a compact-resolvent argument at positive omega.

The geometric correction for a bare kinetic energy, and connections
in constrained quantum dynamics, are established phenomena; see
[Wachsmuth and Teufel](https://arxiv.org/abs/1005.1849). Equations
(10)-(11) give the explicit changed kinetic energy used here.

There is a locality condition even in this commuting-source case.
Within the ansatz Pi_a=p_a+sum_i v_ai(q)pi_i, the equation
[Pi_a,c_j^U]=0 forces

    sum_i M_ji v_ai=lambda partial_a S_j,
    v_ai=lambda sum_j N_ij partial_a S_j.               (12)

This follows directly by taking the commutator, with no approximation.
For S_x=q_x^2 and a massless lattice M=L=-Delta it requires
v_ai=2lambda q_a(L^(-1))_ia, after the auxiliary constant mode has
been removed. The inverse has no uniform finite-range stencil:
its Fourier multiplier 1/ell(k) diverges at small nonzero k. On
periodic boxes its row absolute sum is at least 1/ell_min, growing
as the squared side length. A bounded-range stencil with uniformly
bounded coefficients cannot supply it. This is a conclusion about
(12) and these primitive variables, not about every possible
constraint realization or every gauge-fixed gravitational observable.

One can move the inverse by a canonical change of auxiliary variables:

    z=M y, e=N pi, [z_i,e_j]=i hbar delta_ij,
    K=sum_i e_i S_i, c=z+i M e.                        (13)

The generator is then local if the sources are local in the chosen
unreduced physical coordinates. But y=N z and the response terms
-A y and y^T K_vector y contain inverse operators in this description.
The transformation does not make the metric identification, generator
and complete response Hamiltonian simultaneously local. The zero modes
were excluded to define the inverse; they must not silently disappear
from a proposed complete gravitational theory.

## 4. A microscopic strength obstruction for the direct unitary dressing

Here is a finite-spin test independent of continuum ordering. There
are three blocks of R qubits. On block 0 use the Pauli Y sum and on
blocks 1 and 2 the Pauli X sums. Define

    P_(0,R)=sum_a Y_(0,a)/sqrt(2R),
    Q_(i,R)=sum_a X_(i,a)/sqrt(2R), i=1,2,
    K_R=P_(0,R) Q_(1,R) Q_(2,R), U_R=exp[-i lambda K_R]. (14)

hbar=1 in this spin control. At low occupation these approach the
canonical generator p_0 q_1 q_2, while

    ||K_R||=R^(3/2)/(2sqrt(2)).                         (15)

For any decomposition K_R=sum_Z k_Z, define its per-qubit norm sum
B_R=max_a sum_(Z containing a)||k_Z||. Projection onto operators
odd under the global Pauli-Z flip of each of the three blocks is
contractive and preserves K_R. It annihilates every term whose
support misses a block. Each surviving term therefore contains at
least three qubits. Summing the local budgets gives

    3R B_R>=3 sum_Z ||projected k_Z||>=3||K_R||,
    B_R>=sqrt(R)/(2sqrt(2)).                            (16)

The explicit three-qubit expansion attains this bound. It holds for
any support decomposition of this particular generator, even with
large terms or cancellations. It does not exclude a different unitary
path realizing one fixed endpoint.

More directly, take the positive on-site normal Hamiltonian
N_0=sum_a(1-Z_(0,a))/2 and dress it to N_0'=U_R N_0 U_R^dagger.
For a Pauli-Z probe on one control qubit b in block 1,

    ||[N_0',Z_(1,b)]||
      =R max_(c=-R,-R+2,...,R) |sin(2lambda c/(2R)^(3/2))|
      >=R |sin(lambda/sqrt(2R))|.                      (17)

To see this, diagonalize the two control X sums. Their target
rotation angle is theta=2lambda b c/(2R)^(3/2). Flipping the chosen
control changes theta by 4lambda c/(2R)^(3/2). The difference of two
rotated target number operators has norm R times the sine of half
that angle. The all-aligned target state realizes the norm.

Every support decomposition of N_0' satisfies ||[N_0',Z_b]||<=2B_R.
At fixed nonzero lambda, (17) thus forces B_R to grow at least as
|lambda|sqrt(R)/(2sqrt(2)). Unitary equivalence and a fixed gap
therefore do not preserve the required microscopic strength bound.
This example is stronger than merely observing that a usual locality
estimate becomes inconclusive.

The standard locality bounds for unitary lattice dynamics require
controlled interaction norms; see
[Nachtergaele, Sims and Young](https://arxiv.org/abs/1810.02428).
One cannot apply them with an R-independent constant to (14) by
calling its cubic expression local. This conclusion does not say
all dressed parents spread in space: the example involves only
three blocks and its elementary rotations commute.

## 5. A hierarchy repairs strength, at the cost of interaction order

The obstruction in (17) assumes a fixed normal energy coefficient.
The previous slow-clock construction permits a different hierarchy.
Set Gamma_R=1/R, epsilon_R=1/R^2, omega_1,omega_2>0 and take

    H_R=U_R[Gamma_R N_0+epsilon_R(omega_1 N_1+omega_2 N_2)]U_R^dagger.
                                                               (18)

Every transformed single-qubit number projector still has norm one.
Because all elementary generators in (14) commute, a transformed
projector on one block is supported on that qubit and the two other
complete blocks. There are R projectors per block. This explicit
decomposition has

    B_R<=1+(omega_1+omega_2)/R.                         (19)

Its block range is fixed, but each interaction can involve 2R+1
qubits. This is a bound on summed strength, not a fixed-body or fixed
Euclidean-range microscopic locality theorem.

The increasing interaction order is real. For R=2, the coefficient
of Z_(0,a) X_(1,1) X_(1,2) X_(2,1) X_(2,2) in N_0' is

    (1-cos lambda)/8.                                  (20)

It is nonzero away from integer multiples of 2pi, and no decomposition
into operators on at most four qubits can contain that Pauli string.
More generally, for even r<=R the coefficient with r distinct control
qubits from each block and one target Z has leading term

    -(1/2)(-1)^(r/2) r! [2lambda/(2R)^(3/2)]^r.         (21)

The coefficient is a nonzero analytic function of lambda. Outside
a countable exceptional set of lambda values, these strings have
unbounded weight as R increases. Thus this exact family has no
fixed-body representation for generic nonzero lambda. Rescaling
the energy in (18) does not remove its nonzero high-weight strings.
The transformed control-number terms cannot cancel these strings:
they contain a control Z or Y, whereas the displayed strings contain
only control X operators and one target Z.

There is nevertheless a fully controlled quantum limit of (18).
Add complete-exchange penalties J/R sum_(a<b)(1-swap_ab) in each
block, with J>0. They commute with U_R. Before dressing all number
terms are positive, the ground state is the all-up symmetric vector,
and every nonsymmetric sector costs at least J. Dressing preserves
that exact selection and gap. The exchange's per-qubit budget is
at most 2J, so it does not spoil (19).

On the three symmetric blocks, embed occupation n_i<=R in three-mode
Fock space. Each collective P_R,Q_R converges on the finite-particle
core to its canonical quadrature. Essential self-adjointness gives
strong resolvent convergence. Since the three quadratures in (14)
act on different tensor factors, their joint spectral measures
converge. Tightness and bounded continuous functional calculus give

    U_R -> U=exp[-i lambda p_0 q_1 q_2] strongly,        (22)

uniformly on compact lambda intervals on each fixed vector. No norm
convergence of the unbounded generators is asserted.

In physical energy units the undressed Hamiltonian is exactly
R N_0+omega_1 N_1+omega_2 N_2. Every fixed low level therefore has
n_0=0 for sufficiently large R; the exchange sectors also diverge.
Its finite low spectral projectors converge after (22), including
multiplicities. On fixed physical inputs the quantum evolution is

    exp[-it H_R/epsilon_R] U_R(|0>_0 tensor phi_R)
       -> U(|0>_0 tensor exp[-it(omega_1 N_1+omega_2 N_2)]phi),    (23)

uniformly on compact time intervals. Here phi_R is the natural
occupation truncation of phi. The proof is the exact conjugation
in (18), (22), and the number-spectrum truncation; it requires no
approximate fast-kernel error estimate.

The limiting sector has the nonlinear bare-coordinate response

    V^dagger q_0 V=lambda q_1 q_2,
    V=U(|0>_0 tensor identity),                         (24)

while its covariant physical observables and Hamiltonian are exactly
those of the two supplied oscillators. This is an explicit nonlinear
spin-sector control with bounded strengths and a slower normal scale.
It is not a gravitational interaction, a tensor lattice, or a derived
clock symmetry. Its growing-body interactions cannot be substituted
for the earlier three-cell microscopic Hamiltonian without a further
construction and proof.

## 6. Consequence for the Einstein target

The kinetic correction found in the previous turn is not an unavoidable
mass prediction: the covariant off-constraint dynamics (5) cancels it
at the proven response order, and exactly in the commuting control.
The model must specify those dynamics and the physical observables,
instead of keeping a bare momentum after deforming the state space.

The remaining gap is now sharper. A candidate must realize the
correlated response and covariant momentum in the original tensor
channels with microscopic interaction order and strengths controlled
together, and then derive a nontrivial Einstein clock algebra and
physical interaction. The inverse in (12), the strength cost (17)
and the high-weight terms (20)-(21) are explicit tests to meet.
Changing the normal energy scale alone addresses only one of them.
Noncommuting tensor sources, their full regulator removal, protected
interacting masslessness, physical G and the continuum TOE remain open.

## 7. Verification

Run

    OPENBLAS_NUM_THREADS=1 python3 -W error::RuntimeWarning scripts/covariant_constraint_transport_audit.py

The report is
[data/covariant_constraint_transport_audit.json](data/covariant_constraint_transport_audit.json).
Exact identities and 28 numerical cases check unitary and normalized Gaussian compression, the correlated
quartic cancellation, exact covariant differential identities,
the noncommuting regulated band limit, untruncated-control Galerkin spectra, microscopic commutator norms,
high-weight Pauli coefficients, and the symmetric-spin quantum limit.
Numerical cutoff comparisons are corroboration, not interval bounds.
No new Lean theorem or full Einstein dynamics is claimed.
