# Exact clock mediation of nonlinear constraints, and its Einstein boundary

Date: 2026-09-11

The [polynomial spin parent](POLYNOMIAL_SPIN_CONSTRAINTS.md) could not
independently impose noncommuting gravitational sources without an
extra fast energy. A common transformation avoids that problem, but
its direct spin Hamiltonian had interactions of growing order.

An enlarged carrier with clock qubits gives an exact compatible
kernel for a circuit implementing that transformation. Every gate
can have fixed microscopic support. Both interaction order and summed
strength stay bounded, with an explicit shrinking gap and a slower
physical scale. Boundary terms reproduce the supplied nonlinear
response in the low band. This is an encoding theorem for specified
dynamics, not a derivation of Einstein gravity.

Two limitations are explicit. A local boundary observable has the
correct compression but generally incorrect bare products. Also,
serial compatibility is not independence of slicing: a diamond of
two noncommuting source operations has nontrivial holonomy. For the
actual regulated source pair tested here, that diamond loses half
its intended kernel. Einstein refoliation symmetry remains missing.

## 1. Exact finite-spin parent on an enlarged carrier

Let D_0>=0 act on a finite work register. Assume its kernel has an
isometry I_0:C^d -> H_work and its first positive eigenvalue is
delta_0>0. Write D_0 as terms of bounded support and let L_0>0 be
the sum of their norms. The sum D_0 is positive; positivity of each
term is not needed. Thus delta_0<=||D_0||<=L_0.

Supply T>=1 unitary gates U_1,...,U_T, each on at most s work qubits.
Let V_t=U_t ... U_1 and V_0=1. Add T clock qubits, number operators
n_t and raising operators r_t, with boundary values n_0=1,n_(T+1)=0.
The legal clock strings are |t>=|1^t 0^(T-t)>, t=0,...,T. Define

    D_clock=sum_(t=1)^(T-1) (1-n_t)n_(t+1),
    F_t=n_(t-1)(1-n_(t+1)),
    Q_t=F_t[1-r_t U_t-r_t^dagger U_t^dagger],
    C_T=D_clock+(1/T)sum_t Q_t+(1-n_1)D_0/L_0.       (1)

Q_t is positive and has norm at most two: on its guard, the dressed
flip is a self-adjoint involution. The successor guard makes every
clock-violation projector commute with every Q_t, as proved in
[the earlier local clock construction](LOCAL_CAUSAL_CLOCK.md).
The input term also commutes with these diagonal violation projectors.
Every illegal clock sector consequently has energy at least one.

On legal clocks the block-diagonal unitary W=sum_t |t><t| V_t gives

    W^dagger C_T W=(L_path/T) tensor 1
                         +|0><0| tensor D_0/L_0.      (2)

L_path is the graph Laplacian of a path with T edges and unit edge
weights. Therefore the exact full kernel is

    J_T v=(T+1)^(-1/2) sum_(t=0)^T |t> V_t I_0 v.    (3)

J_T is an isometry. Its dimension is exactly d, with no illegal-clock
zero modes. No commutativity assumption on the gates or their physical
sources enters (1)-(3). The kernel is exact at every gate angle. The
positive propagation terms need not mutually commute.

This is a specialized Feynman-Kitaev construction. It uses established
circuit-to-Hamiltonian ideas, including the earlier repo clock, rather
than claiming their invention. For general clock spectra and their
limitations see [Bausch and Crosson](https://arxiv.org/abs/1609.08571).

## 2. A gap and strength estimate with explicit scale dependence

Put n=T+1. In a D_0 eigenvector of eigenvalue d_0>0, the quadratic
form on a clock vector f is

    E(f)=(1/T)sum_(t=1)^T |f_t-f_(t-1)|^2
                                      +(d_0/L_0)|f_0|^2.

Cauchy-Schwarz applied to f_t=f_0+sum_(j=1)^t(f_j-f_(j-1)) gives

    ||f||^2<=2n |f_0|^2+2T n sum_j |f_j-f_(j-1)|^2.

It follows that this pinned path has lowest energy at least
1/[2n max(T^2,L_0/d_0)]. The unpinned path has first positive
eigenvalue (2/T)[1-cos(pi/n)]>=4/(T n^2). Combining these estimates
with the illegal sector proves

    gap(C_T)>=gamma_T,
    gamma_T=1/[2(T+1)max(T^2,L_0/delta_0)].             (4)

There is a normal gap at each finite regulator, not a uniform
microscopic gap as T grows. For a fixed input ratio it scales at
least as T^(-3). Choosing a serial clock removes the exponential
branching bottleneck of the earlier event-ideal example by changing
the allowed histories; it does not prove that arbitrary partial
orders have a polynomial gap.

Each propagation term involves at most s+3 qubits. Each clock qubit
belongs to at most three such terms, giving load at most 6/T. It
also belongs to at most two clock penalties. The first clock qubit
has additional input load at most one. A work qubit has propagation
load at most two, even if every gate uses it, and input load at most
one. Thus

    max_x sum_(Z containing x)||C_(T,Z)||<=9,          (5)
    maximum term support<=max(s+3,k_0+1,2),

where k_0 bounds input-term support. These conservative bounds are
uniform in T and work-register count. They do not establish bounded
Euclidean interaction diameter, fixed clock density per physical
volume, or an autonomous preparation process. Serial clock neighbors
can be attached to distant work supports. A spatial implementation
requires additional routing and geometry estimates.

## 3. The slow Hamiltonian can be inserted at different boundaries

Supply work operators H_base and F_bare, decomposed into terms with
fixed support, and put

    S_T=n[(1-n_1)H_base+n_T F_bare],
    H_(T,epsilon)=C_T+epsilon S_T.                    (6)

On legal clocks, (1-n_1) selects time zero and n_T selects time T.
Their exact compression is

    H_eff,T=J_T^dagger S_T J_T
      =I_0^dagger[H_base+V_T^dagger F_bare V_T]I_0.    (7)

In particular H_base can contain the physical kinetic operator at
the input boundary. Its compression avoids the correction obtained
by applying that same bare operator at the output. The response
F_bare remains at the output. This realizes the compressed Hamiltonian
of [covariant constraint transport](COVARIANT_CONSTRAINT_TRANSPORT.md)
without placing its large-support dressed kinetic operator in (6).
The microscopic realization and observable representation have changed.

There is a quantitative low-band theorem. Let b be an upper bound on
||S_T||, gamma=gamma_T, and epsilon b<gamma/4. In physical units the
Hamiltonian is C_T/epsilon+S_T. Its lowest d eigenvalues E_j obey

    |E_j-eigenvalue_j(H_eff,T)|
             <=epsilon b^2/(gamma-2epsilon b),        (8)
    ||P_epsilon-J_T J_T^dagger||
             <=epsilon b/(gamma-2epsilon b).          (9)

The complementary block is bounded below by gamma/epsilon-b, while
all d low eigenvalues lie in [-b,b]. The Schur complement therefore
differs from P S_T P by at most the right side of (8). Its monotonic
eigenvalue equation gives the ordered bound. The separated-block
Sylvester equation gives (9). These statements also include illegal
clock sectors, which already have the larger positive penalty.

For completeness, the direct rotation R carrying P to P_epsilon has
||R-1||<=2r, r=epsilon b/(gamma-2epsilon b). If K=P R^dagger H R P,
then ||K||<=b and P R P K=P S_T R P. Hence
||K-P S_T P||<=4br. Comparing the two propagators by Duhamel's formula
gives the conservative finite-time estimate

    ||exp[-it(C_T/epsilon+S_T)]J_T
                         -J_T exp(-it H_eff,T)||
       <=16 epsilon b/gamma (1+|t|b).                 (10)

This uses ordinary spectral perturbation on a finite register; related
systematic methods are described by
[Bravyi, DiVincenzo and Loss](https://arxiv.org/abs/1105.0675).

Let ell be the sum of norms in the supplied decompositions of H_base
and F_bare, and set b=n ell. This also bounds every microscopic load
of S_T. For a refinement index j>=2, the choice

    epsilon_j=gamma_T/[j^2(1+b)^2]                    (11)

makes the errors in (8)-(10) vanish at fixed physical time, even when
T, b and the input regulator vary with j. The total microscopic load
of (6) stays below ten. This only compares each regulated model with
its own H_eff,T. Convergence of those target theories under removal
of the physical or spatial regulator is a separate requirement.

## 4. Circuit error does not become an amplified constraint residual

Let U be a desired finite work-register unitary and suppose
||V_T-U||<=eta. Both circuits have exactly normalized histories. In
particular C_T J_T=0 even when eta is nonzero. At fixed regulator,

    ||H_eff,T-I_0^dagger[H_base+U^dagger F_bare U]I_0||
                              <=2||F_bare|| eta.      (12)

There is no eta/epsilon factor: the approximation changes the target
kernel and its response, rather than leaving a residual in the
chosen fast parent. Source commutators are retained in the ordered
gate products to every order; they are not individually discarded.
The circuit length and slow-clock cost of achieving eta remain real
costs. Efficient compilation of a general tensor-field dressing or
its inverse Laplacian has not been established here.

The audit makes this concrete for the Einstein pair

    b=[p_c^2-p_s^2+(q_s^2-q_c^2)/4]/sqrt(2),
    f=(q_0 p_c-p_0 q_c)/4,
    a=[7(p_c^2-p_s^2)-(q_s^2-q_c^2)/4]/sqrt(2),
    omega_b=32, omega_f=1,                            (13)

at k=hbar=1. These are the actual normalized source coefficients
identified in the preceding note. Each physical oscillator is
compressed to two levels, with quadratic operators formed before
compression. Two normal oscillators have four levels each. The work
register thus consists of seven qubits. The generator terms

    G_1=p_(normal,b) b/sqrt(32), G_2=p_(normal,f) f

each act on at most four work qubits. Symmetric product formulas
approximate exp[-i lambda(G_1+G_2)] with gates of that fixed support;
the history terms involve at most seven qubits. The finite input
normal vacuum and its positive number parent are supplied.

Taking H_base=H_2 and F_bare=-lambda a y_b+2y_f^2-1 gives the
regulated response contribution

    H_eff=H_2+lambda^2[-{a,b}/64+2f^2]+O(lambda^4).    (14)

The known bare-kinetic double commutator is absent because H_2 is
inserted at the input boundary. Extra supplied H_3 and H_local,4 can
be inserted as in (7), but the new numerical test does not claim the
complete Einstein quartic. It tests this source-pair contribution,
the physical regulator, and circuit approximation explicitly.

More generally the fixed normal parent imposes no selection law on
the input dynamics: F_bare=0 and H_base=1_normal tensor H_phys make
(7) equal any supplied H_phys. Therefore even an exact compatible
local kernel does not fix Newton's constant or select Einstein's
self-interaction. Hamiltonian simulation is a distinct achievement
from deriving a physical law; see also
[Cubitt, Montanaro and Piddock](https://arxiv.org/abs/1701.05182).

## 5. Boundary compression is not a local physical observable algebra

For a work observable O preserving the input sector, the tagged
operator O_tag=n(1-n_1)O has J_T^dagger O_tag J_T=I_0^dagger O I_0.
But two tagged operators instead satisfy

    J_T^dagger O_tag O'_tag J_T=n I_0^dagger OO' I_0. (15)

Already O=O'=1 gives first moment one and second moment n. A local
boundary insertion is not a kernel-preserving covariant observable,
and cannot be used as though all its unprojected measurement moments
were those of the intended physical operator. Conditioning on the
input clock event has probability 1/n.

The algebra is correct after inserting the physical projection
between operators. The exactly transported work observable on the
legal histories, sum_t |t><t| V_t O V_t^dagger, also preserves it if
O preserves the input sector, but that expression has no established
uniform microscopic support bound. Equations (7)-(10) establish an
effective Hamiltonian, not a simultaneous local realization of all
covariant physical observables.

## 6. A source-order loop is the next consistency test

For two source gates A=exp(-i lambda S_1), B=exp(-i lambda S_2), allow
both histories in the diamond 0->a->ab and 0->b->ab. The unchanged
gate labels give endpoint states BA v and AB v. The zero-energy
condition is

    (BA-AB)v=0,
    holonomy Omega=(AB)^dagger BA,
    kernel dimension=dim ker(Omega-1).                (16)

Gauge away three edge labels. If Omega has phases exp(i theta_l),
the full diamond Laplacian has spectrum

    2-2cos[(theta_l+2pi m)/4], m=0,1,2,3.             (17)

Its effective low-band leading energy is

    lambda^4 [S_1,S_2]^dagger[S_1,S_2]/16.             (18)

This is a loop-holonomy energy in a different parent, not the
coefficient of the independent spin conditions calculated previously.
It follows from Omega=1+O(lambda^2) and (17), or by distributing the
leading mismatch equally over the four edges.

For S_1=diag(sigma_x,2sigma_x), S_2=diag(sigma_z,sigma_z), a small
nonzero lambda removes the entire four-dimensional common kernel.
For the regulated b,f of (13), four of the eight physical directions
survive. The finite physical cutoff changes the canonical source
algebra at its boundary; these counts are statements about the
displayed regulated matrices, not the full gravitational constraint
space. They demonstrate why serial compatibility alone proves no
independence under reordering the source operations.

Replacing the edge a-after-b by B A B^dagger closes this loop exactly:
both paths then give BA. The correction has a fixed-gate sequence
B^dagger, A, B if extra clock events are allowed, but it changes the
operation's dependence on the preceding history. Flatness can be
engineered this way for arbitrary supplied gates.

In general relativity a loop of normal deformations need not be the
identity before quotienting: its leading commutator is a spatial
diffeomorphism, with the inverse metric as a structure function;
see [Teitelboim's spacetime consistency derivation](https://www.fis.uc.cl/~mbanados/Cursos/TopicosRelatividadAvanzada/Teitelboim.pdf).
The b,f here are quadratic response sources, not those complete
Hamiltonian and momentum constraints. Neither declaring their loop
flat nor imposing a preferred serial order derives the Einstein
hypersurface-deformation algebra.

The repo's [conditional gravity calculation](GRAVITY_FROM_CLOCK_CONSTRAINTS.md)
already identifies that algebra and the coefficients it fixes within
a metric Hamiltonian ansatz. The [microscopic bracket test](SPIN_CLOCK_BRACKET.md)
also shows why an energy commutator alone does not give the correct
spatial action on the metric. Clock mediation has not repaired that
spatial-transformation gap; it supplies a different exact realization
of the specified quantum sector.

## 7. Present conclusion and verification

Clock mediation supplies an exact, bounded-strength, fixed-order
spin encoding of the finite-regulator nonlinear sector. It removes
the independent-source fast energy by enlarging the carrier and
using one compatible history, with an explicit gap and scale cost.
It is not an all-order polynomial solution within the original
normal-spin ansatz. The gravitational source coefficients, input
state space, gates, interactions and time calibration are supplied.

The remaining target is a physical constraint algebra that selects
those dynamics and admits consistent changes of slicing, together
with appropriate physical observables and removal of the tensor,
normal and spatial regulators. Protected masslessness, physical G,
Einstein gravity and the TOE remain unproved.

Run

    OPENBLAS_NUM_THREADS=1 python3 -W error::RuntimeWarning scripts/clock_mediated_constraints_audit.py

The 34 numerical cases pass. The report is
[data/clock_mediated_constraints_audit.json](data/clock_mediated_constraints_audit.json).
It checks full spin-clock spectra including illegal sectors, pinned
path gap bounds, slow eigenvalues and evolution, boundary-observable
products, the actual regulated source response, circuit error, and
source-order loops. Numerical comparisons are not interval
certificates. No new Lean theorem is claimed.
