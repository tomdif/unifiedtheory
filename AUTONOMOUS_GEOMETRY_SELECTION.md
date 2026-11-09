# Autonomous focusing and the cubic ground-state test

Date: 2026-09-10

**A constant Hamiltonian exactly focuses the six-site reference state, but
the same triangle-based route does not select the exact cubic-torus family
at zero temperature.** The first result replaces the previous controlled
pulses with a fixed interaction. The second addresses an open scope of the
earlier thermal obstruction: for the regular-sector Hamiltonian below,
the total ground-state probability of all relabellings of a cubic torus is
O(1/N), uniformly over nonnegative triangle penalties, including penalties
that grow with N.

The exclusion concerns an exact graph family. It does **not** exclude a
fluctuating or coarse geometric phase, or the full finite-penalty v2
Hamiltonian outside this sector. An exact lattice event can have small
probability even in a physically useful fluctuating phase. No stable
autonomous preparation of spacetime or complete TOE is established here.

## 1. The Hamiltonian being tested

Use the connected, labelled d-regular, trivial-flux, empty-matter graph
basis and the actual ordered exchange of
[v2](RELATIONAL_QUANTUM_GEOMETRY_V2.md). Write A for its symmetric weighted
configuration adjacency, D for its row-sum diagonal, and L_S=D-A. The
test Hamiltonian is

\[
 H_N=\rho_N L_S+v_N\mathcal T,\qquad
 \rho_N>0,\quad v_N\ge0,
 \tag{1}
\]

where T(G) is the number of triangles and mathcal T its diagonal operator.
This L_S is a **configuration** Laplacian, not the spatial Laplacian of a
particular graph. Each admissible oriented path a-b-c-d contributes weight
two to replacing ab,cd by ac,bd, provided the new links are absent. The
factor two retains the original forward/reverse ordered-operator counting.

Equation (1) is exactly the previously computed compression P H2 P when
v_N=3kappa+lambda. Compression alone does not make that sector invariant:
nonzero wedge and magnetic terms can leave it. Alternatively, (1) has an
exact invariant realization in a **modified** full model: set kappa,
lambda,t,m0 to zero, retain degree and flux penalties plus balanced
exchange, and add an independent occupancy potential v_N sum_f P_f.
This extra coefficient is a new physical input. It is not the tied
magnetic term lambda sum_f(P_f-T_f) of v2.

All phase claims below apply to (1), not automatically to the complete
v2 theory with finite degree/flux penalties and matter dynamics.

## 2. Exact autonomous focusing on six sites

There are 70 connected labelled cubic graphs on six vertices: ten K3,3
graphs (class A) and sixty triangular prisms (class B). Here “cubic” in
graph-theory terminology means degree three; neither class is a large
three-dimensional spatial lattice. In normalized class sums,

\[
 \bar L_S=\begin{pmatrix}144&-24\sqrt6\\-24\sqrt6&24\end{pmatrix},
 \quad\bar{\mathcal T}=\operatorname{diag}(0,2),\quad
 |\Omega\rangle=\frac{|A\rangle+\sqrt6|B\rangle}{\sqrt7}.
 \tag{2}
\]

The audit verifies this invariant subspace using every graph's weighted
transition row. It is not an approximation obtained by grouping only by
triangle count.

Energy conservation is necessary for exact transfer of Omega into A:

\[
 \langle\Omega|H|\Omega\rangle=12v/7,
 \qquad\langle A|H|A\rangle=144\rho.
\]

Consequently the only possible constant resonance is v=84rho. It also
suffices. At that value define

\[
 R=\frac1{\sqrt7}\begin{pmatrix}1&\sqrt6\\\sqrt6&-1\end{pmatrix},
 \quad R^2=I,\quad R|\Omega\rangle=|A\rangle,
 \quad H_*=168\rho I-24\sqrt7\rho R.
 \tag{3}
\]

Exponentiating gives the exact solution

\[
 e^{-itH_*}|\Omega\rangle=e^{-168i\rho t}
 \big[\cos(\theta)|\Omega\rangle+i\sin(\theta)|A\rangle\big],
 \quad \theta=24\sqrt7\rho t,
\]

\[
 \Pr(A,t)=\frac{1+6\sin^2(24\sqrt7\rho t)}7.
 \tag{4}
\]

Thus the probability rises from 1/7 to **one** at
t_*=pi/(48 sqrt(7) rho), without changing the Hamiltonian during evolution.
At 2t_* it is back to 1/7. A maximally mixed graph input stays maximally
mixed and does not undergo this focusing.

This is a finite realization of known continuous-time quantum-search
physics, not a new general amplitude-amplification principle.
[Farhi and Gutmann](https://arxiv.org/abs/quant-ph/9612026).
The exact reduction, coupling and probabilities are calculations for the
repository's exchange normalization. The supplied pure input, chosen
coupling, and target class remain inputs. Observing or freezing the
focused state still requires appropriate timing or additional dynamics.

The stationary ground state must also be distinguished from the evolved
state. Its class-A probability is

\[
 p_A^{\rm gs}(v)=\frac12\left(1+
 \frac{v-60\rho}{\sqrt{(v-60\rho)^2+3456\rho^2}}\right).
 \tag{5}
\]

At resonance this is (1+1/sqrt(7))/2, approximately 0.689, not one.
It approaches one as v/rho tends to infinity. A closed quench does not
increase its initial population in the new Hamiltonian's ground eigenspace.

### Why finite closed evolution cannot provide permanent attraction

For finite-dimensional Hermitian H, spectral decomposition writes every
matrix element of exp(-itH) as a finite sum of phases. Simultaneous
approximation of the finite eigenvalue differences gives arbitrarily late
times t_j at which exp(-it_j H) approaches a scalar times I. Consequently
every event probability returns arbitrarily close to its initial value.
If a probability has a late-time limit, that limit equals its initial
value. It therefore cannot eventually stay above a threshold greater than
its initial value for all future times.

This excludes irreversible capture by a finite closed constant
Hamiltonian. It permits long metastable intervals, selected stationary
states, open-system preparation, and thermodynamic limits with a
specified order of limits. A reservoir proposal must account for the
information carried away, as in the
[previous preparation bound](COARSE_GEOMETRY_AND_PREPARATION.md).

## 3. Exhaustive tests beyond the two-class system

The new audit enumerates all 38,780 regular graphs across (N,d)=(6,3),
(8,3),(8,4). Of these, 38,745 are connected. It checks reverse weights,
configuration connectivity, and every row of each equitable partition.
The resulting invariant dimensions are respectively 2,5,6.

For eight degree-three sites the five classes have (triangle count,
square count, labelled multiplicity)

| Triangles | Squares | Multiplicity |
|---:|---:|---:|
| 0 | 4 | 2520 |
| 0 | 6 | 840 |
| 1 | 3 | 3360 |
| 2 | 2 | 10080 |
| 4 | 2 | 2520 |

The first two are the Mobius ladder and the ordinary cube. The exact
normalized compression to their triangle-free span is

\[
 \bar L_{\rm tf}=\begin{pmatrix}
 128&-32\sqrt3\\-32\sqrt3&192
 \end{pmatrix}.
 \tag{6}
\]

Its lowest eigenvalue is 96 and its normalized positive eigenvector is
(sqrt(3)/2,1/2). Hence, as v/rho tends to infinity, the full ground-state
probability of the cube class tends to **1/4**, while the Mobius ladder
class receives 3/4. Increasing the triangle penalty does not distinguish
these two triangle-free geometries. At finite coupling the cube weights
are approximately 0.169 at v/rho=84 and 0.243 at v/rho=1000.

For eight degree-four sites the strong-penalty limit instead selects
K4,4, the only triangle-free class there. Favoring a small highly symmetric
graph is not evidence for spatial volume growth or spacetime dimension.

The finite ground energies/probabilities use numerical diagonalization
only after verifying the quotient exactly. A strictly positive lifted
ground vector and connected negative off-diagonals identify the full
ground state by Perron-Frobenius. No quotient excitation gap is reported
as a gap of the full configuration space.

## 4. A zero-temperature theorem for the exact cubic-torus event

Let N=ell^3 with even ell>=6. Let C_N contain **all labelled copies** of
the spatial graph (Z/ell Z)^3 with its six nearest neighbors, and let
P_C project onto their span. For any normalized ground state psi_N of
(1), put p_N=||P_C psi_N||^2.

**Theorem.** For any sequences rho_N>0 and v_N>=0,

\[
 p_N=O(N^{-1})\quad\hbox{as even }\ell\longrightarrow\infty.
 \tag{7}
\]

The constants do not depend on v_N/rho_N. In particular, sending the
triangle penalty to infinity does not repair this exact-cubic test.
The proof has three ingredients.

### 4.1 A trial state with bounded total energy

Let F_N be all connected, triangle-free d-regular labelled graphs, and
let Omega_tf be their normalized uniform superposition. Its triangle
energy is zero. Its Laplacian energy is exactly the average weighted
escape from F_N:

\[
 \langle\Omega_{\rm tf}|H_N|\Omega_{\rm tf}\rangle
 =\frac{\rho_N}{|F_N|}\sum_{G\in F_N}\sum_{G'\notin F_N}A_{GG'}.
 \tag{8}
\]

In a triangle-free input, a flip a-b-c-d can create a triangle only if
one of the length-two paths a-b-c or b-c-d lies in an existing square.
For example, a triangle using the new edge ac must use another common
neighbor x of a,c. The deleted edges rule out x=b,d; the old graph then
contains the square a-b-c-x-a. The two new edges are disjoint, so they
cannot both occur in one triangle.

A square has eight oriented length-two paths. Each has at most d-1
extensions. Counting either position in the length-three path, and the
factor two in the exchange weight, gives the pointwise bound

\[
 \sum_{G'\notin F_N}A_{GG'}\le32(d-1)C_4(G).
 \tag{9}
\]

The audit checks (9) for every triangle-free graph in all three finite
enumerations.

For fixed d, the random-regular short-cycle theorem gives independent
Poisson limits for triangle and square counts, with means (d-1)^3/6 and
(d-1)^4/8. Its bounded second-moment estimate for C4 supplies uniform
integrability, so this is a statement about conditional **means**, not
an unjustified inference of moments from convergence in distribution.
Connectedness has probability tending to one. Therefore

\[
 \mathbb E[C_4\mid T=0,\ \mathrm{connected}]
 \longrightarrow\frac{(d-1)^4}{8}.
\]

The external inputs are the short-cycle distribution and moment
estimates in Theorems 1-2 and equations (2.2)-(2.7) of
[McKay, Wormald and Wysocka](https://users.monash.edu/~nwormald/papers/girth.pdf),
and the fixed-degree connectedness result documented in the
[preceding audit](GEOMETRY_ENTROPY_OBSTRUCTION.md).
These are not inferred from finite simulations or re-proved in Lean.

Rayleigh-Ritz, (8), and (9) now give

\[
 0\le E_0(N)/\rho_N\le 4(d-1)^5+o(1).
 \tag{10}
\]

At d=6 the upper bound is 12500+o(1), independent of the triangle penalty.
This is a deliberately loose total-energy estimate, sufficient for the
argument. It is not a calculation of the actual ground energy or a
certificate that the actual ground state is an expander.

### 4.2 Every cubic move loses squares; repairs occupy bounded regions

Every edge of the even cubic torus with ell>=6 lies in exactly four
squares; its total square count is 3N. All nonbacktracking length-three
paths have distinct vertices and satisfy the exchange absence conditions.
There are N*6*5^2 such paths, giving weighted row sum

\[
 D_C=300N.
 \tag{11}
\]

For a flip a-b-c-d, let I_ad indicate whether ad is present. Removing
ab,cd destroys eight squares, except that their common square is counted
twice when I_ad=1. Bipartiteness forbids any new square containing only
one new edge, since each new edge joins vertices of the same old color.
A square containing both new edges exists exactly when ad is present.
Consequently

\[
 \Delta C_4=-8+2I_{ad}\in\{-8,-6\}.
 \tag{12}
\]

No elementary exchange stays within C_N, even after relabelling. Thus

\[
 P_C H_N P_C=\rho_N D_C P_C.
 \tag{13}
\]

Next fix any graph G adjacent to C_N, choose one cubic parent, and let X
be the four changed endpoints. A repair returning G to any member of C_N
must increase its square count by six or eight. If all vertices of the
repair path lie outside B_3^G(X), every old or new square involved in that
repair is in an unchanged neighborhood of the chosen parent. Its square
change would then be (12), which is negative. Hence every repair has a
path vertex in B_3^G(X).

Degree six gives |B_3^G(X)|<=4(1+6+6*5+6*5^2)=748. For each of four
positions on the path, at most 6*5^2 oriented nonbacktracking paths put a
given vertex there. The weighted number of repairs to **all** cubic
parents is therefore at most

\[
 r_*=2\cdot4\cdot748\cdot150=897600.
 \tag{14}
\]

This coarse constant is independent of N. No uniqueness of a parent or
of a repair is assumed. Restoring square count is only a necessary
condition for repairing a cubic graph, which suffices for the upper bound.

The finite audit checks every root-starting path on tori with 216, 512,
1000 and 1728 vertices. Each has 126 paths with square change -8 and
24 with change -6 per root. It also enumerates every possible exchange
on two damaged 216-site tori: their weighted counts of square-restoring
moves are four and eight, and every restoring path meets the stated ball.
These examples check the local reasoning; (14) is the analytic bound.

### 4.3 Convert repair counting into a ground-state probability bound

Set Q=I-P_C and B=P_C A Q. Its maximum row sum is D_C and its maximum
column sum is at most r_*. Weighted Cauchy-Schwarz gives the Schur bound
||B||^2<=D_C r_*. Projecting the eigenvalue equation and using (13),

\[
 (\rho_N D_C-E_0)P_C\psi_N=\rho_N BQ\psi_N.
\]

For D_C>E_0/rho_N this yields

\[
 (D_C-E_0/\rho_N)^2p_N\le D_Cr_*(1-p_N),
\]

\[
 p_N\le\frac{D_Cr_*}{(D_C-E_0/\rho_N)^2+D_Cr_*}.
 \tag{15}
\]

Combining (10), (11), and (15) proves (7). The displayed constants even
give limsup N p_N<=r_*/300=2992; this is an asymptotic bound, not a sharp
finite-size estimate. The argument bounds arbitrary complex vectors in
the ground eigenspace, and includes arbitrary superpositions of cubic
labellings. It does not assume that one particular graph is the ground
state or treat label multiplicity as a classical mixture.

## 5. The next geometric criterion: consistency of neighborhoods

Triangle suppression cannot distinguish a spatial grid from many other
triangle-free graphs. A more informative candidate requirement is that
local paths fit together into consistent neighborhoods. There is a precise
external theorem supporting such a criterion: a connected graph whose
radius-three neighborhoods are those of Z^3 is covered by the cubic
lattice and has a quotient-lattice description. Its global geometry is
therefore much more restricted than that of an arbitrary degree-six
graph. [Benjamini and Ellis](https://arxiv.org/abs/1409.7587).

For a testable new postulate, let q_v(G) be one when the **rooted induced**
radius-three ball at v is isomorphic to the corresponding ball in Z^3,
and zero otherwise. Then

\[
 V_{\rm patch}(G)=J\sum_v(1-q_v(G))
 \tag{16}
\]

is permutation invariant, bounded by JN, and evaluates bounded graph
neighborhoods at fixed degree. It specifies no embedding or vertex
coordinates. It is a new many-link interaction; locality in a graph
configuration does not by itself prove microscopic tensor-product
locality or efficient implementation on the original qutrit carrier.

Equation (16) is a concrete **next test**, not a proved selected phase.
It explicitly supplies the dimension three and a flat local template.
Its diagonal zero-energy states satisfy the certificate; it has no graph
preparation dynamics by itself. Once exchanges, matter and curvature are
included, the ground phase and its stability need fresh proofs. The old
fixed-temperature entropy bound still applies on the full graph carrier.

Even exact local lattice structure does not establish a noncollapsed
three-dimensional limit. For example, C8 x C8 x C_L, L>=8, has the same
radius-three balls, while for 8 much smaller than r much smaller than L
its ball volume is at most 64(2r+1), effectively one-dimensional. The
shortest nontrivial identification length must grow with the desired
continuum scale. Curvature, Lorentz symmetry, a gravitational action and
chiral interacting matter are separate requirements.

The audit checks rooted neighborhood isomorphism for the ordinary torus,
an exchanged torus, a triangle-free circulant, and C8 x C8 x C128. The
last example passes the radius-three certificate, but its measured ball
volumes at r=8,16,32 are 576,1600,3648, exactly 128r-448. This is an
explicit test of why local template agreement still needs noncollapse.

The proposed organizing idea is **consistent local transport with a
noncollapsing large-scale limit**. The evidence above motivates testing
it. Neither this idea nor (16) is derived from a unique deeper physical
principle in the repository.

## 6. Verification and exact scope

- [The audit script](scripts/autonomous_geometry_audit.py) checks symbolic
  resonance, the complete finite graph quotients, triangle-free escape
  bounds, local cubic moves, and the proposed patch criterion. It writes
  [the reproducible report](data/autonomous_geometry_audit.json).
- [The Lean module](UnifiedTheory/Audit/KFCausalAutonomousGeometry.lean)
  proves eight supporting results: resonance energy balance, weighted
  Cauchy-Schwarz, the real Schur bound, two ground-event inequalities,
  vanishing from the inverse-volume bound, the recurrence-limit step,
  and the explicit repair constant. The graph and spectral suppliers
  remain the analytic arguments above. The full asymptotic theorem is
  not advertised as a complete Lean formalization.
- The finite matrix and cycle checks do not prove a continuum, physical
  attraction, a gap uniform in N, or the phase of (16). The exact-cubic
  theorem does not decide the probability of a broader geometric event.

Run `OPENBLAS_NUM_THREADS=1 python3 -W error::RuntimeWarning
scripts/autonomous_geometry_audit.py` from the repository root, followed
by `lake build`. Earlier source-hash-pinned artifacts remain unchanged.
