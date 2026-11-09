# Relational Quantum Geometry v2: balanced moves and an explicit phase test

Date: 2026-09-10

**This is the current research candidate, not a proved TOE.** The
[phase proof attempt](QUANTUM_GEOMETRY_PHASE_TEST.md) lowers confidence in
the original Hamiltonian: its moves freeze saturated triangle-free graphs,
and a variational family beats the particle-empty, trivial-flux cubic
state at cap six. The proof survives arbitrarily large system size.
It does not rule out every geometric phase or every matter sector.

The response is an explicit change of Hamiltonian. Include exchanges that
change shape at fixed degree, balance each elementary geometry move with
its diagonal contribution, and expose the degree preference as an input.
The original [v1 proposal](RELATIONAL_QUANTUM_GEOMETRY_PROPOSAL.md) and its
audits remain the historical specification to which the obstruction applies.

The revised organizing hypothesis is:

> Spacetime could emerge from reversible, gauge-preserving quantum
> interactions. As a reference dynamics, geometry moves penalize amplitude
> differences between accessible configurations. Any preference for a
> macroscopic geometry must then be demonstrated from the remaining
> interactions, state counting, and the quantum state.

The first sentence remains a physical hypothesis. The choice in the second
sentence is a new modeling postulate, not a consequence of unitarity or a
universal law of nature. The resulting reference Hamiltonian is of the
known Rokhsar–Kivelson / stochastic-matrix-form type. This is an adaptation
of that construction to this repository's constrained dynamical links,
not a claim of inventing it. [Henley](https://arxiv.org/abs/cond-mat/0311345),
[Castelnovo et al.](https://arxiv.org/abs/cond-mat/0502068).

## 1. Carrier, constraints, and the revised Hamiltonian

Keep v1's absent-or-present quantum links, local Gauss constraints, and
joint matter/link state. For the fully specified finite prototype, the
link basis is `absent`, `electric +`, `electric -`, charged matter is a
hard-core qubit, and the internal gauge group is Z2. At vertex v,

\[
 G_v=(-1)^{n_v}\prod_{e\ni v}E_e=1,
 \qquad E_e=\operatorname{diag}(1,1,-1).
\]

Write N_e=diag(0,1,1), C_e=|+><absent|, and
T_e=|+><-|+|-><+|. Degree is d_v=sum_{e incident v} N_e.
Work on the degree-capped space range(Pi_Delta). Sites are regulated
quantum subsystems, not spacetime events; regulator size is not time.

For i<j and k distinct, define the **individual** wedge move

\[
 R_{ij;k}=\Pi_\Delta N_{ik}N_{kj}(C_{ij}+C_{ij}^\dagger)\Pi_\Delta.
 \tag{1}
\]

The projection is applied before squaring R. A forbidden creation has
no transition and no balancing diagonal contribution. For distinct
a,b,c,d, define

\[
 A_{abcd}=N_{bc}C_{ac}C_{bd}C_{ab}^\dagger C_{cd}^\dagger,
 \qquad S_{abcd}=A_{abcd}+A_{abcd}^\dagger.
 \tag{2}
\]

S exchanges trivial-flux edges ab,cd with absent edges ac,bd, keeping bc.
It preserves every degree and so commutes with the cap. Each R and S is
a Hermitian partial swap: Q^3=Q. S is a core interaction in v2.

For each unordered triangle f, let T_f be the product of its three T_e
and P_f the product of its three N_e. Then T_f^2=P_f. Let
B_ij=(sigma_i^+ sigma_j^- + sigma_i^- sigma_j^+)T_ij be the dressed
hard-core hopping operator, F count negative electric links, and
N_m=sum_v n_v. The candidate is

\[
\begin{split}
 H_N^{(2)}={}&\frac{U}{2}\sum_v(d_v-\bar d)^2+\epsilon F
       +\lambda\sum_f(P_f-T_f)\\
 &+\kappa\sum_{i<j,\,k\ne i,j}(R_{ij;k}^2-R_{ij;k})
       +\rho\sum_{a,b,c,d\ \mathrm{distinct}}(S_{abcd}^2-S_{abcd})\\
 &-t\sum_{i<j}B_{ij}+m_0N_m .
\end{split}
 \tag{3}
\]

All terms act on the capped space. Assume U,epsilon,lambda,kappa,rho>=0,
0<=dbar<=Delta, and t,m0 real. The exchange sum is over **ordered**
quadruples; repeated copies are included in the definition of rho.
There are no dimensionful physical predictions from these trial couplings.

The soft degree potential makes the density input explicit. For U=u>0,
the old mu E+u W equals this potential plus a constant when
dbar=(u-mu)/(2u). The original example preferred dbar=17/22, not six.
Choosing dbar=6 would supply a valence preference, not derive three spatial
dimensions: many incompatible geometries have the same degree.
The cap may exceed the trial valence; exchanges work even at saturation.

The magnetic term changes from -lambda T_f to lambda(P_f-T_f).
The added face energy is **not** a global constant when faces can appear
and disappear. It is another explicit physical change to the model.
It supplies a nonnegative magnetic term; it does not resolve vacuum
energy or the cosmological constant problem.

Every term commutes with all Gauss constraints and the relabeling action.
Matter number and the partition into connected components are preserved
in this prototype. A full permutation quotient with relational apparatus
is still required. Component conservation also means an initially
disconnected state cannot assemble one connected universe under (3).
The evolution parameter, physical state, and refinement maps remain inputs.

For compact internal groups, the absent/trivial-representation moves and
their balanced squares have the same definition. Replacing the Z2 flux,
Wilson, and hard-core matter terms by compatible compact-group and fermion
operators is further work. In particular the finite norm estimate below
does not bound unregulated compact-group electric Casimirs. Spin(10) and
its 16-dimensional representation remain possible supplied internal data;
neither their selection nor a physical chiral spectrum follows here.

## 2. What balancing proves

For a Hermitian partial swap Q, set L_Q=Q^2-Q. Direct multiplication gives

\[
 L_Q^2=2L_Q,\qquad L_Q^\dagger L_Q=2L_Q,\qquad L_Q\ge0.
 \tag{4}
\]

Thus L_Q/2 is an orthogonal projection. Its exact real-time gate is

\[
 e^{-i\theta L_Q}=I+\frac{e^{-2i\theta}-1}{2}L_Q.
 \tag{5}
\]

These moves retain coherent quantum evolution; their relation to a
classical stochastic generator does not replace real-time unitarity.
In the specified configuration basis, their nonnegative weighted sum is
the Laplacian of the **configuration transition graph**:

\[
 L_{xy}=-w_{xy}\ (x\ne y),\quad L_{xx}=\sum_{y\ne x}w_{xy},
 \qquad
 \langle\psi,L\psi\rangle=
 \sum_{\{x,y\}}w_{xy}|\psi_x-\psi_y|^2\ge0.
 \tag{6}
\]

Here x,y are entire configurations, not vertices in physical space.
The kernel consists of amplitudes constant on each component joined by
positive-weight transitions. This follows because every summand in (6)
must vanish, then equality propagates along paths. On a connected finite
transition graph, the normalized constant vector is the unique ground
state of L. Magnetic P_f-T_f obeys the same argument in the Z2 basis.
The potential and hopping terms need not share this kernel, so the
full Hamiltonian is not asserted to have that ground state.

Balance **before summing parallel moves**. If c elementary wedges induce
the same swap X on a two-state block, their correct contribution is
c(I-X). Squaring the aggregated cX instead gives c^2 I-cX, an extra
c(c-1)I. At c=2, the correct eigenvalues are 0,4 and the erroneous ones
are 2,6. The executable implements the former, including at the cap.

The previous variational argument used [[0,-b],[-b,delta]], which has a
negative eigenvalue for b nonzero even if delta>0. The balanced block is

\[
 \begin{pmatrix}b&-b\\-b&b+\delta\end{pmatrix},\qquad
 (x,y)H(x,y)^T=b(x-y)^2+\delta y^2\ge0
 \tag{7}
\]

for b,delta>=0. In the earlier matching family, the control multiplicity
is four and b=4kappa. At dbar=6, deleting one matching edge costs delta=U.
Other balanced terms have nonnegative compressed quadratic forms, so the
old bare-rewiring lowering below the zero degree-energy baseline is gone
in the particle-empty sector. This does **not** rank the revised full
cubic and competing ground states: exchanges also act on the cubic state.
For a potential with delta<0, classical degree relaxation can still lower
energy. Neither effect is hidden by balancing.

This convention removes the pure kinetic preference for greater outgoing
conductance in the constant-amplitude reference state. It does not remove
graph-count entropy, select a manifold, or prove that other physical
Hamiltonians ought to use this convention.

## 3. Exchanges remove the demonstrated freezing

The old path a-b-c-d and the exchanged path a-c-b-d connect the same
vertices; every endpoint loses and gains one edge. Trivial-flux deletion
still cannot erase stored nontrivial electric flux. On a triangle-free
regular graph of degree at least two, a simple three-edge path gives an
allowed S in the trivial-flux state. Balancing adds a diagonal term but
retains the nonzero off-diagonal transition for rho>0.

Consequently the old fixed-connectivity subspace is no longer invariant
on those backgrounds. The earlier 64-site cubic example changes its
four-cycle count from 240 to 232 through one exchange, with all degrees
six and connectedness preserved. These facts and their exact tests are
in the [phase note](QUANTUM_GEOMETRY_PHASE_TEST.md). They do not establish
ergodicity in all flux sectors or convergence to a geometric phase.

Local degree-preserving exchanges and path-controlled edge additions have
precedent in quantum graphity. The gauge-constrained partial swap and its
balanced term specify their use here.
[Konopka–Markopoulou–Severini, section II.3.3](https://arxiv.org/html/0801.0861v2#S2.SS3.SSS3).

## 4. An exact benchmark exposes what is and is not fixed

Take all labeled three-regular graphs on six vertices, with trivial flux,
empty matter, and exchange-only dynamics of unit coefficient. Set all
other couplings to zero, or use a degree potential vanishing at degree
three. There are 70 configurations: 10 copies of K3,3 (no triangles)
and 60 copies of the triangular prism (two triangles). To see that the
list is complete, the complement is two-regular on six vertices: either
two disjoint three-cycles or one six-cycle. Their labeled counts are
6!/[2(3!)^2]=10 and 5!/2=60. The exchange transition graph is connected,
as the exhaustive audit verifies. Counting all ordered exchange moves gives

| Starting graph | Moves to K3,3 class | Moves to prism class | Total |
|---|---:|---:|---:|
| K3,3 | 0 | 144 | 144 |
| Triangular prism | 24 | 48 | 72 |

In normalized orbit-sum vectors, raw exchange adjacency and its balanced
Laplacian restrict to

\[
 \bar A=\begin{pmatrix}0&24\sqrt6\\24\sqrt6&48\end{pmatrix},\qquad
 \bar L=\begin{pmatrix}144&-24\sqrt6\\-24\sqrt6&24\end{pmatrix}.
 \tag{8}
\]

The connected nonnegative adjacency has a strictly positive eigenvector
constant within each class, with eigenvalue 24(1+sqrt(7)). This is its
Perron eigenvalue, so the **raw** Hamiltonian -A has ground energy
-24(1+sqrt(7)) and total K3,3 probability (1-1/sqrt(7))/2, about 0.3110.
For the balanced Hamiltonian L, (6) gives ground energy zero and equal
amplitudes over all 70 configurations. K3,3 probability is then **1/7**,
and prism probability **6/7**.

This proves that the raw exchange term changes the shape distribution
beyond labeled graph multiplicity, and that balancing removes that effect
in this benchmark. It also shows why equal amplitudes do not mean equal
probability for distinct shapes. A permutation-invariant vector in the
labeled Hilbert space still has this orbit-size weighting. Changing the
physical inner product or choosing a different quotient would change
the model and needs an independent justification.
Six-site probabilities are not predictions about spacetime.

## 5. Stability and the retained quantum mechanism

For fixed Delta and couplings, Hermitian column-sum bounds give

\[
 \|H_N^{(2)}\|\le N\left[
 \frac{U\Delta^2}{2}+\frac{(\epsilon+|t|)\Delta}{2}
 +\frac{\lambda\Delta(\Delta-1)}{3}
 +\kappa\Delta(\Delta-1)
 +4\rho\Delta(\Delta-1)^2+|m_0|\right].
 \tag{9}
\]

Proof: edges <=N Delta/2; wedges <=N Delta(Delta-1)/2; triangles are at
most one third of the wedge count. A balanced active move contributes
twice its rate to the absolute column sum. Ordered active exchanges are
at most 2N Delta(Delta-1)^2, counting forward and reverse control paths.
The degree potential per vertex is at most U Delta^2/2 since dbar lies
between zero and Delta. Every other term uses the same capped occupancy
counts. Hermiticity bounds spectral norm by the largest absolute column
sum. Positivity of all terms except hopping and possibly m0 N_m also gives

\[
 H_N^{(2)}\ge-N\left[|t|\Delta/2+\max(0,-m_0)\right]I.
 \tag{10}
\]

This is extensive stability of the finite prototype, not existence of a
thermodynamic limit, a spectral gap, or an emergent propagation cone.

The three-site interference experiment remains exact with the revised
geometry gate. Prepare v1's state `(matter 110, links (-,absent,+))`, apply
U=exp[-i(pi/4)(R^2-R)], a matter hopping pulse V(phi), then U-dagger.
The resulting probabilities are:

| Matter pulse phi | Target connection present | Charge at destination |
|---|---:|---:|
| 0 | 0 | 0 |
| pi/2 | 3/4 | 1/2 |
| pi | 1 | 0 |

Amplitudes change phases relative to v1, but these probabilities persist.
This is a controlled unitary experiment with the retained joint state;
it is not a claim about autonomous thermalization under the sum (3).

## 6. Verification and the next physical test

[The executable audit](scripts/balanced_quantum_geometry_audit.py) builds
the actual revised Z2 Hamiltonian independently in the full capped Gauss
basis. It checks exact Hermiticity, matter-number and component
conservation, cyclic relabeling covariance, the balanced quadratic form,
and column bounds in dimensions 27, 249, and 729. At three sites it also
compares the independently assembled Hamiltonian against the original
full-space operators restricted to the 27-dimensional Gauss sector.
It verifies unitary feedback, the multiplicity negative control, the
balanced variational block, and all 70 configurations of (8).

[The Lean module](UnifiedTheory/Audit/KFCausalBalancedGeometry.lean) proves
nine supporting results: the balanced-square, adjoint and Gram identities;
the real finite-Laplacian constant vector, quadratic form and positivity;
equality along positive-weight edges at zero energy; the balanced
two-state inequality; and the multiplicity counterterm identity. All use
only the usual Lean foundational axioms. The complex matrix corollary,
path-connected kernel argument, operator assembly, stability estimates,
and six-site spectral inference are analytic or exact executable work,
not claimed as a complete Lean formalization of the physical model.
[The report](data/balanced_quantum_geometry_audit.json) pins source hashes.

The next decision is whether (3) has a growing, stable geometric scaling
regime. Test the same joint state with volume growth, spectral dimension,
matter dispersion, and operational influence; compare clustered, thin,
and rapidly expanding graph families. Neither an input valence nor a
single fitted dimension statistic counts as a successful phase test.
The pure balanced kinetic benchmark alone supplies no manifold selector.

The RK correspondence relates reference excitation energies to classical
relaxation rates; it does not ensure relativistic dispersion. A common
Lorentz cone must be derived rather than assumed from the word "local."
[Henley](https://arxiv.org/abs/cond-mat/0311345).
If no stable geometric regime exists, reject or explicitly revise (3)
again. A chosen target geometry cannot be inserted into amplitudes and
then reported as an emergent prediction.

Only after a successful phase test can the repository's conditional
continuum and Einstein-action results become possible downstream tools.
One must still derive compatible experiment-level refinement, a physical
spin-two sector and gravitational constraints, the selected continuum
action, and interacting chiral matter from the **same** dynamics.
The current findings justify a more testable candidate and less confidence
in a near-term TOE claim; they do not close those gaps.
