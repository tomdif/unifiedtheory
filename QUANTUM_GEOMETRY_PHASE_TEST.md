# Trying to prove the quantum-geometry candidate: bounds, obstruction, and a repair

Date: 2026-09-10

The [proposed Hamiltonian](RELATIONAL_QUANTUM_GEOMETRY_PROPOSAL.md) passes
an all-size energy bound, but its original connection moves have an exact
freezing defect. Every graph that saturates the degree cap and has no
triangles has fixed connectivity under that Hamiltonian. This includes
both three-dimensional cubic tori and one-dimensional graph families.

There is also an analytic variational obstruction: at cap six and nonzero
rewiring coupling, the particle-empty cubic sector cannot contain the
ground state of the particle-empty connected Z2 theory when electric
energy is nonnegative (epsilon>=0). An explicit
competitor lowers energy by an amount proportional to the number of sites.
The restriction to the particle-empty sector is essential: it is not a
theorem about an interacting filled fermion vacuum or every possible
geometric phase of the Hamiltonian family.

A new reversible two-edge exchange removes the freezing defect while
preserving degrees, Gauss constraints, connected components, and extensive
energy bounds. It is a specified **modification**, not a hidden change to
the earlier proposal. Selecting a geometric phase, obtaining Lorentz and
Einstein limits, and constructing chiral matter remain open.

## 1. Model and scope of the calculation

Use the proposal's Z2 link basis (absent, electric +, electric -), hard-core
charged matter, a fixed maximum degree Delta, and its actual Hamiltonian

\[
 H=\Pi_\Delta\left[
 \mu E+u W+\epsilon F-\lambda\sum_{\triangle}T_\triangle
 -g\sum_{i<j}c_{ij}(C_{ij}+C_{ij}^\dagger)
 -t\sum_{i<j}B_{ij}+m_0\mathcal N\right]\Pi_\Delta.
 \tag{1}
\]

On each graph basis state,

\[
 E=\#\text{present edges},\quad
 W=\sum_i\binom{d_i}{2},\quad
 c_{ij}=\#\{k:i\sim k\sim j\}.
\]

F counts negative electric links, N counts matter particles, T_triangle
flips the three electric signs around a present triangle, and B is the
gauge-dressed number-conserving hopping operator. In the rewiring term,
c_ij is an operator on the other links and commutes with C_ij. All
couplings are fixed real numbers independent of system size. The Hilbert
space is the range of Pi_Delta with Gauss constraints, not the kernel of
the compression projector.

The two no-matter trial states below have every present link in electric +.
They satisfy Gauss exactly. The no-matter sector is invariant because (1)
conserves particle number. No statement equates that sector with the
physical relativistic vacuum.

## 2. An extensive operator bound at every finite size

For N sites with degrees at most Delta, exact counting gives

\[
 E\le N\Delta/2,\quad
 W\le N\Delta(\Delta-1)/2,\quad
 T\le W/3,
 \tag{2}
\]

where T counts triangles. The first is the handshaking identity. The
second counts unordered neighbor pairs at each vertex; each triangle
contributes three such pairs to the third inequality.

In any fixed basis column of (1), each hopping term contributes magnitude
at most |t| on each present edge; each triangle contributes at most
|lambda|; and each neighbor pair contributes at most |g| to rewiring.
When several neighbor pairs produce the same transition their amplitudes
add, so the bound counts their multiplicities. A flux restriction or the
degree cap can only remove transitions. The diagonal contribution has
absolute value at most |mu|E+|u|W+|epsilon|E+|m_0|N.

Therefore every absolute column sum is at most N K_Delta, where

\[
 K_\Delta=\frac\Delta2(|\mu|+|\epsilon|+|t|)
 +\frac{\Delta(\Delta-1)}2
       (|u|+|g|+|\lambda|/3)+|m_0|.
 \tag{3}
\]

Hermiticity gives the same row bound. The finite Schur bound then proves

\[
 \boxed{\|H_N\|\le N K_\Delta,\qquad
              H_N\ge-NK_\Delta I.}
 \tag{4}
\]

For completeness, the Schur estimate follows by Cauchy–Schwarz:
|sum_j H_ij x_j|^2 <= (sum_j |H_ij|)(sum_j |H_ij||x_j|^2).
Sum over i and apply the row and column bounds. Restricting to an
invariant Gauss or connected-component sector cannot increase the norm.

This establishes extensive boundedness of the microscopic Z2 family,
despite the O(N^2) possible link registers. It does not establish a
thermodynamic limit, a geometric state, or compactness of geometries.
For larger matter representations or group cutoffs, the local operator
norms and occupation bounds must be included rather than reusing (3).

## 3. An exact invariant family with frozen connectivity

**Freezing theorem.** Suppose every vertex has degree Delta and the graph
has no triangles. Every original connection creation/deletion term
annihilates every state supported on this graph.

Proof: creating an absent edge would increase both endpoint degrees above
the cap. Deleting a present edge requires a common neighbor of its
endpoints; that would form a triangle. Thus neither move is allowed.
Matter hopping and electric evolution preserve edge presence, and no
triangle Wilson term exists. Consequently the entire fixed-graph matter/
link subspace is invariant, at every choice of the other couplings.
Matter can evolve there, but it cannot change that graph's connectivity.

This theorem includes all internal link states, not just a classical
approximation or the trivial-flux state. It is a defect in the intended
connectivity backreaction mechanism on these backgrounds. It is not a
general no-go theorem for gravity emerging from some other observables.

At Delta=6, consider even L>=4 and N=L^3:

- The Cartesian cubic torus (Z/LZ)^3 has nearest-neighbor edges.
- On Z/NZ, join each site to offsets +/-1, +/-3, +/-5.

Both graphs are connected, six-regular, and triangle-free. Each has 3N
edges and W=15N. Yet their spatial growth is different. For integer
r<L/2, a cubic ball contains

\[
 |B(r)|=(4r^3+6r^2+8r+3)/3.
 \tag{5}
\]

The offset graph has |B(r)|<=10r+1 before finite-size wrapping; it also
contains the ordinary nearest-neighbor cycle, giving linear lower growth
on that window. Thus the two frozen graph families have three-dimensional
and one-dimensional spatial growth respectively. This is a statement
about supplied graph metrics, not derived spacetime dimension.

With no matter particles, trivial electric links, and any epsilon, both
are exact eigenstates with

\[
 E_0=N e_6,\qquad e_6=3\mu+15u.
 \tag{6}
\]

The degree and edge terms cannot distinguish these states. Equal energies
alone would not establish ground-state degeneracy; the next calculation
shows why neither supplied state is a ground state when g is nonzero.

## 4. An all-size competitor with a strict energy-density gain

On the same N=L^3 sites, take the connected circulant graph with offsets
+/-1, +/-2, +/-3. It is also six-regular, so its no-matter, all-positive-
electric state has diagonal expectation E_0. It has triangles and is not
an eigenstate of the rewiring Hamiltonian.

Let M be the matching of N/2 edges

\[
 (0,1),(2,3),\ldots,(N-2,N-1).
\]

Consider the 2^(N/2)-dimensional trial space spanned by deleting arbitrary
subsets of M, with all remaining links in electric + and no matter.
Every graph stays connected: all offset-2 and offset-3 edges remain, and
these connect the entire ring. Degrees are five or six, so the cap holds.

Removing one selected edge changes the diagonal energy by

\[
 \delta=-\mu-10u.
 \tag{7}
\]

Every selected edge has exactly four common neighbors. Removing other
matching edges leaves those four control paths intact, since no other
selected edge touches either endpoint. Thus the rewiring amplitude
between its present and absent states is exactly -4g.

Projecting (1) onto this trial space gives **exactly**

\[
 P H P=E_0 I+\sum_{e\in M}
 \begin{pmatrix}0&-b\\-b&\delta\end{pmatrix}_e,
 \qquad b=4g.
 \tag{8}
\]

The selected-edge terms act on separate two-state factors. All other
rewiring terms leave this trial space. A triangle Wilson operation creates
negative electric flux, hence has zero matrix elements inside it. Electric
energy and hopping vanish there. Projection is used for a variational
bound; the trial space is not asserted to be invariant under the full H.

Diagonalizing each two-state matrix gives the upper bound

\[
 \frac{E_{\mathrm{ground}}}{N}
 \le e_6+\frac{\delta-\sqrt{\delta^2+64g^2}}4
 < e_6\qquad(g\ne0).
 \tag{9}
\]

This is a strict nonvanishing energy-density advantage for fixed nonzero
g and fixed couplings. It does not rely on extrapolating a small lattice.

There is also a rational trial witness avoiding square roots. Put
r=b/(1+|delta|) and use (|present>+r|absent>)/sqrt(1+r^2) on each matching
coordinate. Its shift per coordinate is

\[
 q(b,\delta)=
 \frac{b^2[\delta-2(1+|\delta|)]}{(1+|\delta|)^2+b^2}<0
 \quad(b\ne0).
 \tag{10}
\]

The numerator is negative because delta<=|delta|; the denominator is
strictly positive. The full trial energy is E_0+(N/2)q. Eleven Lean results
support the graph and variational argument, including this strict sign.

For example, choose u=11/10, g=2/5, and mu=-12. Deleting an edge costs
delta=1 on the diagonal, so a classical deletion does not improve energy.
Nevertheless r=4/5 gives q=-48/41, a quantum gain of **24/41 per site**.
With the original example's mu=-3/5, the conservative rational witness
gives a gain of 5312/16565 per site. These are regulator energy units,
not physical constants or predictions about the universe.

If epsilon>=0, every particle-empty state supported on a frozen six-regular
triangle-free graph has energy at least E_0: its only extra term is
nonnegative electric energy. That subspace is invariant. Since (9) puts
the particle-empty ground energy strictly below E_0, any ground eigenvector
in the connected no-matter sector is orthogonal to the whole frozen
six-regular triangle-free subspace. In particular it has no probability
on the exact cubic graphs considered above.

This conclusion assumes cap six, g nonzero, and the stated particle-empty
sector. It does not exclude an unsaturated geometric phase, cap greater
than six, a fluctuating phase with other graph support, an interacting
filled matter state, or a different Hamiltonian. Nor does the trial graph
identify the true ground state; it merely beats the proposed frozen one.

## 5. A concrete additional move that removes the freezing defect

For four distinct vertices a,b,c,d, define

\[
 A_{abcd}=N_{bc}C_{ac}C_{bd}C_{ab}^\dagger C_{cd}^\dagger,
 \qquad S_{abcd}=A_{abcd}+A_{abcd}^\dagger.
 \tag{11}
\]

It exchanges present trivial-flux edges ab,cd for absent edges ac,bd,
while keeping the control edge bc. Its reverse does the opposite.
Different edge operators commute. On each nonzero support block S is a
two-state swap, and elsewhere it is zero. Therefore

\[
 S^\dagger=S,\quad S^3=S,\quad
 e^{-i\theta S}=I+(\cos\theta-1)S^2-i\sin\theta S
 \tag{12}
\]

is unitary for every real theta. Each C commutes with the endpoint gauge
actions, so S preserves every Gauss constraint. It still cannot delete a
nontrivial flux link without another operation that transfers its state.

Every affected vertex loses one edge and gains one. Hence S commutes
with every degree operator and respects any degree cap. The old path
a--b--c--d and the new path a--c--b--d each connect all four vertices;
other edges are unchanged, so connected components are preserved.

In a triangle-free graph, any simple three-edge path has ac and bd absent.
Thus it supplies an allowed switch in the trivial electric state, even
when every vertex saturates its degree cap. Such a path exists in a
triangle-free regular graph of degree at least two: choose a neighbor a
of b distinct from c and a neighbor d of c distinct from b. Triangle
freeness ensures the four vertices are distinct and the two new edges
are absent. This removes the specific saturated freezing mechanism.

On a 64-site cubic torus, one such switch preserves all degrees at six
and preserves connectedness, but changes the number of four-cycles from
**240 to 232**. The graphs are therefore not isomorphic: this is a change
of relational structure, not merely a relabeling of vertices.

A specified extension is

\[
 H'_N=H_N-\rho\sum_{a,b,c,d\ \mathrm{distinct}} S_{abcd}.
 \tag{13}
\]

Here the sum is over ordered distinct quadruples, so its repeated copies
are part of the definition of rho. The sum is invariant under vertex
relabeling. A state can activate at most N Delta(Delta-1)^2 forward
ordered paths and the same number of reverse paths. The previous bound
therefore extends to

\[
 \|H'_N\|\le N[K_\Delta+2|\rho|\Delta(\Delta-1)^2].
 \tag{14}
\]

This correction supplies actual geometry-changing matrix elements on the
previously frozen backgrounds. It does not prove that cubic geometries
are preferred, that their fluctuations are gravitons, or that rewiring
respects a common emergent Lorentz cone. It adds the coupling rho; it is
not a uniqueness theorem selecting dynamics from consistency.

Exchange interactions already occur in quantum-graphity research. The
contribution here is the explicit constrained move and its checks for
this repository's absent/flux link carrier, together with the identified
defect of its original move set.
[Konopka–Markopoulou–Severini, section II.3.3](https://arxiv.org/html/0801.0861v2#S2.SS3.SSS3).

## 6. Verification and remaining proof target

`UnifiedTheory/Audit/KFCausalQuantumGeometryPhase.lean` proves eleven
supporting results: capped creation, triangle-free deletion, their combined
freezing criterion, edge and wedge bounds, the missing edges of a switch,
the rational Rayleigh identity and its negative sign, the resulting
energy-density comparison, a minimization contradiction, and the endpoint
degree arithmetic. The actual Hamiltonian assembly, explicit graph
families, tensor trial state, and spectral inference are analytic proofs
above, not fully assembled Lean theorems.

`scripts/quantum_geometry_phase_audit.py` checks:

- All 33,867 labeled simple graphs on one through six vertices, including
  110 saturated triangle-free graphs, with exact counts and move eligibility.
- Frozen cubic and linear-growth families at 64, 216, 512, and 1,000 sites,
  and the matching/control-path and connectedness suppliers of (8).
- Actual rational Hamiltonian compression on 64 trial basis states at
  N=64, with two choices of mu, verifying the product-state energy formula.
- The original full 216-dimensional prototype's row sum: 11/2, bounded by
  the analytic extensive estimate 111/10.
- Every basis input of the four-site switch: 11,664 configurations,
  192 nonzero transitions, exact involution, gauge, degree, connectedness,
  and arbitrary-angle gate checks.
- An isomorphism-invariant change in the switched cubic graph.

The report `data/quantum_geometry_phase_audit.json` records the results and
source hashes. Older proposal files and their audit hashes are preserved;
this document explicitly changes the candidate by (13).

The next physical proof target is a geometric phase of the revised
Hamiltonian or of a justified unsaturated sector of the original one,
with a nontrivial matter state and controlled joint refinement. The
obstruction above eliminates a natural but incorrect route to that proof.
The new switch makes that route dynamically possible; it does not yet
establish dimension, Lorentz symmetry, Einstein gravity, chiral matter,
or a physical TOE.
