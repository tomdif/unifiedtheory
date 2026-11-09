# Coarse geometry, finite quantum information, and reversible preparation

Date: 2026-09-10

**Coarse-graining and state preparation must pay explicit information
costs.** This follow-up strengthens the [v2 entropy result](GEOMETRY_ENTROPY_OBSTRUCTION.md)
in three ways. It counts microscopic configurations compatible with
coarse geometry, including all cell assignments and arbitrary internal
graphs. It constructs an optimal reversible preparation with an explicit
record register. It tests a compact graph-state encoding and finds an
exact incompatibility with the original conditional exchange.
It also constructs a coherent two-pulse preparation which evades the
mixed-input premise at finite size, while retaining the full quantum state.

These results narrow the replacement-model requirements. They do not
select spacetime dimension, derive gravity, or exclude every possible
operational notion of emergent geometry.

## 1. Count the coarse event itself

Let N=M b, where M is the number of coarse cells and each cell contains
b microscopic vertices. The fine graph has degree cap Delta>=3 and at
most K=Delta N/2 edges; take sizes with Delta N even. The allowed coarse
templates have maximum degree z, with at most F_M unlabelled templates.
A fine edge is local if both ends lie in the same coarse cell or in
neighboring cells of the template. Every other edge is called far.

Define G_(N,M,eta) to contain all fine graphs admitting **some** balanced
assignment to **some** allowed template, with at most eta K far edges,
where 0<=eta<=1. No restriction is made on the internal graph of a cell,
or on which allowed vertices neighboring cells connect. The event also
retains all permitted electric and matter states. A requirement that at
most an eta fraction of the actual present edges be far is a subset of
this event; for Delta-regular graphs the two edge budgets coincide.

For a fixed cell assignment and template, let A_l and A_f count possible
local and far unordered vertex pairs. Then

\[
 A_l\le\frac{(z+1)Nb}{2},\qquad A_f\le\frac{N^2}{2}.
 \tag{1}
\]

Put weight 1/b on a local edge and 1/N on a far edge. A graph with E
edges, r of them far, has product weight b^(-E) M^(-r). If E<=K and
r<=eta K, its weight is at least b^(-K) M^(-eta K). Summing over all
subsets of possible edges therefore gives the generating-function bound

\[
 \#\{\text{allowed graphs for this assignment}\}
 \le b^K M^{\eta K}(1+1/b)^{A_l}(1+1/N)^{A_f}
 \le b^K M^{\eta K} e^{(z+2)N/2}.
 \tag{2}
\]

The first sum deliberately includes graphs violating the degree cap,
which only enlarges the bound. The last inequality uses log(1+x)<=x.
Integer far-edge budgets can use floor(eta K) before the displayed bound.

There are at most M^N cell assignments. One labelled representative per
unlabelled template suffices: composing the cell assignment with a coarse
isomorphism covers all labellings. For a fine graph, at most 2^K electric
assignments occur, and in the Z2 prototype Gauss fixes the matter bits
from their flux parities. Consequently the event projector obeys

\[
 \operatorname{rank}P_{N,M,\eta}
 \le F_M M^N 2^K b^K M^{\eta K} e^{(z+2)N/2}.
 \tag{3}
\]

This overcount includes every cell assignment, all internal fine graphs,
all allowed cross-cell endpoint choices, and all microscopic flux states.
No independently chosen preferred partition is hidden in it.

The full connected Gauss space contains all connected Delta-regular
trivial-flux graphs. Fixed-degree enumeration gives
log D_N >= (Delta/2)N log N-O(N), using the connectedness result already
documented in the previous note. The enumeration input is external;
the coarse-event count above is the present derivation.
[McKay–Wormald](https://users.cecs.anu.edu.au/~bdm/papers/McKayWormaldSqrtN.pdf).
Since log N=log M+log b, (3) implies

\[
 \log\frac{\operatorname{rank}P_{N,M,\eta}}{D_N}
 \le-\underbrace{\left[(1-\eta)\frac\Delta2-1\right]}_{a}
            N\log M+O(N)+\log F_M.
 \tag{4}
\]

Assume z and Delta fixed and F_M<=exp(c M) for fixed c. Since M<=N,
the template factor is absorbed in O(N). If

\[
 \eta<1-\frac2\Delta,
 \tag{5}
\]

then a>0. Whenever M tends to infinity, the rank fraction vanishes
faster than exp(-c' N) for every fixed c'>0, even if cells contain
arbitrarily many microscopic vertices as N grows.

At degree six, a=2-3eta. Thus the bound covers eta<2/3; at eta=0 the
deficit is **2N log M**. This threshold is sufficient for the counting
obstruction, not a physical critical fraction or a sharp phase boundary.
For M=N^alpha, the deficit becomes 2alpha N log N at eta=0.
For slowly growing M the same conclusion holds, with a slower onset.

Applying the previous quantum Gibbs bound gives, for the actual v2
Hamiltonian with ||H_N||<=K_Delta N,

\[
 \Pr_\beta(G_{N,M,\eta})
 \le \exp[-aN\log M+O(N)+2\beta K_\Delta N]\longrightarrow0
 \tag{6}
\]

at fixed finite beta and fixed couplings, under (5) and M tending to
infinity. This closes the coarse-cell loophole for the event just
defined, including its unrestricted microscopic degeneracy.

The assumptions still matter. This is a statement about near-local
**edge presence** on bounded-degree coarse templates with the stated
template count. It does not cover every manifold discretization or a
geometry inferred solely from state-dependent operational influence.
A construction in which many present links are dynamically ineffective
would need its own observable and rank analysis. It also does not cover
a zero-temperature scaling limit or arbitrary low-entropy initial states.
The beta in (6) uses regulator energy units; its relation to physical
temperature remains part of the missing refinement construction.

## 2. Reversible preparation: a sharp capacity bound and a construction

Let the graph system have dimension D and initial state I_D/D. Add an
R-dimensional record register in a specified pure state, allow any joint
unitary U, and ask that the final graph system lie in a rank-m target
sector P. Then

\[
 p_{\rm success}
 =\operatorname{Tr}[(P\otimes I_R)
 U(I_D/D\otimes|0\rangle\langle0|)U^\dagger]
 \le\min\left(1,\frac{mR}{D}\right).
 \tag{7}
\]

Proof: the joint input and output density operators have largest
eigenvalue 1/D. Therefore the output is bounded above by I_(DR)/D;
the event projector has rank mR. Taking its trace proves (7).
More generally, for any input rho with a pure uncorrelated register,
p_success<=mR ||rho||_infinity. No measurement or entropy reset is used.

The bound is attainable without imposing locality. Index the joint basis
as |i,r>, with flat index iR+r. Map each input basis vector |i,0>
to the joint basis vector of flat index i, for i=0,...,D-1. Extend this
injection to a permutation of the remaining joint basis states. It is a
unitary, and exactly min(D,mR) images lie in the target range i_system<m.
It recovers every input, including coherent superpositions, under its
inverse. If D=mR, the maximally mixed input becomes I_m/m on the chosen
sector and I_R/R on the record, with the total entropy unchanged.

The executable includes the 70 connected three-regular graphs on six
vertices. A seven-dimensional register suffices to prepare their
10-dimensional triangle-free sector with probability one from I_70/70.
Preparing a specified **pure** state from I_70/70 instead requires R>=70;
the construction reaches that bound too. The target sector is supplied
to the construction. These operations are arbitrary joint permutations,
not a derived local, permutation-covariant law of nature. They quantify
the resources rather than establish physical geometry selection.

Combining (4) and (7), preparation of the coarse event from a maximally
mixed graph input with fixed positive success probability p0 requires

\[
 \log R_N\ge aN\log M-O(N)+\log p_0.
 \tag{8}
\]

An ancillary register with only a fixed number of qubits per fine vertex
has log R_N=O(N) and cannot supply this resource when M grows. The same
conclusion holds for a Gibbs input at fixed regulator beta: its largest
eigenvalue is at most exp(2 beta K_Delta N)/D_N, which changes only O(N).
Already supplying a sufficiently pure geometric input evades the premise,
but then its preparation is the resource to explain. Correlated initial
registers and external reservoirs require separate joint-state accounting.

Crucially, a **pure uniform superposition** of graph states is not I_D/D,
despite giving the same graph-measurement distribution. Its largest
density-matrix eigenvalue is one, and (7) does not apply to it. A unitary
can turn known coherence into a concentrated measurement distribution
without exporting entropy. The finite protocol below demonstrates this
distinction explicitly.

This is an information-capacity bound. No numerical heat or work cost
is asserted without a reservoir Hamiltonian and thermodynamic protocol.
For the distinct thermodynamic entropy/heat statement, see
[Reeb–Wolf](https://arxiv.org/abs/1306.4352).

## 3. Finite quantum data cannot retain unrestricted sharp graph readout

Suppose M_graph possible graph configurations are encoded as density
operators rho_g in a D_code-dimensional Hilbert space. A single-copy
measurement tries to identify g, with POVM effects E_g summing to I.
For a uniform prior,

\[
 p_{\rm decode}=\frac1{M_{\rm graph}}
       \sum_g\operatorname{Tr}(E_g\rho_g)
 \le\frac1{M_{\rm graph}}\sum_g\operatorname{Tr}E_g
 =\frac{D_{\rm code}}{M_{\rm graph}}.
 \tag{9}
\]

The inequality uses 0<=rho_g<=I and E_g>=0. In particular, constant
average decoding success requires D_code>=p0 M_graph. Orthogonal
sharp graph configurations require at least one dimension each.
This does not limit how many **nonorthogonal** states can be specified,
or how much information can be accumulated from many independently
prepared copies. It limits the distinguishable configurations available
in the single physical register being modeled.

The v2 conditional flips connect all connected regular graphs. Therefore
these three requirements cannot hold together as N grows, at fixed
degree greater than two:

1. Only a fixed finite quantum dimension q per independent vertex/cell,
   so the total dimension is at most q^N.
2. The original graph configurations remain sharply distinguishable, or
   uniformly decodable with constant average success.
3. Every original allowed conditional flip remains available, so the
   state space containing one such graph is closed over its full regular
   graph component.

Even counting unlabelled graphs leaves exp[(d/2-1)N log N+O(N)] choices,
which outgrows q^N. A smaller carrier must alter the observable graph
distinctions or the closure of the moves. Calling the states relational
does not implement either change by itself.

### An explicit compact encoding fails the dynamics test

A natural attempt is the standard N-qubit graph state

\[
 |\gamma(G)\rangle=\prod_{ij\in E(G)}CZ_{ij}|+\rangle^{\otimes N},
 \tag{10}
\]

whose computational amplitude at bit string x is
2^(-N/2)(-1)^(sum_(ij in E) x_i x_j). This construction has only 2^N
dimensions and can encode many nonorthogonal graph states. It is
established quantum-information machinery, not a new encoding invented
here. [Hein–Eisert–Briegel](https://arxiv.org/abs/quant-ph/0307130).

An unconditional CZ toggle of a named edge is a valid unitary on (10).
The original **conditional** flip is a different requirement. Let F
be the involution which exchanges ab,cd with ac,bd when its control
and occupancy conditions hold, and otherwise fixes the graph. Any
unitary implementing F on encoded rays must preserve
|<gamma(G)|gamma(H)>| for every pair.

For six vertices and the tuple (a,b,c,d)=(0,1,2,3), the audit finds
connected three-regular graphs G,H with

\[
 |\langle\gamma(G)|\gamma(H)\rangle|=\tfrac14,
 \qquad
 |\langle\gamma(FG)|\gamma(FH)\rangle|=\tfrac12.
 \tag{11}
\]

It supplies their full edge lists and verifies all 2,415 pairs in the
70-graph family: 432 pairs violate overlap-magnitude preservation.
Thus no unitary on these six qubits implements this original flip on
all encoded states, even allowing input-dependent overall phases.
The nonorthogonal encoding does not preserve the old dynamics. This
does not exclude a different finite-qubit Hamiltonian with an emergent
operational geometry; that would change the model.

## 4. A coherent preparation works, and protection is a separate test

The old six-site benchmark also permits an exact **real-time** check,
separate from the previous stochastic stress tests. Let |A> be uniform
over the 10 triangle-free three-regular graphs, and |B> uniform over
the 60 triangular-prism graphs. Their span is invariant under the actual
balanced exchange Hamiltonian, whose restriction is

\[
 H_{AB}=\rho\begin{pmatrix}144&-24\sqrt6\\-24\sqrt6&24\end{pmatrix}
       =\rho L,\qquad L^2=168L.
 \tag{12}
\]

Consequently exp(-it rho L)=I+(exp(-168 i rho t)-1)L/168. The known
reference ground state is |Omega>=(|A>+sqrt(6)|B>)/sqrt(7). Its triangle-free
probability is 1/7, but it is a pure state with retained coherence.

Supply two independently controlled Hamiltonian pulses: the diagonal
triangle-occupancy operator T=sum_f P_f for pulse area pi/2, followed by
the balanced exchange for time pi/(168 rho), with rho>0. Both preserve
Gauss constraints and degrees. On the invariant span above they give

\[
 V=e^{-i\pi\mathcal T/2}=\operatorname{diag}(1,-1),\qquad
 U=e^{-i\pi L/168}=I-L/84=2|\Omega\rangle\langle\Omega|-I,
\]
\[
 UV|\Omega\rangle=
 \frac{-17|A\rangle-3\sqrt6|B\rangle}{7\sqrt7},\qquad
 \Pr(A)=\frac{289}{343}\simeq0.843.
 \tag{13}
\]

The inverse pulses recover |Omega> exactly. No register, measurement,
postselection, or reset is used. For the maximally mixed I_70/70 input,
any such unitary leaves the state unchanged and the probability stays
1/7. This is an instance of the known two-reflection amplitude-amplification
mechanism, implemented here in the graph benchmark; it is not a new
general quantum-search algorithm.
[Grover](https://arxiv.org/abs/quant-ph/9605043).

The triangle phase is an **additional independent control**, not autonomous
evolution under v2 with its magnetic face/flux coefficients tied together.
The selected class, initial pure state, pulse timing, and ability to
switch terms are inputs. At six sites the symmetry leaves only two
relevant energies, enabling this exact reflection. No equally simple
reflection, scalable preparation time, or manifold selector has been
derived at large N. This is a constructive finite escape from the
mixed-input bound, not a demonstration of emergent geometry.

Preparation also does not ensure stability. Starting in the coherently
prepared |A> and letting the exchange act gives

\[
 \Pr(B,t)=\frac{24}{49}\sin^2(84\rho t).
 \tag{14}
\]

At t=pi/(168 rho), the leakage is 24/49, without measurements, resets,
or loss of unitarity. These are six-site graph classes, not spacetime
phases. The result demonstrates that a preparation protocol alone does
not make its chosen sector dynamically invariant. Equation (14) starts
from the pure coherent |A>; the seven-state-record protocol above yields
the mixed state I_A/10 and is not asserted to have this time dependence.

## 5. Verification and the resulting model requirement

[The exact audit](scripts/coarse_geometry_audit.py) checks:

- All 32,768 edge subsets on six vertices against the product generating
  function, plus degree-constrained graph counts and Gauss-state ranks
  at four far-edge budgets.
- Every balanced cell assignment for three coarse-partition tests:
  90 assignments for six vertices in three pairs, and 2,520 assignments
  each for two eight-vertex tests in four pairs. It minimizes the number
  of far edges over all assignments for 38,780 regular graph configurations.
- Five complete preparation permutations, including a 4,900-dimensional
  joint space, their inverses, coherent recovery, and saturation of (7).
- A four-state qubit POVM saturating (9) at decoding probability 1/2;
  all graph-state pairs in (11); and the exact 70-state Hamiltonian
  restriction, coherent amplification, inverse pulses, and leakage in
  (12)-(14).

Finite coarse fits can be permissive: all 19,355 three-regular graphs
on eight vertices fit a four-cycle of two-vertex cells with no far edges.
For four-regular graphs at the same size, 5,915 fit exactly and 13,440
need at least one far edge. Thus a good fit to a tiny coarse template is
not evidence of a large-scale geometric phase. The finite inequalities
need not yet be numerically restrictive; the growing-M conclusion uses
the analytic counting bound and the cited large-N graph count.

[Seven supporting Lean results](UnifiedTheory/Audit/KFCausalCoarseGeometry.lean)
prove the actual finite weighted-edge-family bound, the coarse exponent
identity and threshold, POVM trace-sum capacity and its uniform-success
corollary, and the register-capacity/entropy algebra. The spectral
suppliers, operator preparation theorem, graph encodings, and asymptotic
assembly are analytic or exact executable arguments, not a complete Lean
formalization of quantum gravity. [The report](data/coarse_geometry_audit.json)
pins source hashes.

The finite-information proposal now has a concrete requirement: if
geometry is encoded in q^N quantum states, it must be defined through
the distinguishable operational records that the new dynamics actually
supports. It cannot keep unrestricted sharp graph configurations and
the complete old conditional flip dynamics simultaneously. A reversible
preparation must account for its initial purity and record capacity,
and the resulting geometry must remain stable under the specified
Hamiltonian. The coherent pulse protocol supplies a finite example of
using purity without a record register; a scalable autonomous version
is still missing. V2 has not met the full requirements. This follow-up
does not yet supply a replacement Hamiltonian that derives spacetime.
