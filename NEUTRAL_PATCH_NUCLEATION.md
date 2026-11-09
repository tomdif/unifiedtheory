# Neutral moves can nucleate the first cubic neighborhood

Date: 2026-09-10

The 124-site obstruction in
[the reservoir construction](RESERVOIR_GEOMETRY_PREPARATION.md) can be
escaped: an independently replayed sequence has **3,359 neutral flips
followed by one defect-lowering flip**, producing its first correct
radius-three cubic neighborhood. Every intermediate graph is connected
and degree six. The earlier strict-descent obstruction remains valid.

A larger analytic result follows in a specified **quantum Markov model**.
Distinct neutral and lowering jump channels make its graph populations
obey a classical absorbing process exactly, for arbitrary quantum input.
It reaches the event “at least one good neighborhood” with probability
one. An 88-site construction and an external flip-chain mixing theorem
give a polynomial upper bound on the mean first-hitting time, with a
very large exponent. This does not establish a useful preparation rate,
a positive density of good neighborhoods, or a geometric phase.

The Lindblad generator below is a new open-system law. A finite collision
step has an explicit energy-preserving isometry, but its fresh pure
registers and Markov limit are supplied. The constant Hamiltonian bath
of the previous note is not shown to produce these neutral channels.

## 1. The maximum-defect plateau has an exit

Let Omega_N be the connected labelled simple 6-regular graph carrier.
Retain the supplied patch readout from
[the patch protection test](PATCH_GEOMETRY_PROTECTION.md): q_v=1 exactly
when the rooted induced radius-three ball agrees with that in Z^3.
Write g=sum_v q_v, D=N-g, and define

\[
\mathcal A_N=\{G:g(G)\ge1\},\qquad
\mathcal B_N=\{G:D(G)=N\}.                              \tag{1}
\]

The flip graph on Omega_N is connected. This follows from the
irreducibility result discussed in
[Cooper, Dyer, Greenhill and Handley, Section 1.2](https://arxiv.org/pdf/1701.03856).
If A_N is nonempty, take any finite flip path from a B_N graph into A_N.
Before its first entry into A_N, every vertex on this path has D=N.
All preceding flips are therefore neutral, and the first entry lowers D.
No energy barrier is required to create the **first** good neighborhood.

The executable witness starts at the identical connected double cover of
the F_5 projective-plane incidence graph used in the preceding note.
It has 124 vertices and no square. The stored sequence has 3,360 moves:

\[
D(G_0)=\cdots=D(G_{3359})=124,\qquad D(G_{3360})=123.
                                                               \tag{2}
\]

The last move is (a,b,c,d)=(28,55,64,63); root 31 becomes good.
The audit checks the legality of every exchange, every degree and
connectivity condition, and all 124 rooted patch tests at every step.
It performs 416,764 rooted tests in total, including the input graph.

The witness was found by a target-guided search, then shortened by
removing loops and truncated at the first good root. It is an existence
certificate, not a sample of an unbiased cooling process or an estimate
of its typical runtime. The analytic argument does not depend on that
search procedure.

## 2. Exactly 88 sites suffice for one good root

The radius-three cubic ball has 63 vertices and 114 internal edges.
Twenty-five vertices are at distance at most two and already have all
six neighbors in the ball. Its 38 boundary vertices have internal
degrees 1, 2, 3 with multiplicities 6, 24, 8 respectively. The number
of required edges from the ball to its exterior is therefore

\[
6\cdot63-2\cdot114=150.
\]

An outside vertex can receive at most six of these edges. Thus any
degree-six graph containing one such induced ball must have

\[
N\ge63+\left\lceil{150\over6}\right\rceil=88.             \tag{3}
\]

This bound is attained. Add 25 new vertices to the template. In a fixed
order, give each boundary vertex its missing neighbors by continuing a
cyclic traversal of the 25 outside labels. Its deficit is at most five,
so none of its added edges repeat. There are exactly 150 additions, so
every outside vertex has degree six. No extra edge joins two template
vertices. The graph is connected and its root has precisely the required
induced ball. The audit constructs it and verifies that root 31 is good.

For N=89,...,94, the same distribution of the 150 edges leaves a simple
residual degree sequence on the outside vertices; the audit constructs
each completion. For N>=95, attach the fixed 88-site gadget to any
connected 6-regular graph on N-88 sites as follows. Choose a fixed gadget
edge xy from its boundary to its exterior, and a deterministically chosen
core edge uv. Replace xy,uv with xu,yv. Each component remains connected
when its chosen edge is removed: a connected even-regular graph cannot
have a bridge, since every cut has even size. The two new cross edges
join the components. The root ball is unchanged. Thus A_N is nonempty
for every N>=88.

This joining switch is a **counting construction**, not an allowed local
flip between disconnected initial components. The dynamics starts in
Omega_N and uses only the existing connected-graph flips.

## 3. Counting one patch gives a polynomial hitting bound

Keep the gadget labels fixed, with all other labels assigned to the
core. Exactly two edges cross this known partition. Their core endpoints
recover uv, so restoring that edge recovers the entire input core graph.
The construction is injective. Let C_N=|Omega_N| and let
pi_N(A_N)=|A_N|/C_N be the uniform event probability. For N>=95,

\[
\pi_N(\mathcal A_N)\ge{C_{N-88}\over C_N}.                \tag{4}
\]

The audit checks this injection on all 105 labelled 6-regular graphs
on eight core sites, and on additional larger cores. The proof applies
to every connected core, not just the tested ones.

The fixed-degree enumeration formula and probability of connectedness
tending to one give

\[
C_N\sim { (6N)!\over(3N)!2^{3N}(6!)^N}\,e^{-35/4}.
\]

These are the external asymptotic suppliers already used in
[the entropy audit](GEOMETRY_ENTROPY_OBSTRUCTION.md); the counting formula
is the fixed-degree case of
[McKay and Wormald](https://users.cecs.anu.edu.au/~bdm/papers/McKayWormaldSqrtN.pdf).
Taking the ratio at a fixed difference of 88 gives the sharper result
needed here; the coarser statement log C_N=3N log N+O(N) alone would
not suffice:

\[
{C_{N-88}\over C_N}
\sim \left({10\over3}\right)^{88}N^{-264}.                \tag{5}
\]

Indeed, the factorial ratio contributes (6N)^-528 (3N)^264,
and the remaining factor is 2^264 720^88. Equation (5) is an
asymptotic lower bound on the event mass, not its exact asymptotic size.

For the unrestricted flip chain, choose a vertex uniformly and take
three random-walk steps, rejecting invalid paths. Its transition matrix
P is symmetric. At degree six,
[Theorem 1.1 of Cooper et al.](https://arxiv.org/pdf/1701.03856) gives

\[
\tau(\varepsilon)\le480\,6^{35}N^{15}
\left(6N\log(6N)+\log\varepsilon^{-1}\right).             \tag{6}
\]

Set q=pi_N(A_N) and take an integer block length T>=tau(q/2).
From any initial graph, the probability to be in A_N after T proposals
is at least q/2, by total variation. Being there implies that A_N was
hit during the block. The Markov property therefore yields

\[
\Pr(\tau_A>kT)\le(1-q/2)^k,
\qquad \mathbb E\tau_A\le{2T\over q}.
\]

Equations (5)-(6) give, uniformly over the initial graph,

\[
\boxed{\mathbb E[\text{proposals to first good root}]
       =O(N^{280}\log N).}                              \tag{7}
\]

This is a conservative existence bound with enormous constants and
exponent. It is not evidence of practical or cosmological efficiency.
Rejecting all increases of D leaves the process **identical to the
unrestricted chain until this first hit**, because D already has its
maximum value outside A_N. Once A_N is hit, such rejection preserves it.

## 4. Quantum populations follow the process exactly

Classical reachability alone does not eliminate quantum dark states.
For example, let states 1 and 2 couple coherently to a hub 3, with
H_neutral=|1><3|+|2><3|+h.c., and let the only lowering channel be
L=|0><3|. Both leaves have classical routes to target 0, but

\[
|d\rangle=(|1\rangle-|2\rangle)/\sqrt2,
\qquad H_{\rm neutral}|d\rangle=L|d\rangle=0.             \tag{8}
\]

Its density matrix is exactly stationary in the corresponding
Hamiltonian-plus-loss master equation. Graph connectivity misses this
destructive interference.

Here is a specified generator that avoids that problem. For each
ordered four-site partial exchange S_p, retain its components with
nonnegative defect drop r:

\[
M_{p,r}=\sum_{G:\ D(G)-D(S_pG)=r}|S_pG\rangle\langle G|,
\quad r=0,\ldots,748,\qquad L_{p,r}=\sqrt\gamma M_{p,r}.
                                                               \tag{9}
\]

The sum includes only valid exchanges. The radius bound and local
decision rule are as in the preceding note. Each M is a partial
permutation matrix: at most one nonzero entry per row and per column.
Supply the time-independent Lindblad generator

\[
\dot\rho=-i[JD,\rho]+\sum_{p,r\ge0}
\left(L_{p,r}\rho L_{p,r}^\dagger
-\tfrac12\{L_{p,r}^\dagger L_{p,r},\rho\}\right).         \tag{10}
\]

There is no additional coherent exchange rho L_S in (10). In particular,
this is not the unchanged patch Hamiltonian plus an assumed cooling law.

For a partial permutation M, (M rho M†)_GG has one possible source
population, and M†M is diagonal. Hence off-diagonal matrix entries of
rho do not enter the equations for p_G=rho_GG. Equation (10) gives exactly

\[
\dot p_G=\sum_{H\ne G}(w_{GH}p_H-w_{HG}p_G),\qquad
w_{GH}=\gamma\sum_{p,r}|(M_{p,r})_{GH}|^2.               \tag{11}
\]

It is unnecessary to label each complete input graph in the outgoing
record; recording the partial move and energy branch suffices for this
diagonal closure. Relabelling permutes the channels. The moves preserve
degrees and the empty-matter, plus-connection Gauss sector, and their
energy branches satisfy [JD,M_{p,r}]=-rJ M_{p,r}.

The ordered-move normalization gives w_{GH}=2 gamma times the number
of forward three-step path descriptions, for retained transitions.
Uniformizing at rate lambda=2 gamma N 6^3=432 gamma N therefore gives
the flip proposal chain with all uphill proposals rejected. Equations
(1)-(7) apply to (11), and thus to **every quantum input**, including
marginals of states entangled with a reference:

\[
\boxed{\operatorname{Tr}(P_{\mathcal A_N}\rho_t)\longrightarrow1,
\qquad \mathbb E[\text{first-hit time}]
       =O(N^{279}\log N/\gamma).}                        \tag{12}
\]

The time refers to the absorbing population process, or the corresponding
observed jump process; it is not an unmeasured quantum arrival observable.
Equation (12) asserts target-event probability, not convergence to a
unique pure graph. Also,

\[
{d\over dt}\langle JD\rangle
=-\gamma J\sum_{p,r}r\,
  \operatorname{Tr}(M_{p,r}^\dagger M_{p,r}\rho)\le0.
\]

Distinct **neutral** records now matter as well as distinct lowering
records. On the four-state example, replace coherent hub transport with
four directed neutral jumps and keep |0><3| as the lowering jump. The
exact killed population generator has eigenvalues -1,-2-sqrt(3),
-2+sqrt(3), and mean absorption times 4,4,3 in unit-rate time. The full
16-dimensional superoperator has only |0><0| as a stationary state.
The audit verifies diagonal closure on every matrix unit, including
off-diagonal inputs, and for a weighted partial permutation jump.

## 5. A collision dilation exposes the physical inputs

Let G=sum L†L, which is diagonal, and choose h>0 with hG<=I. Define

\[
K_0=\sqrt{I-hG},\qquad K_{p,r}=\sqrt h L_{p,r},
\qquad
V_h\psi=K_0\psi\otimes|\mathrm{vac}\rangle
+\sum_{p,r}K_{p,r}\psi\otimes|p,r\rangle.                 \tag{13}
\]

Then V_h†V_h=I exactly. Give the register record |p,r> energy rJ and
the vacuum zero energy. The energy-resolved identity in (9) implies

\[
(JD\otimes I+I\otimes H_R)V_h=V_h JD.                   \tag{14}
\]

An isometry from the vacuum-input subspace into the same total-energy
subspace extends to a unitary in each finite energy block. Thus a single
step admits an energy-conserving reversible dilation. Appending the
free unitary exp(-iJD h), its reduced map is I+h L+O(h²) at fixed N,
where L is (10). Repeated collisions with fresh pure registers give the
usual finite-dimensional continuous-time limit as h tends to zero.
The audit verifies (13)-(14) exactly as a 24 by 4 isometry for the
four-state example at h=1/4.

The r=0 records are distinct **zero-energy** states. They still consume
pure record capacity. An indefinitely repeated collision model supplies
fresh registers indefinitely; it does not reset them for free or derive
a time-independent physical conveyor of registers. In particular, the
gapped half-line reservoir from the previous note is not automatically
a source of these neutral zero-energy records. A physical autonomous
reservoir limit and its resource scaling remain separate requirements.

Quantum Markov state preparation is an established framework, for
example [Kraus et al., 2008](https://arxiv.org/abs/0803.1463). The claims
here concern the particular graph readout, neutral paths, and bounds,
not a new general principle of dissipation.

## 6. What this changes, and what it leaves open

The maximal-defect obstruction was a failure of immediate descent. A
neutral route exists, and recording neutral moves supplies a sufficient
quantum Markov mechanism to follow such routes without coherent dark
states. The exact 88-site threshold also makes the first-root event
nonempty and gives an explicit counting injection for growing N.

One root contributes only 1/N to the good-root fraction. At lower defect
levels, a path to more good roots may require an uphill step; the
maximum-level argument then no longer applies. Neither the witness nor
the polynomial bound proves positive-density order, continued growth,
or absence of metastable components below the top level.

The first-root event has rank deficit at most 264 log N+O(1) by (4)-(5).
The earlier positive-density event instead has a necessary record budget
of order N log N under its stated mixed-input premise. The first-root
result therefore does not remove that extensive preparation obligation
or the fixed-temperature obstruction.

The model's next tests are growth after the first seed, the energy
barriers between subsequent defect levels, and a physical reservoir
that realizes neutral information transport with controlled resources.
Dimension three, noncollapse, a Lorentzian continuum, and Einstein
dynamics are still not derived.

## 7. Verification boundary

- [`scripts/neutral_patch_audit.py`](scripts/neutral_patch_audit.py) checks
  the minimal gadget, injective attachment, all moves and rooted tests in
  the witness, full small-system Lindblad identities, a coherent dark
  state, finite collision energy conservation, and an exact mixing-block
  absorption estimate.
- [`data/neutral_patch_path.json`](data/neutral_patch_path.json) stores
  the actual 3,360-move witness, separate from the search that found it.
- [`UnifiedTheory/Audit/KFCausalNeutralPatch.lean`](UnifiedTheory/Audit/KFCausalNeutralPatch.lean)
  proves eight supporting results: the first-drop argument, the 88-site
  lower bound, single-source population dependence, disjoint-column Gram
  diagonality, nonpositive energy drift, the mixing-event bound, geometric
  block survival, and the resulting mean-bound inequality. These take
  the graph and stochastic suppliers at the stated finite scope.
- [`data/neutral_patch_audit.json`](data/neutral_patch_audit.json) records
  the executable results and source hashes. External graph enumeration
  and mixing theorems, and the analytic Lindblad/collision-limit argument,
  are not whole-model Lean claims.
