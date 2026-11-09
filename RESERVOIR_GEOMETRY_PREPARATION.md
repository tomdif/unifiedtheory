# Autonomous graph-class preparation with an explicit reservoir

Date: 2026-09-10

The six-site benchmark now has a time-independent, globally unitary
preparation mechanism for **every initial graph state**, including mixed
states and states entangled with an untouched reference. Forty-five
distinguishable emission channels remove all unwanted dark directions.
Semi-infinite channels give asymptotic target-class probability one;
finite channels give an explicit interval of greater than 99% success.
Energy and input information remain in the joint graph/reservoir state.

This is a new, exactly soluble reservoir Hamiltonian on the existing
70-state benchmark. Its target is a supplied class of ten labelled
K3,3 graphs, not a three-dimensional lattice or continuum. It replaces
bare graph transitions with composite graph/bath transitions. It does
not establish cooling for the unchanged spatial patch Hamiltonian,
derive a physical reservoir, or complete a TOE. An explicit 124-site
counterexample below obstructs the most direct strict-descent extension.

## 1. Why distinct outgoing records matter

Use the connected labelled 3-regular graphs on six sites from
[the autonomous benchmark](AUTONOMOUS_GEOMETRY_SELECTION.md).
Here “3-regular” means degree three, not spatial dimension three.
The graph Hilbert space decomposes as

\[
\mathcal H_G=A\oplus B,\qquad \dim A=10,\quad\dim B=60,
\]

where A comprises K3,3 graphs with zero triangles and B comprises
triangular prisms with two triangles. All connection states are plus
states and matter is empty, as in the earlier reference sector.

For an ordered quadruple p=(a,b,c,d), the existing Hermitian partial
exchange S_p keeps bc and swaps ab,cd with ac,bd whenever allowed.
Project its lowering part:

\[
M_p=P_A S_p P_B.
\]

The 360 ordered quadruples give 45 distinct 10 by 60 matrices M_mu,
each repeated eight times. Each distinct matrix is a partial matching
with four entries equal to one. Exact enumeration gives

\[
\boxed{\sum_{\mu=1}^{45}M_\mu^\dagger M_\mu=3I_B},\qquad
\sum_{\mu=1}^{45}M_\mu M_\mu^\dagger=18I_A.             \tag{1}
\]

Consequently the map

\[
T\psi={1\over\sqrt3}\sum_\mu M_\mu\psi\otimes|\mu\rangle,
\qquad T:B\longrightarrow A\otimes\mathbb C^{45}          \tag{2}
\]

is an isometry: T†T=I_B. There is no nonzero B vector annihilated by
all channels. Distinct matrices also have disjoint entry supports, so
Tr(M_mu† M_nu)=4 delta_mu,nu. Relabelling the six sites permutes the
45 channels; the audit checks all five adjacent-transposition generators.
The construction preserves the reference-sector degrees and Gauss law.

Keeping the channel label is essential. A single coherent emission
operator C=sum_mu M_mu instead obeys

\[
CC^\dagger=14I_{10}+4\mathbf 1\mathbf 1^\mathsf T,
\qquad \operatorname{rank}C=10.
\]

It therefore has **50 exact dark directions in B**. A calculation only
on the uniform class sums misses this obstruction. Equation (2) repairs
it by placing distinguishable output records in the reservoir. The
normalization below uses the 45 distinct channels; it is not the old
360-term exchange sum with its rate silently retained.

## 2. A constant Hamiltonian and its exact reduction

Set hbar=1. Supply positive constants kappa and Delta with Delta>2 kappa.
The graph energy is H_G=Delta P_B. In this toy D_toy=6P_B, so Delta=6J
would match the earlier toy defect gap; this is not a definition of the
large-graph radius-three defect operator.

The bath has vacuum |vac> and 45 independent chains with positions
j=1,...,R, or j in the positive integers. Each excitation has on-site
energy Delta and hopping -kappa. On the vacuum/one-excitation sectors,

\[
H_B=\Delta\sum_{\mu,j}|\mu,j\rangle\langle\mu,j|
-\kappa\sum_{\mu,j}\bigl(|\mu,j+1\rangle\langle\mu,j|+\mathrm{h.c.}\bigr),
\]

\[
H_{\rm int}=-{\kappa\over\sqrt3}\sum_\mu
\bigl(M_\mu\otimes|\mu,1\rangle\langle\mathrm{vac}|+
M_\mu^\dagger\otimes|\mathrm{vac}\rangle\langle\mu,1|\bigr),
\qquad H=H_G+H_B+H_{\rm int}.                            \tag{3}
\]

All terms are time independent. The operator
Q=P_B tensor I + I tensor n_B is conserved: lowering graph energy
creates exactly one bath excitation and the reverse move absorbs it.
Thus the bare energy Delta Q is conserved, in addition to total H.
Starting from any graph state and bath vacuum reaches only Q=0 and Q=1.
Ordinary bosonic chains give the same restriction to these sectors;
no claim requires a bath reset or discarding a measurement outcome.

The Q=0 subspace A tensor |vac> is stationary. Identify the following
subspace of Q=1 with B tensor span{|0>,...,|R>}:

\[
\psi\otimes|0\rangle\mapsto\psi\otimes|\mathrm{vac}\rangle,
\qquad
\psi\otimes|j\rangle\mapsto T\psi\otimes|j\rangle\quad(j\ge1).
\]

By (1), this identification W is isometric, and (3) becomes

\[
\boxed{H_{\rm bright}=I_B\otimes
\left[\Delta I-\kappa\sum_{j=0}^{R-1}
(|j+1\rangle\langle j|+\mathrm{h.c.})\right].}            \tag{4}
\]

The bath-channel complement to T(B) is never populated from the input.
It has its own uncoupled chains. All Q=1 energies are bounded below by
Delta-2 kappa>0, so the target-vacuum subspace is the zero ground sector
within Q=0 plus Q=1. The semi-infinite restriction is a bounded
self-adjoint operator and defines unitary evolution.

As a direct assembly check, the audit constructs the full 970-dimensional
Q=0 plus Q=1 matrix for R=2, its 190-dimensional bright/target restriction,
and the sparse embedding W. It verifies H†=H, W†W=I and HW=WK exactly,
including the factors 1/sqrt(3). This is independent of the numerical
propagation checks of (4).

The bath chains are a supplied transport structure. In particular, their
locality is not emergent graph locality, and the projections in M_mu are
defined on the complete six-site graph. Covariance under relabelling
does not by itself supply a scalable local interaction.

## 3. Exact preparation for arbitrary input

Remove the common Delta phase in (4). On the half-line, the sine spectral
transform gives the boundary return amplitude

\[
a_\infty(t)={2\over\pi}\int_0^\pi\sin^2q\,
 e^{2i\kappa t\cos q}\,dq
={J_1(2\kappa t)\over\kappa t},\qquad a_\infty(0)=1.      \tag{5}
\]

For example, integrate the derivative of sin(q) exp(i x cos(q)) to
relate the weighted integral to the derivative of the J_0 integral.
The Bessel integral representations are given by
[NIST DLMF 10.9](https://dlmf.nist.gov/10.9). The spectral measure
2 sin²(q)dq/pi integrates to one, fixing the normalization at t=0.

Let p_B(0)=Tr(P_B rho_G) for any initial density matrix. Orthogonality
of the vacuum and emitted subspaces and W†W=I imply the exact identity

\[
\boxed{p_B(t)=p_B(0)|a_\infty(t)|^2,\qquad
p_A(t)=1-p_B(t).}                                        \tag{6}
\]

It also holds if rho_G is the marginal of an input entangled with an
untouched reference. There is no initial-purity assumption.

The integer-order Bessel integral gives |J_1(x)|<=1 for real x, hence

\[
p_B(t)\le {p_B(0)\over(\kappa t)^2}\longrightarrow0.
                                                               \tag{7}
\]

The usual [Bessel asymptotic expansion](https://dlmf.nist.gov/10.17)
sharpens the large-time envelope to O((kappa t)^-3); the weaker bound
(7) suffices for the rigorous retention certificate. The probability
is not monotone, and it is not an exact exponential decay law.

At any time write c=exp(-i Delta t)a(t). The reduced graph channel is

\[
\Phi_t(\rho)=(P_A+cP_B)\rho(P_A+\bar cP_B)
 +{1-|c|^2\over3}\sum_\mu M_\mu\rho M_\mu^\dagger.       \tag{8}
\]

Equation (1) proves trace preservation. This is derived from the
unitary chain evolution, rather than postulating a dissipative
semigroup. Equation (7) establishes convergence of the reduced graph
state into the target class. The outgoing reservoir wavepacket escapes;
we do **not** assert convergence of the full joint vector to a stationary
vector. An infinite bath is precisely where finite recurrence no longer
forces the emitted record to return.

## 4. A finite reservoir with a rigorous retention interval

For R finite, the phase-removed return amplitude is exactly

\[
a_R(t)={2\over R+2}\sum_{k=1}^{R+1}\sin^2\!\left({\pi k\over R+2}\right)
\exp\!\left[2i\kappa t\cos\!\left({\pi k\over R+2}\right)\right].       \tag{9}
\]

Finite and infinite return moments agree through order 2R+1. A closed
walk from zero must take at least 2R+2 steps to visit the first missing
site R+1 and return. Their first differing moment is exactly one walk.
Using adjacency norm <=2 and the exponential series, for |t|<=T,

\[
|a_R(t)-a_\infty(t)|\le
2\sum_{m\ge K}{x^m\over m!}
\le {2e^x x^K\over K!}=:\delta_R(T),\qquad
x=2\kappa T,\quad K=2R+2.                               \tag{10}
\]

The last inequality uses (K+l)!>=K!l!. For t in [t_0,T], (7) and
the triangle inequality therefore give

\[
p_B(t)\le p_B(0)\left({1\over\kappa t_0}+\delta_R(T)\right)^2.        \tag{11}
\]

Take **45 chains of length R=128**, a total of **5,760 bath sites**,
initially in their joint vacuum. Set kappa t_0=11 and kappa T=20.
The exact rational comparison

\[
\delta_{128}(T)<{2\,3^{40}\,40^{258}\over258!}<{1\over1000},
\qquad
\left({1\over11}+{1\over1000}\right)^2
={1022121\over121000000}<{1\over100}                      \tag{12}
\]

uses e<3 and is checked with integer arithmetic. Equations (11)-(12)
prove **p_A(t)>99% for every input throughout kappa t in [11,20]**.
This is a whole-interval bound, not an inference from sampled times.
The numeric R=128 sample has worst unwanted probability about
0.00017749 in that interval; the rigorous bound is deliberately looser.

Longer prescribed retention requires more bath. For any fixed tolerance
the factorial tail in (10) can be made arbitrarily small. In fact
K!>=(K/e)^K gives a sufficient R=O(kappa T+log(1/delta)) bound:
K>=4ex and K>=log(2/delta) imply delta_R(T)<=delta.
There is no finite-bath permanent-capture theorem. For R=1 the phase-
removed amplitude is cos(kappa t), and kappa t=pi returns the entire
unwanted population. The audit checks this recurrence explicitly.

## 5. Where energy and information go

Bare graph energy falls by Delta p_B(0)(1-|a(t)|²), while bath
occupation energy rises by exactly the same amount. Total Hamiltonian
energy is conserved as well. The vacuum and the emitted wavepacket,
including its channel label, retain the quantum input reversibly.

The limiting graph channel is

\[
\Phi_\infty(\rho)=P_A\rho P_A+
{1\over3}\sum_\mu M_\mu\rho M_\mu^\dagger.               \tag{13}
\]

It prepares a graph **class**, not a unique pure state. Two exact checks
make that distinction explicit:

- Maximally mixed graph input I_70/70 produces I_A/10. Its effective
  bath record at each fixed nontrivial late time has rank 46: one vacuum
  record and 45 orthogonal channel records. In the asymptotic output
  their weights are 1/7 and 2/105 per emitted channel. Orthogonality here
  follows from Tr(M_mu† M_nu)=4 delta_mu,nu, not just from their labels.
- The old pure uniform graph input Omega=(|A>+sqrt(6)|B>)/sqrt(7)
  produces a graph state with eigenvalues 17/35 once and 2/35 nine
  times, and purity 13/49. The full state stays pure: the mixed graph
  state results from graph/bath entanglement.

The earlier rank-capacity theorem requires a pure record register of
dimension at least 70/10=7 for universal exact class compression. This
construction has sufficient capacity, without claiming optimality.
An inverse of the full unitary recovers the input; resetting the bath
would be an additional physical operation not included here.

This suggests a precise sufficient mechanism: **energy-lowering moves
that form an isometry into distinguishable outgoing records can prepare
a supplied class when a reservoir transports those records away.**
It applies more generally to any finite A,B and family satisfying (1)
with 3 replaced by a positive constant. The chain construction then
proves (6). It is a mathematical design principle, not a derived unique
law of nature. Reservoir engineering and dissipative state preparation
are established ideas; see, for example,
[Kraus et al., 2008](https://arxiv.org/abs/0803.1463). The contribution
here is the exact graph-channel construction and its resource checks.

## 6. Why strict patch cooling does not yet scale

For the large-graph proposal, keep the supplied radius-three local
template and defect D_3 from
[the patch test](PATCH_GEOMETRY_PROTECTION.md). At degree six, changing
four endpoints can affect at most

\[
4(1+6+6\cdot5+6\cdot5^2)=748
\]

rooted radius-three tests. A possible bare-energy-conserving coupling
would resolve each partial move F_p by its positive defect drop:

\[
M_{p,r}=\sum_{G:\ D_3(G)-D_3(F_pG)=r}|F_pG\rangle\langle G|,
\qquad 1\le r\le748,\qquad
[J D_3,M_{p,r}]=-rJ M_{p,r}.                             \tag{14}
\]

Only valid exchanges enter the sum. The decision uses bounded graph
neighborhoods around the affected endpoints, including the further
radius needed to evaluate the changed patches. Reservoir modes of
energy rJ can absorb the drop. But unlike (1), these moves do not have
a positive uniform Gram bound on the bad sector.

**Counterexample.** Take the point/line incidence graph of the projective
plane over F_5: 31 points and 31 lines, with incidence given by a zero
dot product between normalized nonzero triples. Each vertex has degree
six. Form a connected double cover by twisting one edge between the
two sheets. The resulting graph has 124 vertices, is connected and
bipartite, and has no four-cycle. The audit constructs it directly and
verifies all of these facts. It exceeds the 63-site patch-template size.

On any bipartite square-free graph, one allowed exchange cannot create
a square. A square containing exactly one new edge would require an
old three-edge path between vertices in the same bipartition, which is
impossible. A square containing both new edges requires the old edge
ad as well as bc, and therefore an old square abcd, also impossible.
Squares using no new edge were absent initially.

Every good cubic root requires 12 squares through that root. Thus
D_3=124 both initially and after **each of the 18,600 oriented moves**
(9,300 distinct output graphs). Every positive-drop channel (14)
annihilates this input:

\[
\sum_{p,r>0}M_{p,r}^\dagger M_{p,r}\not\ge cP_{\rm bad}
\quad\hbox{for any }c>0.                                \tag{15}
\]

This rules out the proposed strict-descent-only repair condition on
the stated carrier. It does not rule out neutral rearrangements,
multi-step nucleation, or other interactions. The first flip generally
breaks bipartiteness, so the proof does not claim the plateau is closed
under repeated zero-energy moves.

There are two further independent scaling obligations:

1. The finite positive-temperature entropy obstruction remains valid.
   For universal preparation from the maximally mixed large graph
   carrier into a positive-density good-root event, the earlier count
   and rank bound require log R_record >= (alpha/100) N log N-O_alpha(N).
   A fixed number of ancillary states per graph site cannot silently
   supply that record. Energy capacity and travel/retention times also
   require explicit scaling.
2. Equation (14) resolves the diagonal defect energy. The actual patch
   Hamiltonian also contains the noncommuting exchange term rho L_S.
   Cooling eigenstates of that full Hamiltonian is a different task;
   adding (14) does not automatically preserve its previous protection
   theorem or inherit the six-site chain reduction.

The next construction must permit neutral motion, show that unwanted
states reach emitting moves, control unwanted invariant subspaces and
preparation time, and provide the required physical record capacity.
Even a successful local-order preparation would leave noncollapse,
dimension selection, Lorentz symmetry, and Einstein dynamics open.

## 7. Verification and its scope

- [`scripts/reservoir_geometry_audit.py`](scripts/reservoir_geometry_audit.py)
  checks all 45 channels, both exact Gram identities, the collective
  dark subspace, relabelling covariance, a finite channel isometry,
  exact full-Hamiltonian intertwining, and output information accounting.
  It checks 810 finite-chain time samples, six independent spectral
  integrals, eight moment comparisons, the rational retention bound,
  and every one-step exchange on the 124-site plateau.
- [`UnifiedTheory/Audit/KFCausalReservoirGeometry.lean`](UnifiedTheory/Audit/KFCausalReservoirGeometry.lean)
  contains ten supporting results: isometric recovery, absence of dark
  vectors, Gram preservation, energy-filter commutators, cancellation of
  graph/bath energy shifts, the strict-descent plateau implication,
  amplitude and probability bounds, the numerical retention inequality,
  and the implication from return-amplitude decay to class preparation.
  The half-line spectral transform, graph enumeration, and infinite-bath
  limit are analytic/executable suppliers, not whole-model Lean claims.
- [`data/reservoir_geometry_audit.json`](data/reservoir_geometry_audit.json)
  records the finite evidence and hashes this note, its new sources,
  and the immutable predecessor sources used in the calculation.

The established advance is universal autonomous preparation of a supplied
finite graph class with explicit energy and information transport. The
counterexample identifies a concrete failure of its simplest spatial
extension; the large-scale geometric and physical bridges remain open.
