# Patch geometry: protection, preparation, and temperature

Date: 2026-09-10

**The proposed neighborhood interaction gives a uniform bound on local
geometric defects.** Its ground states, and autonomous evolution from a
supplied perfect lattice, have expected defective-vertex fraction at most
300rho/J. This is a positive result about fluctuating states, rather than
the probability of one exact graph family.

There are two distinct limits to that result. The uniform pure graph
state has too much energy to become mostly ordered under the same strong
constant penalty without somewhere to transfer that energy. Separately,
at every fixed nonzero temperature, the expected fraction of good cubic
neighborhoods tends to zero on the current regular-graph carrier. The
thermal statement counts the local-order event directly and does not
assume a bound on the number of macroscopic geometric shapes.

The template explicitly supplies three-dimensional local flatness.
The results do not derive spacetime dimension, establish macroscopic
noncollapse, construct autonomous cooling, or complete a TOE.

## 1. A specified Hamiltonian and observable

Work on the orthonormal basis of connected labelled simple six-regular
graphs on N vertices. Use the actual weighted configuration exchange
Laplacian L_S from [the preceding audit](AUTONOMOUS_GEOMETRY_SELECTION.md).
For each vertex v let q_v(G) be one exactly when the rooted **induced**
radius-three ball around v is isomorphic to that in Z^3. Define

\[
 g(G)=\sum_v q_v(G),\qquad D_3(G)=N-g(G),\qquad
 H_{\rm patch}=\rho L_S+J D_3,\quad \rho>0,\ J>0.
 \tag{1}
\]

The D3 operator is diagonal in the graph basis. Expected g/N is the
probability that a uniformly chosen root passes this specific local
geometry test after measuring the graph. A bound on its mean is not a
probability-one statement about every vertex or every measured graph.

This is a new interaction postulate on a regular sector. It has an
invariant realization in the full qutrit model by retaining balanced
exchange and diagonal degree/flux penalties, setting the wedge,
magnetic and hopping coefficients to zero, and adding the same diagonal
neighborhood observable. The regular trivial-flux block is invariant.
Selecting that block among all degrees and fluxes remains
a separate question. The results here do not cover the complete v2
Hamiltonian with its other finite couplings restored.

There are at most N*6*5^2 admissible oriented length-three paths. Each
contributes exchange weight two, so every configuration row sum is at
most 300N. Symmetry, nonnegative weights, and the Laplacian quadratic
form imply

\[
 0\le L_S\le600N I,\qquad
 0\le H_{\rm patch}\le(600\rho+J)N I.
 \tag{2}
\]

For example, the quadratic bound follows by applying
|a-b|^2<=2|a|^2+2|b|^2 to the weighted edge sum. These are full
configuration-space operator inequalities, not bounds on a quotient
excitation spectrum or on the spatial graph Laplacian.

## 2. Uniform ground-state and real-time protection

Take N=ell^3 with even ell>=8, so an ordinary cubic torus G0 has all
q_v=1. Its weighted exchange row sum is exactly 300N, and hence

\[
 \langle G_0|H_{\rm patch}|G_0\rangle=300\rho N.
 \tag{3}
\]

Rayleigh-Ritz gives E0<=300rho N. Since H_patch>=J D3, every normalized
ground state obeys

\[
 \frac{\langle D_3\rangle_{\rm gs}}N\le\frac{300\rho}{J},
 \qquad
 \frac{\langle g\rangle_{\rm gs}}N\ge1-\frac{300\rho}{J}.
 \tag{4}
\]

The same bound holds at **every real time** for
psi(t)=exp(-it H_patch)|G0>, because its total energy remains (3):

\[
 \sup_t\frac{\langle\psi(t)|D_3|\psi(t)\rangle}{N}
 \le\frac{300\rho}{J}.
 \tag{5}
\]

More generally any initial state of energy at most eN has mean defect
fraction at most e/J throughout its closed evolution. At J=30000rho,
(4)-(5) guarantee at least 99% good roots **in expectation**, uniformly
in N. The coefficient is conservative, not a critical coupling.

For a graph measurement, Markov's inequality also gives
Pr[D3/N>=delta]<=300rho/(J delta). This is the appropriate way to
convert the expected-density result to a probabilistic one. It does not
give a uniform bound on the chance of any defect when N grows.

If rho_N/J_N tends to zero, (4)-(5) give vanishing expected defect
density, uniformly in time for the stated initial states. Fixed-ratio
small defect density does not exclude long-range shortcuts, and perfect
radius-three neighborhoods still permit thin tori. These distinctions
prevent interpreting (4) as a complete spatial continuum theorem.

## 3. Why protection is not autonomous preparation

Let Omega_N be the normalized coherent uniform state over **all**
connected six-regular graphs. It satisfies L_S Omega_N=0. Put

\[
 d_0=\langle\Omega_N|D_3|\Omega_N\rangle/N.
\]

After switching to the constant Hamiltonian (1), energy conservation and
(2) give

\[
 JNd_0=\rho\langle L_S\rangle_t+J\langle D_3\rangle_t,
 \qquad
 \frac{\langle D_3\rangle_t}{N}\ge d_0-\frac{600\rho}{J}.
 \tag{6}
\]

This inequality is exact for every N and time. It applies to the known
**pure** input; no mixed-state entropy argument is being substituted.

A good cubic root belongs to exactly twelve squares. Summing square
incidences over vertices gives

\[
 12g(G)\le4C_4(G),\qquad g(G)\le C_4(G)/3.
 \tag{7}
\]

The external fixed-degree short-cycle mean is
E C4 -> 625/8, also after conditioning on connectedness. It follows that
d0->1; the same conclusion follows from the event count below. The
needed short-cycle moment and connectedness inputs are documented in
[the previous proof](AUTONOMOUS_GEOMETRY_SELECTION.md).

Thus the coupling ratio guaranteeing 99% expected good roots for a
prepared low-energy state allows **at most 2%+o(1)** expected good roots
when starting instead from Omega_N. A protecting energy penalty gives
the unprepared state a high energy; closed evolution has no mechanism
for discarding it. These are compatible statements about different
initial conditions.

A concrete matter reservoir would need an adequate energy range. For
example, append 0<=H_B<=bN I and an interaction W with ||W||<=gamma N.
If its initial reservoir energy is zero, achieving a state of mean defect
fraction delta from the uniform graph input requires

\[
 b+600\rho+2\gamma\ge J(d_0-\delta).
 \tag{8}
\]

This follows by comparing the initial lower energy JNd0-gamma N with
the final upper energy JNdelta+600rho N+bN+gamma N. It is necessary,
not sufficient. Reservoir dynamics, locality, preparation time, and
retention still need construction. A finite closed reservoir also does
not remove the recurrence obstruction to permanent attraction.

## 4. Count local order without a macroscopic shape assumption

Fix alpha in (0,1], and let E_alpha contain graphs with g(G)>=alpha N.
We prove an entropy deficit for this event itself.

In any degree-six graph a vertex lies in at most
binom(6,2)*5=75 squares. A square therefore intersects at most 300
squares when intersections mean sharing a vertex. A greedy maximal
collection of vertex-disjoint squares covers all squares by these
intersection neighborhoods. If k_max is its size, then

\[
 C_4(G)\le300k_{\max},\qquad
 g(G)\le100k_{\max}.
 \tag{9}
\]

Consequently every G in E_alpha contains a collection of
k=ceil(alpha N/100) vertex-disjoint squares.

There are exactly

\[
 \frac{(N)_{4k}}{8^k k!}
 \tag{10}
\]

such collections in the complete labelled graph. For a specified
collection, each of its 4k vertices has two required incident edges.
For N>=144 and k<=N/4, the regular-graph edge inclusion estimate gives

\[
 \Pr[\text{specified collection}\subset G]
 \le\frac{30^{4k}}{2^{4k}(3N-72)_{4k}}
 \le(10/N)^{4k}.
 \tag{11}
\]

Here (x)_m is a falling factorial. The first inequality is an application
of Theorem 3(a) of
[McKay, Wormald and Wysocka](https://users.monash.edu/~nwormald/papers/girth.pdf).
Its condition 4k+72<=3N is satisfied. For the second inequality, each
denominator factor 2(3N-72-j) is at least 3N for 0<=j<4k<=N.
No Poisson approximation for an extensive cycle count is being used.

The first moment of the number of collections, (10)-(11), bounds the
event probability for the uniform simple regular graph:

\[
 \Pr(E_\alpha)\le\frac{1250^k}{k!}.
 \tag{12}
\]

Conditioning on connectedness multiplies this by at most two for all
sufficiently large N, since connectedness has probability tending to
one. Using log(k!)>=k log k-k, we obtain the rank-fraction bound

\[
 \log\frac{\operatorname{rank}P_{E_\alpha}}{\dim\mathcal H_N}
 \le-\frac{\alpha}{100}N\log N+O_\alpha(N).
 \tag{13}
\]

The constant 1/100 is not claimed sharp. This counts **all** graphs
with a positive density of good cubic neighborhoods, irrespective of
their global topology, shortcuts, coarse partitions, or shape count.
The proof applies to the stated regular-graph Hilbert space; extending
the event bound to other carriers requires a new count.

### Every fixed positive temperature loses this local order

For beta>=0, (2) implies

\[
 \Pr_\beta(E_\alpha)\le
 \frac{\operatorname{rank}P_{E_\alpha}}{\dim\mathcal H_N}
 \exp\{\beta(600\rho+J)N\}.
 \tag{14}
\]

Indeed, exp(-beta H)<=I bounds the numerator by the event rank, while
exp(-beta H)>=exp(-beta(600rho+J)N)I bounds the partition function
below. This argument requires no commutation of H and the event.
For every fixed finite beta,J,rho, (13)-(14) imply
Pr_beta(E_alpha)->0 for every fixed alpha>0. Since 0<=g/N<=1,

\[
 \langle g/N\rangle_\beta\le\alpha+\Pr_\beta(E_\alpha),
 \qquad\lim_{N\to\infty}\langle g/N\rangle_\beta=0.
 \tag{15}
\]

For J>300rho, this differs from the positive ground-state lower bound
(4). Taking zero temperature before large N and taking large N at a
fixed nonzero temperature do not give the same order bound. In
particular, (4) does not establish a finite-temperature ordered phase.
Constant positive event probability would require at least

\[
 \beta_N(600\rho_N+J_N)\ge(\alpha/100)\log N-O_\alpha(1).
 \tag{16}
\]

This is a necessary scaling requirement, not a sufficient cooling
schedule or an estimate of a critical temperature.

## 5. Do virtual exchanges select noncollapsed geometry?

We also evaluated the first nontrivial perturbative test. At fixed N,
write H=J(D3+z L_S), z=rho/J, and let P project onto D3=0. The standard
second-order effective term is

\[
 -Jz^2 P L_S Q(D_3|_Q)^{-1}Q L_S P,\qquad Q=I-P.
 \tag{17}
\]

This is finite degenerate perturbation theory. Its general framework is
described by [Bravyi, DiVincenzo and Loss](https://arxiv.org/abs/1105.0675).
Their results for a supplied spin lattice do not automatically establish
uniform convergence for this graph carrier.

For a torus G, the diagonal coefficient of (17) is

\[
 -\frac{\rho^2}{J}\sum_{G'\sim G}
       \frac{A_{GG'}^2}{D_3(G')}.
 \tag{18}
\]

The transition weight must be squared **after** all elementary moves
leading to the same graph have been combined. The audit independently
counts their multiplicities. It evaluates the actual rooted patch
isomorphism test after each representative exchange, and uses only
translations, reflections, permitted axis permutations, and path
reversal to reduce equivalent cases. Each root has all 150 oriented
paths represented; the counting reproduces the weighted row sum 300N.

For equal-period tori the five path types have the following values:

| Path directions | Oriented paths/root | Transition weight | Defects at side 8 | Defects at tested sides 10,16,20 |
|---|---:|---:|---:|---:|
| AAA | 6 | 4 | 62 | 62 |
| AAB or ABB | 48 | 4 | 66 | 64 |
| ABA | 24 | 4 | 74 | 74 |
| AB(-A), closing a square | 24 | 8 | 52 | 52 |
| ABC | 48 | 4 | 68 | 68 |

Here A,B,C are mutually perpendicular unit directions. Define the
positive diagonal magnitude per site
s(G)=N^(-1) sum A_GG'^2/D3(G'). For the tested larger equal-period tori,

\[
 s=\frac{48}{62}+\frac{384}{64}+\frac{192}{74}
       +\frac{384}{52}+\frac{384}{68}
 =\frac{5678226}{253487}\simeq22.40046235.
 \tag{19}
\]

The equal-size comparisons are especially useful:

| Same vertex count | Tori compared | Difference in s, thick minus thin |
|---:|---|---:|
| 4096 | C16^3 and C8 x C8 x C64 | 4/33 |
| 8000 | C20^3 and C10 x C10 x C80 | 0 |

Thus this diagonal second-order test distinguishes circumference eight,
but already fails to distinguish the tested circumference-ten thin
torus from its thicker competitor. It does not prove noncollapse.
Off-diagonal mixing in (17), higher orders, and a remainder controlled
uniformly in N have not been computed. In a degenerate problem diagonal
entries alone are not ground energies, so the first row is not advertised
as a phase-selection theorem.

## 6. What changed in the model assessment

The radius-three interaction is now an explicit example with a rigorous
expected local-order guarantee at zero temperature, and a uniform-in-time
protection guarantee for specified low-energy inputs. It retains genuine
quantum exchanges and allows defects; freezing every graph is not needed
for these bounds.

It also shows why three questions must remain separate: local order,
preparation, and large-scale geometry. The present carrier destroys the
tested order at fixed positive temperature; the uniform pure input needs
an energy-transfer mechanism; and the local template plus the computed
virtual corrections does not select a noncollapsed spatial limit.

A next construction must provide compatible graph/matter energy transfer
and an explicit thermodynamic or nonequilibrium scaling, or change the
carrier so that the local-order event does not incur the N log N entropy
cost. Physical locality, dimension selection, curvature, Einstein
dynamics and chiral matter are still open. This patch extension remains
a scoped research model, not a completed replacement TOE.

## 7. Verification

- [The audit](scripts/patch_geometry_audit.py) evaluates the six torus
  excursion families; exhaustively checks square packing and motif first
  moments on all 19,355 eight-site degree-four graphs; checks the finite
  application of the edge-probability bound with exact fractions; and
  checks conserved-energy inequalities in the full 70-state six-site
  model with an explicitly different toy template. Its 808 sampled
  evolutions support, but do not prove, the all-time inequalities.
- [The Lean module](UnifiedTheory/Audit/KFCausalPatchGeometry.lean) proves
  eight supporting inequalities for defect energy, the uniform quench,
  reservoir capacity, finite covers, square packing, threshold means,
  the moment denominator and vanishing defect density. Spectral, graph,
  recognition and external enumeration suppliers remain explicit in the
  analytic proofs above; the complete phase statements are not claimed
  as fully formalized Lean results.
- [The report](data/patch_geometry_audit.json) records exact coefficients,
  numerical finite checks and source hashes. Prior hash-pinned artifacts
  remain unchanged.

Run `OPENBLAS_NUM_THREADS=1 python3 -W error::RuntimeWarning
scripts/patch_geometry_audit.py`, then `lake build`, from the repository
root.
