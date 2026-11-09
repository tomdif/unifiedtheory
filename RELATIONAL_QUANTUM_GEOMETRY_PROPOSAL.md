# Relational Quantum Geometry: a replacement TOE candidate

Date: 2026-09-10

**Proposal, not an established theory of everything.** Replace the classical
birth-order ontology by a quantum system whose interaction connections are
themselves dynamical. Matter changes the connections through which it can
propagate. Spacetime is a proposed collective phase of that joint system.

The guiding hypothesis is:

> Spacetime is the large-scale organization of reversible, gauge-invariant
> quantum interactions. Changing a connection must preserve the physical
> information that subsequent experiments can recover.

This is the strongest replacement I would pursue from the repository's
results. It supplies a concrete finite Hamiltonian family and an exact
matter/connection interference experiment. Its proposed geometric phase,
Einstein limit, and chiral particle spectrum remain to be established.
The finite Hamiltonian does not yet specify a unique physical TOE: its
group, couplings, state, and continuum trajectory require selection.

## 1. The change in the foundational picture

The [support obstruction](EMERGENCE_SUPPORT_AND_GAUGE_COMPACTNESS.md)
rules out faithful causal/volume reconstruction from the collapsing
harmonic law, even after an absolutely continuous change of the full
history measure. Therefore the new candidate changes the microscopic
carrier and dynamics; it is not another normalized tilt of that law.

At regulator size N, sites label quantum subsystems, not completed spacetime
events. Connections can be present, absent, or in coherent superposition.
N is a resolution/size parameter, not the universe's physical time.
At this stage the regulator does use an evolution parameter tau. Turning
that parameter into relational clock time, with no observable preferred
foliation in the continuum, is an additional open requirement.

Causal order is to be inferred from the ability of physical interventions
to influence other physical records. It is not identified with the order
in which an algorithm allocates sites. Thus the original collapse theorem's
hypotheses no longer apply directly. This does **not** prove that the new
model has a noncollapsing geometric phase; that is a mandatory test below.
If both models are eventually compared as laws on the same faithfully
reconstructed causal histories, the earlier singularity requirement still
applies.

The principal ingredients have substantial precedent. Quantum causal
histories attach quantum dynamics to causal structure; quantum graphity
and evolving-graph matter models make interaction structure dynamical.
The proposal is a repository-specific synthesis, not a claim that these
ideas or emergent geometry were first invented here.
[Markopoulou](https://arxiv.org/abs/hep-th/9904009),
[Konopka–Markopoulou–Severini](https://arxiv.org/abs/0801.0861),
[Hamma et al.](https://journals.aps.org/prd/abstract/10.1103/PhysRevD.81.104032).

## 2. A microscopic carrier with reversible connection changes

For a supplied compact internal group G and matter representation R, use

\[
 \mathcal H_N=
 \bigotimes_{v=1}^N\mathcal F(R)_v\ \otimes
 \bigotimes_{i<j}\left(\mathbb C|\varnothing\rangle
                   \oplus L^2(G)_{ij}\right).
 \tag{1}
\]

Here F(R) is a finite on-site fermion Fock space for the physical research
candidate. The exact prototype below instead uses charged hard-core matter
qubits. Its particles are not a construction of chiral fermions.

An absent edge is a singlet. A present edge transforms by the left/right
regular actions at its two endpoints. Physical states satisfy every local
Gauss constraint. Vertex relabeling acts on matter and links together.
The Hamiltonian below commutes with that action; a complete permutation
quotient including relational apparatus is a further construction.

With normalized Haar measure, the constant function Omega(g)=1 is a unit
vector invariant under both endpoint actions. Define

\[
 C_{ij}=|\Omega\rangle\langle\varnothing|,
 \quad N_{ij}=P_{L^2(G)},
 \quad C_{ij}^\dagger C_{ij}=P_\varnothing,
 \quad C_{ij}C_{ij}^\dagger=P_\Omega.
 \tag{2}
\]

Thus C commutes with every Gauss transformation, and C+C-dagger generates
unitary rotations between an absent connection and its trivial electric
representation. Crucially,

\[
 \langle\Omega|\xi\rangle=0\quad\Longrightarrow\quad C^\dagger|\xi\rangle=0.
 \tag{3}
\]

A bare deletion cannot erase a nontrivial flux state. Flux may instead be
transported, rerouted, or removed by an interaction that also changes the
other relevant registers. This is a constraint on a particular reversible
move, not a prohibition on every topology change with flux present.
The whole quantum state is retained; no hidden measurement or reset is
part of connection deletion.

For a finite compact-group regulator, retain a finite collection of full
Peter–Weyl representation blocks including the trivial one. This preserves
the endpoint group actions and (2). Projected link multiplication remains
gauge covariant, but is generally not unitary. Its regulator limit must be
analyzed before using the repository's unitary-link overlap results.

## 3. A concrete Hamiltonian family

Let d_i=sum_j N_ij. At a fixed degree cap Delta, let Pi_Delta project onto
graphs with d_i<=Delta. Define link multiplication U_ij to vanish on an
absent edge, electric Casimir E_ij to vanish there, and W_ijk to be the
real normalized Wilson trace around a present triangle, zero otherwise.
For real couplings, take

\[
\begin{aligned}
H_N=\Pi_\Delta\Big[&
 \mu\sum_{i<j}N_{ij}
 +\frac u2\sum_i d_i(d_i-1)
 +\epsilon\sum_{i<j}E_{ij}
 -\lambda\sum_{i<j<k}W_{ijk}\\
 &-g\sum_{i<j}\sum_{k\ne i,j}
       N_{ik}N_{kj}(C_{ij}+C_{ij}^\dagger)\\
 &-t\sum_{i<j}(\psi_i^\dagger U_{ij}\psi_j+\mathrm{h.c.})
 +m_0\sum_i\psi_i^\dagger\psi_i
\Big]\Pi_\Delta.
\end{aligned}
\tag{4}
\]

The physical Hilbert space is the range of Pi_Delta intersected with the
Gauss-invariant space. States outside that range are not additional
zero-energy physical states of the compressed Hamiltonian.

The connection term adds or removes an edge only when an alternative
two-edge path already exists. It preserves graph connected components;
within the bounded-degree sector its degree check depends on the affected
endpoints. Other terms describe edge cost, degree cost, electric energy,
loop energy, gauge-dressed matter transport, and an on-site number energy.
The parameter m_0 is not already an identified relativistic particle mass.

At finite N and finite representation cutoff, (4) is a finite Hermitian
matrix, commutes with all Gauss transformations and vertex relabelings,
and defines U(tau)=exp(-i tau H_N). These statements follow from the
operator transformations and adjoints; they are not proofs of a continuum
limit. The coefficients are new microscopic inputs. Delta is a regulator/
model choice, not a deduction of spatial dimension from a chosen valence.

For the first internal-unification investigation I would use the repo's
Spin(10), 16-dimensional internal carrier as a **trial input**. Its family
multiplicity and symmetry-breaking dynamics are unresolved. This proposal
does not inherit three families, Higgs/Yukawa couplings, or old numerical
mass identifications as predictions. The model is a family until those
choices and the physical state are fixed.

There is a major locality issue to test: a move local in the current graph
can create shortcuts relative to an earlier graph. Bounded degree and
Hermiticity do not automatically yield a common continuum light cone.
One cannot transfer a fixed-geometry locality theorem to arbitrary quantum
superpositions of these graphs without a new uniform argument.

## 4. An exact first result: matter changes a connection's interference

The new executable prototype uses G=Z2, three matter qubits, and three
link qutrits with basis

\[
 |\varnothing\rangle,\quad |+\rangle,\quad |-\rangle.
\]

On each link define

\[
 N=\operatorname{diag}(0,1,1),\quad
 E=\operatorname{diag}(1,1,-1),\quad
 T=|+\rangle\langle-|+|-\rangle\langle+|,
 \quad C=|+\rangle\langle\varnothing|.
\]

The local Gauss generator is (-1)^{n_i} times the product of incident E's.
Gauge-invariant hopping is
B_ij=(sigma_i^+ sigma_j^-+sigma_i^- sigma_j^+)T_ij.
The connection move is
R_ij=N_ik N_kj(C_ij+C_ij-dagger), with k the third site.
Both are Hermitian, commute with every Gauss generator, and satisfy
R^3=R, B^3=B. Therefore their gates are exactly

\[
 e^{-i\theta R}=I+(\cos\theta-1)R^2-i\sin\theta R,
 \tag{5}
\]

and likewise for B. These are actual unitary gates, not stochastic
normalizations of a list of graph outcomes.

Start with the path 0--1--2, charges at 0 and 1, negative electric flux on
01, positive electric flux on 12, and edge 02 absent. This satisfies all
Gauss constraints. Apply

\[
 U=e^{-i(\pi/4)R_{02}},\qquad
 V=e^{-i(\pi/2)B_{02}},\qquad U^\dagger.
\]

Let |o> be the initial state, |p> the same charges with edge 02 in |+>,
and |f> the state with charges at 1 and 2 and edge 02 in |->.
The final state is exactly

\[
 U^\dagger VU|o\rangle
       =\tfrac12|o\rangle+\tfrac i2|p\rangle
                              -\tfrac1{\sqrt2}|f\rangle.
 \tag{6}
\]

Consequently:

| Protocol/readout | Exact probability |
|---|---:|
| Edge 02 present after U | 1/2 |
| Edge 02 present after U, V, U-dagger | 3/4 |
| Edge 02 present after U, U-dagger without transport | 0 |
| Charge reaches site 2 after the coupled protocol | 1/2 |
| Edge 02 present with a pi-angle coherent matter return | 1 |
| Charge remaining at site 2 after that coherent return | 0 |

Matter can hop only when the connection is present. Its transported charge
changes the link flux, and the bare reverse connection move cannot erase
that flux branch. Thus matter affects connection evolution and connections
affect matter propagation in one joint quantum model.

There is also a purely coherent effect. Replace the matter angle pi/2 by
pi. Matter returns to its original charge configuration and the final state
is i|p>: the connection is present with probability one although no charge
remains at site 2. In general, with matter angle phi, the three final
amplitudes are (1+cos phi)/2, i(1-cos phi)/2, and -sin phi/sqrt(2).
Matter's phase can therefore change connectivity without a permanent
transferred charge. This effect would be lost by treating every intermediate
graph as a classical sampled outcome.

If instead an intermediate measurement dephases edge presence in the
no-transport control, the final presence probability is 1/2 rather than 0.
Discarding a measurement outcome does not undo the measurement. This
demonstrates why a classical graph history with repeated Born sampling is
a different dynamics from the proposed coherent network.

The calculation has 216 total basis states, 27 Gauss-invariant states,
and a 20-dimensional connected physical sector. Exact arithmetic verifies
12 Hermitian gauge-invariant generators, preservation of that sector,
number conservation, all six vertex relabelings of a specified symmetric
Hamiltonian, the gate identities, and the probabilities above. Selected
gates refer to labeled apparatus in this benchmark; a relational experiment
must transform its preparation, apparatus, and readout together.

This is finite quantum backreaction on connectivity. Calling it Einstein
gravity, a manifold, or a new empirical prediction would overstate it.
Code: [relational_quantum_geometry_audit.py](scripts/relational_quantum_geometry_audit.py).
Results: [the exact audit](data/relational_quantum_geometry_audit.json).
No additional Lean theorem is claimed for this prototype.

## 5. Refinement must preserve experiments and their memory

The [autonomy theorem](QUANTUM_REFINEMENT_PROOF.md) rules out demanding exact
closed unitary dynamics on every retained matrix for every joint input
while still coupling to discarded variables. The
[memory construction](QUANTUM_MEMORY_CLOSURE.md) supplies the appropriate
alternative in its finite example: retain the algebra needed by future
experiments, including its correlations.

For this candidate, define an experiment by its physical preparation,
instrument maps, clock readings, and final effect. At resolution N its
probability is the trace of their composition with joint unitary evolution.
A refinement map must transport the **whole experiment**, with

\[
 |p_{N'}(\iota_{N'N}\mathcal E)-p_N(\mathcal E)|
       \le\varepsilon_{N,N'}(\mathcal E)\longrightarrow0
 \tag{7}
\]

for fixed bounded physical experiments. Reduced dynamics may have memory;
the environment is not reset. Summing instrument outcomes means the
nonselective instrument, not absence of the intervention.

Neither the maps in (7), their composition, nor their error bounds for (4)
have been constructed. Independently selecting a ground state at each N
does not establish them. Exact invariance of a selected finite family of
experiments also would not determine every microscopic coupling.

## 6. How Einstein gravity could follow, and where the real conjecture is

The central physical conjecture is that a stable phase/continuum trajectory
of (4), or a clearly specified extension, has all of the following jointly:

1. Three extended spatial dimensions and a Lorentzian propagation limit,
   identified by several independent observables over a growing range of scales.
2. A common limiting light cone for the matter species and physical
   geometric fluctuations, with no observable preferred regulator frame.
3. Coordinate redundancy and its Ward/constraint identities, plus a
   positive-norm massless helicity-two excitation with universal coupling.
4. Refinement limits of the joint experiments, controlled modulo coordinate
   transformations and with nonlinear fluctuation terms retained.

This is a critical-phase hypothesis to investigate, not a consequence of
the Born rule, graph valence, or normalization. Quantum refinement alone
already admitted arbitrary dynamics in the repo's earlier audit.

If these properties hold and a local derivative expansion exists, the
leading gravitational effective action in four dimensions can have the form

\[
 \Gamma_{\mathrm{IR}}=
 \int d^4x\sqrt{-g}\left[
 \frac{R-2\Lambda}{16\pi G_N}
 +\mathcal L_{\mathrm{matter,gauge}}
 +\alpha R^2+\beta R_{\mu\nu}R^{\mu\nu}+\cdots\right].
 \tag{8}
\]

The Einstein regime also needs positive finite G_N and suppression/control
of the higher-derivative terms at the tested scales. With those suppliers,
the repo's [variational bridge](CONTINUUM_EINSTEIN_BRIDGE.md) becomes a
matching and verification target for the gravitational action. Inserting
that action as a new microscopic term would define a different route and
would not prove that (4) generates it.

The soft-graviton argument constrains couplings universally **after** a
Lorentz-invariant scattering limit with the requisite massless spin-two
pole exists; it does not create that pole or derive the full ultraviolet
theory. [Weinberg's original argument](https://journals.aps.org/pr/abstract/10.1103/PhysRev.135.B1049).

The Weinberg–Witten restriction must also be confronted: an ordinary
Lorentz-covariant local quantum field theory with the applicable covariant
conserved stress tensor cannot simply contain an energy-carrying emergent
massless spin-two particle. The proposed microscopic network has no given
Lorentz spacetime, but that observation alone is not a completed evasion.
Its infrared gravitational redundancy and stress observables must be derived.
[Weinberg–Witten](https://www.sciencedirect.com/science/article/pii/0370269380902129).

Vertex relabeling is not the gravitational constraint algebra. Regulator
refinement and restoration of diffeomorphism symmetry are separate issues,
as emphasized by [Bahr–Dittrich](https://arxiv.org/abs/0909.5688).
Likewise, entanglement equilibrium could be a useful derived diagnostic;
using it to assume Einstein dynamics would not supply the missing phase.
[Jacobson's result](https://arxiv.org/abs/1505.04753) has explicit local-vacuum,
fixed-volume and field-theory assumptions.

## 7. How the surviving repository results enter

| Existing result | Role in this candidate | Missing supplier |
|---|---|---|
| Collapse and support obstruction | Reject a density repair of the old faithful-order law | A nondegenerate geometric phase of the new carrier |
| Quantum refinement and memory | Define which experiments must survive reduction | Actual refinement maps and bounds for (4) |
| Finite dynamical gauge model | Template for exact constraints and joint unitary feedback | Continuous-group interacting continuum |
| Overlap chirality and weak Abelian locality | Fermion regulator tests on suitable supplied geometries | Extension to dynamical geometry, non-Abelian fields, and a common quantum limit |
| Classical Einstein variational bridge | Independent infrared matching target | Derivation of its action and controlled physical metric limits |
| Proper-time compactness | Require compactness modulo coordinates | Control of curvature and physical gravitational waves |

The Euclidean chiral benchmark cannot simply be pasted onto the real-time
network. Mirror removal, anomaly cancellation, physical positivity, and
Lorentzian reconstruction must be compatible with the same dynamics.
The cosmological constant and observed particle parameters are not fixed
by (8); this proposal currently has no new numerical prediction for them.

## 8. The decisive next experiment

The first priority is the geometry phase, ahead of fitting mass ratios.
Study the specified Hamiltonian on increasing connected sectors, with
couplings and readouts fixed before examining the results. Compare at least
chains/trees, locally extended graphs, clustered graphs, and expanders.
Degree costs and loop energies can favor the wrong phases; an attractive
small graph or a fitted ordering statistic is insufficient.

For a semiclassical spatial sector, measure ball-volume growth, heat-kernel
return probabilities, low-energy dispersion, and propagation responses.
A candidate three-dimensional spatial regime should give mutually
compatible scaling across these diagnostics, not merely degree six or one
spectral estimate. For example, a heat-kernel window with P(s) proportional
to s^(-3/2) would test spatial spectral dimension three; it does not by
itself prove a 3+1 Lorentzian spacetime.

Refine a fixed physical observation region with spatial and temporal
resolution together. A fixed finite spatial graph evolved for arbitrarily
long times is a different limit. In a faithful limiting causal record,
positive-volume separated spatial patches must retain a positive fraction
of incomparable event pairs, as required by the earlier cross-pair theorem.
For continuous Hamiltonian propagation, exponentially small responses
outside an effective cone are not exact microscopic incomparability;
the causal readout and its limiting error must be specified.

Reject or revise this Hamiltonian if no suitable growing geometric window
exists, if rapid rewiring destroys a common limiting cone, or if geometry
requires a persistent preferred frame. If it passes, test the constraint
identities and spin-two sector before claiming Einstein gravity, then test
the chiral matter continuum on that **same** family of states and dynamics.

The proposal's concrete advance is a reversible, gauge-constrained quantum
connection model with demonstrable matter feedback and interference.
Its central unresolved claim is that such dynamics has a phase describing
our spacetime and particles. That is a precise replacement research target;
it is not a completed TOE or a claim that known obstructions have all vanished.
