# Projected geometry: a freezing obstruction and a local dynamical repair

Date: 2026-09-10

The exact cubic-root projector has a previously untested rigidity:
**every elementary exchange touching a good root makes it bad**. A
complete radius-three calculation proves this for every graph completion.
The one-probe constraint therefore forbids changes to the occupied
root's incident edges. Strengthening it to require good roots everywhere
removes every elementary geometry transition on that sector.

The model revision below allows local geometric defects while bounding
distortion relative to a supplied reference lattice. It has extensively
many quantum geometry variables, uniformly noncollapsed graph metrics,
and a common propagation bound for geometry and neutral hard-core matter
observables. These are regulator-level statements. **The reference
geometry is supplied, not emergent**, and the construction does not
derive Einstein gravity, physical charged matter, or a complete TOE.

The old [energetic approximation](ENERGETIC_PROBE_SECTOR.md) remains valid
in its stated model. The new carrier is an explicit change of the model,
not evidence that the unrestricted Hamiltonian selects this carrier.

## 1. The occupied-root obstruction

Let q_v(G) be the existing rooted induced radius-three cubic indicator.
Let p=(a,b,c,d) be an active exchange path, replacing ab,cd by ac,bd
while keeping bc. If v belongs to p and q_v(G)=1, then

```
q_v(S_p G)=0.                                             (1)
```

**Proof by complete finite local enumeration.** A cubic root belongs to
twelve four-cycles. For any graph, that count can be evaluated as

```
C4_v = sum_{unordered {x,y} subset N(v)} (|N(x) intersect N(y)|-1).
```

All four vertices of p lie in the original B_3(v). After the exchange,
every neighbor of v has original distance at most two from v. Every
vertex used to complete a four-cycle through v consequently lies in
the original B_3(v). Thus the post-exchange C4_v is completely determined
by the 63-vertex cubic ball, regardless of how its boundary is completed.

There are exactly 600 forward ordered paths containing the root: four
possible root positions and 150 paths for each position. The executable
enumerates all of them directly in the induced 63-vertex ball. The
complete histogram is

| Post-exchange four-cycles at the root | Ordered paths |
|---:|---:|
| 7 | 192 |
| 8 | 312 |
| 9 | 96 |

None has twelve squares, proving (1). Reverse-active descriptions are
forward paths in their reverse order, so the same conclusion covers all
active S_p. A separate 1,000-site torus calculation verifies the histogram
and rejects all 600 resulting roots by full rooted isomorphism.

The completeness and boundary argument are analytic; the exact 600-case
graph calculation is executable, not a Lean formalization of the graph
theorem. The Lean module checks the resulting square-count contradiction
and the relevant compression algebra.

## 2. What the exact projectors do and do not freeze

For the previous **one-probe** projector
`P|G,v>=q_v(G)|G,v>`, equation (1) implies that a retained geometry move
cannot contain the occupied vertex. Its current incident edges cannot
change in that move. The probe can still hop, and remote geometry can
still change. This does not prove that the entire one-probe dynamics
is frozen, or that it violates every possible causal estimate.

Now consider the stronger **all-good** graph projector

```
P_all |G> = (product_v q_v(G)) |G>.
```

For every elementary S_p, `P_all S_p P_all=0`. The balancing diagonal
survives compression. Every good graph is triangle-free and degree six;
there are 150 forward length-three paths per vertex and twice that many
active ordered descriptions in the S_p sum. Consequently, at fixed N,

```
P_all (rho L_S + J D3) P_all = 300 rho N P_all.            (2)
```

Adding the graph-diagonal probe hopping does not restore graph
transitions. The probabilities of graph configurations are constant in
this all-good model, although an initial superposition can still acquire
probe-dependent phases and correlations. Replacing the retained diagonal
by a rebalanced move Laplacian would be another Hamiltonian change.

There is also a known global rigidity: connected graphs satisfying the
cubic radius-three condition everywhere are normally covered by the
cubic lattice. This is Theorem 1 of
[Benjamini and Ellis](https://arxiv.org/html/1409.7587v9), through the
implication from their 3-local to weakly 3-local hypothesis. Their result
gives a quotient-lattice structure; it is not a derivation of physical
spacetime curvature. Exact local flatness is therefore a restrictive
choice for a universal geometric constraint.

## 3. Revised carrier: separated local switches

Start with an even cubic torus of side L=k ell, with even ell>=12 and
k>=2. This reference has N=L^3 vertices and distance d_0. In each
ell-by-ell-by-ell cell choose the straight path with local coordinates

```
a=(4,4,4), b=(5,4,4), c=(6,4,4), d=(7,4,4).
```

There are M=k^3=N/ell^3 disjoint paths. A bit z_s chooses either the
original edges ab,cd (z_s=0), or ac,bd (z_s=1), retaining bc. Call the
resulting graph G_z and its carrier projector P_C. There are exactly
2^M distinct labelled graphs: each selected edge ab reads its bit.
All other reference edges stay fixed.

The selected path supports are disjoint, their endpoint radius-three
neighborhoods are disjoint, and the unchanged gaps between supports are
at least nine edges. A radius-three neighborhood cannot meet the changed
edges of two switches. This supplies both independent patch accounting
and a local tensor description.

Every G_z is connected and degree six. Each new edge is an original
two-step path. Conversely, the removed edge ab is replaced by a-c-b,
and the removed edge cd by c-b-d. Other switches cannot spoil these
detours. Therefore, for every pair of vertices and every configuration,

```
(1/2) d_0(u,v) <= d_Gz(u,v) <= 2 d_0(u,v).               (3)
```

This has consequences absent from the earlier local-defect test:

```
B_0(v,floor(r/2)) subset B_Gz(v,r) subset B_0(v,2r),
diam(G_z)/N^(1/3) >= 3/4.                                (4)
```

For example, choose a torus antipode at original distance 3L/2 and use
(3). At scales 1<=r<=L/4 the ball inclusions give uniform upper and
lower cubic volume bounds. The inequalities hold in every basis geometry
and hence give probability-one geometric support for every quantum
state on the carrier. They do not assert a unique metric for a quantum
superposition or identify this regulator metric with a spacetime metric.

## 4. Exact compression and real geometry fluctuations

Let X_s toggle bit s and n_s=(I-Z_s)/2. A straight switch creates no
triangle and removes eight squares. Separated switches cannot form
additional triangles or squares jointly. Thus

```
C4(G_z)=3N-8 sum_s z_s.
```

The existing finite patch calculation gives 62 defective roots for one
straight switch. It is determined by its finite neighborhood; separated
supports ensure that defects add:

```
D3(G_z)=62 sum_s z_s.                                    (5)
```

The new audit independently checks this count, the changed square count,
and the disjoint affected sets in all tested configurations. The older
straight-switch counts appear in
[the patch audit](data/patch_geometry_audit.json).

In the old ordered exchange convention each selected toggle has weight
four. Every G_z remains triangle-free, so the diagonal of the full
all-move Laplacian is still 300N. Distinct switch configurations differing
in more than one bit cannot be connected by a single exchange: their
edge-change supports are disjoint and exceed four changed edges. Hence

```
P_C (rho L_S + J D3) P_C
 = 300 rho N I - 4 rho sum_s X_s + 62 J sum_s n_s
 = E_offset I + sum_s [4 rho(I-X_s)+62 J n_s],
E_offset=300 rho N-4 rho M.                              (6)
```

Removing the displayed global constant is harmless. Equation (6) is
an exact compression in the regular, trivial-flux graph sector, including
its diagonal costs. It is not a compression of all charged/flux sectors
of the full v2 proposal.

With matter absent, the independent-switch Hamiltonian has gap

```
Omega=sqrt((62J)^2+64rho^2)
```

and ground active-bit probability

```
p=(1-62J/Omega)/2.                                      (7)
```

For rho>0 and finite J>=0 this probability is positive, and the ground
state is a coherent product of switch states. There are extensively
many fluctuating geometry variables at fixed ell. The changing square
count shows that these transitions are not merely vertex relabelings.
Meanwhile all their graph metrics satisfy (3). The graph-only ground
sector is gapped; this construction does not supply gravitons or an
Einstein action. Its restricted state counting also does not resolve
the entropy obstruction on the unrestricted graph carrier.

## 5. One-probe propagation with arbitrary geometry dynamics

A useful general statement does not require independent switches.
Suppose every graph in a finite carrier has degree at most six and every
edge has d_0-length at most R. Let

```
H=B+T,
T=-kappa sum_G |G><G| tensor A_G,
[B,Pi_v]=0 for every probe-position projector Pi_v.
```

B may contain arbitrary quantum geometry dynamics, even depending on
the probe position. For all u,v,t and mu>0,

```
||Pi_u exp(-itH) Pi_v||
 <= exp(6 kappa |t| exp(mu R)-mu d_0(u,v)).               (8)
```

The norm includes the entire geometry register, so the estimate holds
for arbitrary initial geometry superpositions and with spectator
entanglement. Its constant is independent of graph count and N.

**Proof.** Use the position weight
`W=sum_x exp(mu d_0(x,v)) Pi_x`. B commutes with W. Every nonzero entry
of WTW^-1 gains at most exp(mu R); its absolute row and column sums are
at most 6kappa exp(mu R). In the interaction picture of B, the weighted
hopping norm has the same bound, since B's unitaries commute with W.
The Dyson series is bounded by `exp(6kappa |t| exp(mu R))`. Taking the
u,v position block removes the weight and proves (8).

Our revised carrier has R=2. In contrast with an additive energetic
approximation error, (8) is a uniform spatial estimate for this carrier.
The earlier shortcut family is excluded by the new carrier assumption.
There is no contradiction with its finite-penalty obstruction.

This theorem alone controls particle transport, not arbitrary signaling
by the geometry: an arbitrary nonlocal B could still transmit geometry
information. The explicit local B in (6) permits a stronger statement.

## 6. A common bound for geometry and neutral matter observables

Give every reference vertex a neutral hard-core matter qubit, with
number m_v and raising/lowering operators b_v^dagger,b_v. Write
`h_uv=b_u^dagger b_v+b_v^dagger b_u`; this has norm one. Together with
the M switch qubits, the full tensor-product Hamiltonian is

```
H_local = -4rho sum_s X_s + 62J sum_s n_s
          - kappa sum_{uv in E_0} h_uv
          + kappa sum_s n_s(h_ab+h_cd-h_ac-h_bd).         (9)
```

The geometry-only constants in (6) have been omitted explicitly.
Equation (9) conserves total neutral matter number. In each geometry
basis state it gives hopping on precisely G_z. Its one-particle sector
is the probe Hamiltonian of section 5. At arbitrary occupation, geometry
and matter still interact, and geometry can change while a particle
occupies a defective root. The old cubic-root projection would forbid
that transition.

This neutral matter model is a diagnostic extension. It has no supplied
identification with electrons, fermions, or the earlier charged Gauss-law
sector. Transferring the construction to that physical sector requires
an explicit compatible local encoding and Hamiltonian.

For a common operator bound, use the reference graph with an extra
pendant site for switch s attached to its vertex a. This defines an
augmented metric d_*. Each interaction in (9) acts on at most three
tensor sites and has d_*-diameter at most four. A matter site is in at
most six ordinary hopping terms and two controlled corrections. A
switch site is in four controlled terms plus its own geometry term.
Consequently

```
sup_x sum_{Z containing x} ||Phi(Z)|| <= J_*,
J_*=8kappa+4rho+62J.                                    (10)
```

The same bound applies at every size and every matter occupation.
For observables A,B supported on nonempty site sets X,Y, respectively,

```
||[exp(itH_local) A exp(-itH_local), B]||
 <= 2 |X| ||A|| ||B||
    exp(6 J_* exp(4mu)|t|-mu d_*(X,Y)),   mu>0.          (11)
```

One may also take the smaller trivial bound `2||A||||B||`. Equation
(11) is a Lieb-Robinson bound, with exponentially small tails rather
than an exactly vanishing relativistic commutator. It controls geometry,
matter, and mixed local observables under their joint evolution.

**Derivation and external input.** Use the interaction-chain recursion
in equations (2.9)-(2.12) of
[Nachtergaele, Ogata, and Sims, Propagation of Correlations in Quantum Lattice Systems](https://arxiv.org/abs/math-ph/0603064).
The first interaction in a chain has total norm at most |X|J_*; each
successor intersects at most three sites of the previous interaction
and has total norm at most 3J_*. A chain of n interactions reaching Y
has `d_*(X,Y)<=4n`. Weighting by exp(mu d_*) and summing the time-ordered
series yields, for disjoint supports, the sharper expression

```
(2|X|/3)||A||||B|| exp(-mu d_*(X,Y))
    (exp(6J_* exp(4mu)|t|)-1).
```

Dropping the factor 1/3 and subtraction gives (11). Overlapping supports
include the zeroth-order term and satisfy the stated looser bound too.
Thus the reference lattice gives one uniform cone for all these local
observables. This is an application of established locality theory,
not a new general Lieb-Robinson theorem or a derivation of Lorentz
invariance. Equal maximum propagation bounds do not establish equal
dispersion relations or a relativistic equivalence principle.

## 7. What changed in the proposed theory

The practical revision is to stop treating **exact cubic neighborhoods
as the fundamental physical constraint**. Retain their defect count as
a diagnostic or energy term. A geometric sector instead needs controlled
distances across scales while allowing quantum shape changes.

The supplied separated-switch carrier is a concrete benchmark for this
revision: it admits defects, extensive geometry fluctuations, and a
common matter/geometry propagation bound without freezing. The common
structure comes from bounded local interactions on its reference
regulator. It is not inferred from the propagation behavior of one probe
after the fact.

The cost is substantive. The spatial lattice, dimension three, selected
switch locations, carrier restriction, and external time remain inputs.
This branch supplies locality at the regulator level and allows the
metric to fluctuate within a uniform comparison class. To recover the
original stronger ambition of emergent spacetime, one must derive a
physical sector of this kind or show independence from the auxiliary
regulator in a continuum limit. Merely adjoining all label permutations
does not supply that derivation.

The next targets are therefore collective geometry modes beyond the
independent gapped switches, compatible charged/gauge matter, and a
continuum limit with the intended causal and gravitational dynamics.
The present result establishes neither a failure of every possible
one-probe projected model nor a complete physical TOE.

## 8. Verification

- [The executable audit](scripts/projected_geometry_audit.py) enumerates
  all 600 rooted flips in the exact cubic ball and independently checks
  all 600 resulting torus neighborhoods by isomorphism.
- Four configurations of a 13,824-site graph test connectivity, degree,
  triangles, squares, defect additivity, move multiplicities, metric
  detours, antipodal distances, and ball bounds.
- The complete eight-cell construction checks all 1,104 affected roots
  with every switch active: 496 defects and no triangles. It also checks
  the full local interaction support and norm accounting, including
  nearest-cell separations. Its 256 configurations are not all enumerated.
- A 55,296-dimensional joint graph/probe Hamiltonian tests actual shape
  changes, matter/geometry entanglement, energy and norm conservation,
  and the position bound. These sampled states do not replace the
  analytic arbitrary-state theorem.
- A complete five-qubit local matter/switch motif verifies the hopping
  operator in every occupation column, exact number conservation, and
  nonzero mixed geometry/matter commutators. The independent-switch
  spectrum and ground occupation are checked symbolically.
- [Ten supporting Lean results](UnifiedTheory/Audit/KFCausalProjectedGeometry.lean)
  verify the square-count contradiction, compression, detour and ball
  inequalities, noncollapse arithmetic, interaction constants, and
  exponential bounds. The graph enumeration and general propagation
  proof remain explicitly analytic/executable suppliers.
- [The report](data/projected_geometry_audit.json) records results and
  source hashes. Earlier hashed artifacts remain unchanged.

Run `OPENBLAS_NUM_THREADS=1 python3 -W error::RuntimeWarning scripts/projected_geometry_audit.py`
and `lake build`.
