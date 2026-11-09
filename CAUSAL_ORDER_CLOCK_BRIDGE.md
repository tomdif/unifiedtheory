# The partial order as clock: an exact finite quantum bridge

Date: 2026-09-10

**Yes: causal order is the proposed primitive temporal structure.** The
recent regulated Hamiltonian calculation introduced a separate evolution
parameter, without identifying it with the repository's causal clock.
That is a gap in that calculation, not an absence of temporal structure
in the original proposal. This note supplies a finite relational
formulation and identifies its remaining physical assumptions.

The result is an exact, finite quantum-history construction. Conditional
evolution can be indexed by causal pasts rather than an external real
time. Its consistency is equivalent to a local diamond equation. A
local-gate implementation of the regulated matter/geometry Hamiltonian
satisfies this equation and converges to that Hamiltonian at fixed finite
volume. Neither the history constraint nor this circuit construction
selects a physical spacetime order or derives Einstein gravity.

## 1. What the existing clock results already say

The repository has several distinct temporal constructions:

- [Birth-clock rates](UnifiedTheory/Audit/KFCausalBornRateAndDilation.lean)
  identify a dimensionless discrete tick and fix a continuous rate once
  the tick interpretation is specified. Exact-flow and implicit-Euler
  interpretations provably give different rates for the same update.
- [Volume gauge](UnifiedTheory/Audit/KFCausalCSpecVolumeGauge.lean)
  proves that interval counts give relative proper times under an
  assumed common dimension and volume law. Absolute units require a
  density calibration. Its exact scale gauge is
  `rho C tau^d = (a^d rho) C (tau/a)^d`.
- [Two-embedding proper time](UnifiedTheory/Audit/KFCausalCSpecTwoEmbeddingProperTime.lean)
  bounds the disagreement between two reconstructions using the same
  interval count, given curvature and count-error bounds.

These are real mathematical results with stated hypotheses. They do not
establish that every allowed order has a manifold interpretation or that
the new Hamiltonian's parameter already measures this proper time.
Assigning a duration to an individual birth is a convention; a single
causal link does not carry a universally fixed continuum proper duration.
Count-to-volume laws are statistical or mesoscopic inputs.

For a locally finite order and comparable events x<=y, the maximum number
of strict steps in a chain from x to y, h(x,y), is intrinsic and finite.
Concatenation proves h(x,z)>=h(x,y)+h(y,z). This can be strict: a different
branch from x to z can be longer than every path through y. Thus h is a
candidate maximal elapsed time, not the accumulated time along every
worldline. Conversion to continuum duration needs an approximation law
and scale. Metric reconstruction from random causal orders is already
part of the causal-set literature; see
[Brightwell and Gregory (1991)](https://journals.aps.org/prl/abstract/10.1103/PhysRevLett.66.260).

An event's position in an arbitrary enumeration is different. If x<y
and k unrelated spectator events are present, the enumeration gap from
x to y can be any integer from 1 to k+1 while the causal interval is
unchanged. The cardinality of a specified causal past is intrinsic; the
choice of past at a given global birth number need not be.

## 2. A clock reading can be a causal past

Let P be a finite event poset and J(P) its set of order ideals (downsets).
An ideal I describes which events have occurred. An allowed tick adds an
event x outside I whose strict predecessors are all in I:

```
I -> I+x,             I+x := I union {x}.
```

This clock is partially ordered by inclusion. Two independent ticks can
be performed in either order. No distinguished total enumeration is
needed. A fixed ideal contains its own causal history; it is generally
more information than one local observer can measure. Treating its basis
label as an accessible register is an explicit finite-model assumption.

Choose a finite matter Hilbert space H and a unitary U_x(I) for each
allowed tick. The desired relational equation is

```
psi(I+x) = U_x(I) psi(I).                              (1)
```

For simultaneously addable distinct x,y, consistency requires

```
U_y(I+x) U_x(I) = U_x(I+y) U_y(I).                    (2)
```

Equation (2) is the diamond equation. For context-independent gates it
reduces to commutation at incomparable events. For context-dependent
gates, commutation of the two gates at I alone is not sufficient.

**Finite consistency theorem.** Equation (1) has one solution for every
initial vector psi(empty), on every ideal, if and only if (2) holds on
every diamond. Solutions are unique after fixing the initial vector.

Proof: two enumerations of an ideal are linear extensions of its induced
order. They are connected by swaps of adjacent incomparable events. To
see this, move the first event of the target enumeration leftwards in
the other enumeration. Every event it crosses must be incomparable:
a predecessor could not follow it in the target enumeration, and a
successor could not precede it in the starting enumeration. Delete the
common first event and repeat. Each swap is one diamond, so (2) makes
the ordered product independent of the enumeration. Conversely, if
solutions exist for every initial vector, the two routes around each
diamond agree on every vector at I: transport from the empty ideal to
I is unitary and hence onto. The two operators in (2) are equal.

This is finite consistency, not a new general theorem of quantum gravity.
Related frameworks include
[quantum causal histories](https://arxiv.org/abs/hep-th/0302111).
The construction here has a fixed common H and unitary ticks; varying
local Hilbert spaces and general quantum channels need extra conditions.

## 3. A stationary constraint with internal conditional evolution

Let V(I) be the enumeration-independent product, V(empty)=1. On
K=l2(J(P)) tensor H, define for each ideal edge e=(I,J=I+x)

```
B_e = <J| tensor 1 - <I| tensor U_x(I),
C_P = sum_e B_e^dagger B_e >= 0.                       (3)
```

It follows directly that ker(C_P) is exactly the solution space of (1).
This is a constraint operator; its eigenvalues are not being identified
with physical energies or an emergent time generator.

Define the block-diagonal unitary W by W(|I> tensor v)=|I> tensor V(I)v.
Using V(J)=U_x(I)V(I), each constraint becomes

```
B_e W = V(J) (<J|-<I|) tensor 1.
```

Consequently

```
W^dagger C_P W = L_ideal tensor 1,                    (4)
```

where L_ideal is the ordinary unweighted graph Laplacian of ideal
inclusions by one event. The graph is connected: delete maximal events
until the empty ideal is reached. Thus ker(C_P) has dimension dim(H).
For any normalized psi0, its normalized history vector is

```
|Psi> = |J(P)|^(-1/2) sum_I |I> tensor V(I)|psi0>.      (5)
```

Conditioning on a clock reading I gives exactly V(I)psi0. Equation (5)
is static and (1) is its conditional dynamics; no independent real-time
parameter is needed to state either. This use of clock correlations is
related to [Page and Wootters (1983)](https://journals.aps.org/prd/abstract/10.1103/PhysRevD.27.2885).
Uniform weighting comes from the chosen unweighted constraint; it is
not a derived cosmological probability law over causal pasts or posets.
Physical clock records, preparation, and multiple-time measurement
protocols have not been derived by writing (5).

Nor is (3) proved to be a uniformly local Hamiltonian on physical clock
degrees of freedom. Encoding ideals by one occurrence bit per event
requires enforcing predecessor constraints; their support can grow with
the order. The algebraic construction does not solve that resource and
locality problem.

Exact vector equality in (2) matters when histories interfere. Merely
commuting up to a phase is insufficient for this particular constraint
unless the clock transport is enlarged to compensate that phase. There
can be nonzero solutions for some states even when full flatness fails;
the theorem concerns every initial vector.

## 4. Apply the bridge to the regulated local Hamiltonian

For the finite reference carrier in
[the local model](PROJECTED_GEOMETRY_AND_LOCAL_DYNAMICS.md), write
H_local=sum_r h_r, retaining the geometry gates and conditional hopping
terms. Choose a finite sequence of gate occurrences with tick size
delta, U_r=exp(-i delta h_r). Generate an event order by requiring an
earlier occurrence to precede a later one whenever their tensor supports
overlap, then taking transitive closure.

Incomparable events have disjoint supports, so their gates commute.
Equation (2) holds. The entire history construction (1)-(5) therefore
applies, including coherent changes of the geometry bits. There is no
replacement by a mean graph. At a specified complete-round ideal its
conditional state equals the usual local product of gates.

At fixed finite volume, R gates per round and m rounds of delta=T/m
approximate the previously analyzed Hamiltonian:

```
|| (U_R ... U_1)^m - exp(-i T sum_r h_r) ||
  <= T^2/(2m) sum_{r<s} ||[h_r,h_s]||.                 (6)
```

Here the gate U_r in (6) uses delta=T/m, with T>=0. The two-term bound
follows by integrating the commutator in the Duhamel formula; iterate
over the R terms. Telescoping over m products introduces the factor m,
with all surrounding factors unitary. No exponential norm factor is
needed. Equation (6) is not volume-uniform as written.

This shows exactly how the supplied Hamiltonian can be encoded in an
order clock. It does not derive the order or its tick calibration from
the unchanged causal-set growth law. The initial gate schedule and
support geometry are inputs; removing enumeration dependence *within*
that order does not prove independence from all choices of order or
slicing. The old canonical harmonic law still has the
[eventual-chain obstruction](HARMONIC_BORN_EVENTUAL_CHAIN_COLLAPSE.md).

## 5. An order clock does not change the dispersion by itself

The previous one-probe band is epsilon(k)=k^T D k+O(|k|^4). If one
causal tick implements exp(-i delta H), this is the phase per tick,
scaled by delta. A change of clock units multiplies all frequencies
by the same factor and preserves their momentum ratios. For small
collinear k, epsilon(2k)/epsilon(k) tends to 4, whereas a massless
linear band has ratio 2. A momentum-dependent clock adjustment would
not be one common clock for a superposition of momenta.

More generally, a common smooth monotone reparameterization T=T(t)
gives instantaneous generator (dT/dt)H and leaves those ratios intact.
It need not preserve stationarity. Scale-dependent choices of tick
duration are possible, but require a physical continuum calibration:
they are precisely the scaling question, not its answer. Nothing here
rules out a massive particle with a quadratic low-momentum band.

Thus the collective-wave investigation is still relevant. A large-spin
phase expansion and a fast-geometry limit are prospective controlled
extensions, not established results of this clock audit. Any eventual
wave cone must agree with the physical causal order and use its
calibrated clock. We must not manufacture that agreement by defining
the order after seeing the desired dispersion.

## 6. Revised principle and scope

The useful principle is **physical evolution depends on causal history,
not the arbitrary numbering of causally unrelated events**. The finite
diamond equation makes it testable. Causal order supplies temporal
precedence; causal histories can supply internal quantum clock readings;
counts can supply durations under an established geometric approximation.

What is established here is the conditional finite bridge, not a new
physical TOE. Still needed are a law selecting nondegenerate spacetime
orders, an intrinsic identification of the local matter/geometry
updates, a continuum approximation with calibrated durations and a
common matter cone, and gravitational dynamics. The coherent quantum
history does not by itself explain why a particular history is realized.

`scripts/causal_order_clock_audit.py` checks enumeration dependence of
birth labels, every extension and diamond in finite examples, the full
constraint/Laplacian equivalence, a noncommuting failure case, and the
local geometry/matter product limit. The Lean module proves nine supporting
swap-chain invariance and algebraic clock/transport results. Poset
extension connectivity, the full Hilbert-space construction, and (6)
are analytic proofs above, not claimed as fully formalized Lean results.
