# A local realization and local readout of the order clock

Date: 2026-09-10

The finite clock bridge can be completed as an explicit constrained
quantum model on event bits. It no longer needs one abstract basis label
for an entire causal past. For the supplied regulated circuit, the new
constraint has bounded interaction size, a uniform interaction-strength
bound, exactly the desired history space, and local clock readouts that
recover the correct reduced matter state. The previous Schroedinger
continuum also admits an explicit realization through these clock ticks.

This completes these finite/local parts of the clock construction. It
does not complete a physical TOE or derive Lorentzian spacetime. The
event order, work registers, gates, and duration calibration remain
inputs. Locality also fails to guarantee a polynomial constraint gap:
a nearest-neighbor circuit below has an exponentially small gap. This
obstructs a general gap-based preparation guarantee, not every possible
preparation algorithm. Constraint energy and physical clock frequency
are distinct throughout.

## 1. Event bits and bounded predecessor sets

Use context-independent unitary gate occurrences U_v on a tensor product
of work registers. Each support S_v contains at most s registers. On
each work register, put its gate occurrences in their supplied order;
join consecutive occurrences by a directed edge. Call this acyclic
directed graph D and its reachability order P. Duplicate edges are
removed. Each event has at most s incoming and s outgoing neighbors.
The same order results from the previous prescription of ordering every
pair of overlapping occurrences. No total ordering of disjoint gates
is physically used after D has been specified.

Add a qubit for each event v, with n_v=|1><1| and raising operator
r_v=|1><0|. A bit configuration is an ideal of P exactly when

```
D_clock = sum_(u->v in D) (1-n_u)n_v
```

vanishes. Indeed, an included event must include every immediate
predecessor, and iteration includes every ancestor. Conversely every
ideal satisfies these two-bit constraints.

Define the guard and the dressed clock flip

```
F_v = product_(u->v) n_u product_(v->w) (1-n_w),
R_v = r_v tensor U_v + r_v^dagger tensor U_v^dagger.
```

F_v commutes with R_v, F_v is a projection, and R_v is a self-adjoint
involution. Therefore

```
Q_v = F_v(1-R_v) >= 0,        ||Q_v|| <= 2.             (1)
```

The successor guard is essential: reversing a completed event while
one of its successors remains completed would otherwise leave the
ideal sector. On an ideal, (1) permits exactly the allowed addition or
removal of v and applies the corresponding matter unitary.

Each Q_v commutes with every violation projector (1-n_u)n_w. For edges
not incident on v, that projector is diagonal on unchanged clock bits.
For an incoming edge to v, F_v enforces n_u=1; for an outgoing edge,
it enforces n_w=0. Both incident violations vanish on the guard, on
either side of the flip. This proves exact invariance, not merely a
large-penalty approximation.

## 2. Exact kernel on the full tensor product

For J_c>0 and positive numbers w_v, define

```
C_local = J_c D_clock + sum_v w_v Q_v.                 (2)
```

On illegal clock configurations, D_clock has eigenvalue at least one.
It commutes with all terms, which are positive. Thus the entire illegal
sector has energy at least J_c. On the legal sector, (2) is exactly the
weighted version of the [previous history constraint](CAUSAL_ORDER_CLOCK_BRIDGE.md).
Its unitary gauge transformation gives

```
W^dagger (C_local restricted to legal clocks) W
  = L_ideal,w tensor 1.                               (3)
```

L_ideal,w has edge weight w_v when an ideal gains event v. Because
disjoint gates commute, the diamond equation holds. The ideal graph is
connected, and positive edge weights leave its constant kernel intact.
Consequently the full kernel of C_local consists precisely of

```
|Psi(psi0)> = |J(P)|^(-1/2) sum_(I ideal) |bits(I)> V(I)|psi0>,
```

with arbitrary initial work vector psi0. Its dimension is dim(H_work).
There are no extra zero modes outside the ideal sector. Moreover

```
gap(C_local) >= min(J_c, w_min gap(L_ideal)).           (4)
```

This is a supplied positive constraint. It does not dynamically repair
illegal clocks: violation sectors are conserved. Ground-state
preparation is a separate problem. Related local-clock constructions
already exist in [space-time circuit-to-Hamiltonian work](https://arxiv.org/abs/1311.6101);
the claims here are the explicit event-bit realization and bounds for
the current model, not an invention of the history-state method.

## 3. Uniform locality requires controlling repeated use of a register

A propagation term acts on at most 1+2s clock qubits and s work
registers, hence at most 1+3s sites. This alone does not bound the total
interaction at a work register: it can be used arbitrarily many times.

Let j_q(v)>=1 be the position of occurrence v along work register q.
Set k_v=max_(q in S_v) j_q(v) and choose the constraint weights

```
w_v = 1/[k_v(k_v+1)].                                 (5)
```

They depend on preceding occurrences, not on a future circuit length.
For any work register q,

```
sum_(v touching q) w_v
 <= sum_(j>=1) 1/[j(j+1)] = 1,                        (6)
```

by telescoping. These weights do not change the kernel, conditional
gate dynamics, or calibrated duration of any tick. They change the
constraint spectrum and its fictitious Hamiltonian flow.

A work site sees total term norm at most 2. A clock site appears in
at most 1+2s propagation terms, each of norm at most one since w_v<=1/2,
and at most 2s penalty terms. Therefore, uniformly in spatial volume
and number of clock events,

```
sup_x sum_(Z containing x) ||Phi(Z)|| <= K,
K = 1+2s+2s J_c.                                     (7)
```

Here s>=1, so K>=2. Suppose each gate's work support has diameter at
most r in the supplied work metric. Attach its event-clock site to one
work site in that support. Neighboring events in D share a work site.
Every propagation support then has diameter at most 4r+2; the two-clock
penalties obey the same bound. The usual interaction-chain proof gives

```
||[A(theta), B]|| <= 2 |X| ||A|| ||B||
 exp(2(1+3s)K exp(mu(4r+2)) |theta| - mu d(X,Y)).       (8)
```

For the previous neutral matter/geometry carrier, s=3 and r=4 suffice,
so terms involve at most ten sites, have diameter at most eighteen,
and K=7+6J_c. The constants are deliberately loose. This applies
[established Lieb-Robinson theory](https://arxiv.org/abs/math-ph/0603064).
The parameter theta in (8) is the flow generated by the constraint;
it is not identified with proper time or the clock's conditional gate
evolution. Reference spatial geometry is still supplied.

## 4. A local observer does not need the whole causal past

Choose a set Q of observed work registers. On register q, specify a
cut after its j_q-th gate occurrence. Read the last clock bit as one
and the next as zero; at an initial or final boundary only the existing
bit is required. This uses at most 2|Q| clock bits. On legal clocks,
these readings fix the entire completed prefix on each observed
register, because its event bits are monotone along the wire.

Assume the readings are compatible with at least one ideal. Let C be
the union of the causal pasts, including the events themselves, of the
last completed occurrences on Q; empty prefixes contribute nothing.
Then C is an ideal and itself satisfies the cut readings. Every ideal
I compatible with those readings contains C. Every extra event in
I\C acts outside Q: otherwise it would be a completed occurrence of
an observed register missing from its specified prefix.

Enumerate C first inside I, which is possible because C is an ideal.
Then V(I)=V_extra V(C), where V_extra acts only on Q's complement.
For every initial density matrix, including initially entangled ones,

```
Tr_Qc[V(I) rho0 V(I)^dagger]
 = Tr_Qc[V(C) rho0 V(C)^dagger].                       (9)
```

Measuring the indicated clock bits in the history state and tracing
out the unobserved clock and work registers gives a mixture over such
I. Every term has the same reduced state (9), so the conditional local
state is exactly (9). No global-ideal postselection is needed.

This is a single-readout theorem. It does not construct an observer,
derive record formation, or establish the statistics of sequential
measurements with backreaction. The readout probability can depend
on the rest of the finite history. Dropping the next-bit condition or
reading only a total event count generally changes the conditional
state; the audit includes a failure example.

## 5. Put the actual low-band continuum on this clock

The construction can realize the already derived
[one-probe continuum](COLLECTIVE_SPACETIME_TEST.md), with an explicit
joint limit rather than only fixed-volume product convergence.

Let a be the reference lattice spacing on a fixed physical three-torus,
and n_work(a)=O(a^-3) count matter plus geometry registers. Write the
regulated Hamiltonian as a sum of local terms with per-site norm sum
at most J_* as in the earlier local-model note. The sum of pairwise
commutator norms satisfies

```
sum_(r<s) ||[h_r,h_s]|| <= n_work(a) J_*^2.            (10)
```

Indeed, disjoint supports commute. Bound each remaining commutator by
twice the product of the norms, sum ordered overlapping pairs, and
overcount by shared sites. The resulting bound is the sum over sites
of the squared norm load. Scalar ground-energy shifts do not alter
commutators. Include their phases in the tick unitaries when comparing
vectors rather than density matrices.

For each a, choose a *microscopic* circuit tick delta_a=a^6, with one
gate of duration delta_a for every local term in each complete round.
Give a complete round the calibrated macroscopic duration a^2 delta_a
=a^8, consistent with the previous quadratic band scaling. At a clock
cut after m_a(t)=floor(t/a^8) rounds, the completed microscopic duration
is m_a(t)delta_a. For 0<=t<=T,

```
product error <= (T/2) n_work(a) J_*^2 a^4 = O(a),
time rounding error <= a^6 ||K_a|| = O(a^3).           (11)
```

The first is the unitary product estimate with m_a(t) rounds. For the
second, the shifted one-probe Hamiltonian obeys
||K_a||<=M(a)Omega+12kappa=O(a^-3). It preserves the one-probe sector,
as do all the gates. Combining (11) with the earlier dressed-band
embedding J_a and its momentum cutoff |p|_1<=P gives

```
||V_a(I_m(t)) J_a - J_a exp(-it H_eff)||
 <= (T/2)n_work J_*^2 a^4 + a^6(M Omega+12kappa)
    + T[C_band a^2 P^4 + P^2 |D_x,M-D_x,infinity|]
 -> 0.                                                (12)
```

Thus the specified Schrödinger continuum has a causal-order clock
implementation. The clock is read by events; t is the chosen limiting
coordinate assigned to those readings. The calibration a^8 is an
explicit input, not a derivation of proper seconds. The construction
uses O(a^-11) event bits over fixed T and physical volume. Equation
(12) proves existence of a controlled encoding, not efficient physical
preparation. It gives no massless relativistic dispersion.

The convergence in (12) concerns conditional work propagators. It does
not construct a normalized limiting history state over an infinite
clock or a limiting probability distribution for its readings.

## 6. A sharp preparation obstruction even on a line

Uniform locality does not imply a polynomial constraint gap. Consider
n>=2 work qubits on a line, with these gate occurrences:

1. Independent initial one-qubit gates a_0,...,a_(n-1).
2. Nearest-neighbor gates (0,1),(1,2),...,(n-2,n-1).
3. One central gate c on register n-1.
4. The nearest-neighbor sweep in reverse order.
5. Independent final one-qubit gates b_0,...,b_(n-1).

All gates can be chosen arbitrarily on their displayed supports.
There are 4n-1 events. Every initial/sweep event precedes c, and c
precedes every reverse-sweep/final event. In the ideal graph there is
exactly one edge crossing from c=0 to c=1: all preceding events must
be complete and all following events absent.

The number A_n of ideals before c is

```
A_n = 2^n + sum_(j=0)^(n-2) 2^j = 3*2^(n-1)-1.
```

The first term counts ideals with no forward-sweep gate. The other
terms classify the last completed sweep gate. Reversing the event
order identifies the two sides of the central cut, so there are A_n
clock states on each side. A test vector equal to +1 before c and -1
after c is orthogonal to the constant ground state and has Rayleigh
quotient 2w_c/A_n. Hence

```
gap(L_ideal,w) <= 2w_c/[3*2^(n-1)-1].                 (13)
```

With (5), c is its register's third occurrence, so w_c=1/12. All
registers occur at most six times and all gates have at most two-site
support. The obstruction therefore persists with bounded local clock
density and bounded spatial interaction range. Even setting all
weights to one leaves an exponentially small upper bound in n.

This concerns this event-ideal constraint and says nothing against
polynomial gaps proved for other circuit-clock encodings. Modifying
the clock representation, inserting extra occurrences, or changing
history weights changes the model; it must be analyzed separately.
Spectral constraints on branching history constructions are also
studied in [Bausch and Crosson](https://arxiv.org/abs/1609.08571).

## 7. What has and has not been completed

The local realization, correct legal kernel, uniform norm locality,
local reduced-state readout, and the explicit order-clock encoding of
the already established continuum are analytic results above. The
accompanying audit checks the full tensor clock construction, legal
restriction, every compatible finite local readout, missing-guard
failures, interaction loads, and the exponential bottleneck family.
The Lean file proves twelve supporting algebra, positivity, and load results;
it does not claim formalization of all operator or continuum arguments.

There is still no derivation of the physical causal order, Lorentzian
geometry, a common relativistic matter cone, or Einstein dynamics.
Those gaps cannot be removed by calling the clock constraint itself
gravity. The intended physical principle remains dependence on causal
history rather than event enumeration; the next physical requirement
is a law selecting suitable histories and their calibrated dynamics.
