# Energetic selection of a neutral propagation sector

Date: 2026-09-10

The hard neutral-probe gate in [the previous construction](PATCH_GROWTH_AND_NONCOLLAPSE.md)
can be obtained as a controlled **strong-penalty, finite-time limit**.
The error bound below is uniform in graph size, including quantum
exchanges of the geometry on the connected degree-six regular carrier.
It uses local commutators rather than the extensive norm of the graph
Hamiltonian. This closes a specific Hamiltonian-realization gap for the
supplied neutral probe. It does not establish a spacetime propagation
cone for the fluctuating model.

There is also a sharp limitation: every fixed finite defect penalty
still violates the previous uniform exponential propagation bound on
the static shortcut family. Strong-penalty convergence and exact spatial
locality are distinct statements. The three-dimensional patch template,
one neutral probe, and its new energy coupling remain physical inputs.

## 1. Relation to existing strong-coupling results

Suppression of transitions between strongly separated sectors is
standard quantum Zeno dynamics. See Facchi and Pascazio,
[Quantum Zeno subspaces](https://arxiv.org/abs/quant-ph/0201115),
and Burgarth, Facchi, Nakazato, Pascazio, and Yuasa,
[Generalized Adiabatic Theorem and Strong-Coupling Limits](https://arxiv.org/abs/1807.02036),
Theorem 1 and Remark 1. The latter give finite-dimensional strong-coupling
limits and quantitative estimates. A finite-dimensional O(1/Delta)
statement alone does not control the constants as the system grows.

The contribution here is an explicit commutator estimate and its
application to this repository's local graph exchanges and probe
readout. No priority claim is made for the general Zeno mechanism or
integration-by-parts method. The older
`UnifiedTheory/LayerB/QuantumZeno.lean` does not prove the quantitative
operator estimate used here.

## 2. A bound that avoids the extensive Hamiltonian norm

Let K be any self-adjoint matrix and P any orthogonal projector on a
finite-dimensional Hilbert space. Put

```
R = I-P,
D = PKP + RKR,
V = PKR + RKP,
H_Delta = Delta R + K,
H_0 = Delta R + D,
v = ||V||,   c = ||[D,V]||,   Delta > 0.
```

All norms in the theorem are induced Hilbert-space operator norms.
For every real t,

```
|| exp(-it H_Delta) - exp(-it H_0) ||
    <= [2v + |t|(c+v^2)] / Delta.                         (1)
```

Consequently, on a normalized input in Ran(P), the difference from
`exp(-it PKP)` and the amplitude outside Ran(P) are at most the same
quantity. Leakage probability is at most its square (or one, when the
bound is larger). This is a bare-P input statement, without replacing
P by an exact low-energy spectral projector.

**Proof.** Set S=[R,V]. The two-block decomposition gives

```
[R,S]=V,    ||S||=v,    ||[D,S]||=c.
```

For `F(s)=exp(is H_Delta) S exp(-is H_0)`, differentiation gives

```
F'(s) = i exp(is H_Delta) (Delta V + [D,S] + VS) exp(-is H_0).
```

Duhamel's identity writes
`exp(it H_Delta)exp(-it H_0)-I`
as `i integral_0^t exp(is H_Delta)V exp(-is H_0) ds`.
Substitute the derivative identity into that integral. Unitarity bounds
the two endpoint terms by 2v, and the integral remainder by
`|t|(c+v^2)`. Division by Delta proves (1), also for negative t by
integrating over the reversed interval. No gap between the spectra of
the two **full** blocks is required.

The algebraic identities

```
V = [P,[P,K]],
[D,V] = [K,V] = -[P,[K,[K,P]]]
```

imply

```
c <= ||[K,[K,P]]||.                                      (2)
```

To see the last inequality, set Q=2P-I. The off-diagonal part of any
matrix X is `(X-QXQ)/2`, a norm contraction, and multiplication by Q
turns that part into [P,X]. Remote commuting energies can therefore
make ||K|| arbitrarily large without increasing the bound.

If v<=v_* and c<=c_* uniformly in N, then on every window |t|<=T
the error is at most `[2v_*+T(c_*+v_*^2)]/Delta`. Growing windows T_N
are allowed when that numerator divided by Delta_N tends to zero.
This does not assert infinite-time agreement at fixed Delta.

## 3. Static bounded-degree graphs

For the neutral probe on a fixed graph, choose

```
K = -kappa A_G,    P = diag(q_v(G)),
H_Delta = -kappa A_G + Delta diag(1-q_v(G)),
```

where q_v is the existing radius-three cubic-patch indicator and
kappa>=0. Degree at most six gives `||K||<=6 kappa`. Block compression
and off-diagonal extraction give v<=6 kappa and c<=72 kappa^2. Thus

```
|| (exp(-it H_Delta)-exp(it kappa P A_G P)) P ||
    <= (12 kappa + 108 kappa^2 |t|)/Delta.                (3)
```

This estimate is uniform over all graph sizes and all such fixed graphs.
On the static family of the previous note, the hard gate obeys its
original-distance bound. The energetic probe therefore obeys the
**additive** estimate, for good endpoints,

```
|<u|exp(-it H_Delta)|v>|
 <= exp(6 kappa |t| exp(mu)-mu d_original(u,v))
    + (12 kappa+108 kappa^2 |t|)/Delta.                   (4)
```

An additive error floor is not an exponential spatial bound.

## 4. A fixed joint projector for fluctuating geometry

Use the connected labelled degree-six graph carrier from
[the patch Hamiltonian](PATCH_GEOMETRY_PROTECTION.md), tensored with a
single neutral vertex-position register. On basis states |G,v>, define

```
P|G,v> = q_v(G)|G,v>,
K = G_op + E + T,
G_op = rho sum_p (S_p^2-S_p) tensor I_probe,
E = J D3 tensor I_probe,
T = -kappa sum_G |G><G| tensor A_G,
H_Delta = K + Delta(I-P),        rho,J,kappa >= 0.        (5)
```

The sum uses all ordered distinct quadruples and exactly the existing
controlled partial involutions S_p. For p=(a,b,c,d), the control edge
bc stays present and the exchange toggles ab,cd with ac,bd. The reverse
description is (a,c,b,d). Its active graphs stay connected and regular.

P is a **fixed operator on the joint Hilbert space**, even though its
value depends on G. An externally time-dependent projector or prescribed
classical graph trajectory is unnecessary.

The effective PKP has two consequences:

- Probe hops survive only when both endpoint patches are good in G.
- A graph flip survives at occupied v only when q_v=1 before and after
  that flip. Changes of geometry can therefore be suppressed by the
  probe's energy constraint as well as conversely.

The original diagonal exchange cost is retained by compression. In
particular PKP is **not** obtained by deleting forbidden transitions
and then recomputing a Markov graph Laplacian with new row sums.

This is a specified neutral one-particle extension. It does not replace
the charged Gauss-law matter sector, establish many-particle locality,
or derive q_v's three-dimensional template.

## 5. Uniform joint commutator bounds

Define the degree-six ball envelope

```
b_r = 1 + 6 sum_{i=0}^{r-1} 5^i,
b_3 = 187,     a_g = 1200 b_3 = 224400.
```

For (5), constants independent of N are

```
v_* = a_g rho + 6 kappa,
c_* = 16 b_15^8 rho^2 + 748 a_g J rho
      + (4800+24 a_g) rho kappa + 144 kappa^2.           (6)
```

Equations (1), (2), and (6) imply the uniform joint bound

```
|| (exp(-it H_Delta)-exp(-it PKP)) P ||
  <= [2v_*+|t|(c_*+v_*^2)]/Delta.                       (7)
```

The geometry coefficient is deliberately extremely conservative:
`b_15=45,776,367,187`, and `16 b_15^8` is enormous. It proves existence
of a size-independent constant, not an experimentally practical penalty
scale. Numerical examples use their actual finite commutator bounds.

### 5.1 One local exchange and the first commutator

Changing q_v requires an endpoint of the exchange in B_3^G(v).
Indeed, when no changed edge touches the original ball, the induced
ball cannot change: the first new edge on any newly shortened path
would have an endpoint reachable in at most three old steps.

An active exchange quadruple is a length-three path, in its forward or
reverse order. For any vertex there are at most
`4*6*5^2=600` forward ordered descriptions containing it, and at most
600 reverse descriptions. The factor two is retained because the
Hamiltonian sums ordered S_p's. Therefore at most 1200 b_3 active
descriptions can change q_v. Each off-diagonal coefficient is rho.
The diagonal S_p^2 commutes with P. Hence

```
||[G_op,P]|| <= a_g rho,    ||[T,P]|| <= 6 kappa.
```

These are absolute column-sum bounds; self-adjointness or
skew-adjointness supplies the equal row bounds needed for the Schur
operator-norm estimate. Since ||V||=||[K,P]|| and [E,P]=0, this proves
the bound on v.

### 5.2 Why distant graph moves cancel in the second commutator

Write `h_p=rho(S_p^2-S_p)`. It has at most two entries per column,
with total absolute weight at most 2rho. Moves on disjoint vertex
quadruples commute; their activation controls also commute, since each
reads and changes only edges within its own quadruple.

A single flip changes every graph distance by at most a factor of two:
each new edge replaces an old two-step path, and conversely. If an
active flip changes q_v, all four vertices of its path consequently lie
in the original B_6(v).

**Support lemma.** If
`[h_p,[h_q,P]]|G,v>` is nonzero, both ordered quadruples have all their
vertices in B_15^G(v).

**Proof.** The inner commutator has only a possible flip entry and is
nonzero at a graph X exactly when q is active and changes q_v(X).
Expand the outer commutator into two terms.

1. If the inner commutator is nonzero at G, the q quadruple lies in
   B_6^G(v). When p overlaps q and contributes, p is active at G or
   qG. From a shared vertex its other vertices are at distance at most
   three in that graph, hence at most six in G. Thus p lies in B_12^G(v).
2. If a nonzero inner commutator is encountered only after the p flip,
   p is active at G and q lies in B_6^(pG)(v), contained in B_12^G(v).
   If p overlaps q, its original length-three path puts all its vertices
   in B_15^G(v).
3. For disjoint quadruples the activation and diagonal terms commute.
   If either move is inactive, the nested expression vanishes. Otherwise
   its coefficient is, up to sign, the mixed finite difference
   `q_v(pqG)-q_v(pG)-q_v(qG)+q_v(G)`.
   A nonzero coefficient requires p to change q_v at G or qG, and q
   to change q_v at G or pG. Each quadruple therefore lies in B_6 at
   G or at a one-flip graph, hence in B_12^G(v).

These cases include the diagonal contributions of h_p and exhaust the
expanded expression. They prove the support lemma.

There are at most b_15^8 ordered pairs of quadruples in that ball; this
overcounts even repeated vertices and inactive moves. Each nested
commutator has four words, each with column sum at most 4rho^2.
Its column sum is at most 16rho^2. The sum is self-adjoint, so

```
||[G_op,[G_op,P]]|| <= 16 b_15^8 rho^2.                 (8)
```

This cancellation, rather than bounding each extensive factor G_op
separately, is what removes N from the estimate.

### 5.3 Energy, hopping, and mixed terms

A flip changes D3 by at most `4 b_3=748`, by the endpoint-ball argument
applied to every affected root. Consequently

```
||[E,[G_op,P]]|| <= 748 J a_g rho.
```

E is a scalar on the probe register for each G, so `[E,[T,P]]=0`.
The remaining purely hopping term satisfies
`||[T,[T,P]]||<=4||T||^2<=144 kappa^2`.

For the mixed terms, Jacobi gives

```
[G_op,[T,P]]+[T,[G_op,P]]
  = [[G_op,T],P]+2[T,[G_op,P]].
```

The diagonal part of G_op commutes with T. The adjacency row at probe
position v changes in a flip only if v belongs to its quadruple; then
one neighbor is removed and one is added. At most 1200 ordered active
descriptions contain v, each contributing absolute column weight
2rho kappa. Thus `||[G_op,T]||<=2400 rho kappa`.
The general commutator norm inequality bounds the mixed terms by
`(4800+24 a_g)rho kappa`. Expanding `[K,[K,P]]` now gives (6).

## 6. Finite penalties still transmit through arbitrarily long shortcuts

In the previous static graph family there are good u,v with
`d_original(u,v)>=L/2-5` but `d_G(u,v)=9`. Fix kappa>0 and any finite
Delta>=0, and set `M=Delta+6 kappa`. For H_Delta in section 3,

```
<u|H_Delta^m|v> = 0                    for m<9,
|<u|H_Delta^9|v>| >= kappa^9.
```

An onsite penalty cannot shorten a walk; at order nine every
contributing step must be a hop. All shortest walks have the same
sign. The exponential Taylor remainder after order nine is bounded by
`(M|t|)^10 exp(M|t|)/10!`. Choose

```
t_Delta = kappa^9/M^10.
```

Then `Mt_Delta=(kappa/M)^9<=6^-9`, so its exponential is less than two,
and the remainder is at most one fifth of the lower bound on the
leading term. Therefore

```
|<u|exp(-it_Delta H_Delta)|v>|
  >= kappa^90 / (2*9!*M^90) > 0.                       (9)
```

This is independent of N for fixed parameters, whereas any proposed
`C exp(v_speed |t|-mu d_original(u,v))`, with positive fixed mu and
finite size-independent C,v_speed, tends to zero along the family.
Thus **no fixed finite energetic penalty repairs that exponential
bound**, even between good endpoints. Equation (9) is a rigorous
very-small-time obstruction, not a claim of large practical leakage.

There is a further scaling restriction. If the same bound is required
for all sizes and times with penalties Delta_N, (9) implies

```
90 log((Delta_N+6 kappa)/kappa)
 >= mu d_original(u_N,v_N) - log(2*9!*C) - v_speed t_Delta_N.
```

Hence along this family that particular bound requires penalties
exponential in the original shortcut separation. A polynomial penalty
can make the additive error in (7) vanish on polynomial time windows,
but cannot restore this stronger exponential-in-original-distance
estimate. This conclusion keeps mu fixed in the original lattice-step
metric; it does not exclude continuum statements with rescaled
distances, different observables, or spectral dressing.

The familiar virtual-process interpretation is also explicit. Two good
sites linked only by two consecutive bad sites with unit hopping have
an energy-zero Schur-complement off-diagonal entry
`-1/(Delta^2-1)` for Delta>1. This exact resolvent calculation illustrates
residual coupling, while (9) proves the propagation obstruction on the
actual static family without a perturbation expansion in Delta.

## 7. Model revision and remaining physical task

An overarching candidate principle is **low-energy compatibility between
matter propagation and geometry**: the propagating sector pays an energy
cost when its local geometric support fails its allowed structure.
Equation (5) gives one precise implementation. The hard constraint then
emerges in a controlled limit, and suppresses incompatible graph changes
as well as incompatible probe hops.

The result supports that mechanism as a model-building option. It does
not uniquely select it or derive the cubic template, couplings, physical
particle content, or dimension. A probe constrained at its current
position is not a proof of a common causal cone through a changing
geometry. Nor does the penalty prepare a macroscopically ordered graph.

The next mathematical target is the joint **projected** dynamics PKP:
construct an operational distance or relational observables whose
propagation remains controlled under its allowed graph flips. Then
choose a continuum scaling compatible with the explicit finite-penalty
error. Bounds on volume growth, a selected phase, matter dynamics,
Lorentz symmetry, and an Einstein effective action remain separate
requirements. No complete TOE or derivation of GR follows here.

## 8. Verification and scope

- [The audit](scripts/energetic_probe_audit.py) checks exact matrix
  identities, an exact virtual bridge, full-operator numerical dynamics
  for a generic complex Hamiltonian, and cancellation of a large remote
  commuting energy in the double commutator.
- It recognizes every root of a 512-site torus after one legal exchange,
  constructs a 1,024-dimensional graph/probe Hamiltonian for its two
  snapshots, and compares three good input states at two times and three
  penalties. This is a one-channel dynamical test with actual q_v,
  not an enumeration of the full graph carrier.
- Selected nested-commutator columns on a 4,096-site torus test both
  exact cancellation of remote flips and nonzero nearby contributions.
  Rational Taylor-tail checks support (9). Finite tests do not replace
  the general support lemma and operator proof above.
- [Ten Lean results](UnifiedTheory/Audit/KFCausalEnergeticProbe.lean)
  verify block and commutator algebra, the static coefficient, scalar
  uniform accuracy and leakage bounds, and the final tail inequality.
  The analytic differentiation, integral/norm estimates, graph support
  proof, and continuum claims are not formalized by those lemmas.
- [The report](data/energetic_probe_audit.json) records the numerical
  results, exact constants, scope, and source hashes.

Run `OPENBLAS_NUM_THREADS=1 python3 -W error::RuntimeWarning scripts/energetic_probe_audit.py`
and `lake build`. Earlier hashed research artifacts are unchanged.
