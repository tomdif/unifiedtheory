# What the quantum-refinement proposal actually proves

Date: 2026-09-09

**Refinement consistency is mathematically realizable, but it does not
derive a theory of everything.** This note proves an explicit quantum
construction, gives its bounded infinite-observable extension, and shows
why the principle does not select the dynamics. It also proves a precise
boundary: exact autonomous unitary evolution of the entire retained
subsystem, for every joint input, forbids coupling to the discarded
subsystem. An interacting two-qubit example exposes the memory lost by an
unjustified reduced evolution law.

The finite results are in
[`KFCausalQuantumRefinement.lean`](UnifiedTheory/Audit/KFCausalQuantumRefinement.lean).
The infinite algebra construction below is an analytic proof, not a
completed Lean formalization. None of these results identifies spacetime,
Einstein dynamics, or the Standard Model with the construction.

## 1. A precise meaning of the same experiment

Let `H` be a retained finite quantum system and `E` an extra finite system.
Represent a retained observable `A` in the finer system by

```text
iota(A) = A tensor I_E.
```

For density matrices `rho` on `H` and `sigma` on `E`, use the refined state
`rho tensor sigma`. Tensor positivity and the trace-product identity give

```text
rho tensor sigma >= 0,
Tr(rho tensor sigma) = Tr(rho) Tr(sigma) = 1,
Tr[(rho tensor sigma) iota(A)] = Tr(rho A).
```

Thus all retained measurement probabilities agree: take `A` to be each
effect in a POVM. Also

```text
Tr_E(rho tensor sigma) = rho,
iota(AB) = iota(A) iota(B).
```

These are finite Lean theorems. The observable map preserves the full
matrix algebra, including noncommuting tests. This construction does not
copy an unknown state: it appends a prepared extra system and specifies
which observable represents the old experiment.

For a general, possibly entangled joint state `X`, the corresponding identity
is `Tr[X iota(A)] = Tr[(Tr_E X) A]`. It follows directly by summing the
discarded matrix index. This partial-trace duality relates the state and
observable versions of the consistency requirement.

## 2. Nontrivial dynamics exist, but are not selected

Choose **any** unitary `U` on `H` and any unitary `W` on `E`. Their joint
unitary `Q=U tensor W` obeys

```text
Q† Q = I,
Q† iota(A) Q = iota(U† A U),
Q^k = U^k tensor W^k             for every natural k.
```

Lean proves all three identities. Partial-trace duality then gives

```text
Tr_E[Q X Q†] = U (Tr_E X) U†
```

for every joint matrix `X`, including entangled density matrices. Evolution
and reduction therefore agree exactly at every time step. Operators on
the two independent factors commute; this finite locality identity is also
Lean-checked. It does not construct Lorentzian light cones.

There is immediate nonuniqueness. Both

```text
U_1 = diag(1,i),       U_2 = [[0,1],[1,0]]
```

are unitary and enter this construction. For input `rho=|0><0|` and the
same measurement `A=|0><0|`, their probabilities are respectively **1 and
0**. Their completeness and the different predictions are Lean-checked.
Refinement consistency therefore does not even select this elementary
transition probability. It cannot, by itself, fix a Hamiltonian or the
Standard Model parameters.

More generally, `U(t)=exp(-itH)` can use any finite Hermitian `H`. The
principle places no spectral restriction on this product construction.
The arbitrary-time unitary family in this sentence is the usual analytic
matrix-exponential construction; the Lean theorem above concerns natural
iterations of a supplied unitary.

These dynamics use the Born-completeness condition `sum_d K_d†K_d=I`
from the proposed quantum construction. They do not impose the separate
operator condition `sum_d K_d=I` used in some earlier repository laws.
For a single Kraus operator `K=U`, that additional condition would force
`U=I`. The nonuniqueness result concerns the stated refinement principle;
compatibility with an additional coherent-sum postulate is a separate test.

## 3. The exact autonomy theorem

Suppose `H` is nonzero, `H` and `E` are finite-dimensional, and both `Q`
and `U` are unitary. Require, for **every** retained matrix `A`,

```text
Q† (A tensor I) Q = (U† A U) tensor I.                (1)
```

Then, and only then, there is a unitary `W` on `E` such that

```text
Q = U tensor W.                                     (2)
```

Here is the proof. Put `L=U tensor I` and `T=Q L†`. Multiplying (1) on the
left by `Q` and on the right by `L†` gives

```text
(A tensor I) T = T (A tensor I)                      (3)
```

for every `A`. Apply (3) to the matrix units `|i><j|`. The diagonal matrix
units force the off-diagonal `H` blocks of `T` to vanish; the off-diagonal
matrix units force all its diagonal `H` blocks to coincide. Thus
`T=I tensor W`, with explicit entries

```text
W[k,l] = T[(i0,k),(i0,l)]
```

for any retained basis index `i0`. Hence `Q=T L=U tensor W`.
Finally `Q†Q=I` and `U†U=I` give `W†W=I`. Conversely, direct tensor
multiplication proves (1) from (2).

Lean checks this argument for arbitrary finite index types in
`retained_commutant_factor`, `autonomous_unitary_factor`, and
`autonomous_unitary_iff_product`. The required nonempty retained space is
represented by the explicit index `i0`.

Equation (1) is equivalent to autonomous retained evolution for every joint
density matrix: observable expectations separate matrices, and density
matrices linearly span the finite matrix algebra. The formal theorem uses
(1); this density-matrix equivalence is the analytic interpretation.

This is a scoped version of an established quantum-information restriction.
A stronger result says that a bipartite unitary which cannot signal in one
direction must be a product unitary; see
[Beckman, Gottesman, Nielsen, and Preskill](https://preskill.caltech.edu/pubs/preskill-2001-causal.pdf).
We do not claim discovery of that general result, nor formalization of its
stronger premise here.

**Scope matters:** this theorem fixes a tensor decomposition and requires
exact, closed unitary dynamics for its entire retained algebra on every
joint input. It does not exclude interactions within either factor,
restricted preparations, a chosen encoded sector, open effective dynamics,
or controlled approximate autonomy. The earlier proposal allowed controlled
errors and a selected observable sector; the theorem diagnoses an overly
strong implementation of it.

## 4. An explicit interaction shows the missing memory

Let `Q=CNOT`, with `H` the control and `E` the target. Let

```text
rho_plus = |+><+| = [[1,1],[1,1]]/2,
sigma_0  = |0><0|.
```

For the explicitly prepared input `rho tensor sigma_0`, one reduced step
is exactly the dephasing channel

```text
Tr_E[Q (rho tensor sigma_0) Q†] = D(rho),
D(rho) = P_0 rho P_0 + P_1 rho P_1.
```

This is a valid Kraus channel: `P_0†P_0 + P_1†P_1 = I`. Its matrix action
is Lean-checked in `cnot_prepared_step` for arbitrary `rho`.

However, **reusing the same extra qubit** gives `Q^2=I`. At the second
step the actual retained state is again `rho_plus`, while iterating the
one-step reduced channel predicts

```text
D(D(rho_plus)) = I/2 != rho_plus.
```

The Pauli-X expectation is **1** in the actual result and **0** in the
iterated reduced prediction. Lean proves the state inequality in
`cnot_memory_counterexample`; the exact audit also checks these expectations.
Resetting the extra system between steps would describe a different physical
protocol. The failure comes from discarding correlations that affect the
next step.

The follow-up [memory-closure proof](QUANTUM_MEMORY_CLOSURE.md) resolves this
specific obstruction. It derives the smallest invariant star algebra
containing all system observables and proves that a projection onto it
preserves every finite history of CNOT and system interventions. Its state
keeps two conditional system matrices indexed by the target's conserved
X label. This algebra has a nontrivial center, so the construction does not
contradict the full-matrix-factor autonomy theorem above.

There is also no reduced map valid for all extra-system preparations:
`rho_plus tensor sigma_0` and `rho_plus tensor rho_plus` have identical
retained marginals, but CNOT produces retained states `I/2` and `rho_plus`
respectively. The exact audit verifies this stronger preparation dependence.

## 5. Encoding can protect quantum coherence

For a unitary encoding `S`, define

```text
iota_S(A) = S (A tensor I) S†,
Q_S = S (U tensor W) S†.
```

The Lean theorem `encoded_refinement` proves

```text
Q_S† iota_S(A) Q_S = iota_S(U† A U).
```

This protects every logical observable, including mutually noncommuting
ones. For `S=CNOT`, the encoded `rho_plus tensor sigma_0` is a Bell state.
Its ordinary one-qubit marginal has purity `1/2`; decoding by `S†` and then
tracing out the extra system recovers `rho_plus`, with purity `1`. These
finite state claims are checked by exact matrices in the audit.

The example shows why the choice of observable algebra and reduction map
is essential. It supplies a protected logical qubit, not a derivation of
particles, spatial locality, or gravitational backreaction. The product
structure in the autonomy theorem is relative to the retained algebra;
changing its encoding does not invalidate the theorem.

## 6. A bounded infinite-observable construction

The consistency requirement has a genuine infinite realization on a
specified observable algebra. Take a countable sequence of finite quantum
systems with normalized positive states `rho_j`. For the first `N` sites,
set

```text
A_N = full matrix algebra on the first N sites,
rho^(N) = rho_1 tensor ... tensor rho_N,
omega_N(A) = Tr(rho^(N) A).
```

Identify `A in A_N` with `A tensor I in A_(N+1)`. These inclusions preserve
products, adjoints, identity, and operator norm. The state identities above
give `omega_(N+1)(A tensor I)=omega_N(A)`. Consequently `omega` is
well-defined on the union of these local algebras.

For a density matrix, spectral decomposition gives
`|Tr(rho A)| <= ||A||`: write `rho` as a convex combination of unit-vector
projectors and bound each matrix element by the operator norm. Thus
`|omega(A)| <= ||A||` uniformly in the number of sites.

Take the operator-norm completion `A_infinity` of the local union. For
`A=lim A_k`, define `omega(A)=lim omega(A_k)`. The bound proves that this
limit exists and is independent of the approximating sequence. Linearity,
normalization, and the norm bound extend by continuity. Positivity also
extends: for positive `B`, approximate `sqrt(B)` by local `C_k`; then
`C_k†C_k -> B`, and each `omega(C_k†C_k)>=0`. Hence `omega` is a normalized
positive state on `A_infinity`, uniquely extending the local assignments.

Independent on-site unitary evolutions likewise define compatible
norm-preserving automorphisms on the local algebras and therefore on their
completion. Their Hamiltonians and local dimensions remain free.

This is the standard construction of a state on a quasi-local observable
algebra; see [Naaijkens' lecture notes](https://arxiv.org/abs/1311.2717).
The proof is included to make the extension and its domain explicit. Its
all-rank completion is analytic here; the script checks an explicit pure
state tower through dimension 32.

This observable-algebra state is **not** a scalar complex measure on every
history event. It does not extend the failed percolation cylinder assignment
from [the previous audit](COVARIANT_QUOTIENT_SELECTION.md). Infinite physical
events outside this norm-completed observable algebra require additional
definitions and arguments.

## 7. Consequence for the proposed TOE

The proposal has a provable mathematical core: quantum descriptions can
preserve a full observable algebra through refinement, admit nontrivial
unitary evolution, and define bounded infinite observables. These properties
also hold for simple independent quantum systems with arbitrary spectra
and no derived spacetime geometry. They are therefore insufficient to
deduce a physical TOE.

A theory with interactions needs an explicit retained algebra, state sector,
and treatment of memory or controlled approximation. The finite autonomy
theorem and CNOT example test those choices. Deriving a geometric phase,
Einstein dynamics, chiral matter, and the observed interactions still
requires a microscopic dynamics and additional physical arguments. The
entanglement-equilibrium analogy does not supply them.

The right next proof target is a specified interacting model with a
quantified reduction error and a controlled geometric limit. A recurrence
that assumes the desired reduction error is small would not establish that
target. See [the closure frontier](GUT_CLOSURE_FRONTIER.md).

## Verification

The exact audit is
[`quantum_refinement_audit.py`](scripts/quantum_refinement_audit.py), with
source-hashed results in
[`data/quantum_refinement_audit.json`](data/quantum_refinement_audit.json).

| Exact finite check | Coverage |
| --- | ---: |
| Retained/extra dimensions | (2,2), (2,3), (3,2), (3,3) |
| Product unitary pairs | 16 |
| Retained observable basis comparisons | 104 |
| Full joint matrix input comparisons | 676 |
| Independent commutant dimensions | 4, 9, 4, 9 |
| Encoded full joint matrix comparisons | 16 |
| Explicit state tower | Dimensions 2, 4, 8, 16, 32 |

The full matrix basis comparisons verify the relevant finite linear maps
on their entire domains. They supplement the arbitrary-dimension Lean
theorems and are not a numerical claim about an infinite spacetime.

```sh
python3 scripts/quantum_refinement_audit.py --output data/quantum_refinement_audit.json
lake build UnifiedTheory.Audit.KFCausalQuantumRefinement
lake build
git diff --check
```

Validation completed on 2026-09-09: all exact finite checks pass, all three
recorded source hashes match, and all thirteen printed main-theorem audits
use only `propext`, `Classical.choice`, and `Quot.sound`. The new module
checks without errors or warnings. The full integrated Lean build passes
(8,912 jobs), and `git diff --check` passes.
