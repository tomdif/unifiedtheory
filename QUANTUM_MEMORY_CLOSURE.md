# An exact interacting reduction with derived sufficient memory

Date: 2026-09-09.

The CNOT counterexample in [the quantum-refinement proof](QUANTUM_REFINEMENT_PROOF.md)
has an exact solution: retain the system state conditioned on a conserved
binary record. The required observable algebra follows from the specified
interaction and the system observables. A projection onto that algebra
preserves every finite experiment made from the interaction and arbitrary
system operations, including adaptive measurement histories, with the same
extra qubit reused throughout.

This proves an interacting finite consistency mechanism. It does not prove
that this interaction describes nature, or derive spacetime, general
relativity, a GUT, or a TOE.

The formal proof is
[`KFCausalQuantumMemoryClosure.lean`](UnifiedTheory/Audit/KFCausalQuantumMemoryClosure.lean).
The explicit conditional-state formulas and algebra dimensions below also
have an independent
[exact matrix audit](scripts/quantum_memory_closure_audit.py), with
[recorded results](data/quantum_memory_closure_audit.json).

## 1. The retained algebra is forced by the interaction

Let A and B be qubits, A the observed control and B the reused target. Set

```text
Q = CNOT = |0><0|_A ⊗ I_B + |1><1|_A ⊗ X_B,
J = I_A ⊗ X_B.
```

The allowed operations are Q and arbitrary system outcome operators
K_A ⊗ I_B. Physical instruments use families satisfying
sum_a K_a† K_a = I_A. No restriction to initially uncorrelated states is
made.

We require a unital star algebra S that contains every A ⊗ I_B and is
invariant under the Heisenberg evolution O ↦ Q† O Q. Closure forces

```text
Q† (X_A ⊗ I_B) Q = X_A ⊗ X_B,
(X_A ⊗ I_B) [Q† (X_A ⊗ I_B) Q] = J ∈ S.
```

Thus every such S contains

```text
B_mem = alg*(M₂(ℂ) ⊗ I_B, J).
```

Conversely, Q belongs to this generated algebra by its displayed
decomposition. Therefore Q† B_mem Q is contained in B_mem. All system
operators also belong to it, so their outcome maps K† O K preserve it.
This proves minimality among invariant unital star algebras containing all
system observables.

Because J commutes with system operators and J² = I, every word in the
generators reduces to

```text
A ⊗ I_B + B ⊗ X_B,     A, B ∈ M₂(ℂ).
```

These matrices form a star algebra. In the X basis of B they are diagonal
blocks A+B and A−B, independently variable. Hence

```text
B_mem ≅ M₂(ℂ) ⊕ M₂(ℂ),
dim_ℂ(B_mem) = 8,     dim_ℂ(M₄(ℂ)) = 16.
```

This minimality statement concerns the specified algebraic requirements.
It is not a claim that eight coordinates are necessary for every prediction
problem or every nonlinear representation. In particular, the linear span
of unperturbed one-time system observables and their CNOT images has
dimension six. Multiplicative closure gives eight.

Lean proves the forced-record identity in `cnot_exposes_memory`,
invariance in `memoryAlgebra_invariant`, and minimality in
`memoryAlgebra_minimal`. The block decomposition proves the dimension
analytically; the exact audit independently derives dimensions 4 → 6 → 8 by
closing the actual system matrix basis under evolution, adjoints, and
multiplication.

## 2. A positive projection onto precisely that algebra

The conserved operator satisfies J† = J, J² = I, and QJ = JQ. Define

```text
P₊ = (I+J)/2,     P₋ = (I−J)/2,
E(ρ) = (ρ+JρJ)/2 = P₊ρP₊ + P₋ρP₋.
```

The P's are orthogonal projections with P₊ + P₋ = I and
P₊†P₊ + P₋†P₋ = I. The displayed Kraus form therefore gives a completely
positive, trace-preserving map. Idempotence follows either by expanding
E(E(ρ)) or using J² = I.

The fixed matrices of E are exactly those commuting with J: if E(ρ)=ρ
then JρJ=ρ, and conversely. In B's X basis these are precisely arbitrary
matrices on the two diagonal system blocks. Consequently

```text
range(E) = {ρ : E(ρ)=ρ} = B_mem.
```

For O ∈ B_mem, cyclicity of trace and JOJ=O imply

```text
Tr[O E(ρ)] = Tr[Oρ].
```

In particular, tracing over B recovers the original system matrix:
Tr_B E(ρ) = Tr_B ρ. The projection discards only the coherences between the
two memory sectors, invisible to the allowed experiments.

Lean proves the Kraus identity, completeness, positivity, trace
preservation, idempotence, equality of the fixed-point set to the derived
algebra, and preservation of the system partial trace. Complete positivity
at all ancillary dimensions is the usual analytic consequence of the
proved Kraus form; this module does not introduce a separate formal
complete-positivity predicate.

## 3. Proof for arbitrary finite histories

Every allowed outcome operator K commutes with J. Because J is
self-adjoint, K† also commutes with it. Therefore, for any joint matrix ρ,

```text
E(KρK†)
  = [KρK† + JKρK†J]/2
  = K[(ρ+JρJ)/2]K†
  = K E(ρ) K†.
```

This holds for nonunitary measurement outcomes as well as for Q. For a
finite branch h=(K₁,…,Kₙ), write W_h = Kₙ⋯K₁. Induction gives

```text
E(W_h ρ W_h†) = W_h E(ρ) W_h†.
```

Taking the trace, or taking the system partial trace, proves respectively

```text
Tr[W_h E(ρ) W_h†] = Tr[W_h ρ W_h†],
Tr_B[W_h E(ρ) W_h†] = Tr_B[W_h ρ W_h†].
```

For a positive, trace-one input and complete physical instruments these
are identical joint branch probabilities and identical unnormalized final
system states. When the common probability is nonzero, normalization also
gives identical conditional states. No division on zero-probability
branches is needed.

An adaptive policy chooses its next instrument from previous recorded
outcomes. For any fixed recorded branch, this specifies a finite list of
allowed operators. The theorem applies to every such list; hence both
descriptions assign the same probabilities to all branches of the policy.
Coarse outcomes with several Kraus operators follow by summing the
equalities over their unrecorded Kraus labels.

The generic formal results are `memoryProjection_all_branches` and
`all_branch_probabilities_preserved`.
`cnot_system_history_exact` explicitly accepts a list whose members are
CNOT or lifted system operators, and proves the two displayed equalities.
It assumes neither a reset of B nor the conclusion of dynamical closure.

## 4. The reduced state and its closed update rule

Let |±> be B's X eigenstates, p± = |±><±|, and define unnormalized positive
system matrices

```text
τ± = Tr_B[(I_A ⊗ p±) ρ (I_A ⊗ p±)].
```

They encode exactly the projected state:

```text
E(ρ) = τ₊ ⊗ p₊ + τ₋ ⊗ p₋,
ρ_A = τ₊ + τ₋,     Tr τ₊ + Tr τ₋ = 1.
```

On the + sector CNOT acts as I_A; on the − sector it acts as Z_A.
The interacting update therefore closes as

```text
CNOT:           (τ₊, τ₋) ↦ (τ₊, Z_A τ₋ Z_A),
system outcome: (τ₊, τ₋) ↦ (K_A τ₊ K_A†, K_A τ₋ K_A†).
```

These formulas give a system coupled to a classical two-sector record.
Calling the record conserved means that Q and the allowed operations do
not transfer states between its sectors. A selective measurement can still
update our probabilities of the sectors. A complete nonselective system
instrument preserves each sector's total weight.

This is a representation of sufficient retained information, not an
assumption that a measurement of B physically occurred. Its two system
matrices retain system-record correlations. Their explicit formulas are
proved analytically above and checked on the complete joint matrix basis;
the generic history theorem itself is formalized in Lean.

For the earlier input |+><+|_A ⊗ |0><0|_B, both initial blocks equal
|+><+|/2. Repeated CNOT gives system X expectations

```text
1, 0, 1, 0, 1, 0, …
```

This recovers the coherence revival that an iterated memoryless dephasing
channel misses.

### Why a marginal and a bare record distribution are insufficient

Compare

```text
ρ = |Φ+><Φ+|,     |Φ+> = (|00>+|11>)/√2,
σ = (I_A/2) ⊗ |0><0|_B.
```

Both have system marginal I_A/2 and record probabilities
Pr(X_B=+1)=Pr(X_B=−1)=1/2. Nevertheless, after one CNOT their system
X expectations are 1 and 0. Thus those marginals do not determine the
next prediction. The conditional matrices distinguish the inputs and
predict both correctly. The exact audit checks this witness.

## 5. What this establishes for the research program

A useful organizing principle is: **close the retained observables under
the dynamics and permitted interventions, then discard only distinctions
invisible to that closure.** Here the finite algebra is derived and its
positive reduction is explicitly constructed. The all-history proof
establishes exact interaction-compatible consistency.

This resolves the earlier finite CNOT obstruction. The reduced algebra has
a nontrivial center and is M₂ ⊕ M₂, so it does not meet the full-matrix-factor
hypothesis of the preceding autonomous-unitary factorization theorem.
There is no contradiction between the two results.

This method belongs to established quantum conditional-expectation and
exact model-reduction theory. Grigoletto and Ticozzi construct exact,
physically admissible reduced models for discrete-time quantum systems in
[Model Reduction for Quantum Systems](https://arxiv.org/abs/2307.06319).
Grigoletto, Tao, Ticozzi, and Viola discuss the distinction between reduced
linear spaces and reduced quantum operator algebras in
[Exact Model Reduction for Continuous-Time Open Quantum Dynamics](https://arxiv.org/abs/2412.05102).
The contribution here is the explicit construction, proof, and audit of
the repository's interacting benchmark; this is not a claim to have
invented that general method.

The input dynamics Q remains specified. For other dynamics, the closure
may be the entire joint algebra, leaving no exact reduction. Nothing here
selects CNOT as a fundamental law, identifies the retained observables
with spacetime geometry, or derives Einstein or Standard Model dynamics.
Those obligations remain in the [GUT frontier](GUT_CLOSURE_FRONTIER.md).
An application to causal growth must supply actual growth operators and
observable definitions, then calculate their closure and demonstrate a
geometric limit.

The instrument convention is Born completeness, sum K†K=I. Although the
pinching projectors also sum to I, the interacting one-outcome law K=Q does
not satisfy the separate coherent sum rule sum K=I from earlier scalar
constructions. This example does not resolve that additional constraint.

## 6. Verification

The exact audit derives the algebra rather than hard-coding a candidate
dimension into the closure iteration. Its assertions then verify:

- system dimension 4, one-time span dimension 6, algebra dimension 8;
- projection rank 8 and center dimension 2;
- 80 intertwining identities on all 16 joint matrix units for CNOT and
  four system matrix-unit outcome operators;
- conditional-state reconstruction and CNOT updates on all 16 matrix
  units;
- the two explicit memory witnesses;
- 496 branches across eight initial states, five interaction rounds, and
  three adaptively chosen complete instruments, including 350 nonzero
  branches and 40 normalized probability trees.

The sampled adaptive trees test the executable representation. The Lean
induction proves the history statement at every finite length.

```sh
python3 scripts/quantum_memory_closure_audit.py --output data/quantum_memory_closure_audit.json
lake build
git diff --check
```

Four source hashes bind the exact audit to its script, the preceding audit
helper, and both quantum proof modules. The new module's fourteen printed
main-theorem audits use only propext, Classical.choice, and Quot.sound.

Validation completed on 2026-09-09: the exact audit passes, all four source
hashes match, and the new Lean module checks without errors or warnings.
The full integrated Lean build passes (8,913 jobs), and
`git diff --check` passes.
