# Causality, grouped amplitudes, and the inherited norm

Date: 2026-09-09

**This does not complete the GUT or derive GR.** It supplies a general
obstruction to parent-independent cut selection, an exact metric for grouping
identical transition amplitudes, and a finite covariant benchmark. The
benchmark is known complex percolation. Its recorded Born growth still fails
the ordering-fraction test for a flat four-dimensional causal diamond.

## 1. Grouping amplitudes must also transport the metric

Fix a parent causal order. Suppose the `m_y` precursor slots producing child
`y` all have the same amplitude `a_y`. Coherent grouping gives

```text
A_y = m_y a_y,
sum_y A_y = sum_precursors a_precursor.
```

If the precursor slots are orthogonal, their quadratic norm is

```text
sum_precursors |a_precursor|^2
  = sum_y m_y |a_y|^2
  = sum_{y:m_y>0} |A_y|^2 / m_y.
```

The flat grouped norm instead has the exact excess

```text
sum_y |A_y|^2 - sum_{y:m_y>0} |A_y|^2/m_y
  = sum_y m_y(m_y-1)|a_y|^2.
```

It is strictly larger whenever a duplicated fiber has nonzero amplitude.
Moreover, requiring a diagonal coefficient `d_y` to obey
`d_y |m_y z|^2 = m_y |z|^2` for every complex `z` uniquely gives
`d_y = 1/m_y` on every nonempty fiber.

These are proved in
[`KFCausalBornCovariantQuotient.lean`](UnifiedTheory/Audit/KFCausalBornCovariantQuotient.lean).
`causal_quotientBornMass_eq_precursor_mass` instantiates the identity with
the repository's actual precursor fibers and invariant transition
multiplicities. Empty fibers contribute zero; Lean uses its usual totalized
division, with `0/0=0`.

The physical assumption is the orthogonal precursor norm. The theorem
identifies the metric inherited from that assumption; it does not establish
that nature chooses it. Nor is coherent grouping an isometry on arbitrary
precursor vectors: `(1,-1)` in a two-slot fiber groups to zero. The identity
applies to the subspace constant on each fiber. The grouped slots need not
all be gauge copies.

Equivalently, orthonormal coordinates are `B_y=A_y/sqrt(m_y)`. In those
coordinates the coherent functional is `sum_y sqrt(m_y) B_y`, rather than
`sum_y B_y`. Both the metric and that functional must be transported.

This provides an alternative to imposing a flat norm on child amplitudes
and then applying a parent-dependent normalization. It does not prove a
universal impossibility of other amplitude or metric choices.

## 2. A principle that survives another birth

Keep the grouped history, its amplitude `Z`, and the number `M>0` of fine
histories it represents. Refining it by a transition fiber of size `m_y`
gives amplitude `m_y a_y Z` and history multiplicity `M m_y`.
If the outgoing row has inherited norm one, then

```text
sum_y |m_y a_y Z|^2 / (M m_y) = |Z|^2/M.
```

If the outgoing coherent sum is one, then
`sum_y m_y a_y Z = Z` as well. Both finite identities are Lean-checked.

The candidate overarching principle is **consistency under refinement of
the description**: when microscopic alternatives are grouped, transport
their amplitudes, quadratic metric, and coherent functional together.
Repeated grouping must agree with grouping in one step. Under the stated
orthogonal, fiber-constant assumptions, inverse multiplicity is forced.

This is a kinematic consistency principle. It neither selects a microscopic
action nor derives the orthogonality assumption. The history statement keeps
the whole grouped history; it does not license merging distinct histories
solely because they end at the same unlabelled order. It also does not prove
an infinite quantum-measure extension.

## 3. A rank-two obstruction to universal cut distributions

Consider a full-support birth law on precursor downsets that is invariant
under order isomorphisms. Suppose its ancestor-count marginal is the same
for every parent of a given size.

For the two-chain let `c0,c1` be probabilities of the empty and singleton
precursors. For the two-antichain let `b0` be the empty probability and `b1`
the probability of either singleton. Isomorphism invariance makes the two
antichain singleton probabilities equal. Parent-independent cut marginals
therefore imply

```text
c0 = b0,             c1 = 2 b1.
```

Let `e0,e1` be the empty and full precursor probabilities at the one-event
parent. Applying the classical Bell spectator-deletion condition to the
singleton-versus-empty comparison in each two-event parent gives

```text
c1 e0 = c0 e1,       b1 e0 = b0 e1.
```

Consequently `2 b1 e0 = b1 e0`, contradicting `b1>0` and `e0>0`.
The six-variable contradiction is Lean-checked in
`parent_independent_cuts_Bell_obstruction`; identifying those variables with
the explicit small causal orders is the argument above.

This excludes an entire design class, including the parent-independent
threshold cut laws in [the contrast note](CAUSAL_CUT_CONTRAST_BOUND.md).
Path covariance is not needed for this obstruction. It applies to the
strict **classical** Bell condition on raw precursor probabilities, not to
every possible quantum causality condition or an arbitrary endpoint law.
The condition and its precursor interpretation follow
[Rideout and Sorkin's sequential-growth construction](https://arxiv.org/html/gr-qc/9904062v3).

Thus a full-support replacement retaining classical Bell must permit
parent-dependent cut marginals. The earlier contrast bound remains valid
under its own assumptions; it does not provide that missing causality.

## 4. A known model passes the finite compatibility test

Use complex percolation with

```text
a = (1+i)/2,         b = (1-i)/2,
a+b = 1,            |a|^2+|b|^2 = 1,
alpha_C(D) = a^{m(D)} b^{n-|D|}.
```

Here `D` is a precursor downset of the `n`-event parent `C`, and `m(D)` is
its number of maximal events. This is an existing complex-percolation
model, discussed in [Gudder's quantum sequential-growth work](https://arxiv.org/abs/1204.5767).
Its use here is a controlled benchmark, not a novel physical theory.

One construction independently proposes a direct bond from each old event
to the newborn, with amplitudes `a` for selected and `b` for unselected.
For proposed bonds to have downward closure exactly `D`, every maximal
event of `D` must be selected, every event outside `D` must be unselected,
and all remaining choices are optional. Summing their amplitudes gives

```text
a^{m(D)} b^{n-|D|} (a+b)^{|D|-m(D)} = alpha_C(D).
```

This proves coherent normalization on precursors. Squared moduli are
`p^{m(D)}(1-p)^{n-|D|}`, where `p=|a|^2=1/2`; the same mandatory/optional
decomposition of independent Bernoulli bonds proves their sum is one.
All precursor probabilities are positive.

Deleting `s` common spectators preserves each maximal count and removes
`s` missing events, so it multiplies both compared amplitudes by `b^s`.
The division-free complex Bell equation follows. For any naturally labelled
path ending at `C`, its raw amplitude is

```text
a^{L(C)} b^{binom(|C|,2)-R(C)},
```

where `L(C)` counts covers and `R(C)` counts strict relations. Each birth
adds exactly its maximal-precursor count to `L` and its ancestor count to
`R`. Hence this expression is independent of the natural labelling.
For a fixed parent and unlabelled child, those same differences show that
all precursor slots in the child fiber have identical amplitudes. The
inherited grouped norm consequently equals one.

At the two-antichain, the grouped amplitudes and multiplicities are

```text
A = (-i/2, 1, i/2),         m = (1, 2, 1).
flat norm = 3/2,            inherited norm = 1.
recorded child probabilities = (1/4, 1/2, 1/4).
```

The ancestor-count distributions are `(1/4,1/4,1/2)` on the two-chain and
`(1/4,1/2,1/4)` on the two-antichain. Their parent dependence avoids the
rank-two obstruction.

**Formal boundary:** Lean proves proposed-bond normalization for arbitrary
finite rank, the precursor Born formula, the spectator-factor Bell identity,
and the product-of-powers identity. The identification of downward closures
and intrinsic path counts is analytic here and independently checked on all
88 parents through rank 5. This is not yet a fully instantiated all-parent
Lean sequential-growth law satisfying every named condition.

## 5. The recorded geometry still collapses

For any fixed real `0<p<1`, construct the recorded transitive-percolation
process from independent forward bonds between naturally labelled events.
If `i` is not an ancestor of `j`, the direct bond must be absent and every
two-bond path `i -> k -> j` must fail. These tests use disjoint bond sets,
so

```text
P(i not before j) <= (1-p)(1-p^2)^{j-i-1}.
```

Let `M_N` count incomparable pairs among the first `N` events and let
`r_N=1-M_N/binom(N,2)`. Summing the bound gives

```text
E M_N <= sum_{d=1}^{N-1} (N-d)(1-p)(1-p^2)^{d-1}
      <= N(1-p)/p^2,
E(1-r_N) <= 2(1-p)/(p^2(N-1)).
```

At `p=1/2`, the last bound is `4/(N-1)`. Markov's inequality at `N=2^k`
makes `P(M_N/N^2>epsilon)` summable in `k`. Borel--Cantelli, first for
positive rational epsilon, gives dyadic convergence almost surely.
Monotonicity of `M_N` and `N^2 >= 2^{2k}` between consecutive dyadic ranks
then gives `M_N/N^2 -> 0`, hence **`r_N -> 1` almost surely**.

This is an analytic theorem about the **recorded Born process**. It does
not establish typicality for an unmeasured interfering quantum event
pre-measure, nor does it say the order eventually becomes a literal chain
or that all later births are timid. It rules out convergence to the flat
4D diamond ordering statistic `1/10` for this record interpretation. The
statistic's geometric scope is explained in
[the contrast note](CAUSAL_CUT_CONTRAST_BOUND.md).

Making the percolation coefficient run with rank does not preserve the same
Bell condition under full support. On an antichain, compare a singleton
precursor with the empty precursor and delete the other events. Cancelling
the nonzero spectator power gives

```text
a_n b_1 = b_n a_1.
```

Together with `a_n+b_n=a_1+b_1=1`, this forces `a_n=a_1`. The last algebraic
implication is Lean-checked. A replacement needs a larger dynamics class
or a different explicitly stated causality or record prescription.

## 6. Finite consistency does not imply an infinite complex measure

There is a second obstruction for this benchmark. For any nonempty parent,
the empty precursor has `m=0` and at least one missing event, while every
nonempty precursor has `m>=1`. Therefore

```text
max_D |alpha_C(D)| <= 1/sqrt(2),
1 = sum_D |alpha_C(D)|^2 <= (1/sqrt(2)) sum_D |alpha_C(D)|.
```

Thus each nonempty parent's raw amplitude row has absolute sum at least
`sqrt(2)`. Let `V_N` be the sum of absolute amplitudes over the partition
into all naturally labelled `N`-event histories. Refining the partition
gives `V_{N+1} >= sqrt(2) V_N`, and hence

```text
V_N >= (sqrt(2))^{N-1},       N>=1.
```

The scalar complex cylinder assignment has unbounded total variation. It
cannot extend to a finite countably additive complex measure on the full
sigma algebra generated by these histories. This is an analytic argument;
the exact finite audit also checks the raw-amplitude cap on every nonempty
parent through rank 5. The extension obstruction for non-real complex
percolation is already known; see
[Surya and Zalel, introduction and extension criterion](https://arxiv.org/html/2003.11311v1#S1).

This statement is specific to the scalar complex cylinder assignment. The
recorded Born probabilities do extend to an ordinary probability measure,
as the independent-bond construction shows. It also does not exclude
assignments on restricted classes of events, conditional convergence
prescriptions, or different Hilbert-space-valued dynamics. The inherited
quadratic norm repairs the stated finite grouping mismatch; it does not
repair the scalar amplitude measure's unbounded variation.

Consequently, consistency under refinement must be supplemented by the
appropriate infinite-event extension condition for the selected event
algebra. A row-by-row normalization result cannot supply that condition.

## 7. Evidence and remaining scope

[`covariant_quotient_audit.py`](scripts/covariant_quotient_audit.py) uses
exact Gaussian rational arithmetic and exhaustive finite combinatorics.
Its source-hashed output is
[`data/covariant_quotient_audit.json`](data/covariant_quotient_audit.json).

| Check | Result |
| --- | ---: |
| Unlabelled parents through rank 5 | 88 |
| Parents with coherent and inherited Born normalization | 88 |
| Parents whose flat grouped Born norm exceeds one | 59 |
| Ordered precursor pairs with actual spectator deletion | 11,993 |
| Natural-labelling paths checked against intrinsic counts | 1,010 |
| Directed-bond configurations in the recorded geometry audit | 36,062 |

Classical Bell is only one possible constraint to retain: recent work on operator
quantum Bell conditions finds substantial restrictions that depend on the
ordering and non-singularity assumptions
([Srivastava and Surya, 2026](https://arxiv.org/abs/2603.25503)). We do not
import those results as a no-go theorem for every quantum growth model.

Reproduce the checks with:

```sh
python3 scripts/covariant_quotient_audit.py --output data/covariant_quotient_audit.json
lake build UnifiedTheory.Audit.KFCausalBornCovariantQuotient
lake build
git diff --check
```

The eleven printed main-theorem audits use only `propext`,
`Classical.choice`, and `Quot.sound`. No physical law-selection, continuum,
or empirical witness is introduced to close a remaining gate. See
[the GUT closure frontier](GUT_CLOSURE_FRONTIER.md) for the unresolved
physical obligations.

Validation completed on 2026-09-09: the exact finite audit passes and all
five recorded source hashes match. The new Lean target and full integrated
build pass (8,911 jobs for the latter); `git diff --check` passes. All eleven
main-theorem axiom audits contain only the three standard axioms above.
