# Complete Chiral Growth: Local Generalization Audit

Date: 2026-07-19

## Scope

This audit tests the newest complete chiral causal-growth law in
`UnifiedTheory/Audit/KFCausalSetCompleteChiralLaw.lean`:

```text
A_lambda(omega,m) = lambda^(omega(omega-1)) (±i)^m
                  = g^choose(omega,2) (±i)^m,
g = lambda^2.
```

The Lean development proves the all-rank statements. The numerical harness is
an independent finite stress test of how the model behaves away from the
rank-two endpoint where it was derived. It does not replace the proof and does
not claim infrared recovery.

The reproducible harness is `scripts/chiral_growth_generalization.py`; its full
machine-readable output is
`results/chiral_growth_generalization/summary.json`.

## Coverage

The run used 90-digit decimal arithmetic and seed `20260719`.

- Every unlabeled finite poset through six elements: counts
  `1, 1, 2, 5, 16, 63, 318`, or 406 parents and 6,378 precursor slots.
- 128 distinct stratified random naturally labelled posets at each rank 7--12:
  768 higher-rank parents.
- Chain, antichain, and complete two-layer families at each rank 7--16:
  30 structured parents, including the 65,536 down-sets of the rank-16
  antichain.
- The certified 14-event `C8`-below-`A6` destructive-interference parent.
- Both chiralities, coupling-sign reflection, exact ordered/unordered-pair
  factorization, and the cross-pair composition law.

Seven coupling regimes were compared:

```text
canonical:    lambda = L_2                     = 1.2656250596...
shifted:      lambda = L_2 + 1                 = 2.2656250596...
subcritical:  lambda = L_2 - 1                 = 0.2656250596...
sparse:       lambda = 0
running:      lambda_n = L_2^(1/max(1,n-1))
rational:     lambda_n = (n+2)/(n+1)
harmonic:     lambda_0=lambda_1=2; lambda_n=1+H_n/(2(n-1))
```

The running schedule keeps the raw full-precursor versus one-missing-ancestor
factor fixed:

```text
lambda_n^(2(n-1)) = L_2^2.
```

## Passed structural tests

All tested parents and coupling regimes passed the following checks.

- Zero observed parent partitions: 0.
- Endpoint partition at the one-event parent: `1+i` for every coupling.
- Exact chirality conjugation checks: 1,204.
- Exact coupling-sign redundancy checks on parents: 8,428.
- Signature factorization checks: 459.
- Cross-pair composition checks: 289.
- Maximum numerical normalization error: approximately `1.3e-89` for the
  fixed couplings; the running model remained within the 90-digit arithmetic
  budget as well.

The old independently compositional character again gives exactly zero on
`C8` below `A6`. The magnitudes of the repaired partitions were:

| Coupling | Repaired partition magnitude |
|---|---:|
| canonical | `4.164e18` |
| shifted | `4.408e64` |
| subcritical | `1.465` |
| sparse | `1.414` |
| running at rank 14 | `62.29` |
| rational critical at rank 14 | `1.306e5` |
| harmonic corrected at rank 14 | `6.529e4` |

Thus the all-rank repair is not merely formal: it survives the known finite
obstruction and every additional finite parent in this test.

## Generalization result: three dynamical regimes

For diagnosis, the harness computes the fraction of the total squared raw
amplitude carried by the full-precursor (timid) slot. This is a concentration
diagnostic, not a classical transition probability. The actual singleton
quantum measure is also recorded separately and can exceed one because of
interference.

### Fixed supercritical coupling: timid runaway

The canonical and shifted couplings both satisfy `lambda > 1`. The quadratic
ancestor exponent then makes the full precursor dominate rapidly.

| Test set | canonical mean timid share | shifted mean timid share |
|---|---:|---:|
| all rank-6 posets | `0.9790168` | `0.999999818` |
| rank-12 random posets | `0.9998712` | `0.999999999999999` |

At rank 16 the canonical timid share is `0.99999927` on the chain,
`0.99998836` on the antichain, and `0.99999418` on the two-layer causet. The
shifted coupling is numerically indistinguishable from one at the displayed
precision. The effective number of raw Born-supported precursor slots tends to
one.

This is the main negative result. The canonical fixed coupling is algebraically
consistent but locally drives growth toward the timid/full-ancestry channel.
That behavior favors chain-like ordering rather than a broad manifold-like
ensemble.

### Fixed subcritical coupling: sparse runaway

The positive transcendental test value `L_2-1` satisfies `lambda < 1` and shows
the opposite phase. Its mean timid share is approximately `9.35e-36` over all
rank-6 posets and `2.77e-153` over the rank-12 random sample. At rank 16 it is
of order `1e-277` or smaller in every structured family.

More generally, a fixed `|lambda|<1` suppresses every precursor containing two
or more ancestors. The large-rank law approaches the sparse zero/one-ancestor
sector. This avoids chain collapse but also removes the multi-ancestor
structure needed for rich emergent geometry.

### Critical running coupling: diversity with interference cost

The tested running schedule approaches the critical surface `lambda=1` while
keeping adjacent high-ancestor sectors at a finite relative scale. It avoids
both fixed-coupling runaways:

| Test set | running mean timid share | largest partition condition number |
|---|---:|---:|
| all rank-6 posets | `0.3198` | `23.0` |
| rank-12 random posets | `0.2398` | `128.6` |
| rank-16 chain | `0.5889` | `1.01` |
| rank-16 antichain | `0.00243` | `652.3` |
| rank-16 two-layer | `0.0607` | `18.2` |

The running law retains many precursor sectors—the rank-16 antichain has an
effective raw Born support of roughly 12,223 slots—but the price is stronger
destructive interference. The antichain condition number of about 652 means
that the normalized answer is much more sensitive to perturbations of the raw
amplitudes than either fixed supercritical law.

## Derived scaling criterion

For a parent with `n` ancestors, the exponent difference between the full
precursor and a precursor missing one ancestor is

```text
n(n-1) - (n-1)(n-2) = 2(n-1).
```

Equivalently, in the identifiable coupling `g=lambda^2`, the cross factor is
`g^(n-1)`. Therefore finite relative weight for one individual adjacent pair
requires

```text
(n-1) log g_n = O(1),
```

or

```text
g_n = exp(kappa/(n-1) + o(1/n)),
lambda_n = exp(kappa/(2(n-1)) + o(1/n)).
```

A fixed coupling away from one is a relevant deformation: `g>1` flows toward
timid dominance, while `0<=g<1` flows toward sparse dominance. The value
`g=1` is the critical boundary, but the repo already proves that the naive
fixed character at that boundary can have exact partition zeros. A viable law
therefore needs a scale-dependent approach to the boundary together with a
mechanism controlling destructive interference. This is an edgewise criterion;
the multiplicity correction below shows that it is not an aggregate-sector
balance criterion.

The qualitative existence half is now machine-checked in
`KFCausalSetCriticalRunning.lean`. For the canonical Liouville number `L`, set

```text
lambda_n = 1 + (L - 1)/(n + 1),
g_n = lambda_n^2.
```

Every `lambda_n` is transcendental, positive, full-support, and zero-free at
every finite parent. Moreover `g_n -> 1` and
`(n+1)(g_n-1) -> 2(L-1)`. The same module proves degree at most `n(n-1)` and
coefficient height at most `2^n` for every n-parent partition polynomial, and
confines every exact cancellation across every finite parent to a countable
algebraic exceptional set. This proves that critical running and exact
zero-freeness are compatible. It does not bound how close a nonzero partition
may come to zero.

`KFCausalSetRationalCriticalRunning.lean` then proves a stronger elementary
result. Every parent polynomial has integer coefficients and constant
coefficient one, so every rational root has absolute value at most one. The
schedule

```text
lambda_n = (n+2)/(n+1),
g_n = lambda_n^2
```

is therefore zero-free for every n-parent, satisfies `g_n -> 1` and
`(n+1)(g_n-1) -> 2`, and defines one rank-dependent normalized, projectively
consistent, strongly-positive infinite-cylinder law. Clearing the denominator
proves the uniform-at-fixed-rank estimates

```text
|Z_C(lambda_n)| >= (n+1)^(-n(n-1)),
condition(C,lambda_n) <= 2^n (n+2)^(n(n-1)).
```

Thus transcendence was sufficient but not necessary. Exact zero-freeness and
an effective finite-rank stability margin now both hold; the certified margin
still deteriorates superexponentially with rank.

The value `kappa=2` is not selected by this construction.
`KFCausalSetRationalCriticalFamily.lean` proves the complete positive-rational
family

```text
lambda_n(a,b) = 1 + (a/b)/(n+1),
(n+1)(g_n(a,b)-1) -> 2a/b,
```

together with zero-freeness, projective strongly-positive dynamics, partition
margin `(b(n+1))^(-n(n-1))`, and condition bound
`2^n(b(n+1)+a)^(n(n-1))`. Consequently `kappa` is a dynamical modulus that
microphysics must select, not a prediction of the kinematic axioms.

## Multiplicity-corrected critical window

The positive-rational family also reveals that selecting a finite `kappa` is
not enough. In an `(n+1)`-antichain there is one timid/full precursor, but
there are `n+1` precursors missing one ancestor. Their incoherent labeled-slot
Born-mass ratio is exactly

```text
M_one-missing / M_timid = (n+1) / g_(n+1)^(2n).
```

The repository's unlabeled transition law first adds isomorphic slots
coherently, so the physical child-sector ratio is instead

```text
M_one-missing / M_timid = (n+1)^2 / g_(n+1)^(2n).
```

`KFCausalSetCriticalMultiplicity.lean` proves both identities and the general
asymptotic theorems

```text
n log g_(n+1) -> kappa in R
  implies
both ratios -> infinity.
```

It then applies the theorem to every positive-rational zero-free law. Thus the
whole finite-`kappa` family is edgewise critical but not coherent unlabeled-sector
critical on antichains. Holding the physical ratio finite and nonzero instead requires

```text
2n log g_(n+1) = 2log(n+1) + O(1).
```

The extra `log n` is a precursor-entropy correction. It is a change of scaling,
not a different choice of the constant `kappa`. The formal theorem rules out
the former finite-`kappa` window as the final infrared law whenever complete
precursor sectors, rather than representative edges, are the observables that
must remain balanced.

`KFCausalSetMultiplicityCorrectedRunning.lean` then proves that the corrected
window is nonempty by an explicit arithmetic construction. Let `H_n` be the
rational harmonic number and define

```text
lambda_0 = lambda_1 = 2,
lambda_n = 1 + H_n/(2(n-1))  for n >= 2,
g_n = lambda_n^2.
```

Every `lambda_n` is rational and strictly greater than one, so the universal
rational-root theorem makes every parent partition nonzero at every finite
rank. The module proves `lambda_n -> 1`, controls the quadratic error between
`log(1+x)` and `x`, and obtains the exact coherent unlabeled limit

```text
(n+1)^2/g_(n+1)^(2n) -> exp(-2*EulerMascheroniConstant).
```

It also packages the schedule as one normalized rank-dependent unlabeled law
whose finite decoherence functionals are projectively consistent and whose
infinite-cylinder functional is Hermitian, normalized, and strongly positive.
Thus zero-freeness and multiplicity-corrected balance are compatible; their
microscopic origin and all-parent conditioning remain open.

The independent exact-binomial scan tracks the convergence and conditioning:

| rank | coherent one-missing/timid ratio | condition | `log(condition)/rank` |
|---:|---:|---:|---:|
| 20 | `0.4133` | `2.019` | `0.0351` |
| 40 | `0.3856` | `1.924` | `0.0164` |
| 80 | `0.3627` | `1.861` | `0.0078` |
| 120 | `0.3522` | `1.834` | `0.0051` |
| 160 | `0.3460` | `1.819` | `0.0037` |
| 200 | `0.3418` | `1.810` | `0.0030` |

The ratio moves toward `exp(-2gamma) ≈ 0.3152`, as proved. The decreasing
log-condition rate is encouraging but remains finite evidence, not a uniform
subexponential all-parent theorem.

## Coefficient-structure result

The hoped-for universal positivity mechanism fails at the first nontrivial
rank. `KFCausalSetPartitionCoefficientStructure.lean` proves exactly that the
two-antichain real parent polynomial has constant coefficient `1` and
quadratic coefficient `-1`. Hence no all-parent nonnegative-coefficient theorem
can improve the arithmetic condition bound.

The exhaustive coefficient census strengthens the diagnosis empirically:

| rank | parents | mixed-sign real coefficients | nonunimodal absolute coefficients |
|---:|---:|---:|---:|
| 2 | 2 | 1 | 0 |
| 3 | 5 | 4 | 0 |
| 4 | 16 | 15 | 0 |
| 5 | 63 | 62 | 0 |
| 6 | 318 | 317 | 26 |

The rational representative nevertheless behaves vastly better than its
worst-case formal estimate over the tested range: its maximum condition number
is `5.97` over all rank-six parents and `14.87` in the rank-twelve random
sample. At rank sixteen it is `1.000001`, `27.39`, and `4.02` on the chain,
antichain, and two-layer families respectively. These are finite observations,
not an asymptotic theorem. An efficient antichain scan shows eventual growth,
so the gap to subexponential control remains real.

The exact-binomial `O(n)` antichain scan makes the tradeoff visible at rank
200:

| displacement `c` | `kappa=2c` | condition | timid raw Born share |
|---:|---:|---:|---:|
| `1/2` | `1` | `3.69e31` | `1.22e-13` |
| `1` | `2` | `5.83e13` | `1.89e-2` |
| `2` | `4` | `61.5` | `0.927` |

Larger `kappa` suppresses the observed cancellation but simultaneously drives
the antichain toward the timid sector. This is evidence for a conditioning--
concentration tradeoff, not yet a theorem: the physically useful selector must
control interference without simply restoring timid runaway.

## Honest conclusion

The newest model generalizes successfully as a normalized, Bell-causal,
strongly-positive finite and infinite-cylinder construction, and now admits a
positive-rational family of explicit zero-free trajectories in the edgewise
critical window. The exact multiplicity theorem shows that every finite-`kappa`
member nevertheless fails coherent unlabeled antichain balance, while the harmonic
rational construction gives a zero-free, strongly-positive trajectory in the
logarithmically corrected window with limiting ratio `exp(-2gamma)`. It does not
yet derive that trajectory from microscopic physics or prove subexponential
all-parent stability. Universal coefficient positivity is now ruled out.
The test replaces the former question “which constant coupling?” with the
sharper problem:

> Derive a refinement-covariant, multiplicity-corrected critical trajectory
> from microphysics and keep its all-parent partition condition numbers
> subexponentially controlled.

The next mathematical target is an RG transformation on the effective
coupling and interference data, not another constant-coupling selection rule.
