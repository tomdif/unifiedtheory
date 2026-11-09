# A sharp contrast bound for microscopic causal selection

Date: 2026-09-09

There is now an all-rank, Lean-checked limit on how strongly a bounded
selection action can change the ancestor-count statistic. If effective
causal-cut weights have maximum-to-minimum ratio at most `A`, their mean
ancestor fraction cannot asymptotically fall below

\[
\boxed{\rho_A=\frac{1}{1+\sqrt A}.}
\]

The bound is sharp. In particular, obtaining the flat four-dimensional
causal-diamond ordering statistic `r -> 1/10` in this class requires
`A >= 81`, or effective free-energy spread at least `log 81`.
This is a constraint on a proposed microscopic law, not a physical
derivation selecting 81 or four dimensions.

The result concerns the statistics of actual maximal births. It goes beyond
the [transport reconstruction schedule](PROTECTED_SELECTION_CONVERGENCE.md),
but does not solve the physical action, covariance, or continuum questions.

## 1. The class of laws being bounded

For a parent with `n` events, let `j=0,...,n` be the number of ancestors of
the new maximal event. Suppose its marginal distribution is

\[
P_C(j)=\frac{w_C(j)}{\sum_{l=0}^n w_C(l)},\qquad
\frac{\max_j w_C(j)}{\min_j w_C(j)}\le A.
\]

Rescaling all weights leaves the law unchanged, so take `1 <= w_C(j) <= A`.
No monotonicity, smoothness, or independence from the parent is assumed.

For the [insertion reference](MICROSCOPIC_SELECTION_PRINCIPLE.md), the neutral
cut law is uniform. A real score `S_C(D)` on downsets induces

\[
w_C(j)=\mathbb E_{\nu_C(\cdot\mid |D|=j)}e^{-S_C(D)},\qquad
F_C(j)=-\log w_C(j).
\]

Thus `max F_C - min F_C <= B` implies `A=e^B`. This is the spread of the
effective free energy after averaging within each cut. It is not a bound
on every microscopic score, nor a derived Lorentzian gravitational action.

## 2. Exact finite optimization and the square identity

Write `mu(w)=sum_j j w_j / sum_j w_j`. For any trial value `a`, the minimum
of the centered linear expression `sum_j w_j(j-a)` over `1<=w_j<=A` uses

\[
v_j(a)=\begin{cases}A,&j<a,\\1,&j\ge a.\end{cases}
\]

Taking `a=mu(w)` proves `mu(v(a))<=mu(w)`. Therefore a global optimizer
can always be found among the `n+2` threshold choices
`w_j=A` for `j<m`, `w_j=1` for `j>=m`.

Put `L=n+1` and `A=s^2`, with `s>=1`. The mean for threshold `m` is

\[
\mu_m=\frac{L(L-1)+(s^2-1)m(m-1)}{2[L+(s^2-1)m]}.
\]

Completing the square gives the exact identity

\[
\mu_m=\frac{L}{1+s}-\frac12+
\frac{(s-1)[L-(1+s)m]^2}{2(1+s)[L+(s^2-1)m]}.
\]

The last term is nonnegative. Combining the threshold reduction and this
identity gives the formal all-rank theorem

\[
\boxed{\mathbb E_C\omega_n\ge
\frac{n+1}{1+\sqrt A}-\frac12.}
\tag{1}
\]

Reflection `j -> n-j` gives the same bound on the number of new incomparable
pairs. The lower-bound theorem, the threshold reduction, the finite mean
formula, and the square identity are all proved in
`UnifiedTheory/Audit/KFCausalBornCutWeightEnvelope.lean`. The reflected
upper bound is a mathematical corollary used here, not an additional named
Lean theorem.

For `A>1`, the real-variable threshold mean decreases up to
`m=L/(1+sqrt A)` and increases afterwards. The exact finite optimizer is
therefore among the floor and ceiling of that value. The script proposes
nearby integer thresholds and then checks an exact zero centered-objective
certificate; floating point is not trusted to certify optimality.

## 3. An overarching principle: optimal selection exhausts its allowed bias

Let `a` be a self-consistent threshold mean. Every allowed weight vector
satisfies the exact regret identity

\[
\begin{aligned}
(\sum_jw_j)(\mu(w)-a)
={}&\sum_{j<a}(A-w_j)(a-j)\\
&+\sum_{j\ge a}(w_j-1)(j-a).
\end{aligned}
\tag{2}
\]

All terms are nonnegative. Equality forces `w_j=A` below the cutoff and
`w_j=1` above it, except for a possible point exactly at the cutoff.
Lean proves this identity and the endpoint-rigidity theorem for arbitrary
finite score sets, not just integer ancestor counts.

Together with the protected-record floor, this gives a practical selection
principle: **a law must have both freedom within its protected records and
enough allowed bias to use that freedom.** Exact normalization alone supplies
neither condition. Near saturation of (1) also constrains the shape of the
effective action; arbitrary small smooth corrections cannot saturate it.

For a fixed continuum profile on normalized cuts `x in [0,1]`, exact
saturation at `A=81` requires the step profile `w=81` below `x=1/10` and
`w=1` above it, up to sets of measure zero. This follows from the integral
version of the nonnegative slack identity (2). A fixed continuous profile
with that contrast cannot attain equality; a sequence can approach the step.
This continuum-profile statement is analytic, not a formal limit theorem
about an independently derived action.

## 4. Consequences for growing causal histories

Let `R_N=sum_{n=0}^{N-1} omega_n` count strict relations after `N` maximal
births, and `r_N=R_N/binom(N,2)`. Assume the same contrast bound applies
conditionally at every parent. Summing (1) gives, for `N>=2`,

\[
\mathbb E r_N\ge\rho_A-\frac{1-2\rho_A}{N-1},\qquad
\mathbb E r_N\le1-\rho_A+\frac{1-2\rho_A}{N-1}.
\]

This does not require independent births. If `mathcal F_n` records the
history, the differences
`omega_n-E(omega_n|mathcal F_n)` are martingale differences with absolute
value at most `n`. Azuma's inequality gives the conservative lower-tail bound

\[
P\left(r_N<\rho_A-\frac{1-2\rho_A}{N-1}-\epsilon\right)
\le\exp\left[-\frac{3\epsilon^2N(N-1)}{4(2N-1)}\right].
\]

The analogous upper tail is also summable in `N`. Applying Borel--Cantelli
for rational positive `epsilon` proves

\[
\rho_A\le\liminf r_N\le\limsup r_N\le1-\rho_A
\quad\text{almost surely}.
\tag{3}
\]

An eventual uniform contrast bound is enough for the same limits; finitely
many initial ranks do not contribute in the limit. This probability-space
and martingale assembly is analytic. Lean proves the finite conditional
inequality (1), not a full theorem for an identified causal-trajectory measure.

The bound substantially improves the earlier sufficient estimate `1/(2A)`:

| Contrast `A` | Earlier lower bound | Sharp asymptotic lower bound |
| ---: | ---: | ---: |
| 1 | 0.5 | 0.5 |
| 2 | 0.25 | 0.41421356 |
| 4 | 0.125 | 1/3 |
| 9 | 1/18 | 1/4 |
| 25 | 1/50 | 1/6 |
| 81 | 1/162 | 1/10 |

In particular, the earlier illustrative weights
`1+m(D)/(1+|D|)` have contrast below 2. Their guaranteed asymptotic ordering
range improves from `[1/4,3/4]` to
`[1/(1+sqrt 2),sqrt 2/(1+sqrt 2)]`.

## 5. What the four-dimensional comparison does and does not say

For a densely sprinkled flat `d`-dimensional causal diamond, the
Myrheim--Meyer relation gives the ordering fraction

\[
r_d=\frac{\Gamma(d+1)\Gamma(d/2)}{2\Gamma(3d/2)}.
\]

This is twice the relation-count ratio in
[Abajian and Carlip, equation (2.2)](https://arxiv.org/html/1710.00938v1#S2).
At `d=4` it is exactly `1/10`. Requiring that limit in (3) implies

\[
\frac1{1+\sqrt A}\le\frac1{10}
\quad\Longrightarrow\quad A\ge81,\quad B\ge\log81\approx4.394449.
\]

This compares like regions: it is a necessary condition for the modeled
grown regions to have the flat causal-diamond statistic. A general curved
four-dimensional spacetime, or a different shape of growing region, need
not have global ordering fraction `1/10`. A bound on global cuts alone is
not a theorem excluding four-dimensional local intervals.

Even the exact matching statistic is far from sufficient. Take ten disjoint
chains, each of length `m`. They have

\[
r=\frac{m-1}{10m-1}\longrightarrow\frac1{10},
\]

but their longest chain has `N/10` events and each nontrivial order interval
is a chain. The script checks this explicit counterexample. It rules out
identifying a single calibrated ordering statistic with geometric emergence.

## 6. A sharp birth-law witness, with its failures exposed

Let `p_n(j)` be an optimal threshold cut law with `A=81`. Define a probability
on precursor downsets of any finite parent by

\[
P_C(D)=(n+1)p_n(|D|)\nu_C(D).
\]

The insertion reference has uniform cut masses, so this is normalized and
has exactly the prescribed cut law. Aggregate probabilities over unlabeled
children, then apply the finite coherent/Born lift. This gives full support
and scalar binormalization at every finite parent.

The rank-wise mean satisfies `mu_n/n -> 1/10`, by the square identity with
a rounded optimal threshold. The martingale argument therefore gives
`r_N -> 1/10` almost surely. Every child probability is at most
`81/(n+1)`, so the factorial history bound also excludes infinite atoms.
These all-rank birth-realization and stochastic statements are analytic;
the finite audit verifies the construction on all 88 parents through rank 5.

The protected correction can then preserve `(ancestor count, frontier hits)`
while lowering the remaining shape observable. All 88 parents pass exact
record-law checks and Arb amplitude lifts; 48 permit strict shape improvement.
Since the whole cut law is protected, this correction retains the calibrated
ordering-fraction limit.

The parameter 81 was chosen to saturate a desired statistic. It is not
independently selected by the repository. The witness also fails strict raw
classical Bell causality: on the two-antichain, the specified-singleton to
empty-precursor probability ratio is `1/162`; removing the spectator changes
it to `1/81`. These are the stronger classical causality conditions associated
with [Rideout--Sorkin sequential growth](https://arxiv.org/abs/gr-qc/9904062),
not merely invariance under order isomorphism. The scalar amplitude lift does
not repair this failure or establish the required quantum replacement.

The [causality follow-up](COVARIANT_QUOTIENT_SELECTION.md) generalizes this
witness: full support, order-isomorphism invariance, and parent-independent
cut marginals contradict strict classical Bell already at rank two. Any
replacement retaining that condition must allow parent-dependent cuts.

## Verification and next physical obligation

The new Lean module prints eight main theorem audits, using only `propext`,
`Classical.choice`, and `Quot.sound`. It contains no `sorry` or trusted
numerical search. The exact script checks:

- 32,776 global-optimality certificates, through rank 4,096 at eight contrasts;
- 224 independent HiGHS linear programs and 6,138 exhaustive weight vertices;
- exact square identities at selected ranks up to 1,000,000;
- all 88 small parents, protected shape corrections, and scalar amplitude lifts;
- the Bell counterexample and the ten-chain geometric counterexample.

Reproduce:

```sh
python3 scripts/causal_cut_contrast_audit.py --output data/causal_cut_contrast_audit.json
lake build UnifiedTheory.Audit.KFCausalBornCutWeightEnvelope
lake build
git diff --check
```

The next physical obligation is an independently justified action/reference
whose cut bias, protected records, quantum causality, and multi-observable
interval geometry are compatible. This result gives a sharp necessary
strength test for that action and a finite way to reject inadequate proposals.

Validation completed on 2026-09-09: the exact/Arb/LP audit passes, all seven
recorded source hashes match, the full integrated Lean build passes
(8,910 jobs), and `git diff --check` passes. All eight printed theorem
audits use only the three standard axioms listed above.
