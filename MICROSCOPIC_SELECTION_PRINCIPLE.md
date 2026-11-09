# Microscopic selection after the chain-collapse obstruction

The strongest new result is a separation of **geometric selection** from
**amplitude normalization**. Changing centered phases in the harmonic law
cannot prevent ordering fraction tending to one. But simultaneous coherent
and Born normalization permits *every* finite probability distribution. The
geometry therefore needs a selection principle for the probabilities, beyond
the positive radial completion and its phase variants.

The proposed overarching principle is **refinement consistency**: increasing
resolution should preserve meaningful probability for macroscopically different
causal past volumes. Occasional branching is insufficient. A sufficient,
testable implementation is a bound on the spread of effective free energies
between causal-volume cuts, after accounting for their multiplicities.

This is a proposed additional physical principle, not a consequence of
covariance, the Born rule, the existing spectator action, or Einstein's
equations. Below it gives an explicit full-support, non-atomic alternative
and an all-rank anti-collapse criterion. It does **not** select four-dimensional
geometry, and the neutral alternative fails strict raw Bell causality.

## What is checked, and what remains analytic

`UnifiedTheory/Audit/KFCausalBornMicroscopicSelection.lean` proves:

- every finite probability vector admits complex amplitudes with coherent
  sum one and exactly those Born probabilities;
- positive probabilities additionally give full amplitude support;
- a centered phase change alters each probability by at most `4/K`;
- the exact ordering-fraction update identifying geometric drift;
- a probability floor on causal-volume cuts gives order-`n` lower bounds
  for both the expected ancestors and expected new incomparable pairs.

The infinite-history phase obstruction, insertion-measure combinatorics,
and stochastic limits below are analytic proofs. Their identification with
Lean causal-trajectory measures is **not** formalized in this module.

`scripts/microscopic_selection_audit.py` checks all 88 unlabeled parents
through rank 5 using exact rational combinatorics and 256-bit Arb balls.
It independently enumerates linear extensions, verifies relabeling,
aggregation, normalization, and chirality, and checks large chains through
rank 100,000. Results are in `data/microscopic_selection_audit.json`.

## 1. The observable the microscopic rule must control

Let `R_n` count strict relations in the parent, and let a new maximal event
have `omega_n` ancestors. Write

\[
r_n=R_n/\binom n2,\qquad D_n=n-\omega_n.
\]

`D_n` is the number of new incomparable pairs. Exactly,

\[
R_{n+1}=R_n+\omega_n,\qquad
I_N=\sum_{n<N}D_n,
\]

and, for `n>1`, the checked algebraic identity gives

\[
\mathbb E[r_{n+1}-r_n\mid\mathcal F_n]
=\frac{2}{n+1}\left(\frac{\mathbb E[\omega_n\mid\mathcal F_n]}n-r_n\right).
\]

Nonzero escape probability, infinitely many branching events, and a
non-atomic history measure can all coexist with `I_N=o(N^2)` and `r_N -> 1`.
The relevant condition concerns **how many incomparable pairs** those births
create, averaged over growth. A uniform sufficient condition is

\[
\delta n\le\mathbb E[\omega_n\mid\mathcal F_n]
\le(1-\delta)n,\qquad \delta>0.
\tag{1}
\]

Bounded-increment martingale concentration then implies, almost surely,
`delta <= liminf r_N <= limsup r_N <= 1-delta`. Indeed the centered sum of
the `omega_n` has increments of interval length at most `n`; the probability
of a deviation of order `N^2` is exponentially small in `N`. Summing those
bounds and applying Borel--Cantelli gives a vanishing normalized fluctuation.
Condition (1) is sufficient, not necessary, and says nothing by itself about
interval statistics, topology, locality, curvature, or manifoldlikeness.

## 2. Why changing the centered phase cannot repair the harmonic law

Let `b^+` be the canonical harmonic positive radial amplitude vector on the
`K` physical children. Put `u=1/K`, `c_j=b^+_j-u`. Then

\[
\sum_jc_j=0,\qquad \sum_j|c_j|^2=1-u,\qquad |c_j|\le1.
\]

For any unit complex `z`, the rotated vector is `b^z_j=u+z c_j`.
Both normalizations remain valid, and

\[
|b^z_j|^2-|b^+_j|^2
=2u\operatorname{Re}((z-1)c_j),\qquad
\big||b^z_j|^2-|b^+_j|^2\big|\le4/K.
\tag{2}
\]

These statements are checked in Lean. The bound also holds coordinatewise
if each `c_j` has its own unit phase, provided the resulting vector still
has coherent sum one. Thus the following argument is not restricted to a
fixed common angle: history-dependent choices also satisfy the bounds.

Use the analytic all-parent estimates from
[the eventual-collapse argument](HARMONIC_BORN_EVENTUAL_CHAIN_COLLAPSE.md):
there are constants `c0>0`, `A0<infinity`, and a fixed rank threshold such that

- every parent has canonical timid probability at least `c0`;
- a parent with a unique maximum has canonical non-timid probability at
  most `A0/n^2`;
- every parent has at least `n+1` distinct physical children.

Equation (2) therefore gives, uniformly over phase choices and histories,
timid probability at least `c=c0/2` at sufficiently large ranks. At parents
with a unique maximum, escape is at most

\[
A_0/n^2+4/(n+1)\le A/n,\quad A=A_0+4.
\]

A maximal birth leaves a unique maximum **if and only if** it is timid:
a proper downset omits a maximal parent event, which stays maximal alongside
the new event. Let `q_n` be the probability the rank-`n` parent lacks a unique
maximum. Conditional probabilities give

\[
q_{n+1}\le(1-c)q_n+A/n.
\]

Choose a sufficiently large `N`, then `B>=max(N,2A/c)` with `N+1>=2/c`.
Induction shows `q_n<=B/n` for all `n>=N`: the right side is at most
`(1-c/2)B/n <= B/(n+1)`. Consequently

\[
\mathbb E D_n\le n\Pr(\text{non-timid at }n)
=nq_{n+1}\le B,
\qquad \mathbb E I_N=O(N).
\]

Markov's inequality at `N=2^k` has a summable bound for
`I_N/N^2 > epsilon`. Borel--Cantelli gives convergence to zero on that
subsequence. Monotonicity of `I_N` extends it to every `N`.

**Analytic conclusion:** every normalized centered-phase modification of
this harmonic amplitude profile has `r_N -> 1` almost surely. This proof
uses the earlier analytic counting estimates; the complete stochastic
statement is not yet a Lean theorem.

### A particularly revealing failed repair

The negative radial branch is `b^- = 2u-b^+`. On any all-timid suffix the
unique-maximum estimate gives `b^+_t=1+O(1/n)` and canonical escape
`O(1/n^2)`. On a fixed finite prefix followed by a chain, the number of
downsets is `n+O(1)`, so `n+1<=K<=n+O(1)` and `u=1/n+O(1/n^2)`.
Equation (2) now reads

\[
1-|b^-_t|^2
=1-|b^+_t|^2+4u\operatorname{Re}(b^+_t-u)
=4/n+O(1/n^2).
\]

Thus any eventual-timid path has zero probability. Any path with infinitely
many non-timid steps also has zero probability, because each such step has
probability at most `1-c` at large ranks. The negative branch is therefore
non-atomic, while its ordering fraction still tends to one.

The certified chain calculation illustrates the mechanism:

| Parent rank | Centered phase | Escape probability (approx.) | Expected new incomparable pairs (approx.) |
| ---: | --- | ---: | ---: |
| 100,000 | positive | 3.15461e-11 | 4.73192e-11 |
| 100,000 | negative | 3.99992e-5 | 1.999991 |
| 100,000 | quarter turn | 1.99996e-5 | 0.999996 |

The negative branch creates only order-one expected incomparable pairs per
birth on a chain. A nondegenerate pair density needs order `n` on average.
An individual phase can have zeros at early ranks; arbitrary-phase full
support is not assumed in the obstruction.

## 3. Normalization leaves the Born distribution free

For `0<=q<=1`, define

\[
\alpha(q)=q+i\sqrt{q(1-q)},\qquad \beta(q)=1-\alpha(q).
\]

Then `alpha+beta=1`, `|alpha|^2=q`, and `|beta|^2=1-q`.
Given any finite positive probability vector `p_1,...,p_K`, set
`s_j=sum_{l>=j}p_l`, `q_j=p_j/s_j`, and recursively split the remaining
amplitude:

\[
b_j=\left(\prod_{l<j}\beta(q_l)\right)\alpha(q_j)\ (j<K),
\qquad b_K=\prod_{l<K}\beta(q_l).
\]

The sum telescopes to one and `|b_j|^2=p_j` exactly. Lean proves the
existence theorem also for distributions containing zeros. Conjugating all
splits gives the reflected chirality. For unlabeled children, ordering by
their canonical finite relation codes gives one isomorphism-invariant
implementation, with zero amplitudes assigned outside physical support.

**Boundary:** this ordering is an extra phase convention. Different
orderings can change interference observables. This construction establishes
compatibility with both scalar normalizations; it does not derive a causal
action, the old `i^m` phase pattern, quantum locality, or unitary dynamics.

## 4. An intrinsic reference measure with sustained causal diversity

For a finite parent `C` with `n` events, let `e(C)` count linear extensions.
Choose a linear extension uniformly, choose one of its `n+1` cuts uniformly,
take the events before the cut as the new event's precursor, and forget the
chosen extension. The resulting probability of downset `D` is

\[
\nu_C(D)=\frac{e(D)e(C\setminus D)}{(n+1)e(C)}.
\tag{3}
\]

The counts refer to induced orders. Every extension with prefix set `D`
is a concatenation of an extension of `D` and one of its complement. For
each size `j`, every extension has exactly one such prefix, hence

\[
\sum_{|D|=j}e(D)e(C\setminus D)=e(C),\qquad
\Pr_\nu(|D|=j)=1/(n+1).
\]

This proves normalization, positive probability for every precursor,
invariance under order isomorphism, and `E omega_n=E D_n=n/2`.
Aggregate these **probabilities** over precursor fibers to obtain a law on
unlabeled children. The preceding section then constructs amplitudes on
those children with exactly that law. It does not coherently sum the
auxiliary extension records and then square the result.

Every physical child has one fixed ancestor count, determined by the
increase in relation count. Its probability is therefore at most `1/(n+1)`;
the timid child has exactly that probability. Every depth-`N` history has
probability at most `1/N!`, so the infinite law has no atoms.

Because the conditional distribution of `omega_n` is the same uniform law
regardless of past history, the `omega_n` are independent across ranks.
For `N>=2`,

\[
\mathbb E r_N=1/2,\qquad
\operatorname{Var}(r_N)=\frac{2N+5}{18N(N-1)},\qquad
r_N\longrightarrow1/2\quad\text{almost surely}.
\]

The variance follows by summing `Var(omega_n)=n(n+2)/12`;
bounded-increment concentration proves the almost-sure statement.
This is a parameter-free anti-collapse benchmark. The value `1/2` matches
the flat two-dimensional interval ordering statistic, but does **not**
establish a two-dimensional continuum. It does not match the flat
four-dimensional interval value `1/10`, obtained by evaluating twice the
ratio in equation (2.2) of
[Abajian and Carlip](https://arxiv.org/html/1710.00938v1#S2).
No dimension has been selected by an independent geometric argument.
For background on the limitations of
single-observable continuum diagnostics, see
[Surya's causal-set review](https://arxiv.org/abs/1903.11544).

## 5. A variational selection principle and its precise guarantee

Update: the [sharp contrast theorem](CAUSAL_CUT_CONTRAST_BOUND.md) improves
the sufficient lower ordering-fraction estimate below from `e^(-B)/2` to
`1/(1+e^(B/2))`. Its all-rank finite cut-mean inequality is Lean-checked;
the history assembly remains analytic. Matching the flat 4D causal-diamond
statistic requires `B>=log 81` in this class, and matching that statistic
alone does not establish geometric recovery.

The reference measure is not forced by general covariance. Its additional
choice is uniformity over compatible total orders and causal cuts. It offers
a concrete way to separate causal-volume alternatives from their different
numbers of microscopic realizations.

Given an intrinsic dimensionless **real** action score `S_C(D)`, minimize

\[
\mathcal J_C(P)=\mathbb E_P S_C+D_{\mathrm{KL}}(P\Vert\nu_C).
\]

The unique minimizer is

\[
P_C(D)=\frac{\nu_C(D)e^{-S_C(D)}}{Z_C},
\qquad Z_C=\sum_D\nu_C(D)e^{-S_C(D)}.
\tag{4}
\]

Indeed `J_C(P)=D_KL(P||P_C)-log Z_C`. Any action coefficient or inverse
temperature must be supplied as part of `S`; the notation does not derive
its physical value. This statistical score is not automatically the
Lorentzian action appearing in an oscillatory quantum path sum.

The *effective* action on a causal-volume cut is

\[
F_C(j)=-\log\mathbb E_{\nu_C(\cdot\mid |D|=j)}e^{-S_C(D)}.
\]

Thus `Pr_P(|D|=j)=e^{-F_C(j)}/sum_l e^{-F_C(l)}`. A sufficient selection
condition, uniform over parents and sufficiently large ranks, is

\[
\max_j F_C(j)-\min_j F_C(j)\le B<\infty.
\tag{5}
\]

It follows directly that

\[
\frac{e^{-B}}{n+1}\le\Pr_P(|D|=j)\le\frac{e^B}{n+1},
\qquad
\frac{e^{-B}}2 n\le\mathbb E_P\omega_n,\mathbb E_PD_n.
\]

Taking `delta=e^{-B}/2` establishes (1), excludes both chain and antichain
pair-density collapse, and bounds every child probability by `e^B/(n+1)`.
Consequently every infinite history has zero probability. For finite real
scores the law also retains full finite support. These guarantees survive
the coherent/Born lift, since that lift preserves probabilities exactly.

Condition (5) concerns free energy **after** averaging within each cut;
it does not require every microscopic action value to have bounded spread.
It is sufficient and deliberately stronger than a necessary continuum
condition. It could exclude physical models with sharply localized birth
volumes, so it must itself be physically justified, not declared universal.

The script implements (4) for positive rational `exp(-S)` and checks an
order-sensitive example `exp(-S(D))=1+m(D)/(1+|D|)`, where `m(D)` counts
maximal precursor events. These weights lie in `[1,2)`, so `B=log 2`
suffices: both expected pair counts are at least `n/4`, and almost-sure
liminf/limsup ordering fractions lie in `[1/4,3/4]`. The finite audit checks
these inequalities exactly on every enumerated parent. This illustrative
score is not selected by the theory; its bounds also exclude the flat 4D
interval ordering statistic. It demonstrates stability under a nonconstant,
order-dependent perturbation of the neutral reference.

The harmonic chain makes the offending scale explicit. Between precursors
with `omega` approximately `xn` and `yn`, the raw log-magnitude difference is

\[
(\omega_x(\omega_x-1)-\omega_y(\omega_y-1))\log\lambda_n
=\tfrac12(x^2-y^2)n\log n+O(n).
\]

It diverges for fixed different volume fractions: refinement creates an
overwhelming preference for including the entire past. Phase rotation cannot
remove that amplitude-magnitude hierarchy. A viable new rule must change
the magnitude selection or the microscopic reference measure so that actual
coarse causal alternatives remain nondegenerate. Equation (5) is one
concrete route; matching a desired ordering fraction by fitting `S` would
not constitute a derivation of dimension.

## 6. Causality and covariance remain substantive constraints

Order-isomorphism covariance is weaker than the natural-labeling path
condition and spectator-ratio condition of
[Rideout and Sorkin](https://arxiv.org/abs/gr-qc/9904062).
The reference law (3) fails those stronger tests already at small ranks:

- On the two-antichain, `P(empty)=1/3` and `P(a specified singleton)=1/6`.
  Their ratio is `1/2`. Deleting the spectator gives the one-event parent,
  where the same ratio is `1`. This violates raw classical Bell causality.
- Two specified naturally labeled paths to a two-chain plus isolated point
  have probabilities `1/12` via the antichain parent and `1/6` via the chain
  parent. Thus strict path-probability covariance fails as well.

The rank-running harmonic raw law also fails strict spectator deletion:
take a two-chain plus one isolated spectator, and compare the whole
two-chain precursor against the empty precursor. The amplitude ratios are

\[
i\lambda_3^2=i\,1225/576,
\qquad i\lambda_2^2=i\,49/16
\]

before and after deleting the spectator. They differ. The repository's
Bell theorem for a **fixed** signature function does not imply Bell causality
for the rank-running schedule. This counterexample concerns raw amplitudes;
it does not assert an identified Bell test for the corrected child measure.

The older `AUDIT_COVARIANCE.md` already records separate no-go results for
the action-phased pi/4 class. Those are a different law and cannot substitute
for tests of either construction here. A proposed quantum replacement for
the strict conditions needs a precise decoherence-functional statement and
proof. Calling a child law covariant is not enough.

## Research consequence

There is now a sharper target for microscopic selection: derive a causal
action and reference measure whose **conditional causal-volume free energies**
stay nondegenerate under refinement, while satisfying the intended quantum
causality and covariance conditions. The normalization problem has a general
solution and need not force the harmonic magnitude profile. The neutral
reference proves that full support, both scalar normalizations, and sustained
pair diversity are compatible; its explicit failures prevent mistaking that
existence result for a completed physical theory.

Reproduce the finite audit with:

```sh
python3 scripts/microscopic_selection_audit.py --output data/microscopic_selection_audit.json
lake build UnifiedTheory.Audit.KFCausalBornMicroscopicSelection
```
