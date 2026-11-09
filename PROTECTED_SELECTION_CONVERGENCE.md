# Protected selection: feasibility, convergence, and growth

Date: 2026-09-09

The [moment-preserving correction](NAVIER_STOKES_GR_TRANSFER.md) now has two
further results: an optimizer-independent obstruction to growth descent,
and convergence for the repository's actual order-derived bridge-census
defect. Repeated selection recovers the transport encoded in a given bridge
order. It does not prove that a microscopic birth law generates that order,
or that its continuum limit satisfies general relativity.

The guiding principle is: **selection can remove only the error that is
free to vary within the records it must preserve.** Conservation constraints
therefore need a feasibility check before a correction is designed.

## 1. A sharp feasibility criterion

Let `p_i > 0` be a normalized law on finitely many alternatives, `H_i` a
protected record, and `G_i` their defect. Set

\[
m_h=\sum_{H_i=h}p_i,\qquad
g_h=\min_{H_i=h}G_i,\qquad
L_H(p,G)=\sum_h m_hg_h,
\]

where only nonempty record classes occur. Every nonnegative law `q`
preserving the complete distribution of `H` satisfies

\[
\mathbb E_qG\ge L_H(p,G).
\]

This bounds all permitted selectors, including selectors outside the affine
or exponential families. It is sharp: within each record put all its mass
on minimum-defect alternatives. A tie-invariant choice is

\[
q_i^*=\begin{cases}
m_{H_i}\,p_i/\sum_{j:H_j=H_i,\ G_j=g_{H_i}}p_j,&G_i=g_{H_i},\\
0,&\text{otherwise}.
\end{cases}
\]

For a full-support law, mix `q*` with `p`:
`q(theta)=(1-theta)q*+theta p`, with `0<theta<1`. This preserves every
record mass and approaches the floor as `theta -> 0`. Consequently,

\[
\boxed{\exists\ q>0\text{ preserving }H,\quad
\mathbb E_qG<D_{\rm parent}
\quad\Longleftrightarrow\quad L_H(p,G)<D_{\rm parent}.}
\]

For sufficiency, if `E_p G > L`, take
`theta=min(1/2,(D_parent-L)/(2(E_p G-L)))`; if `E_p G=L`, the original law
already works. Full support prevents attainment of the exact floor whenever
any alternative has a defect strictly above its record's minimum.

`KFCausalCSpecProtectedSelectionConvergence.lean` proves the general lower
certificate, preservation of record observables, the resulting obstruction
to growth descent, and the strict full-support bound. The minimum-attainer
construction and the displayed equivalence are analytic here, with exact
rational implementations and checks in the accompanying script; they are
not claimed as additional Lean theorems.

This improves on the local conditional-variance test. Positive variance says
that a law can be improved relative to itself. The floor says whether even
the best possible improvement can beat the parent's defect.

## 2. Applying the criterion to actual maximal births

The earlier benchmark counted newly created causal intervals with exactly
one internal event. Let `I_1(C)` count all such intervals in the parent.
Adding a maximal event with precursor downset `D` gives

\[
I_1(C+D)=I_1(C)+\Delta I_1(C,D),\qquad \Delta I_1(C,D)\ge0.
\]

The new maximal event cannot lie between two old events, so every old
interval retains its interior. This is an all-rank combinatorial obstruction:
no birth selector can make this absolute interval count decrease.

The exact audit enumerates all 88 unlabeled parents through rank 5, using
the insertion reference and protecting the joint record `(ancestor count,
maximal-frontier hits)`. It computes the sharp floor over aggregated
unlabeled children. An independent endpoint census checks the displayed
growth decomposition for each child.

| Parent rank | Parents | Improvement over reference possible | Strict positive minimum absolute drift | Strict density descent possible |
| ---: | ---: | ---: | ---: | ---: |
| 0 | 1 | 0 | 0 | 0 |
| 1 | 1 | 0 | 0 | 0 |
| 2 | 2 | 0 | 1 | 0 |
| 3 | 5 | 1 | 4 | 1 |
| 4 | 16 | 6 | 14 | 6 |
| 5 | 63 | 41 | 59 | 36 |

Thus 48/88 allow improvement over the reference, yet **0/88 allow negative
absolute drift**, and 78/88 force strictly positive drift even at the
optimal boundary law. The final column uses the separately defined density
`I_1(C)/binom(|C|,3)`, set to zero below rank 3. It permits strict descent
on 43/88 parents; the script constructs full-support laws witnessing every
positive case. This is a dilution-sensitive diagnostic, not a curvature
defect, a dimension estimator, or an independently selected physical action.

Ancestor-count protection also retains the insertion law's ordering-fraction
limit `1/2`. Changing this within-record selector cannot turn that benchmark
into a derivation of four-dimensional geometry.

## 3. A convergence rate for the actual bridge-census defect

For each of the five `fourState` edges, the candidate transport is one of
six permutations of three directions. The existing definition is

\[
G_e(\tau)=18-\operatorname{permScore}
\bigl(b,\ b\circ\sigma_e^{-1},\ \tau\bigr),
\qquad \sigma_e=\texttt{fourState.perm e}.
\]

The profiles `(2,-1,-1)`, `(-1,2,-1)`, `(-1,-1,2)` have Gram entries 6
on the diagonal and -3 off it. Hence

\[
G_e(\tau)=9\bigl(3-\#\operatorname{Fix}(\sigma_e^{-1}\tau)\bigr).
\]

The exact six-candidate defect census is:

| Relative permutation | Candidates | Defect | Selection weight |
| --- | ---: | ---: | ---: |
| Identity | 1 | 0 | 1 |
| Transposition | 3 | 18 | 1/2 |
| Three-cycle | 2 | 27 | 1/4 |

Use the positive weight `w_e(tau)=1-G_e(tau)/36` and repeatedly multiply
and normalize the law within each edge. The constant 36 is a conservative
algorithmic choice justified by `0<=G<=27`, not a physical coupling.
For an initial prior with positive mass on the canonical candidate,

\[
q_{e,k}(\tau)=
\frac{p_e(\tau)w_e(\tau)^k}{\sum_\rho p_e(\rho)w_e(\rho)^k}.
\]

Let `O_e=(sum of initial wrong mass)/(initial correct mass)`. Lean proves

\[
P_{q_{e,k}}(\tau\ne\sigma_e)\le O_e2^{-k},\qquad
0\le\mathbb E_{q_{e,k}}G_e\le27P_{q_{e,k}}(\tau\ne\sigma_e),
\]

and both limits are zero. The rate follows from the actual census gap; it
is not supplied as a descent-rate assumption. Every finite round retains
full support if the initial prior has full support. The existing finite
coherent/Born lift therefore remains available at every round. This scalar
lift does not establish quantum causality or interference compatibility
between distinct histories.

Full support also makes the mean defect strictly positive at every finite
round: wrong candidates retain positive mass and have positive defect.
Thus this method gives asymptotic recovery. It cannot directly replace the
existing supplied repair relation's exact-zero guarantee at a finite
deterministic deadline.

For a uniform six-candidate prior, put `t=2^(-k)`:

\[
P_{\rm wrong}(k)=\frac{3t+2t^2}{1+3t+2t^2},\qquad
\mathbb E G_k=\frac{54t+54t^2}{1+3t+2t^2}.
\]

| Selection rounds | Wrong probability | Mean defect |
| ---: | ---: | ---: |
| 0 | 0.833333 | 18 |
| 4 | 0.163399 | 3 |
| 8 | 0.0116128 | 0.209302 |
| 16 | 0.0000457747 | 0.000823949 |

The audit independently computes profile scores and fixed-point defects for
all 30 edge/candidate pairs. It checks the actual one-step iterates against
the closed form through round 64, including unequal protected edge masses,
nonuniform candidate priors, and Arb scalar amplitude lifts.

## 4. An exact obstruction from protecting too much

As a mathematical stress test, additionally protect the parity of the
relative permutation `sigma_e^(-1) tau`. This parity is defined using the
given order's canonical transport; it is not identified with a physical
horizon observable or the repository's chirality parameter.

Under the uniform prior, the odd record has mass `1/2`, and every member
has defect 18. Therefore every selector preserving this record law obeys

\[
\mathbb E_qG_e\ge9,\qquad P_q(\tau\ne\sigma_e)\ge\tfrac12.
\]

The bounds are sharp. Conditional reweighting within the two parity records
has the exact formulas

\[
\mathbb E G_k=9+\frac{27\,4^{-k}}{1+2\,4^{-k}}\to9,\qquad
P_{\rm wrong}(k)=\frac12+\frac{4^{-k}}{1+2\,4^{-k}}\to\frac12.
\]

Lean proves the more general certificate
`E_q G_e >= 18 P_p(H != H(canonical))`. The explicit parity census and sharp
limit formulas above are checked by exact rational arithmetic in the script.
This is an obstruction to every permitted selector, not a failure specific
to the chosen weight or step size.

## 5. What survives when the reconstruction problem grows

An explicit algorithm adds one uniform-prior transport record each stage
and gives every old record one more selection pass. At stage `N` there is
one record of each age `a=0,...,N-1`. Linearity of expectation and the
geometric bound give

\[
\mathbb E W_N\le5\sum_{a=0}^{N-1}2^{-a}<10,\qquad
\mathbb E(W_N/N)\le10/N\to0.
\]

The Lean module proves the finite sum bound and vanishing fraction for a
general common prior, with constant `2 O_e`; its uniform specialization
gives 10. These are deterministic sums of posterior error probabilities,
without a formal probability-space construction.

There is also an analytic almost-sure extension under an explicit sampling
assumption. If candidates are sampled independently across records within
each stage, `Var(W_N)<=E W_N` and

\[
\mathbb E W_N^2\le110,\qquad
P(W_N/N>\epsilon)\le\frac{110}{\epsilon^2N^2}.
\]

Summing over `N` and applying the first Borel--Cantelli lemma for positive
rational `epsilon` gives `W_N/N -> 0` almost surely. Independence between
stages is unnecessary. This stochastic assembly is analytic, not a Lean
measure-theoretic theorem. The script checks exact first and second moments
through `N=256`; its expected wrong count there is approximately 2.597833.

The newest record always has error probability `5/6`. Neither eventual
perfect reconstruction at every stage nor a vanishing absolute wrong count
follows. The schedule also performs a number of internal updates proportional
to `N` per new record. Its identification with physical local causal growth
is an additional obligation, not a consequence of the expectation bound.

## 6. Physical frontier and verification

The [cut-contrast follow-up](CAUSAL_CUT_CONTRAST_BOUND.md) now addresses a
different part of actual birth selection: how much effective cut bias is
necessary to change its limiting ordering statistic. It proves a sharp
all-rank mean bound and combines a calibrated cut law with the protected
shape correction. The calibrated witness still fails strict Bell causality;
it does not discharge the physical obligations below.

The next physical input must identify a defect on actual grown orders and
protected records whose sharp floor lies below the parent's appropriately
scaled defect. Then one needs a realizable birth/update kernel, a quantitative
drift estimate, and the intended quantum-causality conditions. Reconstructing
the transport already encoded in the constructed bridge order does not
settle those requirements, select four dimensions, or recover Einstein's
equations. The additional supplied count-window, curvature-bias, and
spectral-locality terms in the full physical distortion are not handled by
this census-only convergence theorem.

The new module prints the axioms of its main results. They depend only on
`propext`, `Classical.choice`, and `Quot.sound`; there is no `sorryAx` or
compiler-trusted finite search. Reproduce with:

```sh
python3 scripts/protected_selection_convergence.py --output data/protected_selection_convergence.json
lake build UnifiedTheory.Audit.KFCausalCSpecProtectedSelectionConvergence
lake build
git diff --check
```

The JSON contains source hashes, all 88 parent certificates, the census
iteration checks, and the growing-bank moment checks.

Validation completed on 2026-09-09: the exact/Arb audit passes, all nine
recorded source hashes match, the integrated `lake build` succeeds
(8,909 jobs), and `git diff --check` passes. The new module's eight printed
audit results use only the three standard axioms listed above.
