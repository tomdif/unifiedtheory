# Navier--Stokes methods transferred to microscopic selection

The useful connection to GR is **nonlinear backreaction and correction
subject to constraints**. The immediate repo result is a new finite selector:
it changes birth probabilities to improve a specified defect while preserving
the entire joint distribution of protected observables. It can preserve
causal-volume diversity and a finite horizon channel simultaneously.

This is a transfer of a construction strategy. No Navier--Stokes theorem is
being asserted as an Einstein theorem, and no physical action or 4D continuum
has been derived.

## What the linked work contributes

The [OpenAI announcement](https://openai.com/index/navier-stokes-solution/)
and [paper, Theorem 1.1](https://cdn.openai.com/pdf/32d9f210-8b73-45e0-91bc-82a30aef8a9a/navier-stokes.pdf)
describe finite-time blowup with smooth compactly supported forcing and zero
initial velocity, while kinetic energy remains bounded. The forcing is part
of that theorem; this is not the unforced Navier--Stokes claim.

The construction realizes missing stress through quadratic oscillatory
contributions, maintains a positive stress-cone margin, and corrects moment
errors while improving the residual. Those are the transferable methods.
See the paper's sections 3, 7--9 and Appendix A.

I inspected the published
[Lean source](https://github.com/openai/NavierStokesAndEuler/tree/8937a8f4cbc7abaab5e9e97d1cc7f5d2319d9538),
including `PrimaryCovarianceBounds`, `MatchingDebtBounds`, and
`ResidualStability`. Its toolchain is Lean 4.34.0-rc2; this repo uses 4.28.0.
The external project was not rebuilt or independently audited in full, and
none of its code was imported. The new finite proofs below are local.

## The actual general-relativistic connection

Nonlinear averaging need not commute with the field equations. Schematically,
small oscillations with vanishing first moment can leave a quadratic stress:

\[
\langle v\rangle=0,\qquad \langle v\otimes v\rangle\ne0.
\]

For GR, there are rigorous high-frequency vacuum constructions whose limits
solve equations with effective matter. Huneau and Luk prove realization
results for suitable small, local solutions with polarized `U(1)` symmetry
and multiple null-dust families; their later work treats suitable small,
localized `U(1)`-symmetric massless-Vlasov solutions. These hypotheses matter:
this does not allow arbitrary stress tensors or arbitrary backgrounds.
See [the null-dust construction](https://arxiv.org/abs/1706.09501) and
[the Vlasov extension](https://arxiv.org/abs/2506.21779).

The corresponding research target here is to identify which stresses the
actual microscopic fluctuations can realize, then check whether the desired
Einstein residual lies in that set. Positivity, tensor structure, conservation,
and propagation conditions must be proved. Defining a stress tensor to be
the remaining Einstein residual would only rename the missing physics.

A second relevant precedent is constraint-preserving gluing of Einstein
initial data; [Corvino and Pollack](https://arxiv.org/abs/1102.5050) describe
the scalar-curvature deformation and gluing framework. Our finite adaptation
below preserves specified probability marginals, not the Einstein PDE
constraints. That distinction is the outstanding physical bridge.

## Exact protected selection: the incorporated result

Fix one parent and let `i` index its physical unlabeled children. Let
`p_i>0`, `sum p_i=1`. Choose a protected record `H_i` and an intrinsic
real defect `G_i`. Define

\[
\bar G(h)=\mathbb E_p[G\mid H=h],\qquad
r_i=G_i-\bar G(H_i),\qquad
q_i=p_i(1-\epsilon r_i).
\tag{1}
\]

Conditional centering gives `sum_{H_i=h} p_i r_i=0` for every record.
Consequently, for every function `f` of that record,

\[
\sum_iq_i f(H_i)=\sum_ip_i f(H_i).
\tag{2}
\]

This is exact for finite `epsilon`: the full protected distribution, every
moment, and every protected expectation are unchanged. Normalization follows
by choosing `f=1`. A sufficiently small positive step always exists; e.g.
`epsilon=1/[2(1+sum_i |r_i|)]` gives strict positivity. The executable uses
the less conservative `1/[2(1+max_i |r_i|)]`, retaining at least half of
each child's original probability.

The defect change is also exact:

\[
\mathbb E_qG=\mathbb E_pG-
\epsilon\,\mathbb E_p\!\left[\operatorname{Var}_p(G\mid H)\right].
\tag{3}
\]

Thus strict improvement exists precisely when the chosen defect varies
within at least one positive-mass protected group. If the record identifies
every child, or if `G` is already a function of `H`, there is no such freedom.
Preserving more observables can eliminate the available repair directions.

`UnifiedTheory/Audit/KFCausalBornProtectedSelection.lean` constructs the
conditional residual and proves (2), normalization, positivity, existence of
a positive step size, (3), strict descent given positive conditional variance,
and a coherent/Born lift with precisely the corrected probabilities. The
lift uses the general theorem from the preceding
[microscopic-selection audit](MICROSCOPIC_SELECTION_PRINCIPLE.md).

These are finite exact identities. Equation (3) compares two expectations
over the **same parent's** possible births; it does not prove that the defect
decreases between successive growing parents, or establish a Gate-3
convergence rate. Those require further dynamical estimates.

### Why this escapes the earlier second-order leakage

The earlier horizon module studies a fixed exponential source. First-order
orthogonality to `J` does not force `Cov(J,r^2)=0`, so quadratic leakage can
remain. Equation (1) changes the finite probability update itself. It is not
a claim that the old fixed exponential source has zero quadratic leakage.

A variational version makes the compensation explicit:

\[
q_i(\epsilon)=
p_i\frac{e^{-\epsilon G_i}}
{\mathbb E_p[e^{-\epsilon G}\mid H=H_i]}.
\tag{4}
\]

For `epsilon>0`, this uniquely minimizes
`E_q G + D_KL(q||p)/epsilon` subject to the same `H` marginal. Each group has
its own normalizer. The effective action includes the compensating term
`log E_p[exp(-epsilon G)|H]`, whose higher-order terms enforce exact
protection. Formula (4) and its variational characterization are analytic
here; the Lean proof and rational executable concern (1).

The overarching selection principle becomes concrete: **preserve established
coarse observables exactly, and minimize distortion in the remaining
microscopic choices**. Which observables and defect the physical theory
selects is additional content; the variational formula does not choose them.

## A causal-set test with exact arithmetic

The test uses the intrinsic insertion reference from the previous audit.
The protected record is

\[
H(D)=(|D|,J(D)),\qquad
J(D)=|D\cap\operatorname{Max}(C)|.
\]

`J` counts hits on the parent's maximal frontier. The change in frontier
cardinality is exactly `1-J`. This is a concrete finite horizon-like channel;
identifying it with all relevant local GR horizons remains open. Both record
coordinates are determined by the unlabeled child: relation-count increase
gives `|D|`, while maximal-count change gives `J`.

The defect is the number of new causal intervals with exactly one internal
event. It is order-invariant and shape-sensitive, but is **not** claimed to
be the physical Hauptvermutung defect, curvature error, or Einstein action.

`scripts/protected_selection_audit.py` exhausts all 88 parents through rank 5:

| Parent rank | Parents | Strict improvement | Zero conditional variance |
| ---: | ---: | ---: | ---: |
| 0 | 1 | 0 | 1 |
| 1 | 1 | 0 | 1 |
| 2 | 2 | 0 | 2 |
| 3 | 5 | 1 | 4 |
| 4 | 16 | 6 | 10 |
| 5 | 63 | 41 | 22 |

Every parent passes exact rational checks of record distributions, positivity,
normalization and the descent identity, followed by the Arb amplitude-lift
check. All 48 cases with strict improvement have nonzero horizon leakage for
the uncorrected exponential source, demonstrating the distinction above.

For the three-event parent consisting of a two-chain plus an isolated point,
the mean defect changes from `1/3` to `19/60`, with
`epsilon=3/10` and conditional variance `1/18`. The improvement is `1/60`.
The uncorrected exponential source's second horizon derivative is `1/108`;
the corrected law preserves the horizon distribution exactly.

Because ancestor count is protected, its uniform distribution is unchanged.
The modified insertion law therefore retains the analytic `r_N -> 1/2`
limit and non-atomicity. It is still a benchmark, not a 4D candidate. Applying
this correction while preserving the harmonic law's ancestor probabilities
would retain its timid probabilities and its chain-collapse obstruction.
The coarse distribution must be made physically viable before protecting it.

## What this advances in the repository

The [convergence follow-up](PROTECTED_SELECTION_CONVERGENCE.md) now gives
a sharp protected-record floor, an explicit convergence rate for the actual
bridge-census defect, and a growing reconstruction schedule with vanishing
expected error density. It also exposes a limit of the benchmark above:
maximal births never decrease the absolute number of existing intervals.
The earlier 48/88 improvement is relative to the reference birth law, not
negative drift of that absolute geometric count.

The existing horizon-orthogonal machinery supplies useful perturbative
conditions. The new module adds an exact finite alternative with an explicit
feasibility test: positive conditional variance. It also composes with the
new normalization lift and the causal-volume anti-collapse criterion.

For a physical result, instantiate `G` with an independently justified
order-derived geometric defect, specify the protected horizon records,
prove that enough repair freedom survives refinement, and establish actual
growth drift and quantum causality. The new result reduces one obstruction;
it does not discharge those remaining hypotheses.

Reproduce:

```sh
python3 scripts/protected_selection_audit.py --output data/protected_selection_audit.json
lake build UnifiedTheory.Audit.KFCausalBornProtectedSelection
```
