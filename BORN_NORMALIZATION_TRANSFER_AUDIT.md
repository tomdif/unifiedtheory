# Born-normalization transfer audit

**Date:** 2026-08-04
**Formal module:** `UnifiedTheory/Audit/KFCausalBornNormalizationTransfer.lean`

## Executive verdict

Replacing the coherent Markov rule

\[
\sum_c a_c=1
\]

by the Born rule

\[
\sum_c |a_c|^2=1
\]

does not modify the old theory. It defines a second theory. The two rules are
logically independent: the formal module contains exact binary witnesses in
both directions.

Born normalization has one immediate and important payoff. The path weights
\(|A(\gamma)|^2\) form an exactly projectively consistent classical cylinder
probability. The normalization-flow defect vanishes separately at every
parent, so the fully dephased member has zero normalization churn by theorem,
not by a numerical observation.

Born normalization alone does **not** make the old rank-one coherent
decoherence functional projective. Independent ket/bra cylinder projectivity
still requires the coherent sum. Thus a Born-only phase-decorated tree may
carry finite-depth interference, but it does not automatically define the
same infinite quantum history theory.

The important positive result is that the intersection is nonempty. The
repository's canonical harmonic Born-shell law already satisfies both rules
at every parent and every rank. It therefore has both:

1. an exact diagonal Born martingale; and
2. an exactly projective, normalized, strongly positive coherent cylinder
   functional.

Moreover, the convex measure-level interpolation between its coherent quantum
measure and Born diagonal is normalized and projective for every dephasing
strength. Whenever the original event has nonzero interference, every
dephasing value other than one retains it by the exact factor
\(1-\lambda\). This is the finite-cylinder answer to the registered question:

> A growth law can interfere and remember simultaneously, but it must be
> bi-normalized (or use a more general operator-valued consistency law).

This is not yet a tail-event convergence theorem, a laboratory-time collapse
law, or a derivation of a CPTP record instrument.

## Double-conservation rigidity

The follow-up module `KFCausalDoubleConservationLaw.lean` proves that the
intersection is not merely a convenient sufficient condition.  For any finite
successor fiber, require one unresolved birth to preserve every incoming
complex amplitude and every resolved Born mass:

\[
\sum_e z a_e=z,
\qquad
\sum_e |z a_e|^2=|z|^2
\quad\text{for every }z\in\mathbb C.
\]

These two operational requirements hold if and only if

\[
\sum_e a_e=1,
\qquad
\sum_e|a_e|^2=1.
\]

The carrier-valued theorem is equally exact.  Requiring, for every incoming
carrier amplitude `X`,

\[
\sum_e K_eX=X,
\qquad
\sum_e(K_eX)^\dagger(K_eX)=X^\dagger X
\]

is equivalent to

\[
\boxed{\sum_eK_e=I,
\qquad
\sum_eK_e^\dagger K_e=I.}
\]

This is the repo's **double-conservation law**: coherent quantum data and Born
record weight survive the same local causal refinement exactly when the birth
operators are bi-normalized.  It is basis-free and needs no tensor-product
environment, partial trace, or record algebra.  The all-rank harmonic scalar
law and both concrete causal-holonomy operator laws satisfy it.

The rigidity is conditional on the two universal conservation demands.  It
does not prove that causal order imposes them or select the microscopic
operators.  Those are now the sharply isolated physics questions.

## Recorded-refinement origin

`KFCausalRecordedRefinementDilation.lean` gives the paired equations a common
finite microscopic carrier. Stack the birth operators into

\[
V:H\longrightarrow H\times\mathrm{Outcome},
\qquad
V_{(i,e),j}=(K_e)_{ij}.
\]

The formalization proves the converse as well as the standard forward
Stinespring calculation:

\[
V^\dagger V=I
\quad\Longleftrightarrow\quad
\sum_eK_e^\dagger K_e=I.
\]

Thus Born completeness is exactly reversibility of recorded refinement on its
image. Define the coherent record codiagonal by

\[
E_{i,(j,e)}=\delta_{ij}.
\]

Then

\[
EV=\sum_eK_e,
\]

so exact unresolved recovery `EV=I` is equivalent to coherent exhaustivity.
Every double-conservation law therefore has both an adjoint recovery and a
counital recovery for every incoming carrier amplitude.

The two requirements remain independent. The formal module lifts the exact
binary counterexamples into one-dimensional recorded dilations: an isometric
recording can fail counital recovery, and counital recovery can fail
isometric recording. Consequently the candidate natural principle must
demand both, or derive both from a still-stronger microscopic axiom.

This first construction uses an abstract finite outcome-indexed record
carrier. `KFCausalNativeSuccessorRecord.lean` closes that finite kinematic gap:
at a parent `(n,h)`, the outcome type is definitionally

\[
\{c:c\in\mathrm{physicalCausalSuccessors}(n,h)\}.
\]

It is finite and nonempty directly from the unlabeled one-element-extension
theory. Forgetting the child is the unique map to the terminal one-point type;
retaining the parent carrier coordinate gives the unique record projection,
whose unit-weight complex linearization is the native codiagonal. No outcome
enumeration or external record labels remain. The canonical harmonic law,
restricted to this exact physical subtype, retains both normalization sums and
therefore realizes the isometric and counital dilation at every causal parent.

`KFCausalNativeSuccessorInstrument.lean` then closes the finite channel
question while proving that the coherent codiagonal is the wrong candidate for
physical erasure. Every Born-complete child-operator family produces a genuine
CPTP `KrausRepresentation`; its enumerated implementation is proved equal to
the intrinsic sum over physical children. The state-independent operation
forgetting the record is the partial trace, which exactly recovers this channel
from the recorded Stinespring state and preserves trace, Hermiticity, and
positivity. With two distinct records, the coherent codiagonal fails the
single-Kraus completeness equation and therefore cannot be trace-preserving.

For the canonical harmonic scalar lift, the native CPTP instrument exists at
every parent and every rank. Its resolved child operation has trace weight
`|a_c|^2` times the incoming trace, but its unconditioned one-dimensional
channel is exactly the identity and is independent of parent, rank, and
chirality. Thus the causal information is operationally located in the record,
not in the reduced scalar carrier. A nontrivial reduced observable still needs
a higher-rank child-operator law; uniqueness of such a law and its laboratory
interpretation remain dynamical questions.

## The exact local law

For a finite successor fiber, simultaneous normalization implies

\[
\left|\sum_c a_c\right|^2-\sum_c|a_c|^2=0.
\]

The left side is total real off-diagonal interference. The law does not demand
that every interference term vanish; it demands exact cancellation of their
total at each parent. At binary branching this reduces to quadrature. At
higher rank it permits genuinely multichannel cancellations.

This is the scalar version of the already-formalized operator law

\[
\sum_c K_c=I,
\qquad
\sum_c K_c^\dagger K_c=I,
\]

whose total operator interference also vanishes.

## Transfer ledger

| Existing result | Born-only status | Reason |
|---|---|---|
| Finite causal-order combinatorics, action gaps, parity, collision tables, CSpec geometry | **Transfers** | These statements do not use either normalization rule |
| Finite Gram strong positivity and the Sorkin grade-two identity | **Transfers at each fixed depth** | Any chosen amplitude vector gives a rank-one positive kernel; cross-depth consistency is separate |
| Diagonal path probability / classical cylinder martingale | **New theorem, transfers exactly** | Local Born normalization gives `sum_child |A child|² = |A parent|²` |
| Rank-one coherent cylinder projectivity | **Does not transfer from Born normalization alone** | It uses `sum_child a = 1` independently on ket and bra |
| Binary quadrature law | **Does not transfer to Born-only theory** | Born normalization leaves a phase continuum; quadrature follows in the bi-normalized intersection |
| Funding theorem and the computed hbar windows | **Must be re-derived** | Their constraints are the complex linear wave equations generated by the coherent sum |
| Aging obligation | **Must be re-derived** | The Paper-3 certificate subtracts coherent Markov equations; those equations are absent in Born-only growth |
| Necessity theorem for hereditary-real support | **Must be re-derived and is not expected generically** | Its lone-apex step takes an imaginary part of the coherent wave equation |
| Dust telescope and stationary/factorization no-gos | **Must be re-derived** | Their all-plus or cancellation equations are coherent-sum equations, not consequences of squared-modulus normalization |
| Positivity principle for history-counting conventions | **Still valid within a fixed equation family** | Positive multiplicity reweighting preserves a sign-pure certificate; changing the normalization law changes the equations themselves |
| Self-similarity and funding certificates | **No automatic transfer** | Their feasible polytopes were cut out inside the coherent wave family |
| Canonical harmonic Born-shell cylinder law | **Already bi-normalized** | It is the explicit all-rank intersection witness |

The proposed shortcut “sign-pure results transfer on inspection” is therefore
too broad. Sign purity protects a certificate against positive coefficient
changes. It does not protect it when the complex linear equation containing
that certificate is removed.

## Exact martingale interpolation

For a bi-normalized law, write

\[
Q_n(E)=\left|\sum_{\gamma\in E}A_n(\gamma)\right|^2,
\qquad
P_n(E)=\sum_{\gamma\in E}|A_n(\gamma)|^2.
\]

Both are cylinder-projective. Hence for any real \(\lambda\),

\[
M_{\lambda,n}(E)
=(1-\lambda)Q_n(E)+\lambda P_n(E)
\]

is normalized and projective. For \(0\leq\lambda\leq1\), it is also
nonnegative. Its residual interference is exactly

\[
M_{\lambda,n}(E)-P_n(E)
=(1-\lambda)\bigl(Q_n(E)-P_n(E)\bigr).
\]

Thus every \(\lambda<1\) retains any interference present in \(Q\) while
having zero normalization-flow churn. The earlier `SUM_RULE_MOD.md`
experiment failed because it dephased a coherent-only law whose diagonal was
not normalized; the obstruction was not dephasing itself but failure to start
inside the bi-normalized intersection.

## What remains open

1. **Microscopic law.** The harmonic Born-shell intersection is selected by
   the support-relative radial/least-disturbance rule. Whether causal
   microdynamics forces that rule remains open.
2. **Kernel-level interpolation.** The present interpolation is a certified
   cylinder measure. Constructing a state-independent CPTP instrument or a
   fully biadditive strongly positive interpolated decoherence kernel with a
   protected record algebra is a separate promotion.
3. **Records versus cylinders.** Exact cylinder projectivity does not prove
   convergence of stem-record or tail events. The DJS extension boundary
   remains untouched.
4. **Action-phase transfer.** The funding, hbar-window, aging, and necessity
   programmes must be recomputed under Born-only equations if that theory is
   retained as an independent candidate.
5. **History identity.** Labeled, orbit, and event conventions still define
   different successor multiplicities and different Born laws. Normalization
   does not select the history-counting axiom.

## Claim boundary

The promoted claim is:

> Born-normalized causal branching has an exact diagonal cylinder martingale;
> coherent quantum cylinder projectivity is independent; the canonical
> harmonic Born-shell law realizes both simultaneously and admits a
> projective partially coherent measure at every dephasing strength.

The repo does not yet establish that this law is nature's microscopic growth
law, that macroscopic facts converge, or that its dephasing parameter is a
physical time-dependent coupling.
