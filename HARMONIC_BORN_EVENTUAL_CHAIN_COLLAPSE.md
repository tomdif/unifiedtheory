# Eventual chain growth under the canonical harmonic Born law

Date: 2026-09-09

**Status: analytic theorem with an explicit proof below; the complete theorem
is not yet formalized in Lean.** The harmonic, radial, and chain-tail
inequalities are partly machine checked in
[`KFCausalSetHarmonicBornChainBounds.lean`](UnifiedTheory/Audit/KFCausalSetHarmonicBornChainBounds.lean).
The argument below additionally needs uniform combinatorial estimates and
their stochastic assembly. These are not supplied as Lean axioms.

For the existing canonical positive-radial harmonic Born trajectory law,
almost every history eventually consists entirely of timid births: after a
finite random prefix, each new event lies above every earlier event. The
ordering fraction consequently tends to one almost surely. The trajectory
measure is supported on a countable collection of such histories and is
purely atomic.

This strengthens the separately established
[forever-chain atom](HARMONIC_BORN_CHAIN_ATOM.md), whose probability is between
0.3643588912 and 0.3644055352. The stronger result does not say every history
was a chain from the beginning, or that a finite stage becomes deterministically
absorbing. Every finite allowed transition retains positive probability.

## 1. Uniform raw-amplitude bounds from precursor counting

At an n-parent, scale all raw amplitudes by the full-precursor magnitude and
rotate them so that the timid amplitude is 1. Its transition fiber is a
singleton, as already proved in the repository. A downset omitting k events
has relative magnitude

\[
r_{n,k}=\lambda_n^{-k(2n-k-1)},\qquad 0\le k\le n,
\quad \lambda_n=1+H_n/[2(n-1)].
\]

There are at most binom(n,k) such downsets, independently of the parent
geometry. Aggregating to unlabeled children cannot increase their total
absolute amplitude. Define

\[
B_{n,k}=\binom nk r_{n,k},\qquad B_n=\sum_{k=0}^n B_{n,k}.
\]

If the parent has a unique maximal event, that event is greatest, and every
proper downset omits it. The number of downsets omitting k events is then at
most binom(n-1,k-1)=(k/n)binom(n,k). Therefore the total competing magnitude
is at most

\[
U_n=\frac1n\sum_{k=1}^n kB_{n,k}.
\]

**Uniform estimates:** there are fixed constants C,M and an N such that,
for every n >= N,

\[
B_n\le C,\qquad U_n\le M/n.
\]

Here is a proof with nonoptimized constants C=exp(4)+1 and M=4exp(4)+1.
Put q=lambda_n^(-(n-1)); the checked harmonic inequality gives q^2 <= 2/n.
Let K_n=ceil(16 sqrt(n)). Since

\[
\log\lambda_n\le\frac{1+\log n}{2(n-1)},
\qquad K_n\log\lambda_n\longrightarrow0,
\]

we have lambda_n^(K_n) <= 2 for all sufficiently large n.

For k <= K_n, the exact exponent identity gives

\[
r_{n,k}=(q^2\lambda_n^{k-1})^k\le(4/n)^k,
\qquad B_{n,k}\le4^k/k!.
\]

The k=0 term is 1 and is treated separately. For k > K_n, use
r_(n,k) <= q^k and the elementary bound
binom(n,k) <= (e n/k)^k to obtain

\[
B_{n,k}\le\left(\frac{e\sqrt{2n}}{k}\right)^k\le2^{-k}.
\]

The binomial bound follows from binom(n,k) <= n^k/k! and
log(k!) >= integral_1^k log(x) dx >= k log k-k. The numerical choice 16
leaves ample slack because e sqrt(2)/16 < 1/2.

Summing the two ranges yields

\[
B_n\le e^4+2^{-K_n},\qquad
U_n\le4e^4/n+2^{-K_n}.
\]

Since 2^(-K_n) <= 1/n for all sufficiently large n, the stated constants
follow. These estimates apply to every parent, including parents far from
chains; they are not fitted to typical sampled histories.

## 2. Every parent has a uniform chance of a timid birth

There are at least n+1 distinct physical unlabeled children: a linear
extension supplies one downset of each cardinality, and different precursor
cardinalities give different child relation counts. Let L be this support
size and u=1/L. For the scaled aggregated raw vector A, write

\[
A_t=1,\quad Z=\sum A_j,\quad W=\sum|A_j|^2.
\]

The uniform estimate gives |Z| <= C and 1 <= W <= C^2. All-rank
noncancellation gives Z != 0. The positive radial completion's timid
amplitude can be written exactly as

\[
b_t=u+\sqrt{1-u}\,\frac{|Z|}{Z}
                  \frac{1-uZ}{\sqrt{W-u|Z|^2}}.
\]

The denominator is positive by the existing nonuniformity theorem. Using
the reverse triangle inequality and its upper bound sqrt(W) <= C gives

\[
|b_t|\ge\frac{\sqrt{1-u}(1-uC)}{C}-u.
\]

For sufficiently large n, u <= 1/(4C), hence sqrt(1-u) >= 1/2 and
1-uC >= 3/4. Thus

\[
|b_t|\ge1/(8C),\qquad
\Pr(\text{timid birth}\mid\text{complete past})\ge c:=1/(64C^2)>0.
\]

The bound is uniform over all histories. It implies infinitely many timid
births almost surely: conditionally, avoiding timid births for the next m
steps has probability at most (1-c)^m. The probability of avoiding them
forever after any fixed stage is zero, and the union over starting stages
is countable. Independence is not assumed.

## 3. Departures from a unique maximum are summable

When the parent has a unique maximal event, the competing relative amplitude
sum is at most U_n <= M/n. Then |Z| >= 1-U_n and, for the coherently
normalized vector a and timid unit vector e_t,

\[
\|a-e_t\|_2^2\le2\left(\frac{U_n}{1-U_n}\right)^2.
\]

The checked radial projection estimate gives

\[
\Pr(\text{non-timid birth}\mid\text{past with a unique maximum})
\le8\left(\frac{U_n}{1-U_n}\right)^2
\le32M^2/n^2
\]

for all sufficiently large n, where U_n <= 1/2. Let E_n be the event
that the parent at stage n has a unique maximum and its next birth is
non-timid. Taking conditional expectations gives
Pr(E_n) <= 32M^2/n^2. The first Borel--Cantelli lemma therefore says that
only finitely many E_n occur almost surely. Again, no independence is used.

## 4. Almost-sure eventual chain growth

Take a history on which timid births occur infinitely often but E_n occurs
only finitely often; the preceding sections show that these histories have
probability one. Choose a timid birth after the last E_n. Its child has a
unique greatest event. Every subsequent birth must be timid: a non-timid
birth from that parent would be another E_n. Induction proves an infinite
timid suffix.

Only finitely many incomparable pairs were created before that suffix, and
timid births create none. If their final number is I, then

\[
r_n=1-I/\binom n2\longrightarrow1
\quad\text{almost surely}.
\]

Finite histories form a countable set, and each determines one all-timid
continuation. The probability-one set of eventual-timid histories is thus
countable, proving pure atomicity of the Born trajectory measure.

This is compatible with exact full finite support. Every finite physical
history admits a timid continuation with positive infinite survival
probability: one timid birth creates a unique maximum, the finitely many
early factors are positive, and the remaining losses are summable. Each
physical finite cylinder therefore contains a positive-mass eventual-timid
history, even though the whole law is concentrated on countably many such
infinite histories.

## Scope and next formal target

For an interpretation retaining the grown order as spacetime causality,
this blocks almost-sure emergence of nondegenerate four-dimensional causal
geometry under the current canonical Born law. It does not exclude models
with other microscopic transition laws or additional physical degrees of
freedom that change the order-to-spacetime identification.

The full Lean target is to prove the uniform B_n and U_n bounds, the
all-parent timid probability lower bound, and the Borel--Cantelli assembly
for `harmonicBornTrajectoryMeasure`, using the actual transition subtype.
Until that is done, the complete collapse theorem remains an analytic result
with checked ingredients, not a completed kernel-checked theorem.
