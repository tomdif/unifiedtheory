# A positive-probability infinite chain in the canonical harmonic Born law

Date: 2026-09-09

The canonical positive-radial harmonic Born trajectory measure assigns
strictly positive probability to the history that remains a total order
forever. This is a failure of almost-sure nondegenerate four-dimensional
order emergence for this particular trajectory law. It does not refute all
causal-set dynamics, the repository's operator-valued alternatives, or an
interpretation using a different physical measure.

The proof below is analytic. The companion Lean module
[`KFCausalSetHarmonicBornChainBounds.lean`](UnifiedTheory/Audit/KFCausalSetHarmonicBornChainBounds.lean)
checks the harmonic inequality, radial-projection bound, geometric tail
estimate, and infinite-product criterion. **The complete identification and
assembly into the repository's trajectory measure is not yet formalized in
Lean.** The numerical finite-prefix probabilities use outward Arb ball
arithmetic, not Monte Carlo or a fitted extrapolation.

## 1. Exact restriction of the existing law to chains

An n-element total order has exactly n+1 downsets: the initial segments of
length j, for 0 <= j <= n. Each gives a distinct unlabeled child, since the
new child relation count is the old relation count plus j. Therefore no
coherent multiplicity factor is missing in this restriction.

For chirality +, the raw amplitudes are

\[
A_0=1,\qquad A_j=i\lambda_n^{j(j-1)}\quad(1\le j\le n),
\qquad \lambda_n=1+\frac{H_n}{2(n-1)}\quad(n\ge2).
\]

The n=1 coupling is 2, as defined in the repository; its value has no effect
on these zero exponents. The unique chain-producing child is j=n, the timid
birth. The other chirality conjugates the amplitudes and has identical Born
probabilities.

Let K=n+1, u=(1/K,...,1/K), Z=sum A_j, and a=A/Z. The existing canonical
completion is exactly

\[
b=u+\frac{\sqrt{1-1/K}}{\|a-u\|_2}(a-u),
\qquad p_n=|b_n|^2,\qquad \epsilon_n=1-p_n.
\]

The all-rank support theorem already proves 0 < p_n < 1. The finite chain
prefix through the birth from an N-element parent has probability
P_N=product_{n=1}^N p_n. The rank-zero first birth is certain.

## 2. Harmonic running bounds the competing amplitudes

For n >= 3,

\[
H_n^2\le2(n-1),\qquad H_n>\log n+\tfrac12.
\]

The first inequality follows by induction from H_3=11/6, using H_n <= n
and H_(n+1)=H_n+1/(n+1). The second follows from the decreasing upper Euler
sequence and gamma > 1/2; both facts are available in the pinned Mathlib.
Put m=2(n-1). The elementary inequality log x >= 1-1/x gives

\[
m\log\lambda_n
\ge H_n-\frac{H_n^2}{m+H_n}
\ge H_n-1
>\log n-\tfrac12
\ge\log(n/2).
\]

Consequently, for n >= 8, q=lambda_n^(-(n-1)) satisfies

\[
q^2\le\frac2n,\qquad 0<q\le\tfrac12.
\]

Scale all raw amplitudes by the timid magnitude, so the timid amplitude is
i. A competing nonempty precursor j=n-k has relative magnitude

\[
r_k=\lambda_n^{-k(2n-k-1)}\le q^{k+1},
\quad1\le k\le n-1,
\]

because the exponent difference is
(k-1)(n-k-1) >= 0. The empty precursor has magnitude q^n, equal to the
singleton precursor's magnitude. Thus the sum T_n of all competing
magnitudes obeys

\[
T_n\le q^2\left(\sum_{\ell=0}^{n-3}q^\ell+2q^{n-2}\right)
\le2q^2\le\frac4n.
\]

The duplicated geometric-tail bound follows by induction: its value starts
at 2 and its increment is q^m(2q-1) <= 0.

## 3. The radial completion makes escape summable

In the scaled coordinates, Z=r_empty+i(1+sum r_k), so |Z| >= 1. With e the
unit vector selecting the timid child,

\[
|a_n-1|\le T_n,\qquad
\sum_{j\ne n}|a_j|^2\le T_n^2,\qquad
\|a-e\|_2^2\le2T_n^2.
\]

Here e lies on the same sphere about u as b. Radial projection satisfies

\[
\|b-e\|_2\le2\|a-e\|_2:
\]

its displacement from a is the absolute difference of the two radii,
which is at most ||a-e|| by the reverse triangle inequality. Hence

\[
\boxed{\epsilon_n=\sum_{j\ne n}|b_j|^2
\le\|b-e\|_2^2\le8T_n^2\le\frac{128}{n^2}
\quad(n\ge8).}
\]

All p_n are strictly positive and sum epsilon_n is finite. Therefore
product p_n > 0. The events specifying successively longer chain prefixes
are decreasing measurable cylinders. Continuity from above of the existing
probability measure identifies their limiting probability with the measure
of the forever-chain event. This proves the claimed atom.

This is not a conclusion drawn from a finite plateau: the summable bound
controls the entire uncomputed tail.

## 4. Certified computation and finite geometric census

Reproduce with:

```sh
python3 scripts/harmonic_born_geometry_drift.py \
  --chain-rank 1000000 --output data/harmonic_born_geometry_drift.json
```

The script uses exact rational raw amplitudes and python-flint Arb at 256-bit
precision. Its specialized chain formula agrees with independent exhaustive
unlabeled-child aggregation at ranks 1 through 5. Truncated chain sums carry
explicit outward error bounds and are checked against complete sums at ranks
128, 257, and 1000. The saved artifact records the actual precision and all
enclosures.

For any N > 128, the analytic bound supplies the rigorous enclosure

\[
P_N(1-128/N)\le\Pr(\text{forever chain})\le P_N,
\]

using sum_{n>N} n^-2 <= 1/N and the finite-product inequality
product(1-epsilon_n) >= 1-sum epsilon_n, followed by a limit. See the JSON
artifact for the computed endpoints.

At N=1,000,000, the certified numerical prefix and the analytic tail give

\[
\boxed{0.3643588912 < \Pr(\text{forever chain}) < 0.3644055352.}
\]

Thus approximately **36.44%** of the current Born trajectory measure is
concentrated on this one infinite chain history. The interval is conservative:
its width comes from the proved tail estimate, while the Arb rounding and
truncation enclosures are below 10^-64.

Validation on 2026-09-09: the targeted Lean build passed (8,417 jobs), the
full repository build passed (8,906 jobs), and the numerical audit passed at
one million parent ranks. All five printed Lean axiom audits contain only
`propext`, `Classical.choice`, and `Quot.sound`. The JSON artifact records
the Python/Arb versions, precision, and SHA-256 hashes of all three source
scripts; those hashes were verified against the files used for this run.

Independently, an exhaustive census through rank five tests the finite proxy
(r-1/10)^2, where r is the number of related pairs divided by binom(n,2).
The four-dimensional Minkowski interval expectation is 1/10, following the
[standard Myrheim--Meyer relation](https://arxiv.org/abs/1710.00938) with this
pair-count normalization. Among ranks 2, 3, 4, 5, respectively, the
proxy has positive expected drift on 1/2, 4/5, 15/16, and 62/63 parents;
the only negative-drift parent at each rank is the chain. This diagnostic is
not a Gate-3 Hauptvermutung defect or a continuum test. In particular,
finite-size fluctuations alone can obstruct monotone squared-error descent.
The infinite-chain atom is the stronger obstruction.

## 5. What this changes in the research program

The harmonic schedule was selected partly to balance the coherent
one-missing/timid sectors on antichains. Chains have one precursor per child
and no binomial enhancement. Applying the positive radial Born completion
to the resulting nearly timid raw vector makes departure probability
quadratic in the small competing amplitudes. A coupling tending to one and
exact full support therefore coexist with a macroscopic infinite atom.

Every interval and every induced suborder of a chain remains totally ordered.
An order-preserving coarse graining of this positive-probability sector
cannot produce spacelike-separated events of a nondegenerate 4D causal
geometry. A claim of almost-sure 4D emergence from this exact Born trajectory
measure must therefore change or fail. The atom argument alone does not
establish the behavior of the complementary sector.

The [uniform-counting extension](HARMONIC_BORN_EVENTUAL_CHAIN_COLLAPSE.md)
addresses the complementary sector analytically: almost every history has
an eventual all-timid suffix. Its complete uniform estimates and stochastic
assembly also remain outside the current Lean formalization.

The next physical selection condition must control infinite persistence of
degenerate histories, in addition to normalization, finite support, and
antichain balance. A necessary test for excluding the chain atom is divergence
of sum_n (1-p_n). Proving repair for an independently stipulated relation
cannot supply that missing property for the current kernel.

Sequential-growth dynamics and their continuum limitations predate this
repository; see [Rideout and Sorkin's original paper](https://www2.perimeterinstitute.ca/personal/rsorkin/some.papers/99.csgd.pdf).
The result here concerns the repository's specific harmonic positive-radial
law. No literature-wide novelty claim is made.
