# The causal-set KPZ test: the quantized measure is NOT a Liouville
# geometry — reading (ii), anti-KPZ (2026-08-11)

## What was tested

If the pi/4 bi-normalized growth measure defines a random geometry in
a gamma-LQG class, classical-vs-quantum scaling weights of order
observables must satisfy the KPZ quadratic
x = (gamma^2/4) Delta^2 + (1-gamma^2/4) Delta with ONE gamma, agreeing
with the mating-chart gamma from the ordering fraction
(STRUCTURAL_4_SQRT6_NOTE.md sec. 5).  Readings registered in
kpz_causal_test.py before the run.

Method: direct sampling of both Markov chains to n = 12 (8000 quantum
+ 20000 classical paths).  Key simplification: the double-conservation
constraints see only the child ACTION GAPS, so the gap-grouped
max-entropy law is covariant and needs no canonicalization — sampling
becomes state-local.  (The "gap-max-entropy" law is a member of the
registered selection band: its r(8) = 0.4367 +- 0.0012 vs the
class-max-entropy 0.4136.)  Observables: posts (comparable to all,
x ~ 2, primary gamma probe), height (x ~ 1/2, secondary, extremal-
object caveat), minima (x ~ 1 null: KPZ forces Delta = 1 at EVERY
gamma), links (intended x ~ 0 null).

## Byproducts of independent value

1. FEASIBILITY DEEPENED: 8000 paths x 11 growth steps = ZERO
   infeasible parents.  The pi/4 theory exists on every one of ~88,000
   visited parent states through depth-11 parents (n = 12 causets).
2. r(n) EXTENDED TO 12 (the 2/3-vs-1/2 discriminator):
   quantum r: 0.3049, 0.3414, 0.3824, 0.4142, 0.4367, 0.4552, 0.4700,
   0.4827, 0.4933 (n = 4..12); classical: 0.4938 -> 0.5186.  The
   quantum-classical gap NARROWS (0.094 at n = 8 to 0.026 at n = 12):
   r flows to the classical value (~1/2-ish), decisively AWAY from the
   Brownian-map target 2/3.  Mating chart at n = 12: gamma^2 = 1.97,
   c_eff ~ -2.06 — back at the classical c = -2 point.

## The KPZ verdict

Slopes (log-log, n = 6..12):

  observable   a_cl      a_q       delta-a    KPZ prediction (gamma^2 in [1.65, 2])
  posts       -0.9015   -2.0304    -1.129     +0.40 .. +0.44
  height      +0.5810   +0.6892    +0.108     -0.10 .. -0.11
  minima      +0.1276   +0.1200    -0.008     0 (null)     <- PASSES
  links       +1.7240   +1.9187    +0.195     (control invalid, see below)

- The minima null passes cleanly (|delta-a| = 0.008 < 0.05):
  finite-size distortion is under control for count observables.
- The links control is DEMOTED, honestly: its classical exponent under
  the uniform-growth chain is 1.72 (bulk-like), not the ~1 of the
  sprinkling ensemble assumed at design time — it is not an x ~ 0
  feature in this ensemble and cannot serve as a null here.
- Both gamma-sensitive observables deviate with the SIGN OPPOSITE to
  every positive-gamma^2 KPZ prediction: the quantum measure
  suppresses posts FASTER (n^-2.03 vs n^-0.90; KPZ with gamma^2 > 0
  demands slower), and grows taller orders (height exponent 0.69 vs
  0.58; KPZ demands shorter).  Formal inversions give
  gamma^2(posts) = -0.73 and gamma^2(height) = -2.02 — both NEGATIVE,
  outside the entire LQG family (gamma^2 in (0,4)), and inconsistent
  with the mating value 1.97.

VERDICT: registered reading (ii), strengthened to ANTI-KPZ.  The
quantized causal measure is not a gamma-LQG geometry for ANY gamma:
its deviation from the classical ensemble has the wrong sign structure
for a Liouville measure-reweighting, not merely the wrong magnitude.
Combined with the r-flow back to c_eff ~ -2, the picture at accessible
depth: bulk statistics of the quantized theory converge to the
classical c = -2 point while rare/extremal statistics (posts, height)
deviate strongly with anti-Liouville sign — a genuinely different
deformation class.

## Consequence for the 4/sqrt6 question

The two independent instruments now agree: the mating chart drifts to
the classical point (not c = 0), and the KPZ exponent pairs exclude
every gamma.  **The identity beta_4 = gamma(c=0) = 4/sqrt6 is a
numerical coincidence at every level this program can test.**  Its two
sides remain separately meaningful ("pure quantum geometry <->
dimension four" on each side); no structural bridge survives contact
with the quantized measure.  The structural question opened by
structural-4sqrt6-2026-08-11 is CLOSED NEGATIVE.

## What the theory gained anyway

The quantized theory's own characteristic exponents, now measured:
posts ~ n^{-2.0} (strong suppression of elements causally comparable
to everything — the quantum law disfavors bottleneck/"post"
geometries), height ~ n^{0.69} (super-classical chain growth), minima
saturating (~3.08).  These, with r(n), are the beginning of the
quantized theory's critical-exponent table — its identity card,
whatever universality class it turns out to inhabit.

## Honest scope

- Exponents from n = 6..12 log-log fits; small sizes, no error bars on
  slopes beyond the per-point MC errors (se ~ 0.001-0.005); the posts
  slope at n = 12 rests on counts ~ 0.037 +- 0.002.
- The height observable violates KPZ's independence hypothesis
  (extremal object) — but the verdict does not rest on it: posts alone
  excludes all gamma, and the sign disagreement is robust.
- Gap-max-entropy selection variant (r(8) = 0.437 vs 0.414
  class-variant); the sign structure of delta-a is far larger than the
  selection band.
- The classical anchor is the uniform-growth chain (like-for-like
  Markov comparison), not sprinkling; posts' classical exponent -0.90
  validated near the sprinkling design value -1.

## Registered follow-ups

1. Depth extension of the exponent table (n ~ 16-20 by smarter
   sampling) — does r cross the classical value or converge to it?
2. Identify the quantized theory's actual deformation class: the
   anti-KPZ sign (rare features MORE suppressed) suggests a
   measure-concentration/large-deviation structure rather than a
   metric-measure reweighting; a Legendre/large-deviation exponent
   dictionary is the natural next chart.
3. The posts observable doubles as a physical statement: the quantum
   law exponentially disfavors "post" (bounce/bottleneck) cosmologies
   relative to classical sequential growth — worth a dedicated note
   against the causal-set cosmology literature on posts.
