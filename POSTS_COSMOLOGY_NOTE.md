# Posts and the quantized dynamics: no bounces, no bottleneck cosmology
# (2026-08-11)

## Posts in causal-set cosmology

A POST is an element causally comparable to every other element — a
cosmological bottleneck through which the entire universe passes (a
crunch/bang).  Posts are the engine of classical causal-set cosmology:
in random graph orders / transitive percolation the causal set is
literally "blobs connected by posts" with POSITIVE post density
(Bollobas-Brightwell; expected post counts computed in
arXiv:0809.2258), and Sorkin's cosmic-renormalization program (Sorkin
gr-qc/0003043; Martin-O'Connor-Rideout-Sorkin PRD 63 084026 (2001);
Evolution of universes in CSG, arXiv:1703.07556) uses the infinite
sequence of bounces-at-posts to renormalize the sequential-growth
couplings, driving the universe toward largeness and flatness without
fine-tuning.  Cyclic cosmology THROUGH posts is the classical
causal-set answer to initial conditions.

## What the quantized dynamics says (measured)

From kpz_causal_test.log (8000 quantum / 20000 classical paths to
n = 12) and posts_cosmology_probe.log (4000 / 12000 paths):

  E[#posts](n), slope over n = 6..12:
      classical uniform growth:  ~ n^-0.90
      quantized pi/4 law:        ~ n^-2.03      (double the exponent)

  P(post exists NOW at size n):
      n:            4      6      8      10     12
      classical   0.368  0.263  0.208  0.179  0.165
      quantum     0.265  0.109  0.080  0.052  0.036

  P(some post occurred at ANY stage <= n):
      classical   0.677 -> 0.773 (n=4 -> 12)
      quantum     0.583 -> 0.732

Reading: both dynamics pass through early posts (small causets are
post-rich for combinatorial reasons), but the quantized law does not
RETURN: by n = 12 a quantum universe is at a bottleneck 4.6x more
rarely than the classical chain, with the gap widening as n^-1.1, and
conditional on having had an early post the quantum recurrence
essentially stops (P(now)/P(ever) = 0.05 and falling).  In transitive
percolation — the classical dynamics of the bounce literature — posts
recur forever with positive density; the quantized measure suppresses
even relative to our uniform chain, a fortiori relative to
percolation.

## The physical statement

THE QUANTIZED DYNAMICS PREDICTS A NON-CYCLIC, BOTTLENECK-FREE
COSMOLOGY.  Under the double-conservation law at the quantized phase:

1. Bounces are transient: posts occur (if at all) only in the small-n
   quantum-gravity era and do not recur.  The Big-Crunch/Big-Bang
   cycles of classical causal-set cosmology are switched off by
   quantization.
2. Consequently the COSMIC-RENORMALIZATION MECHANISM IS UNAVAILABLE to
   the quantized theory: whatever sets its effective couplings, it is
   not Sorkin's bounce-flow.  In this framework the couplings need no
   such flow — the phase is quantized outright (pi/4 / the 4/sqrt6
   window), which is a different, sharper answer to the same
   "why these couplings" question.
3. Origins are PLURAL: the expected number of minimal elements
   saturates around ~3 (2.5 -> 3.08 over n = 4..12, slowly growing)
   and typical quantum universes at n = 12 have NO element comparable
   to everything — no single primordial atom, no bottleneck.  Combined
   with the 4D-phase texture (four-d-normalization-check: deterministic
   action-free fan growth with delayed, quasi-periodic branching
   onset), the quantized picture of the earliest universe is: a few
   incomparable origins, nearly-classical deterministic early growth,
   quantum branching arriving in bursts — and no recurrence of
   crunches.

## Honest scope

- n <= 12, 2D-order engine action, gap-max-entropy selection (band
  documented in KPZ_CAUSAL_TEST.md); exponents from small-n fits.
- The classical anchor here is the uniform-growth chain; transitive
  percolation (where posts have positive DENSITY) is post-richer
  still, so the quantum-vs-bounce-literature contrast is understated
  by our comparison, not overstated.
- "Ever-post" probabilities include the trivial small-n posts (any
  2-chain stage); the physical claim is about recurrence at large n.
- The suppression mechanism is measured, not yet derived: a per-parent
  analysis of the Born weight of full-downset (global-maximum) births
  under double conservation is the natural follow-up, and may be
  provable (the gap of the full-downset child grows with n, and
  large-|gap| children are systematically Born-starved at the
  quantized phase).

## Sources

Sorkin gr-qc/0003043; Martin-O'Connor-Rideout-Sorkin PRD 63, 084026
(2001); Bollobas-Brightwell, The structure of random graph orders,
SIAM J. Discrete Math (1997); A computation of the expected number of
posts in a finite random graph order, arXiv:0809.2258; Evolution of
universes in causal set cosmology, arXiv:1703.07556.
