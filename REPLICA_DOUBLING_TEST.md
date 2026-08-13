# The replica exponent-doubling test: the doubling heuristic FAILS as
# stated — and a replica-correlation structure falls out (2026-08-13)

## What was tested

Yesterday's insight note claimed: Q = R^2 (phases idle) should make
rare-event measure-fractions decay at ~2x the one-replica exponent,
and offered the anti-KPZ posts pair (n^-2.03 vs n^-0.90, ratio 2.25)
as the first instance.  Exact-DP test (no sampling noise), 2D pi/4
class-max-entropy law, n = 4..8, four weightings of the same tree
(R one-replica, Q = R^2, P Born diagonal, U uniform chain); rare
events {has-post, is-antichain, 3+ minima} vs bulk controls
{links/n, minima, N1/n}; corroboration slopes from the sampled 4D
posts data.  Readings registered in replica_doubling_test.py.

## Result: the naive doubling is REFUTED; the rare/bulk split survives

  event          a_R      a_Q      a_P      a_U     a_Q/a_R
  has_post      -2.53    -3.59    -1.59    -0.84      1.42
  is_antichain -12.32   -15.49    -9.66   -21.66      1.26
  bulk controls (links/n, minima, N1/n):               1.06-1.12

1. a_Q = 2 a_R FAILS (1.42, 1.26 - far from 2).  Reading (iii) for
   the doubling law itself.
2. The RARE/BULK dichotomy is confirmed: squaring adds suppression
   only to rare events (Delta-a = -1.1 for posts, -3.2 for
   antichains, ~0 for all bulk controls).  Qualitative half survives.
3. ATTRIBUTION CORRECTION (referee note on my own claim): the
   original anti-KPZ pair compared the SAMPLED Born chain to the
   uniform chain - i.e. a_P vs a_U, not a_Q vs a_R.  For posts that
   ratio is ~2 in three independent datasets (exact 2D: 1.90; sampled
   2D: 2.25; sampled 4D: 2.42) - a real regularity - but it is NOT
   universal (antichains: 0.45) and my replica explanation of it was
   wrong.  Yesterday's insight item 4 is hereby corrected: the
   replica square explains the EXISTENCE of rare-specific extra
   suppression, not a factor-2 law.

## What fell out: measurable replica correlation

Per class, Q = R^2 is exact (theorem).  At EVENT level the doubling
would need the two replicas to be independent; the deviation is a new
observable - the replica overlap on an event:

    c(n) = f_Q(A, n) / f_R(A, n)^2
    has_post: 2.40, 3.60, 4.05, 5.40, 7.05   (n = 4..8, GROWING)

c(n) > 1 and rising ~ n^1.5: the two replicas of the growth process
are POSITIVELY CORRELATED on rare events - two "worlds" agree on the
presence of a post far more often than independent worlds would.
This is a nontrivial replica-overlap structure (spin-glass-flavored)
in the covariant quantum measure, and it - not naive squaring - is
the quantitative content of the anti-KPZ deformation class.  The
overlap c(A, n) is now the natural object: the large-deviation
dictionary registered earlier should be built for it.

## Honest scope

- n = 4..8 exact window (5 points); is_chain unreachable at pi/4
  (support-pruned - itself a destructive-interference exclusion,
  consistent with the legislating-phase picture).
- Class-max-entropy variant; sampled corroborations use gap-max-ent.
- The bulk-control ratios (1.06-1.12) are close to but not exactly 1;
  window-limited.

## Registered follow-ups

1. Replica-overlap exponents: c(A, n) ~ n^gamma_A per event class -
   is gamma_A a function of the event's own rarity exponent
   (a candidate scaling law to replace the dead doubling law)?
2. The P-vs-U posts ratio ~2 across engines: separate empirical
   regularity, mechanism unknown - test on more count observables.
3. Formalization target (deferred from yesterday's request): the
   per-class Q = R^2 identity and the event-level overlap bound
   1 <= c(A) <= 1/f_R(A) are Lean-shaped; the interesting content is
   which dynamical laws make c grow.
