# How to get emergent 4D — CORRECTED (2026-08-15)

## RETRACTION of the same-day "locked at d_int = 2" claim

The earlier version of this note reported d_int = 2.00 EXACTLY at
every phase and every interval size, and concluded the growth class
is locally 2-dimensional with phase-independence.  That result was
an ESTIMATOR ARTIFACT, caught when asked to promote it to a theorem:
the Myrheim-Meyer inverter passed a NON-MONOTONIC xp array to
np.interp, which silently clamps every ordering fraction f <= 0.5 to
d = 2.00.  Every "2.00" in that table was the clamp, not physics.
The claim "free-downset sequential growth is locked at d_int = 2" is
therefore REFUTED as stated - it was never supported by the data.

Diagnostic fingerprint for the future: a measured dimension landing
on an exact integer, identically across all conditions and bin
sizes, is an estimator pathology until proven otherwise.  (Same
family as the calibrate-before-hash and diagnostic-vs-name rules.)

## The corrected measurement (monotone inverter, raw f reported)

pi/4 law, n = 24 quick pass (corrected table below from the n = 40
seven-phase rerun, logs_emergent_4d_search_corrected.txt):

  interval size k~4:  f = 0.306  ->  d_int = 2.63
  interval size k~8:  f = 0.384  ->  d_int = 2.34

d_int is NOT 2, NOT phase-independent a priori, and DECREASES with
interval size toward the global (hyper-ordered) figure ~1.8.  Small
intervals are the LEAST ordered structures in the causet - the local
dimension at the discreteness scale sits ABOVE 2 and falls as the
window grows.  The scale profile d_int(k), per phase, is the real
dimension landscape; the corrected 7-phase scan measures it.

## What survives, what changes

SURVIVES: the global/spectral negatives (bare d_eff declines to
~1.67 at n=80; spectral d_s falls monotonically; MM coarse-graining
is thinning-invariant) - none of those used the broken inverter.
Large-scale dimension does not flow up at accessible size.

CHANGES: the local story.  With d_int(k~4) ~ 2.6 > 2 and falling in
k, the correct question is no longer "why is it locked at 2" but:
  (a) how HIGH does small-interval d_int go across the phase family
      (does any phase push the discreteness-scale dimension toward
      4)?  - measured by the corrected scan;
  (b) WHY does d_int fall with scale (the hyper-ordering sets in at
      a characteristic interval size - is that size phase-dependent?);
  (c) the "different growth rule" routes (thicker-antichain /
      higher-arity conservation) remain live but are no longer the
      only options - the phase family has genuine local-dimension
      variation to map first.

## Status

Corrected 7-phase n=40 scan: logs_emergent_4d_search_corrected.txt
(readings re-registered on the corrected estimator: (i) local 4D at
some phase; (ii) landscape max below 4 but phase-dependent - report
the profile; (iii) profile phase-independent within errors).
