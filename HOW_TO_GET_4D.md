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

## RESULT (corrected scans, 2026-08-15): the ceiling is ~2.6.
## No phase pushes toward 4.  Reading (iii) at both depths.

Dense scan, 12 phases phi in [0.3, 3.1] (n=24, 30 paths/phase,
logs_d_int_phase_scan_n24.txt) and 7-phase confirmation at n=40
(logs_emergent_4d_search_corrected_n40.txt):

  d_int(k~4):  2.19 - 2.65  across the entire phase family
  d_int(k~8):  2.07 - 2.48
  d_int(k~16): 1.83 - 2.21
  d_int(k~32): ~1.7 - 1.9   (n=40, low stats)
  global:      ~1.7 - 1.85

1. CEILING ~2.6: the discreteness-scale interval dimension tops out
   at 2.55 (n=24) / 2.65 (n=40, at pi/6), far below manifold-4D.
   No phase in the family reaches toward 4.
2. WEAK PHASE DEPENDENCE: the whole family lives in a narrow band
   (~0.2-0.4 wide).  The phase reweights the measure but cannot
   change the dimension class.  (pi/4 shows the lowest small-interval
   d_int and the highest global ordering - the Born-selected point is
   the most-ordered member - but the band is too narrow and
   n-dependent to over-read.)
3. UNIVERSAL INVERTED-FLOW PROFILE: at EVERY phase, d_int falls
   with scale: ~2.5 (k~4) -> ~2.35 (k~8) -> ~2.1 (k~16) -> ~1.8
   (k~32) -> ~1.7 (global).  The family is ~2.5-dimensional at the
   discreteness scale and flows DOWN to ~1.7 in the IR - the
   OPPOSITE profile to CDT-style dimensional reduction (UV 2, IR 4).

CONCLUSION: emergent 4D is definitively not in the free-downset
gap-phase family - established on the corrected estimator, densely
in phase, at two depths.  The mechanistic routes stand: to get 4D
requires changing the GROWTH CLASS (thickened-antichain / multi-
parent past selection, or a higher-arity conservation law), not the
phase.  The registered open question is now whether a thickened-
antichain growth rule admits a double-conservation (coherent+Born)
formulation at all.
