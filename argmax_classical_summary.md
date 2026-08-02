# Depth-8 extraction: argmax vs classical (2026-08-02)

Logs: argmax_classical.log, membership_fix.log.

1. BENCHMARK CORRECTION.  The classical random-2-order mean ordering
   fraction at n = 8 on the confined family is 0.5000 (4M samples,
   all 14794 stems covered); 0.533 was the n = 7 value.  The depth-8
   sup (0.5353) cleared the depth-appropriate benchmark by 0.035 —
   the "suspicious 0.002 proximity" was a depth-7 number compared
   against a depth-8 quantity.  (The classical value itself converges
   to the continuum 1/2 with n, as expected.)

2. ARGMAX MEMBER.  Uncorrelated with the classical profile:
   corr = 0.0075, L1 = 1.31 (max 2); its top stems carry ~40x the
   classical weights.  The maximizer is not a deformation of
   classical dynamics.

3. MEMBERSHIP.  Min relative L1 distance from the self-similar
   polytope to the classical profile: 1.04 — farther than the
   depth-7 plain-family fit failure (0.77).  The classical point is
   NOT inside, nor near: the polytope crossed the classical MEAN
   while remaining unlike the classical MEASURE.  The onset-capture
   reading (polytope grows until it contains classical dynamics) is
   refuted; the sup crossing is a one-moment statement.

Sup solver cross-check: IPM reproduced sup = 0.5352513327144708 to
13 digits across two independent runs; the simplex path was retired.
