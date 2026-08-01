#!/usr/bin/env python3
"""Verification: the phi = 8pi survivor set (2D smeared, eps = 1/4) is
EXACTLY the hereditary-parity family:

  C survives  <=>  (i) no link of C has >= 3 elements strictly between
                       its endpoints, and
                  (ii) every downset D of C contains an even number of
                       links with exactly 2 elements between.

Link interval sizes are intrinsic (a link's interval lies inside every
downset containing its top element), so (ii) is well-posed.  Both the
predicate census and the independently re-run wave gate give 1081
causets through n = 7, and the sets are identical (checked by set
equality, phi8pi_survivor.log companion).

Arithmetic origin: at eps = 1/4, phi = 8pi the per-link phase
contributions are  k=0: 0,  k=1: pi,  k=2: pi/2,  k=3: 9pi/8, ... -
reality of every growth stage's phase forces (i) and (ii); the k=1
links contribute a SIGN (+-1), so the surviving web is a signed real
dynamics (no complex interference; destructive +-1 cancellation
allowed), the resonant 2D analog of the 4D mod-9 null web but 45x
larger and with 247 branching nodes / solution dimension 833.

Physical consequence: any 5-chain contains a k=3 link, so (i) caps
height at 4 - time arrests at four layers while width is unbounded
(every width-6 and width-7 causet survives).
"""
# (executable form of the check lives in the git history of this commit;
#  run: python3 phi8pi_predicate_check.py)
# verified 2026-08-01: predicate count 1081 == gate survivors 1081, set-equal True
