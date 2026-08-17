# Manifold-likeness ledger (repo-wide sweep, 2026-08-17)

Where manifold structure ACTUALLY shows up across all results to
date, organized by scale and sector.  Full details in the cited
docs; retraction-checked (see JITTER_AUDIT.md; HOW_TO_GET_4D.md).

## POSITIVE (manifold-like), by sector

IR / COMPOSITE SECTOR (the strong signals):
 1. Composite (2x2, 1024 el.) IR interval profile lands ON the 4D
    Minkowski benchmark: f(k~256)=0.1008 vs 0.0994 (1.4%);
    engineered 48x48: f(k~512)=0.0924 (8%).  [COMPOSITE_BRIDGE.md]
 2. Cone rounding: opening angle -> 30.38 deg (exact inscribed
    30 deg), anisotropy ~1/m (12x drop by m=32); ensemble cone
    3.0x rounder than any single history.
 3. SJ modes extended (PR up to 309/576) + massless-like linear
    dispersion on the grown composite (rel. intercept 0.19);
    sprinkling validation textbook.  [GATE 2 OPEN]
IR / FREE GROWTH (chart-free observable):
 4. Height exponent = 0.50 EXACTLY over n=20..80 - the 2D
    longest-chain manifold law.  NEWLY FLAGGED SPLIT: the UV
    exponent is 0.69 (n<=12, anti-KPZ) and flows DOWN onto the
    manifold value 0.50 in the IR.  Previously unremarked.
UV / COHERENT MEASURE (weak, flagged):
 5. Balance point <r>_mu = 0.5060 vs sprinkling 0.5014 exists -
    margin 0.005 SUSPECT (below old-solver contamination scale).

## NEGATIVE (non-manifold-like)

 1. GATE 1 CLOSED (UV texture): N0,N1,N2 gap 8-10x from sprinkling
    under decohered AND coherent measures, growing through n=10
    (corrected converged-law ladder confirms increments RISING).
 2. Free growth global d_eff: monotone decline to 1.666 at n=80
    (asymptote ~1.58), spectral d_s 2.74 -> 0.10 monotone; no
    upturn anywhere.
 3. INVERTED FLOW: free growth runs UV ~2.5 -> IR ~1.7 - the
    OPPOSITE of CDT dimensional reduction.  Member- and
    rate-independent (CHASM_ATTACKS).  UV ceiling 2.65 across the
    12-phase family: 4D not in the free family.
 4. r crosses the 2D manifold value 0.5 at n~11-13 and keeps
    rising (0.6575 at n=80): UV and IR sit on OPPOSITE sides.
 5. Composite is a Winkler (polyhedral) order; exact Lorentz cone
    provably unreachable by finite products; product phase erodes
    under free growth (89% non-product pasts); k not selected.

## THE PATTERN

Manifold-likeness in this program is (a) an IR phenomenon, (b)
concentrated in the STRUCTURED (composite/coupled) sector, (c)
visible even in free growth only through chart-free observables
(height exponent).  The two sectors flow in OPPOSITE directions:
free growth flows DOWN AWAY from its manifold value (2.5 -> 1.7,
crossing 0.5 in r); the composite flows DOWN ONTO its manifold
value (7 -> 4.0, landing on the benchmark).  The gate-1 texture
criterion is maximally UV (0/1/2-element intervals) and fails for
every measure - but UV failure is what discreteness predicts.

## THE CRUX (open, probe running)

Are the gate-1 UV failure and the composite IR success the same
object at two scales?  uv_ir_split.py (registered 2026-08-17,
n=64, 30 causets, converged deterministic law) measures BOTH ends
on the same free-grown causets.  Reading (i): d_int(k) -> 2 in IR
while UV stays off => gate 1 was a UV-only criterion; reading
(ii): off at all scales => free growth is scale-robustly
non-manifold and the composite sector is the ONLY manifold route.
NOTE: the deep-sampler data (d_eff 1.666 falling, inverted flow)
predicts reading (ii) for free growth - which would sharpen the
program's claim: MANIFOLD-LIKENESS IS BOUGHT BY STRUCTURE
(composition/coupling), NOT BY THE FLAT LAW.
