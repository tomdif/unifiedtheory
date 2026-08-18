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

## THE CRUX - ANSWERED (2026-08-17, deep_uvir_stress.py)

The gate-1 UV failure and the composite IR success ARE the same
object at two scales, and both are WINDOWS, not asymptotes:
free growth crosses d=2 at k~32 (n=64) then keeps falling; the
composite crosses d=4 at the SQUARE of the factor crossing scale
(transfer law d_prod(k)=2*d_2D(sqrt k) verified to <=0.07 for
k>=64, exact at k~512).  The flagship "IR=4D to 1.4%" was the
crossing point at 32-element factors.  See COMPOSITE_BRIDGE.md
"THE WINDOW LAW".  Constructive follow-up registered: sqrt-width
factors pinned at d=2 would make the 4D window an asymptote.

## THE CRUX AS ORIGINALLY REGISTERED (superseded)

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

## THE BIRTH-FROZEN WINDOW (2026-08-17, corrected synthesis)

Window scaling (n=32..96): k_x = 4.5*sqrt(n) (ratios 4.2-4.8, no
trend); every fixed-k dimension RISES with n (d16: 2.17->2.58;
d45: 1.89->1.96).  Frontier test REFUTED the naive frontier
reading: bulk(age)-restricted sampling moves the crossing IN
(43.5 -> 30.2, -31%) and lowers d at every k.
MECHANISM (exact structural fact): INTERVALS FREEZE AT BIRTH -
I(x,y) is a function of past(y) only, fixed at y's birth.  The
ensemble profile is an age mixture of frozen snapshots:
  - each element's past is manifold-like up to k ~ 4.5*sqrt(birth
    time), over-ordered beyond (permanent, never heals);
  - fixed-k ensemble d rises with n as young tops dominate;
  - the crossing tracks the youngest tops: k_x ~ 4.5*sqrt(n);
  - age cuts rewind the ensemble (hence the negative shift).
PHYSICAL READING: an observer at cosmic time n inherits a past
manifold-like out to scale ~4.5*sqrt(n); the non-manifold residue
is confined to the deepest (horizon-tail) scales and diverges away
as the universe grows.  Via the verified transfer law the same
statement holds for composites with 4D in place of 2D.
OPEN EDGE (honest): whether the young-top limit profile descends
exactly to 2 (clean manifold bulk) or plateaus slightly above
(2.0-2.2) needs n >> 96.  UV elevation ~2.8-2.9 at k~4-8 is stable.
Trivially provable sub-statement for the Lean file: interval
abundances of (x,y) depend only on the downset of y.

## FIXED-SCALE HEALING (2026-08-18, n=112 quartile run — limit_profile_120.py)

Fifth point on the window law: all-tops k_x = 46.1 at n=112 vs
4.5*sqrt(112) = 47.6 (law holds over 3.5x in n, ratio 4.2-4.8).
Birth-frozen model QUANTITATIVELY CONFIRMED by quartile split:
crossings 25.4 / 38.1 / 50.6 (Q2/Q3/Q4) vs mean-birth predictions
29 / 38 / 44 (+-15%; Q3 exact).
DECISIVE: FIXED-SCALE HEALING - d(45) = 1.89 (n=64) -> 1.96 (96)
-> 2.01 (112): a fixed scale that was sub-manifold has risen
THROUGH 2.  d(16), d(32) still climbing; d(4), d(6) converged
(2.73, 2.83).  Bulk limit profile: discreteness dip at k~4, UV
peak ~3.0 at k~8-11, smooth descent toward 2 at large k.
STATEMENT EARNED: for the free law, manifold-likeness at any fixed
scale is asymptotic in cosmic time - over-ordering at fixed k is a
transient, permanently visible only at the receding 4.5*sqrt(n)
edge.  Same for composites at 4D via the transfer law.  New open
characterization: the UV peak (~3.0, a +1 discreteness-scale
dimensional elevation - a falsifiable signature).
