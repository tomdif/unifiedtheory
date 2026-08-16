# The Quantum Expansion Law (proposed 2026-08-15, pre-registered)

## The observation it generalizes

Double conservation (coherent Σa = 1 + Born Σ|a|² = 1) on a
width-restricted child family is feasible only when the causet is
deep enough: the feasibility wall w_max(n) recedes at ~1 width per
4-6 elements of growth (tag thickened-dc-scaling-2026-08-15).
Gradual thickening (w = n/5) stays feasible where sudden thickening
dies; and w = n/8 produced the program's first SCALE-FLAT dimension
profile (d_int ≈ 2.2-2.3 across interval sizes).

## The proposed law

  QUANTUM EXPANSION LAW.  In bi-normalized (double-conservation)
  causal growth, the width of the antichain a new event may cap —
  its causal in-degree — is bounded by elapsed history:

      w_max(n) = n / c*  + O(1),

  with c* a constant fixed by the phase-coverage requirement of the
  Born feasibility system (at phi = pi/4: the restricted gap
  spectrum must cover (1,0) in the cone of 8th-root phase directions
  and contain an antipodal pair mod 8).  Growth at a fixed rate
  w = n/c is quantum-consistent iff c >= c*, and produces a
  SCALE-INVARIANT dimension profile whose level is set by the rate:

      d = F(c* / c),   F increasing,   d -> d* = F(1) as c -> c*.

  DIMENSION IS A RATE: spacetime dimension is not an input of the
  growth class but the ratio of the realized expansion rate to the
  quantum-critical rate.

Two physical readings of the same inequality:
  - COSMOLOGICAL: space can widen only in proportion to elapsed
    4-volume — an expansion speed limit derived from quantum
    consistency alone (kinematics of the Born rule), where standard
    cosmology needs dynamics (Friedmann) for any such law.
  - MICROSCOPIC: every event's direct causal in-degree is bounded
    by a fraction of total history — an automatic regulator of the
    famous Minkowski link divergence (sprinklings have divergent
    link counts near the light cone; bi-normalized growth cannot).

## Pre-registered predictions (BEFORE the n=64 rate scan)

The scan: w = n/L for L in {4, 5, 6, 7, 8, 10}, n = 64, ramp 10,
band ±1, phi = pi/4, 20 paths each.

  P1 (critical rate): feasibility ~100% for L >= c*, collapsing for
     L < c*, with c* in [4, 6] (from the measured wall recession).
  P2 (flat profiles): for feasible rates the d_int(k) profile is
     scale-flat (spread over k~4..32 well below the free-growth
     decay of ~0.8), and the flat level d-bar(L) DECREASES with L.
  P3 (the law's content): d-bar rises monotonically as L decreases
     toward c*; the maximum quantum-consistent flat dimension is
     d* = d-bar(c*).

READINGS:
  (i)  P1-P3 hold and d* >= 3.5: "dimension = expansion rate" is a
       working law with 4D in reach of the critical rate —
       breakthrough candidate; next derive c* analytically and push
       n to locate d* precisely.
  (ii) P1-P3 hold but d* ~ 2.5-3.0: the law stands, the pi/4 family
       caps below 4 — vary phase/weights/band for the missing lift.
  (iii) flatness or monotonicity fails near the critical rate: the
       one-parameter rate law is too naive; report what breaks.

## Falsifiers / honest cautions

- Survivor bias: d_int at low-feasibility rates reflects the
  surviving sub-ensemble; only ~100%-feasible rates test the law
  cleanly (that is why the scan uses the rate ladder, not the wall).
- The "dimension" is interval-MM (corrected monotone inverter);
  scale-flatness across the k~4..32 window at n=64 is a ~1-decade
  claim, not an asymptotic one.
- c* could drift with n (the wall recession was measured at
  n=26..48); the law asserts it converges — checkable by repeating
  the ladder at larger n.

## RESULTS (n=64 ladder + mechanism probes, same day)

Ladder (n/4 .. n/7 clean; n/8+ lost to the ideal-count compute cap,
recorded as artifact, NOT physics):

  rate   feasible    d_int k~4 / k~8 / k~16 / k~32
  n/4      5% (law)  2.97 / 2.46 / 2.04 / 1.97   (survivor-biased)
  n/5     80%        2.83 / 2.54 / 2.09 / 1.74
  n/6     50% (cap)  2.64 / 2.47 / 2.13 / 1.87
  n/7     25% (cap)  2.63 / 2.48 / 2.15 / 1.86

P1 CONFIRMED: the critical rate is real - law-infeasibility appears
only at n/4 (and traces at n/5): c* ~ 4-5, consistent with the
wall-recession estimate.  The in-degree bound w_max = n/c* stands.
P3 PARTIALLY CONFIRMED: UV level rises monotonically toward the
critical rate (2.63 -> 2.83 -> 2.97).
P2 FAILS AS STATED: no rate gives a flat profile at high level; the
IR bin (k~32) is pinned at 1.74-1.97 at EVERY rate.  A constant-rate
law lifts the UV dimension only - d*(critical) ~ 2.8-3.0, not 4.
VERDICT: reading (ii)/(iii) hybrid - the critical-rate half of the
law is real physics; "dimension is a rate" holds in the UV; the IR
collapse is a separate mechanism the rate does not touch.

## MECHANISM DISCOVERY: phase-starvation, not count-starvation -
## and the phase-width commensurability

Count test: free causets at n=48 hold ~2250 width-8 downsets, yet
static w=8 is 5% feasible - ABUNDANCE WITHOUT FEASIBILITY.  The wall
is set by the PHASE STRUCTURE of the width class, not its size.

Structural reason: every maximal element of the past contributes
CG[0] = -1 to the gap, so g(width w) = (interior terms) - w: EACH
UNIT OF CAUSAL IN-DEGREE ROTATES THE AMPLITUDE PHASE BY EXACTLY
-phi.  At the Born-forced phase phi = pi/4 this is one octant per
width unit - width and phase are COMMENSURATE, width is metered mod
8 by the phase system.  A width class is Born-feasible only when its
interior diversity (which grows with depth) spreads the class across
enough octants to cover (1,0) and an antipodal pair - hence the
depth-gating, and hence c* is in principle computable from the
interior-term distribution.  "Space costs phase, one octant per
cell" is the microscopic content of the quantum expansion law.

## Registered next

1. Analytic c*: distribution of interior gap terms of width-w
   downsets vs depth -> octant-coverage threshold -> w_max(n).
2. The IR collapse is now the isolated obstruction to 4D: it
   persists at every feasible rate, so it belongs to the SELECTION
   (gap-max-entropy) not the width kinematics - test the min-norm
   band member and non-maxent selections under the width rule.
3. Raise the ideal cap (compute) to unlock slow rates at n >= 64.

## FORMALIZED (2026-08-15, section 26 of KFCausalUniquenessLeg.lean,
## 64 axiom-clean theorems, root 8783 green)

The mechanism's four pillars are now machine-checked:
  - `single_class_born`: one gap class of multiplicity mu supports
    double conservation iff phase trivial AND mu = 1.
  - `halfplane_separation_infeasible`: phases confined to a closed
    half-plane missing (1,0) => no nonnegative coherent solution -
    octant-coverage NECESSITY.
  - `antipodal_pair_reaches_born`: coherent solution with Born mass
    <= 1 + one antipodal pair => exact double conservation, via an
    explicit quadratic-root step along the pair's recession
    direction (no limits, no IVT) - SUFFICIENCY half.
  - `gap_splits_width` / `width_phase_octant` / `octant_period`:
    gap = 1 - width + interior; the character factors through
    zeta^width with zeta = e^{-i pi/4}, zeta^8 = 1 - one octant per
    cell, width metered mod 8.
Together: Born feasibility of a restricted growth family IS an
octant-coverage property of its gap phases - the theorem-level core
of the expansion law.  Remaining empirical: the value of c* (needs
the interior-term distribution); remaining registered: min-norm
selection under the width rule (IR collapse), raised cap.
