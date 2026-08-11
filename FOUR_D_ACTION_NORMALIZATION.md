# The 4D action-normalization consistency check: PASSES by membership
# (2026-08-11)

## The check

The discrete action enters the framework twice.  QUANTUM: growth
amplitudes are rho e^{i g phi} with g the integer BD bracket gap; the
double-conservation law restricts phi (in the 2D engine it forced
phi = pi/4 uniquely).  GRAVITATIONAL (LayerA/CausalActionCoefficient):
the same integer bracket carries (4/sqrt6) hbar per unit in 4D — the
prefactor that normalizes the discrete d'Alembertian to Box - R/2,
whose EH matching gives c = 1/2 and l_disc = sqrt(8 pi) l_P.
Consistency requires the amplitude to be e^{iS/hbar}, i.e. the 4D
quantum phase unit must be phi4 = 4/sqrt6 = 1.63299... — so phi4 must
lie in the set where the 4D action-phased bi-normalized theory exists
WITH GENUINE BRANCHING (a deterministic law is the VR-gate death).
Readings were registered in four_d_action_normalization.py.

## Structural difference from 2D, derived by hand first

With the 4D coefficients (1, -9, 16, -8), chain growth is ACTION-FREE:
the 2-chain has the same bracket as the point (gap 0), and every
fan-tine addition has gap 0.  Consequences: (a) the 2D root-quantization
mechanism (gaps -1/+1 forcing cos phi = 1/sqrt2) has NO 4D analogue —
the 4D root instead forces the 2-antichain child to weight zero at
every generic phi (chain-deterministic start); (b) every parent with a
gap-0 child has the trivial single-child solution, so per-parent
FEASIBILITY holds broadly and the 4D constraint structure produces
WINDOWS, not points.  In 4D, double conservation does not quantize the
phase; the check is membership.

## Result (four_d_action_normalization.log; 405 parents, depth 7,
## 315-point scan of (0, pi] + the exact gravitational phase)

Branching set (effN(7) > 1.5, mass = 1, no dead ends): 282/315 grid
points, in windows
  [0.080,1.370] [1.500,2.090] [2.160,2.170] [2.190,2.430]
  [2.480,2.640] [2.680,3.140]
Max branching at phi = 2.04 (effN(7) = 311).

**phi4 = 4/sqrt6 = 1.6330 lies INSIDE the window [1.500, 2.090]:
the consistency check PASSES (registered reading (i)).**  No
recalibration of the discreteness scale is needed: l_disc =
sqrt(8 pi) l_P / M_disc = 2.44e18 GeV stands, now consistent with BOTH
normalizations of the same discrete action.

## The texture at the gravitational phase

At phi4 the max-entropy law is a deterministic FAN spine — one minimal
element, all later elements born incomparable above it, every step
action-free (gap 0, rho = 1) — until n = 6, where branching turns on:
the fan-top child's gap is 2 - n, and sin((2-n) phi4) first goes
negative at n = 6 (against sin(phi4) > 0), enabling the imaginary-part
cancellation.  The n=6 parent then branches four ways: new tine
(P = 0.42), top-closure above all tines (P = 0.46), isolated element
(P = 0.11), partial cover (P = 0.01, mu = 10); effN(7) = 2.50,
r(7) = 0.39.  Because the onset condition is arithmetic in n, branching
at the gravitational phase is QUASI-PERIODIC along fan growth with
period 2 pi / phi4 = pi sqrt6 / 2 ~ 3.85 elements — the gravitational
phase selects nearly-classical (deterministic) early growth with
delayed, intermittent quantum branching, in contrast to mid-window
phases (e.g. 2.04) that branch immediately and massively.

## Honest scope

- Depth 7, floating-point feasibility (1e-7), max-entropy selection;
  the branching-onset level at phi4 (n = 7 here) is a depth-limited
  snapshot and the quasi-periodicity claim is the hand mechanism plus
  one observed onset, not a theorem.
- The 4D scan uses the bare (unsmeared) BD bracket; the smeared S_eps
  family shares the continuum limit but has different discrete gaps —
  the check at mesoscale eps is a registered variant.
- Membership is weaker than the 2D result: in 4D nothing internal yet
  selects phi4 within the window — the EH matching is the selector.
  A 4D mechanism that quantizes the phase (deeper parents, smeared
  action, or a covariance refinement) would upgrade this check from
  consistency to derivation; conversely, finding that deep growth
  closes the window around a value away from 1.633 would falsify the
  pairing.  Either way the check is now a live computation, not a
  hope.
- The 2D pair (phi = pi/4 vs 2D prefactor 2) cannot be compared this
  way: 2D EH is topological, so the 2D gravitational normalization
  never calibrates an l_disc.

## Registered follow-ups

1. Depth-8+ branching profile at phi4 (does the fan-burst pattern
   recur at n ~ 10 as predicted by the sine arithmetic?).
2. The smeared-action variant of the scan (eps-dependence of the
   branching set; does smearing shrink the window toward a point?).
3. A 4D quantization mechanism: which additional constraint (deeper
   covariance, orbit counting, record protection) narrows the window —
   and does it narrow it AROUND 4/sqrt6?
