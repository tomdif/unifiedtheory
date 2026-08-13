# Integrability probe + finite-size control: the TW headline corrected
# (2026-08-13)

## 1. The Born chain is NOT a tilted Plancherel measure (exact, n<=8)

Test: is ln[P_Born/P_Plancherel] affine in the action (+ local
invariants)?  Exact class-level comparison (class-max-ent DP vs
permutation counts):
   TV(Born, Plancherel) = 0.557 / 0.582 / 0.609 / 0.645 at n=5..8
   (GROWING); tilt fit R^2 = 0.01 (S), 0.10-0.31 (S+minima+links),
   log-residuals up to ~9; supports mismatch both ways; height
   marginals qualitatively different (Born peaks h=3, Plancherel h=4).
VERDICT: registered reading (iii).  The natural integrable-transfer
route (RSK/Schur with an exponential potential) is CLOSED.  If a
determinantal representation of the Born chain exists it must come
from a different structure (LGV on the ideal lattice remains
unexplored); absent that, any TW-like behavior is universality-class
phenomenology, NOT machinery that could transfer to the RH program.

## 2. Finite-size control: the TW yardstick at n=28 was wrong

Uniform-permutation LIS (the integrable case) at matched sizes,
150k MC each:
   n=20: skew +0.363   n=28: +0.351   n=40: +0.350   (SE 0.006)
   vs TW asymptote 0.224 - the integrable ensemble itself sits at
   ~0.35 in this size range (slow BDJ convergence).
CONSEQUENCE for the n=28 quantum result (+0.257 +- 0.071): it is
consistent with the TW asymptote (z +0.5), consistent with finite-
size Plancherel (z -1.3), and excludes Gaussian (z +3.6).  The
defensible statement is: NON-GAUSSIAN, POSITIVELY SKEWED, KPZ-
NEIGHBORHOOD - not yet a class assignment.  The classical
uniform-downset chain (+0.648 +- 0.14) differs from BOTH references;
the quantum-vs-classical contrast stands.

## 3. Corrected interpretation frame for the hardening run

The multi-size run (tw_harden, in flight) must be read against THREE
references at matched size: finite-size Plancherel (~0.35), TW
asymptote (0.224), Gaussian (0).  Outcomes: quantum tracking ~0.35 =
finite-size-Plancherel-like fluctuations (class contact, still not
integrability - see part 1); stable ~0.25 = below the integrable
finite-size curve, a DISTINCT skewed law; drifting to 0 = Gaussian
after all.  The multinomial Delta-LL vs the asymptotic TW density is
correspondingly demoted from class test to non-Gaussianity test.

## Process note

Both corrections originated from referee-style pressure on a
same-day headline ("consistent with TW") before it propagated: the
structural transfer hope is closed by exact computation, and the
moment-level claim is re-based to matched-size references.
