# The censorship mechanism: meter rotation vs interior spread
# (2026-08-16, deep dive)

## De-confounding: censorship is GEOMETRY-SELECTIVE, not universal

The grown-ensemble censorship curve (wmax ~ n/c*) was confounded:
grown widths are themselves ~n/5.  The de-confounder is an
engineered geometry solved ANALYTICALLY: k parallel chains.  For
the 4D coefficients the per-chain contribution to a downset's gap
telescopes to c(a) = 0, -1, 8, -8, 0, 0, ... (prefix length a) -
verified exactly against direct interval counting.  Hence
gap = 1 + sum_i c(a_i), and mod 8 only a_i = 1 contributes: the
collapse family {width >= w} covers ALL EIGHT OCTANTS at every w,
and maxent feasibility holds at every width (k=8, m=5: all
families w=2..8 feasible, 1.7M downsets at w=2).
COLLAPSE OF ARBITRARILY WIDE PARALLEL-CHAIN REGIONS IS UNCENSORED.

## The starvation mechanism in grown causets: the meter rotates the
## family into the anti-coherent half-plane

Octant-mass tables of the collapse family {indegree >= w} at n=22:
as w rises the mass distribution ROTATES by ~ -1 octant per width
unit (the width-phase meter acting on the family) and NARROWS:
  w=2: peaks at octants 0,7 (coherent side)  -> feasible 12/12
  w=4: peaks at 6,7                          -> feasible 12/12
  w=5: mass at 4,5,6 (anti-coherent side)    -> feasible 3/12
  w=6: mass at 3,4,5                         -> feasible 1/12
  w=7: mass at 2,3,4 - half-plane missing (1,0) -> feasible 0/4
The wall is exactly the machine-checked half-plane criterion
(halfplane_separation_infeasible, section 26) firing on the rotated
family.  MECHANISM: censorship = meter rotation (-1 octant per unit
of demanded convergence) outrunning the family's interior phase
SPREAD; feasibility survives while the spread can still bridge back
to the coherent direction (1,0).  Parallel chains evade it because
their interior structure cancels the rotation mod 8 (flat
geometry); generic grown geometry cannot.

## Quantum vs classical grown: nearly identical censorship

Classical uniform-grown causets show the same rotation and nearly
the same wall (w=5: classical 9/12 vs quantum 3/12 feasible - the
quantum-grown geometry is slightly MORE censored).  Censorship is a
property of GENERIC grown geometry under the Born-feasibility test,
not of the quantum ensemble per se.

## The analytic c* route (registered, now concrete)

wmax(n) = the width at which rotation (-w octants) exceeds the
family's phase spread sigma_oct(n), which grows with n through
interior interval diversity.  c* = lim n / wmax = the ratio of
depth-growth of sigma_oct to the one-octant-per-unit rotation.
Fitting sigma_oct(n) from the octant tables gives c* analytically -
the registered next step.

## Corrected physics statement

The Born rule censors the simultaneous collapse of GENERIC grown
regions at the same rate it rations expansion (one constant c*),
because demanded convergence rotates the option-family's quantum
phase into the anti-coherent half-plane faster than geometric
diversity can compensate.  Specially structured (rotation-
cancelling, "flat") regions - parallel chains - collapse freely at
any width.  Censorship is a GEOMETRIC SELECTION EFFECT of the
octant meter, not a universal prohibition.
