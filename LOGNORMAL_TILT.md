# The tilt mechanism: f_R is the geometric mean of counting and
# coherence — the "0.7" demoted to an artifact (2026-08-13)

## The test

Ansatz: per level, ln R across classes is ~Gaussian and conditioning
on an event shifts its mean, not its variance.  Parameter-free
consequences tested (lognormal_tilt_test.py, exact DP, 12 events,
n = 4..8): T1 c(A)·f_count(A) = 1; T2 a_Q + a_count = 2 a_R;
T3 participation density N_part(A)/|A| uniform across events.

## Result: reading (i) with honest caveats

  T2 (the linear exponent law): residual a_Q + a_count - 2 a_R has
      MEAN +0.074 across 12 events spanning a_Q from -3.6 to +4.4;
      scatter +-0.4 (5-point windows, three fits each); the one large
      outlier (-0.90) is the antichain - a SINGLE class at n = 8, the
      extreme tail where a mean-shift-only ansatz must fail.
  T1: c·f_count = 0.79-0.99 for 11/12 events at n = 8, flat in n
      (antichain again the exception, 0.33).
  T3: participation density 0.33-0.48 across events with |A| from
      960 to 12444, ratio to Omega 1.0-1.5 - near-uniform.
  Gaussianity: ln R has skew ~ -0.4, excess kurtosis ~ -0.4,
      sigma(n) growing 1.31 -> 1.59 - roughly Gaussian, thin tails.

## The law, in its clean form

    f_R(A)^2  ~=  f_count(A) * f_Q(A)        (to ~15%, 11/12 events)

**The R-fraction of any event is the geometric mean of its counting
fraction and its coherent fraction**: the four measures line up as an
exponential tilt family theta = 0 (counting), 1 (R), 2 (Q = coherent),
with ln f_theta(A) approximately LINEAR in theta.  Everything else
follows: c(A) = 1/f_count(A) (overlap = inverse counting rarity);
gamma_A = -a_count exactly; and the "0.7" of yesterday's scaling law
is DEMOTED - it was the regression slope of gamma against a_R,
dominated by the heaviest events, i.e. the average of the
non-universal ratio a_count/a_R (measured 0.85 +- 0.58 across events).
The fundamental object is the linear tilt identity, not any single k.

## What this closes and opens

CLOSED: the anti-KPZ deformation class is identified - it is the
EXPONENTIAL-TILT (lognormal) class: quantum suppression of rare
geometry = counting rarity acting twice (once as itself, once through
the tilt), nothing more exotic.  The replica overlap, the
effective-geometry counting, and the a_Q/a_R ~ 1.3-1.4 ratios are all
faces of one Gaussian tilt structure with slowly growing sigma(n).

OPEN (registered):
1. Second-order tilt: the antichain deviation should be captured by a
   variance-shift term (a_Q + a_count - 2a_R = -Var-shift); one more
   moment closes the extreme tail.
2. Where does P sit on the tilt line?  W is not e^{2x} of the same
   variable; measuring the effective theta_P(A) per event would place
   the Born channel inside the family (and may explain the P-vs-U ~ 2
   posts regularity).
3. sigma(n) growth (1.31 -> 1.59, ~ +0.09/element): the one remaining
   dynamical input; a random-multiplicative-cascade argument for the
   R-DP would derive it and with it every exponent in this note.

## Honest scope

Five-point exponent windows; 12 events, one engine, one selection;
the ansatz is verified at the ~15%/±0.4-exponent level, not exactly;
the antichain tail genuinely deviates (as the mechanism itself
predicts it must).
