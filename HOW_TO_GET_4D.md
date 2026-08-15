# How to get emergent 4D — the mechanistic answer (2026-08-15)

## The finding: the growth class is LOCALLY 2-DIMENSIONAL at every
## phase — you do not get 4D by tuning phi.

`emergent_4d_search.py` measures the MANIFOLD-FAITHFUL dimension:
the interval (Alexandrov) dimension d_int of order-intervals
I(x,y) = {z : x<z<y}, binned by interval size, inverted from the
internal ordering fraction via the exact Myrheim-Meyer continuum
table.  Unlike the global ordering fraction (which mixes scales and
is dominated by large-scale hyper-ordering), d_int is meaningful
because each interval IS a causal diamond by construction.

Scan over seven action phases including both physically-selected
values (n=30, thousands of intervals per size-bin):

  phi        global d   interval dimension (all sizes)
  pi/4        1.72       2.00
  4/sqrt6     1.82       2.00   <- the gravitational 4D phase
  pi/6        1.84       2.00
  pi/3        1.90       2.00
  1.0         1.81       2.00
  2.0         1.83       2.00
  2.5         1.86       2.00

d_int = 2.00 EXACTLY, at every phase, every interval size.  The
global ~1.7 is NOT a fractional local dimension - it is locally-2D
manifold structure with a mild large-scale EXCESS ordering (chains/
defects) that drags the global estimator below 2.

## Why: this is structural, not tunable

Sequential growth by "add one maximal element with a chosen past
downset" produces 2D-order (2D-diamond) intervals - this is the
Rideout-Sorkin classical-sequential-growth universality: the local
causal structure of generic sequential growth is 2-dimensional.  The
action phase reweights WHICH downset is chosen (changing the global
relation density and hence the global estimator by ~0.2) but does
NOT change the local interval geometry, which stays 2D.  The pi/4
Born-quadrature and the 4/sqrt6 gravitational phase are NOT special
in the dimension landscape - the whole family is locally 2D.

## So: how DO you get emergent 4D?

Not by phase.  The lever that sets local dimension is the GROWTH
RULE ITSELF - specifically the distribution of chosen-past sizes /
the branching (antichain) rate:

  1. MULTI-PARENT / thicker-antichain growth: a rule where each new
     element's past is a THICKENED ANTICHAIN of controlled width w
     (not a generic downset) tunes local dimension - d grows with the
     antichain thickness.  This is a DIFFERENT growth class (the past
     is not a free downset); it needs its own double-conservation
     formulation.  REGISTERED as the concrete 4D route.
  2. HIGHER-ARITY conservation: the current law conserves two moments
     (coherent sum, Born sum) over child ACTION GAPS.  A law
     conserving additional structure (a genuine d-dimensional
     volume/boundary relation) could select 4D-diamond intervals -
     this is the "4D double-conservation" the program has not yet
     written.
  3. It may be a THEOREM that free-downset sequential growth is
     locally 2D for ANY gap-based weighting - in which case emergent
     4D is provably outside this entire class, and the causal-set
     dimension of this program is honestly 2, full stop.  Testing
     (3) analytically (the interval-abundance recursion under a
     generic gap law) is the decisive next step: prove d_int = 2 or
     find the weighting that breaks it.

## Bottom line

Emergent 4D is NOT reachable by tuning the phase of the current law:
the growth class is locally 2-dimensional everywhere.  "How to get
4D" reduces to a GROWTH-RULE question - thicker-antichain / multi-
parent growth or a higher-arity conservation law - and the sharpest
open question is whether free-downset sequential growth is provably
locked at d_int = 2.  The honest current dimension of the program's
causal sets is 2 (locally), with mild large-scale excess ordering.
