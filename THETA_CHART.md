# The path-level chart: N_eff IS the path count, theta-linearity to
# first order, and the cascade constants split (2026-08-13)

Going one level below the class tilt law: at the path level every
measure is T_theta(C) = sum_paths e^{theta x}, theta = 0 (path count),
1 (R), 2 (P = Born), with Q = T_1^2.  Three tests (theta_chart_test.py,
exact DP).

## Finding 1 (the sharp one): effective history multiplicity IS the
## path count

    ln N_eff vs ln N_paths:  slope 0.93-0.97 (predict 1),
    corr = +0.985 / +0.986 / +0.988 at n = 6/7/8,
    residual std ~ 0.17-0.20,
    implied within-class path-log spread s^2 = 0.22-0.31,
    nearly class-uniform (std ~ 0.19).

So N_eff(C) ~= N_paths(C) * e^{-s^2} with s^2 almost constant across
geometries: **the dynamically computed history multiplicity of the
coherent measure is, to 99% correlation, literal path counting with a
nearly uniform quantum damping factor.**  The I2 identity
Q = P * N_eff sharpens to Q ~= P * N_paths * e^{-s^2}: the coherent
channel weights geometries by HOW MANY GROWTH HISTORIES reach them -
the labeled-counting answer to the history-identity question, now
derived as the dynamical output (with the orbit/event alternatives
measurably disfavored by the same 99% correlation).  This also
explains the measured corr(ln N_eff, ln P) -> +0.70.

## Finding 2: the theta-chart is linear to first order; the P-vs-U
## regularity is a CURVATURE effect

Equal-spacing test (a_2 - a_1) - (a_1 - a_0): 8/12 events within
|0.26| (mean +0.20); clear curvature for has_post (+1.00), stem6
(+0.74), antichain (-0.51).  Interpretation: events can shift the
path-log VARIANCE as well as the mean (second-order tilt); posts do
so strongly.  Consequences: (a) the class-level tilt law (r-axis) plus
first-order theta-linearity form the base chart, with a per-event
curvature coefficient as the single correction; (b) the old P-vs-U ~ 2
posts regularity lives in the curvature term - explaining why it was
real for posts and absent for antichains.  Notably a_0(post) = -2.46
~ a_R(post) = -2.53: path counting alone already carries essentially
ALL the post suppression; the Born channel is post-friendlier than
linear (curvature +1.0), the coherent channel doubles down via r = 2.

## Finding 3: the cascade constants split into named parts

    E[1/nu_eff] = 0.62-0.67  vs  measured g = 0.83-0.91:
      the smoothing constant exceeds the uncorrelated-parent value by
      ~0.2 - the SIBLING-PARENT CORRELATION excess (a child's parents
      are (n-1)-causets sharing all but one element; their log-weights
      are strongly correlated, weakening the smoothing).
    Var(ln nu_eff) = 0.12-0.14  vs  v = 0.24-0.30:
      parent-number fluctuation supplies roughly HALF the injection;
      the remainder is share-weighted mean-vs-gain spread.

g and v are now structurally decomposed (uncorrelated-parent baseline
+ correlation excess; nu-fluctuation + residual); the fully analytic
derivation reduces to computing one correlation and one residual
variance from the double-conservation structure - the last two
concrete lemmas of the statistical program.

## Scope

Exact DP, n <= 8, 2D engine, class-max-ent law (selection-robustness
of the class tilt law established separately); five-point exponent
windows; curvature coefficients not yet fit per event (registered).
