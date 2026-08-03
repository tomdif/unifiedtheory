# The Lambda(t) bridge (opened 2026-08-03, ordering-fraction discipline)

Standard (referee): derive the aging theorem's PERMITTED DRIFT CLASS
first - shape and sign, no fit; pre-register the DESI falsifier;
state the benchmark redshift; then let the number land.

## The chain, with its non-obvious step

1. AGING THEOREM [certificate, Paper 3]: stationary per-precursor
   rules are impossible at every phase (two-phasor kill at n <= 2).
   Epoch dependence is forced.
2. BUT the drift cannot live in per-precursor couplings at all:
   the Bell-causality kill (bell_cut_2d certificate: per-precursor
   => SZ-ratio Bell => signature factoring => collision-table death)
   operates WITHIN a single stage, so stage-dependent w_n(P) does
   not evade it.  Aged per-precursor is dead for the same reason
   stationary was dead under covariance.
3. THEREFORE the forced epoch dependence lives in the effective
   action statistics of the covariant family itself.  Definitions
   [PHYS: identification of the action's volume term with Lambda]:
   for a member Psi at level n,
     Lambda_eff(n) := <S>_n / n     (mean action per element),
     deltaLambda(n) := deltaS(n)/n  (amplitude-weighted std of S).
4. Everpresent-Lambda phenomenology (Sorkin) is the hypothesis
   deltaS(n) ~ sqrt(n) with zero-mean sign - i.e. deltaLambda ~
   1/sqrt(V).  Here it is NOT assumed: step 5 measures the class.

## Step 5 - the permitted class, measured (shape and sign, no fit)

Compute <S>_n and deltaS(n), n = 2..7, under psi- and psi^2-
weighting, for two independent members (max-min interior member;
max-deep-support member) at phi in {0.9, 1.2, pi/3}.
PRE-REGISTERED READINGS:
  (i)  deltaS/sqrt(n) ~ const with sign-symmetric fluctuations ->
       the covariant family's intrinsic drift class IS
       everpresent-Lambda-shaped; bridge stands; proceed to the
       DESI-facing amplitude statement.
  (ii) clear power alpha != 1/2 -> the class differs; report alpha
       and the modified phenomenology, no rescue language.
  (iii) systematic nonzero drift of <S>/n dominating fluctuations ->
       deterministic Lambda drift: different physics, reported as
       such.

## Step 6 - DESI falsifier (registered before any number)

Given (i): the class predicts stochastic w(z) excursions with
envelope deltaLambda/Lambda ~ (V0/V(z))^(1/2) x (measured
normalization from step 5); benchmark redshift z ~ 0.5 (DESI BAO);
the class is falsified by a measured smooth monotone w(z) departure
exceeding the envelope, or by bounds confining |w+1| below the
class's minimum excursion amplitude.  Quantification via
everpresent_desi.py machinery AFTER shape and sign land - the
amplitude is a measurement, the falsifier is registered now.

Scope: 2D sharp, depth <= 7, representative phases; psi/psi^2 both
reported; member-dependence reported; step-3 identification tagged
[PHYS].


## Step 5 RESULT (2026-08-03, lambda_bridge_step5.log) - readings (ii)+(iii)

Measured, n = 2..7, all three phases, both members, both weightings:

  SHAPE: deltaS/sqrt(n) RISES monotonically everywhere (0.71 at n=2
  to 1.6-2.4 at n=7); deltaS/n approaches ~0.8-0.9 at the top
  depths.  The fluctuation envelope is near-LINEAR (alpha ~ 0.8-1),
  NOT the everpresent alpha = 1/2.  Reading (ii): the intrinsic
  class differs from everpresent-Lambda at accessible depth; alpha
  reported; no rescue language.

  SIGN: <S>/n - 1 drifts systematically from -0.50 to ~ -0.9..-1.05:
  Lambda_eff = <S>/n DECLINES from +0.5 toward ~0 with growth, with
  fluctuations of comparable size.  Reading (iii) component: a
  deterministic negative drift of the effective volume term is
  present alongside the fluctuations.  (Observation recorded without
  promotion: the mean action per element self-tunes toward zero with
  growth.  It is a two-line data statement, not a mechanism claim.)

CONSEQUENCE, per the registered conditionals: the DESI-facing
amplitude statement (step 6) was conditional on reading (i) and is
NOT licensed.  The bridge's first contact stands as: at depths
n <= 7, in this observable, the covariant family's intrinsic drift
class is NOT everpresent-shaped.  The one honest escape route is
depth (small-n transients; the linear envelope may reflect
finite-size link-count growth), and it is a computation, not an
argument: the n = 8 extension is the registered next step of this
thread, with the same three readings.  Until it runs, the program's
data-facing thread reports: shape measured, sign measured, bridge
not established.
