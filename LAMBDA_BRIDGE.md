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
NOT licensed.  THE TWO-SENTENCE DISTINCTION (referee), explicit:
the claim is "comparison unlicensed" - the theory as computed does
not produce the statistics the everpresent framework feeds to data,
so no fit may be run.  The claim is NOT "everpresent-Lambda
falsified in this class": alpha is measured on six points in the
deep-UV (n = 2..7) while everpresent-Lambda is an asymptotic
statement ~10^120 elements away, and the onset lesson cuts
symmetrically - a scaling exponent measured at depth 7 has no more
right to extrapolate than the constraint that dissolved at depth 8
had.  "At accessible depth" is the entire claim.

EXPONENT WIDTH (referee): alpha ~ 0.8-1 brackets two different
stories - diffusive-with-correlations versus ballistic - and six
points cannot split them.  The note says so; the n = 8 extension
may narrow it.  The bridge's first contact stands as: at depths
n <= 7, in this observable, the covariant family's intrinsic drift
class is NOT everpresent-shaped.  The one honest escape route is
depth (small-n transients; the linear envelope may reflect
finite-size link-count growth), and it is a computation, not an
argument: the n = 8 extension is the registered next step of this
thread, with the same three readings.  Until it runs, the program's
data-facing thread reports: shape measured, sign measured, bridge
not established.

## The self-tuning follow-up, pre-registered BEFORE any deeper run

The unpromoted observation - <S>/n declining toward ~0 - is what a
dynamically relaxing effective Lambda looks like, and unlike
everpresent-Lambda it would be THIS THEORY'S OWN drift law rather
than an imported ansatz.  Registered now (referee):
  SURVIVES if: the limit of <S>/n - 1 is exactly -1 (i.e. <S>/n -> 0)
  under the n = 8 extension and beyond, with a convergence rate
  distinguishable from finite-size boundary transients (the rate
  must stabilize as a function of n, not track the boundary-layer
  fraction of the ensemble).
  DIES if: the limit sits elsewhere than -1, or the rate is
  consistent with boundary effects (tracks the fraction of
  near-boundary elements).
If it survives, the bridge's negative result acquires a positive
successor: the theory replacing the phenomenology it declined to
license with a drift law of its own.

## Window-edge uniformity (referee): measured (lambda_edges.log)

At phi = 0.15, 0.30 (lower edge) and 1.40, 1.50 (approaching pi/2):
the near-linear fluctuation envelope holds everywhere (deltaS/sqrt(n)
rises monotonically to 2.0-3.0 at n = 7, slightly STEEPER at the low
edge), and the negative Lambda_eff drift holds everywhere (to
~ -0.9..-1.1, one n=7 fluctuation blip at phi = 0.3).  Readings
(ii)+(iii) are WINDOW-WIDE, not a mid-window artifact.  One edge
datum recorded: the max-min member's t* collapses at the low edge
(4e-6, 3e-5) while sitting at 1.0 near pi/2 - the interior thins
toward the lower window edge.


## The unknown-physics probe (2026-08-03, unknown_physics_probe.log)

Four candidate mechanisms for the measured class were named with
discriminators; the two cheap ones ran (pre-registered readings):

C (SPACETIME PHASE COEXISTENCE) - DIES at accessible depth: the
psi-weighted S-distribution at n = 7 is broad, smooth, UNIMODAL
(monotone rise to S = 1 at 12.8%, monotone fall; the n = 6 bumps
read as small-n discreteness, smoothing at 7).  Single-phase
ballistic spread, not coexistence.

D (COUNTING-ENTROPY DOMINANCE) - WINS the discrimination:
ext-only weighting (the pure count of birth orderings, NO quantum
dynamics at all) reproduces the drift class in shape AND magnitude:
<S>/n - 1: -0.500 -> -1.013 across n = 2..7 (crossing -1 at n = 7),
deltaS/n -> 0.803, against the full dynamics' -0.949 / 0.899.
A-only (amplitudes without ext) OVERSHOOTS (-1.23, 1.37): the
dynamics does not oppose the entropy, it adds to it.

CONSEQUENCES, stated at width:
1. The drift class - including the self-tuning - is, at accessible
   depth, a property of the LABELED-HISTORY COUNT MEASURE, present
   with no dynamics.  The "dynamically relaxing Lambda" reading of
   candidate B is demoted: the relaxation is ENTROPIC, not
   dynamical, as far as n = 7 can see.
2. The physical drift law therefore inherits the history-counting
   axiom's convention-dependence: ext is a multiplicity object, and
   under orbit counting the class must be re-measured (registered).
   Every trail this week - selection, quadrature, now Lambda - ends
   at the same axiom.
3. The self-tuning fork (limit -1, rate) becomes an ANALYTIC
   question: the ext-weighted ensemble is the uniform measure on
   labeled growth histories, a known-adjacent random-order model
   whose interval-count asymptotics may be derivable in closed form
   - better than any scan, and the registered route for settling
   the pre-registered fork.
4. The remaining home for genuinely unknown physics in this thread
   is candidate A: whether pure covariant growth decoheres action
   sectors AT ALL (off-diagonals of the decoherence functional,
   open problem 3) - if not, classicality requires an ingredient
   the theory does not currently contain.
