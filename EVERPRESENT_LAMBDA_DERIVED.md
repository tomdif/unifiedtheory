# The everpresent-Lambda amplitude, parameter-free (2026-08-11)

## The cancellation

Unimodular conjugacy reads a fluctuation of the total causal action as
an effective cosmological-constant fluctuation over 4-volume V:
dLambda = 8 pi G dS/(hbar V).  Insert the framework's three previously
derived/measured constants:

  kappa = 4/sqrt6          quantum of action per unit BD bracket
                           (quantum-consistency status: exact analog
                           forced in the 2D engine (pi/4); inside the
                           unique 4D branching window —
                           four-d-normalization-check-2026-08-11)
  l_disc^2 = 8 pi G hbar   causal-action coefficient c = 1/2
                           (LayerA/CausalActionCoefficient, Lean)
  Var S = kappa^2 [c_N N + (pi/4) M(eps) g N tau^2]
                           measured (ACTION_VARIANCE_REPORT, MC + exact
                           M(eps))

With dS = kappa hbar sqrt(v_eff N) and N = V/l_disc^4:

  dLambda = [8 pi G hbar / l_disc^2] kappa sqrt(v_eff)/sqrt(V)
          = kappa sqrt(v_eff(eps, tau)) / sqrt(V)     EXACTLY.

Every Planck factor cancels, BY the same c = 1/2 matching that fixed
the discreteness scale.  The July arc had to calibrate this amplitude;
it is now an output.  (July's alpha was defined in corner-gate units
l_c = (24/pi)^{1/4} l_p with an explicit calibration step; the derived
reduced-Planck density and the exact cancellation replace both.)

## Evaluated consequences (lambda_amplitude_derived.py / .log)

Geometry: Planck-2018 LCDM past light cone: T0 = 0.951/H0,
V_lc = 0.1231/H0^4 (kappa_V = 0.1505).  Lambda_obs = 2.055 H0^2.

**1. The floor channel (Sorkin 1/T^2 law) becomes a sharp internal
constraint.**  Omega_fluct(floor) = kappa sqrt(c_N)/(3 sqrt(V)) =
1.55 sqrt(c_N): the naive Poisson floor c_N ~ O(1) gives Omega ~ 1.6 —
and c_N* = 0.195 would reproduce Lambda_obs exactly.  But this channel
follows the CLASSIC scale-invariant law that the July analysis showed
is CMB-fatal at such amplitudes (Omega(z=1100) ~ Omega(today)).
Early-dark-energy limits (~3%) therefore DEMAND

    c_N <= 3.7e-4:

the N-D covariance cancellation observed qualitatively in the MC
(variance dipping below Poisson at strong damping) must suppress the
floor by >= 3 orders below naive.  This is a computable, falsifiable
internal prediction: an exact deep-damping evaluation of the
per-element smeared-action variance decides, and c_N > 4e-4 KILLS the
theory against the CMB with no remaining freedom.  (The July MC noise
floor ~0.3 cannot resolve it.)

**2. The edge channel predicts the gravitational nonlocality scale.**
dLambda_edge = kappa sqrt((pi/4) M(eps) g) (T0/l_disc)/sqrt(V) — the
Lambda ∝ 1/T thawing channel (CMB-safe, w ~ -1/2 -> -2/3, the
DESI-preferred side; shapes unchanged from ACTION_VARIANCE_REPORT).
Setting it equal to Lambda_obs with NO free amplitude:

    eps* = 2.0e-81,   l_k = l_disc eps*^{-1/4} = 12.1 fm
    (11.5-12.9 fm for g in [0.5, 1.0])

The gravitational nonlocality scale is nuclear-sized, now as a
PREDICTION rather than a calibration (July's 2.5-3.8 fm shifts to
~12 fm under the derived reduced-Planck density and the exact
cancellation; the nuclear-scale conclusion is robust, its provenance
is now parameter-free).

**3. A single nonlocality scale is excluded by magnitude.**  If
gravity shared the matter-sector bound l_k <= 1e-19 m (LHC), the edge
channel would give Lambda_edge/Lambda_obs = 1.8e15.  The
gravity/matter nonlocality split is FORCED by fifteen orders of
magnitude — no longer a "4 orders of tension" between calibrations but
an overproduction catastrophe of the single-scale hypothesis.

## Status against data

The model now has ZERO free amplitude parameters: Lambda_obs fixes
l_k; the CMB fixes c_N to be negligible; the w(z) shape statistics are
then pure predictions (from July: CMB-safe by ~t_rec/t_0, w drift
-1/2 -> -2/3 thawing, wa median +0.08, ~9% of realizations inside the
DESI DR2 box).  The DESI likelihood run (BAO + SN + CMB distances,
realization-marginalized) is now a zero-parameter test of the
framework's dark-energy sector.

## Honest scope

- [PHYS] assembly: the unimodular dLambda = 8 pi G dS/V reading and
  the independent-increment realization of S(V) are model choices
  inherited from the everpresent literature and the July arc.
- kappa's quantum status: forced exactly only in the 2D engine; in 4D
  it is window-membership (nothing internal yet selects 4/sqrt6 within
  [1.50, 2.09]).  The gravitational side (BD normalization + c = 1/2)
  is what pins it here.
- g: this script's refit gives 0.87 at eps = 1.0, 0.5 (July: 0.7);
  small-eps fits are noise-dominated; the l_k sensitivity to g in
  [0.5, 1] is +-6%.
- The tau^2 edge law is extrapolated ~60 orders beyond the MC range
  (backed by the exact edge integral; inherited caveat, stated).
- kappa_V uses the past light cone of comoving observers; other
  volume choices (Hubble 4-volume etc.) shift sqrt(V) by O(1) —
  reflected in the c_N* and l_k error budget at the factor-<2 level.
- LHC nonlocality bound 1e-19 m is schematic (collider contact-
  operator scale); the e15 conclusion is insensitive to its exact
  value.

## Registered follow-ups

1. THE DECISIVE COMPUTATION: exact deep-damping per-element variance
   (c_N) including the N-D covariance — kills or clears the theory
   against the CMB with no freedom.  (Lean-shaped: the diagonal-
   Campbell reduction is `variance_rate`-shaped per the July report.)
2. Zero-parameter DESI likelihood run.
3. Lean lemma for the Planck cancellation identity
   (8 pi G / l_disc^2 = 1 under c = 1/2 => dLambda sqrt(V) =
   kappa sqrt(v_eff)).
4. Derive g (the diamond depth-average geometry factor) exactly.
