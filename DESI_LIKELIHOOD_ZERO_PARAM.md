# The zero-parameter DESI likelihood run: the everpresent-Lambda
# sector is EXCLUDED as the dark energy; l_k >= 27 fm derived
# (2026-08-11)

## Setup

Data: the official DESI DR2 BAO vector and covariance (13 entries,
CobayaSampler/bao_data desi_bao_dr2 = arXiv:2503.14738) + Planck-2018
compressed distance priors (R, l_A, omega_b) with their correlations
(arXiv:1808.05724).  Model: the fully pinned everpresent sector
(EVERPRESENT_LAMBDA_DERIVED + CN_DEEP_DAMPING): amplitude
parameter-free, RMS dLambda(T0) = Lambda_obs (= l_k = 12.1 fm), action
law Lambda ~ 1/T; realizations via the July process machinery
(independent increments in V^{3/2}); flatness closes Omega_m per
realization; h profiled (fine grid, spacing 0.001); r_d from the
standard early-universe formula (the model's DE is ~1e-4 at
recombination).  References fitted on identical data.  Readings
registered in desi_likelihood_zero_param.py before the run.

## Pipeline validation

  flat LCDM:   chi2 = 18.20  (Om = 0.307, h = 0.680)
  w0waCDM:     chi2 =  7.74  (Om = 0.335, w0 = -0.60, wa = -1.2,
                              h = 0.653)
  Delta-chi2(w0wa - LCDM) = -10.5

This reproduces the published DESI DR2 + CMB preference for thawing
w0waCDM (w0 ~ -0.6, wa ~ -1, Delta-chi2 ~ -10) — the pipeline is
sound.

## Verdict on the everpresent sector: registered reading (ii), DEAD

STOCHASTIC (the actual derived law; 400 realizations, 103 with
f(today) > 0 and viable backgrounds):

  chi2: min = 59.3, median = 2.1e4, 84% = 1.0e5
  Delta-chi2 vs LCDM: min = +41, median = +2.1e4
  realizations beating LCDM: 0 of 400
  ensemble-marginal factor: 3e-12

Mechanism of death: the process decorrelates across the BAO range
(corr(z=1, z=0) ~ 0.16, RMS growing into the past as 1/T), so every
realization predicts order-unity meanders of rho_DE(z) that precision
distances annihilate.

DETERMINISTIC ENVELOPE (the sign-coherent drift law
rho_DE = 0.685 rho_c0 (t0/t), the lambda-bridge self-tuning channel's
1/T version): chi2 = 989 (+971 vs LCDM).  Its effective
(w0, wa) = (-0.65, +0.23) has w0 in DESI's preferred range but the
WRONG SIGN of wa, and its past-growing envelope puts Omega_DE ~ 25% at
z = 2.3 — CMB-safe exactly as advertised, but fatal to Lya/QSO BAO.

Both realizations of the derived law are excluded by enormous margins.
**The framework's discrete action fluctuations cannot be the observed
dark energy.**

## The constructive output: a derived bound on l_k

Exclusion -> bound.  For a subdominant everpresent envelope atop a
constant Lambda (total pinned to 0.685 today),
rho_DE/rho_c0 = 0.685 + A((t0/t) - 1):

  A:        0.00   0.02   0.04   0.06   0.08   0.10   0.12
  dchi2:    0.00  +0.62  +0.34  +3.09  +8.91  +17.5  +28.5

  A_2sigma = 0.061  ->  with amplitude ~ l_k^-3:

      l_k >= 12.14 fm * (0.685/0.061)^{1/3} = 27 fm.

DESI DR2 + CMB force the gravitational nonlocality scale to at least
~27 fm (2-sigma), sharpening the July estimate (~30 fm) with real
likelihood machinery.  Since matching Lambda_obs REQUIRED
l_k = 12.1 fm, the two demands are incompatible by a factor ~2.2 in
scale (~10 in amplitude): the parameter-free everpresent
identification is self-inconsistent against data, independent of
realization details.  Equivalently: the everpresent component today is
at most ~6% of the critical density.

## What this means for the framework

1. The dark-energy sector's honest final state: Lambda in this
   framework must be (effectively) CONSTANT — the mean-action /
   self-tuning channel — with the fluctuation component hidden below
   6%.  The framework does NOT explain the DESI thawing hint; if that
   hint hardens into a detection of wa < 0 dynamics, it is evidence
   AGAINST this sector being the whole story (our derived dynamics
   has the opposite wa sign).
2. The derivation chain (Planck cancellation, c_N clearing) stands as
   mathematics; what died is the everpresent phenomenological
   identification.  This is the program's referee culture doing its
   job on a data-facing claim: pre-registered, zero-parameter, killed
   cleanly at first contact.
3. Surviving falsifiable content: l_k(grav) >= 27 fm (this bound
   tightens with future BAO); the gravity/matter nonlocality split
   (LHC vs 27 fm) stands at >= 12 orders in scale.

## Honest scope

- Perturbative overlay (no back-reaction); realization shapes frozen
  on the fiducial background; the bound scan holds Om at the flatness
  value 0.315 rather than profiling it (conservative direction not
  guaranteed; the A_2sigma changes at the ~tens-of-percent level, not
  the conclusion).
- CMB compressed priors with approximate correlation matrix; r_d
  fitting formula; no supernovae included (adding SN would only
  strengthen the exclusions — the misfit is in distance shape).
- The stochastic-model death is driven by the independent-increment
  structure [PHYS]; increment correlations over cosmological volumes
  would need a mechanism the variance analysis does not provide.
- w0waCDM reference on a coarse grid (its chi2 could improve by O(1)
  with refinement; irrelevant at these margins).

## Registered follow-ups

1. Update EVERPRESENT_LAMBDA_DERIVED status: the l_k = 12.1 fm
   "prediction" is superseded — it is now the EXCLUDED point; the
   living statement is the bound l_k >= 27 fm.
2. If DESI's wa < 0 hardens: quantify the incompatibility as a
   falsification statement for the whole everpresent family in this
   framework.
3. The self-tuning mean channel (<S>/n drift -> constant Lambda):
   whether the framework can PREDICT the constant's value is now the
   only route to a dark-energy derivation - back to the drift-law
   analytics (entropy-dominance arc).
