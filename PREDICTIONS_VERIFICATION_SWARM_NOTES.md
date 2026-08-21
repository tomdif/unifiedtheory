# Predictions Verification Swarm Notes

Date: 2026-08-21

Scope: repository inspection only. I did not compare against current external
data, run Lean, run `lake build`, modify `.lake`, commit, or push.

## Frozen Forward Predictions

The strongest formal preregistration object is
`UnifiedTheory/LayerB/PreRegistrationLedger.lean`. It defines exactly five
`PreRegistered` entries, a five-row `falsificationTable`, and the master theorem
`pre_registered_master`.

| Prediction | Frozen form | Status before data comparison |
|---|---|---|
| Higgs trilinear | `kappa_lambda = 1.00 +/- 0.04`, SM-equivalent tree plus one-loop band | Freeze exact survival/falsification windows by experiment and specify whether comparison is to tree-level `1`, SM loop band, or framework-specific deviation. |
| CKM `|V_ub|` | `sqrt(21)/1200 ~= 0.003819`, equivalently `|V_ub|^2 = 7/480000` | Strongest clean forward bet. Need lock Belle II dataset version, inclusive/exclusive treatment, covariance, and central-value rule. |
| Baryon/dark ratio | `Omega_b/Omega_DM = 4/21 ~= 0.1905` | Needs a cosmology-data protocol before comparison: define whether using physical densities, density fractions, inferred model, priors, covariance, and which survey release. |
| Proton decay | `tau_p proportional to M_X^4/alpha_GUT^2`, `P_alpha = 1024*pi^2/9` | Not a single-number prediction because `M_X`, hadronic matrix element, and prefactor convention are open inputs. Treat as a structural scaling plus exclusion map, not a direct yes/no number. |
| Muon `g-2` | `a_mu = a_mu^SM(BMW) = 116592000 x 10^-11` | Frozen as a methodological commitment to BMW/lattice HVP. Need lock final HVP arbitration rule before using future discrepancy as falsification. |

## Prediction-Shaped But Not Frozen TOE-Core Bets

| Item | Repo location | Current classification |
|---|---|---|
| Four older falsifiable predictions: no axion, P-sector DM near Higgs, 6 Planck-mass black-hole remnants, lightest neutrino near 5 micro-eV | `UnifiedTheory/LayerB/FalsifiablePredictions.lean`, README table | Not in the five-entry prereg ledger. They depend on physical identifications or interpretation bridges and need to be ported into the formal ledger or explicitly demoted. |
| CKM full table beyond `V_ub` | `UnifiedTheory/LayerB/CKMPreRegistration.lean` | Contains useful windows, but the ledger treats only `V_ub` as the named frozen PR2; several other CKM forms are audit-driven/post-diction or consistency checks. |
| Post-diction audit identities | `PreRegistrationLedger.lean`, `STATUS.md` | Formally tagged as post-dictions or consistency checks. Do not present as forward predictions. |
| Pi/4 ordering fraction and lambda record-regression signatures | `PI4_FIRST_PREDICTION.md`, `pi4_first_prediction.log`, `lambda_observable.log`, `logs_lambda_sharp_prediction.txt` | Internal dynamical signatures. Useful for future preregistration, but currently toy/finite-depth or mapping-assumption dependent. |
| Everpresent-Lambda / DESI confrontation | `DESI_LIKELIHOOD_ZERO_PARAM.md`, `ACTION_VARIANCE_REPORT.md` | Failure/bound ledger: the zero-parameter everpresent dark-energy identification is recorded as excluded; surviving content is a bound on gravitational nonlocality scale. |
| LSBridge wavepacket slowdown | `LS_BRIDGE_EXPERIMENTAL_REGIMES.md`, `results/lsbridge_predictions/` | Candidate lab protocol with sharp dimensionless curve, but physical-unit map depends on free natural length scale and ansatz/coupling assumptions. |
| QQG tensor-to-scalar bound | `UnifiedTheory/Cosmology/QQG/StrongCouplingPrediction.lean` | Formalizes a paper formula and its algebraic threshold. It is conditional on the leading slow-roll/large-N formula, not derived from repo dynamics. |

## Physical-Identification Assumptions Still Open

- The top-level core still depends on two physical identifications and the Planck
  mass for Layer 3 parameter claims.
- Dark-matter abundance has atomic matches, but thermal freeze-out and the
  physical dark-sector mechanism are not derived.
- Proton decay lacks a derived `M_X`, hadronic matrix element, and unique
  convention for the rate prefactor.
- Muon `g-2` inherits the SM/BMW HVP choice; the repo does not derive the QCD
  spectral function.
- LSBridge requires a physical length scale, ansatz validity, and matter-coupling
  identification before a null lab result can falsify the general theory.
- Pi/4/lambda signatures need a 4D physical law and observable map, not only
  finite-depth toy dynamics.
- Continuum GR/QFT/SM infrared recovery remains a TOE gate, not a closed result.

## Verification And Preregistration Checklist

1. Create one canonical machine-readable ledger with fields:
   `id`, `category`, `closed_form`, `dependencies`, `frozen_date`,
   `data_release`, `observable_definition`, `estimator`, `uncertainty_model`,
   `survival_window`, `falsification_rule`, `status`, `source_theorem`,
   `citations`.
2. Add an `AssumptionTag` layer to each pre-registered entry:
   `finite theorem`, `conditional bridge`, `physical identification`,
   `external SM/QCD input`, `external data protocol`.
3. Promote or demote the older four `FalsifiablePredictions.lean` entries:
   either add them to the canonical ledger with explicit assumptions and tests,
   or change README language so they are not confused with the five formal PRs.
4. Split proton decay into separate rows:
   exact framework prefactor, rate-scaling law, and conditional lifetime bands
   for named `M_X`, `|A|^2`, and prefactor conventions.
5. For `g-2`, write a pre-comparison arbitration rule for BMW/lattice versus
   dispersion HVP before looking at future combined results.
6. For cosmology, version-lock Planck/CMB-S4/DESI inputs, parameter definitions,
   priors, covariance matrices, and model class before comparing ratios or dark
   energy bounds.
7. For LSBridge, freeze one physical platform protocol with calibration runs,
   confound controls, a fitted-or-fixed natural length rule, and a null-result
   interpretation that cannot move after data.
8. Add a failure ledger row for the excluded everpresent-Lambda identification
   and mark superseded values wherever the old `l_k = 12.1 fm` claim appears.
9. Require every public prediction table to state whether it is forward,
   post-diction, consistency check, or conditional proposal.
10. Before any external comparison, snapshot the exact code commit, script
    command, input data files, and generated result hash.

## Citation And Documentation Hygiene Risks

- README still highlights four falsifiable predictions from
  `FalsifiablePredictions.lean`, while `PreRegistrationLedger.lean` says the
  honest forward list is exactly five. This is the largest public-facing
  inconsistency.
- `FalsifiablePredictions.lean` says the four predictions have zero tunable
  parameters, while also saying they rely on two identifications. That needs
  assumption-tagged wording.
- Several tables cite dated empirical values such as PDG 2024, Planck 2018,
  Super-K 2024, and Belle II projections. Before comparison, replace prose-only
  citations with versioned source records and fixed data files.
- Some files describe successful/falsified phenomenology in strong language.
  They should point to a central status field: `active`, `superseded`,
  `excluded`, `conditional`, or `internal signature`.
- The formal five-entry ledger is excellent, but it stores metadata as strings.
  For rigorous preregistration, encode the survival windows and falsification
  rules in structured Lean or JSON so downstream scripts cannot reinterpret them.
