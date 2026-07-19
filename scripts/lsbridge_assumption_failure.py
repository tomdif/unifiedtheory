"""
LSBridge assumption-failure simulation sweep.

Tests whether the photonic falsification pipeline (Bayesian inference +
confounder discrimination) gives reliable verdicts when REAL-WORLD
photonic assumptions fail.

Six scenarios:
  (S0)  Clean LSBridge truth (baseline)
  (S1)  Finite chip truncation:  σ_0 > 5 μm gives unmeasurable doubling
  (S2)  Elevated noise (10%, e.g., from moderate scattering loss)
  (S3)  Confounding Anderson localization at ξ_loc = 8 μm
  (S4)  Moderate Kerr nonlinearity (kerr_strength = 0.1)
  (S5)  σ_0 calibration bias (10% systematic widener)
  (S6)  ALL of the above combined ("realistic experiment")

For each scenario, we run the Bayesian inference layer + the confounder
classifier, and report:
  • Recovered ℓ with 95% credible interval
  • log Bayes factor vs R ≡ 1 null
  • Classifier verdict (lsbridge / linear_loss / kerr / AL / nnn)
  • Whether the pipeline correctly identifies LSBridge

Output: per-scenario table + JSON summary.
"""

from __future__ import annotations

import json
import math
import sys
from pathlib import Path

import numpy as np

SCRIPT_DIR = Path(__file__).resolve().parent
sys.path.insert(0, str(SCRIPT_DIR))

from lsbridge_ell_inference import Measurement, R_predicted  # noqa: E402
from lsbridge_bayesian_inference import (  # noqa: E402
    compute_posterior, bayes_factor_interpretation,
)
from lsbridge_confounder_discrimination import (  # noqa: E402
    R_linear_loss, R_kerr_self_focusing, R_anderson_localization,
    R_nnn_hopping,
)
from lsbridge_blind_challenge import FITTERS, classify  # noqa: E402


OUT_DIR = SCRIPT_DIR.parent / "results" / "lsbridge_predictions" / "assumption_failure"
OUT_DIR.mkdir(parents=True, exist_ok=True)


# =============================================================================
# 1. Ground-truth LSBridge data generator.
# =============================================================================

def truth_R(sigma_phys_um, ell_um=1.0):
    return R_predicted(sigma_phys_um / ell_um)


# =============================================================================
# 2. Assumption-failure modifiers.
# =============================================================================

def apply_chip_truncation(sigma_list, R_list, chip_T_max_ratio=1e5):
    """Drop measurements where T_LS would exceed chip length.
    Crude model:  R > chip_T_max_ratio → unmeasurable."""
    kept = []
    for s, r in zip(sigma_list, R_list):
        if r < chip_T_max_ratio:
            kept.append((s, r))
    if not kept:
        return sigma_list[:1], R_list[:1]  # avoid empty
    return [k[0] for k in kept], [k[1] for k in kept]


def apply_kerr_nonlinearity(sigma_list, R_list, kerr_strength=0.1):
    """Observed R = R_LS · R_Kerr (multiplicative combination)."""
    return sigma_list, [r * R_kerr_self_focusing(s, kerr_strength)
                        for s, r in zip(sigma_list, R_list)]


def apply_anderson_localization(sigma_list, R_list, xi_loc=8.0):
    """Observed R = R_LS · R_AL (multiplicative combination, but AL
    dominates above threshold)."""
    out = []
    for s, r_ls in zip(sigma_list, R_list):
        r_al = R_anderson_localization(s, xi_loc)
        out.append(r_ls * r_al if r_al > 1 else r_ls)
    return sigma_list, out


def apply_calibration_bias(sigma_list, R_list, bias=0.10):
    """Experimentalist labels σ_0 but actually launches σ_0·(1+bias).
    The 'true' R at σ_0_actual = σ_0·(1+bias) gets recorded as 'R at σ_0_nominal'."""
    out = []
    for s_nominal, _ in zip(sigma_list, R_list):
        s_actual = s_nominal * (1.0 + bias)
        r_actual = truth_R(s_actual)
        out.append(r_actual)
    return sigma_list, out


# =============================================================================
# 3. Synthetic measurement generator.
# =============================================================================

def make_measurements(sigma_list, R_list, noise=0.05, seed=42):
    rng = np.random.default_rng(seed)
    return [
        Measurement(
            sigma_0_phys=s,
            R_measured=max(r * (1.0 + noise * float(rng.standard_normal())), 1e-6),
            R_err=max(r * noise, 1e-3),
        )
        for s, r in zip(sigma_list, R_list)
    ]


# =============================================================================
# 4. Per-scenario evaluation.
# =============================================================================

def evaluate(scenario_name, measurements, truth_ell=1.0):
    fit = compute_posterior(measurements)
    classified, fits_dict = classify(measurements)
    verdict, BF = bayes_factor_interpretation(
        fit["log_bayes_factor_LS_vs_null"])
    return {
        "scenario": scenario_name,
        "n_measurements": len(measurements),
        "MAP_ell_um": fit["ell_MAP"],
        "median_ell_um": fit["ell_median"],
        "CI_95_um": fit["ell_CI_95"],
        "log_BF_vs_null": fit["log_bayes_factor_LS_vs_null"],
        "BF_verdict": verdict,
        "classifier_label": classified,
        "classifier_correct": classified == "lsbridge",
        "ell_relative_error_pct": (fit["ell_MAP"] - truth_ell) / truth_ell * 100,
        "classifier_chi2": {lbl: x[0] for lbl, x in fits_dict.items()},
    }


def print_scenario(result):
    s = result
    print(f"\n[{s['scenario']}]   ({s['n_measurements']} measurements)")
    print(f"  MAP ℓ:                {s['MAP_ell_um']:.4g} μm  "
          f"(truth 1.0;  rel.err = {s['ell_relative_error_pct']:+.2f}%)")
    print(f"  95% CI:               [{s['CI_95_um'][0]:.4g}, "
          f"{s['CI_95_um'][1]:.4g}] μm")
    print(f"  log BF vs null:       {s['log_BF_vs_null']:.2f}")
    print(f"  Bayes verdict:        {s['BF_verdict']}")
    print(f"  Classifier label:     {s['classifier_label']}  "
          f"({'✓ correct' if s['classifier_correct'] else '✗ MISIDENTIFIED'})")


# =============================================================================
# 5. Run all six scenarios.
# =============================================================================

def main():
    print("=" * 80)
    print("LSBridge assumption-failure simulation sweep")
    print("=" * 80)
    print()
    print("Pipeline:  Bayesian posterior on ℓ  +  classifier (LSBridge vs 4 confounders)")
    print("Ground truth: LSBridge with ℓ = 1.0 μm")
    print("σ_0 schedule (μm):  [0.5, 1.0, 2.0, 3.0, 5.0, 6.0, 7.0]   (catches U-shape)")
    print()

    sigma_sched = [0.5, 1.0, 2.0, 3.0, 5.0, 6.0, 7.0]
    truth_R_vals = [truth_R(s, ell_um=1.0) for s in sigma_sched]

    results = []

    # S0: clean baseline.
    m_S0 = make_measurements(sigma_sched, truth_R_vals, noise=0.05, seed=42)
    results.append(evaluate("S0_clean_baseline", m_S0))

    # S1: chip truncation — drop σ_0 ≥ 6 (where R > 100 → off chip).
    s_S1, R_S1 = apply_chip_truncation(sigma_sched, truth_R_vals,
                                         chip_T_max_ratio=100.0)
    m_S1 = make_measurements(s_S1, R_S1, noise=0.05, seed=42)
    results.append(evaluate("S1_chip_truncation", m_S1))

    # S2: elevated noise.
    m_S2 = make_measurements(sigma_sched, truth_R_vals, noise=0.10, seed=42)
    results.append(evaluate("S2_elevated_noise_10pct", m_S2))

    # S3: Anderson localization at ξ_loc = 8 μm (kicks in at σ_0 = 4 μm).
    s_S3, R_S3 = apply_anderson_localization(sigma_sched, truth_R_vals,
                                              xi_loc=8.0)
    m_S3 = make_measurements(s_S3, R_S3, noise=0.05, seed=42)
    results.append(evaluate("S3_AL_xi_loc_8um", m_S3))

    # S4: Kerr nonlinearity.
    s_S4, R_S4 = apply_kerr_nonlinearity(sigma_sched, truth_R_vals,
                                          kerr_strength=0.1)
    m_S4 = make_measurements(s_S4, R_S4, noise=0.05, seed=42)
    results.append(evaluate("S4_kerr_strength_0.1", m_S4))

    # S5: σ_0 calibration bias (10% wider than labeled).
    s_S5, R_S5 = apply_calibration_bias(sigma_sched, truth_R_vals, bias=0.10)
    m_S5 = make_measurements(s_S5, R_S5, noise=0.05, seed=42)
    results.append(evaluate("S5_sigma0_calibration_bias_10pct", m_S5))

    # S6: ALL combined — realistic experiment.
    s_x, R_x = apply_chip_truncation(sigma_sched, truth_R_vals, chip_T_max_ratio=100.0)
    s_x, R_x = apply_kerr_nonlinearity(s_x, R_x, kerr_strength=0.1)
    s_x, R_x = apply_anderson_localization(s_x, R_x, xi_loc=8.0)
    s_x, R_x = apply_calibration_bias(s_x, R_x, bias=0.10)
    m_S6 = make_measurements(s_x, R_x, noise=0.10, seed=42)
    results.append(evaluate("S6_ALL_FAILURES_combined", m_S6))

    # Print all.
    for r in results:
        print_scenario(r)

    # Summary table.
    print()
    print("=" * 80)
    print("Summary table")
    print("=" * 80)
    print(f"{'scenario':<38}  {'N':>3}  {'ℓ_MAP':>8}  "
          f"{'rel_err %':>10}  {'verdict':>30}  {'correct?':>10}")
    print("-" * 110)
    for r in results:
        print(f"{r['scenario']:<38}  {r['n_measurements']:>3}  "
              f"{r['MAP_ell_um']:>8.4g}  "
              f"{r['ell_relative_error_pct']:>+10.2f}  "
              f"{r['BF_verdict']:>30}  "
              f"{'YES' if r['classifier_correct'] else 'NO':>10}")

    # Save.
    out_json = OUT_DIR / "assumption_failure_summary.json"
    with out_json.open("w") as f:
        json.dump({
            "scenarios": results,
            "interpretation": {
                "S0_clean": "Baseline.  Pipeline should give correct verdict.",
                "S1_truncation": "Drops large σ_0;  fit should still work with the surviving points.",
                "S2_noise": "10% noise vs 5%.  Verdict should remain CONSISTENT but CI widens.",
                "S3_AL": "AL contamination above ξ_loc = 8 μm.  Pipeline may misidentify.",
                "S4_Kerr": "Multiplicative Kerr suppression.  R values are MODIFIED at all σ_0; ℓ fit biased.",
                "S5_calibration": "σ_0 systematic bias.  Inferred ℓ is biased by the same factor.",
                "S6_combined": "Worst-case realistic experiment.  This is the test of the pipeline.",
            },
        }, f, indent=2)
    print(f"\nJSON: {out_json}")

    # Net assessment.
    print()
    print("=" * 80)
    print("Net pipeline robustness assessment")
    print("=" * 80)
    correct = sum(1 for r in results if r["classifier_correct"])
    total = len(results)
    print(f"  Correct classifications: {correct}/{total}")
    rel_errs = [abs(r["ell_relative_error_pct"]) for r in results
                if r["classifier_correct"]]
    if rel_errs:
        print(f"  ℓ recovery error (among correct verdicts):  "
              f"median = {np.median(rel_errs):.2f}%,  "
              f"max = {max(rel_errs):.2f}%")
    failures = [r for r in results if not r["classifier_correct"]]
    if failures:
        print(f"  Pipeline failures:")
        for f in failures:
            print(f"    {f['scenario']}  →  classified as '{f['classifier_label']}'")
            print(f"      (best classifier χ²: "
                  f"{min(f['classifier_chi2'].values()):.3f})")


if __name__ == "__main__":
    main()
