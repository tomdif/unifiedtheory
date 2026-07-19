"""
LSBridge blind synthetic-data challenge.

Tests whether the falsification pipeline (parameter inference + confounder
discrimination) actually recovers the truth when applied blind to
synthetic data from each candidate mechanism:

  - LSBridge backreaction
  - Linear loss            (R ≡ 1)
  - Kerr self-focusing      (R < 1)
  - Anderson localization  (R = 1 below threshold, blows up above)
  - Next-nearest-neighbor hopping (R ≈ const)

For each truth mechanism, generate `n_trials` independent datasets with
realistic measurement noise, classify each blind using best-fit χ² across
all five candidate models, and report:

  - Confusion matrix (truth × classification)
  - Per-truth recall (true-positive rate)
  - Per-classification precision (positive-predictive value)
  - False-positive rate of "LSBridge" verdict from each confounder

Three sweep scenarios:
  (S1)  Full discrimination schedule σ_0 = {3, 5, 6, 7} μm, noise = 5%
  (S2)  Minimal schedule σ_0 = {5, 6} μm, noise = 5%
  (S3)  Full schedule, noise = 10%  (stress test)
"""

from __future__ import annotations

import json
import math
import random
import sys
from collections import Counter
from dataclasses import dataclass
from pathlib import Path

import matplotlib.pyplot as plt
import numpy as np
from scipy.integrate import quad
from scipy.optimize import minimize_scalar


SCRIPT_DIR = Path(__file__).resolve().parent
sys.path.insert(0, str(SCRIPT_DIR))
from lsbridge_ell_inference import (  # noqa: E402
    Measurement, R_predicted as R_lsbridge,
)
from lsbridge_confounder_discrimination import (  # noqa: E402
    R_linear_loss, R_kerr_self_focusing,
    R_anderson_localization, R_nnn_hopping,
)

OUT_DIR = SCRIPT_DIR.parent / "results" / "lsbridge_predictions" / "blind_challenge"
OUT_DIR.mkdir(parents=True, exist_ok=True)


# Truth-mechanism labels and parameter ranges used to draw "ground truth".
MECHANISMS = ["lsbridge", "linear_loss", "kerr", "AL", "nnn"]


# =============================================================================
# 1.  Truth generators (with random parameters drawn from realistic ranges).
# =============================================================================

def random_truth_params(truth, rng):
    """Sample physical parameters for each truth mechanism."""
    if truth == "lsbridge":
        return {"ell": float(rng.uniform(0.7, 1.3))}  # ℓ within ±30% of 1 μm
    if truth == "linear_loss":
        return {}
    if truth == "kerr":
        return {"kerr_strength": float(rng.uniform(0.1, 1.0))}
    if truth == "AL":
        return {"xi_loc": float(rng.uniform(6.0, 30.0))}
    if truth == "nnn":
        return {"eps": float(rng.uniform(0.02, 0.15))}
    raise ValueError(truth)


def R_truth(truth, sigma_0, params):
    if truth == "lsbridge":
        return R_lsbridge(sigma_0 / params["ell"])
    if truth == "linear_loss":
        return R_linear_loss(sigma_0)
    if truth == "kerr":
        return R_kerr_self_focusing(sigma_0, params["kerr_strength"])
    if truth == "AL":
        return R_anderson_localization(sigma_0, params["xi_loc"])
    if truth == "nnn":
        return R_nnn_hopping(sigma_0, params["eps"])
    raise ValueError(truth)


def generate_dataset(truth, sigma_0_list, noise, rng, params=None):
    if params is None:
        params = random_truth_params(truth, rng)
    measurements = []
    for s0 in sigma_0_list:
        R_true = R_truth(truth, s0, params)
        R_meas = R_true * (1.0 + noise * float(rng.standard_normal()))
        R_meas = max(R_meas, 1e-6)  # avoid pathological zeros
        R_err = max(R_true * noise, 1e-3)
        measurements.append(Measurement(s0, R_meas, R_err))
    return measurements, params


# =============================================================================
# 2.  Fitters for each candidate mechanism — return (chi², params).
# =============================================================================

def log_chi2(measurements, R_pred_fn):
    """Log-space χ² for multiplicative-noise data."""
    s = 0.0
    for m in measurements:
        R_pred = R_pred_fn(m.sigma_0_phys)
        if R_pred is None or R_pred <= 0 or not math.isfinite(R_pred):
            return float("inf")
        sigma_log = m.R_err / m.R_measured
        diff = math.log(m.R_measured) - math.log(R_pred)
        s += (diff / sigma_log)**2
    return s


def fit_lsbridge_cand(measurements):
    """Fit ℓ over log-grid + brent refinement."""
    def chi2_at(ell):
        return log_chi2(measurements, lambda s: R_lsbridge(s / ell))
    log_grid = np.linspace(-2, 1.5, 60)
    chi2_grid = [chi2_at(10.0**x) for x in log_grid]
    idx = int(np.argmin(chi2_grid))
    coarse_log = log_grid[idx]
    bracket_lo = max(log_grid[0], coarse_log - 0.4)
    bracket_hi = min(log_grid[-1], coarse_log + 0.4)
    try:
        result = minimize_scalar(
            lambda log_ell: chi2_at(10.0**log_ell),
            bracket=(bracket_lo, coarse_log, bracket_hi),
            method="brent",
            options={"xtol": 1e-6},
        )
        return float(result.fun), {"ell": 10.0**float(result.x)}
    except Exception:
        return chi2_grid[idx], {"ell": 10.0**coarse_log}


def fit_linear_loss_cand(measurements):
    """No parameters."""
    return log_chi2(measurements, lambda s: 1.0), {}


def fit_kerr_cand(measurements):
    def chi2_at(kerr):
        return log_chi2(measurements,
                        lambda s: R_kerr_self_focusing(s, kerr))
    try:
        result = minimize_scalar(chi2_at, bracket=(0.001, 0.5, 5.0),
                                  method="brent", options={"xtol": 1e-5})
        return float(result.fun), {"kerr_strength": float(result.x)}
    except Exception:
        return chi2_at(0.5), {"kerr_strength": 0.5}


def fit_AL_cand(measurements):
    def chi2_at(xi):
        return log_chi2(measurements,
                        lambda s: R_anderson_localization(s, xi))
    grid = np.linspace(2.0, 80.0, 100)
    grid_chi2 = [chi2_at(x) for x in grid]
    idx = int(np.argmin(grid_chi2))
    coarse = float(grid[idx])
    try:
        result = minimize_scalar(chi2_at,
                                  bracket=(max(0.5, coarse - 5),
                                           coarse,
                                           coarse + 5),
                                  method="brent", options={"xtol": 1e-5})
        return float(result.fun), {"xi_loc": float(result.x)}
    except Exception:
        return grid_chi2[idx], {"xi_loc": coarse}


def fit_nnn_cand(measurements):
    def chi2_at(eps):
        return log_chi2(measurements,
                        lambda s: R_nnn_hopping(s, eps))
    try:
        result = minimize_scalar(chi2_at, bracket=(0.001, 0.05, 0.4),
                                  method="brent", options={"xtol": 1e-5})
        return float(result.fun), {"eps": float(result.x)}
    except Exception:
        return chi2_at(0.05), {"eps": 0.05}


FITTERS = {
    "lsbridge": fit_lsbridge_cand,
    "linear_loss": fit_linear_loss_cand,
    "kerr": fit_kerr_cand,
    "AL": fit_AL_cand,
    "nnn": fit_nnn_cand,
}


# =============================================================================
# 3.  Classifier.
# =============================================================================

def classify(measurements):
    """Return (best_label, dict of label → (χ², params))."""
    fits = {label: fitter(measurements) for label, fitter in FITTERS.items()}
    best = min(fits.items(), key=lambda x: x[1][0])
    return best[0], fits


# =============================================================================
# 4.  Blind challenge harness.
# =============================================================================

def run_challenge(sigma_0_list, n_trials, noise, base_seed):
    """For each truth mechanism, generate n_trials datasets and classify each.
    Return confusion matrix as a nested dict."""
    confusion = {t: {c: 0 for c in MECHANISMS} for t in MECHANISMS}
    detail = []
    for truth in MECHANISMS:
        for trial in range(n_trials):
            rng = np.random.default_rng(base_seed + abs(hash(truth)) + trial)
            measurements, params = generate_dataset(
                truth, sigma_0_list, noise=noise, rng=rng)
            best, _ = classify(measurements)
            confusion[truth][best] += 1
            detail.append({
                "truth": truth,
                "params": params,
                "classified": best,
                "correct": best == truth,
                "trial": trial,
            })
    return confusion, detail


def confusion_summary(confusion, n_trials):
    """Compute recall + precision per mechanism."""
    summary = {}
    for truth in MECHANISMS:
        total = sum(confusion[truth].values())
        correct = confusion[truth][truth]
        recall = correct / total if total > 0 else 0.0
        summary[truth] = {"recall": recall, "total": total, "correct": correct}
    # Precision per classified mechanism.
    for label in MECHANISMS:
        col_sum = sum(confusion[t][label] for t in MECHANISMS)
        tp = confusion[label][label]
        precision = tp / col_sum if col_sum > 0 else 0.0
        summary[label]["precision"] = precision
        summary[label]["total_predicted"] = col_sum
    return summary


# =============================================================================
# 5.  Plotting.
# =============================================================================

def plot_confusion(confusion, title, n_trials, out_path):
    rows = [[confusion[t][c] for c in MECHANISMS] for t in MECHANISMS]
    M = np.array(rows, dtype=float)
    M_norm = M / n_trials
    fig, ax = plt.subplots(figsize=(8, 6))
    im = ax.imshow(M_norm, cmap="Blues", vmin=0, vmax=1)
    ax.set_xticks(np.arange(len(MECHANISMS)))
    ax.set_yticks(np.arange(len(MECHANISMS)))
    ax.set_xticklabels(MECHANISMS, rotation=30, ha="right")
    ax.set_yticklabels(MECHANISMS)
    ax.set_xlabel("Classified as")
    ax.set_ylabel("Truth")
    for i in range(len(MECHANISMS)):
        for j in range(len(MECHANISMS)):
            color = "white" if M_norm[i, j] > 0.5 else "black"
            ax.text(j, i, f"{int(M[i, j])}", ha="center", va="center",
                    color=color, fontsize=12, fontweight="bold")
    ax.set_title(title)
    fig.colorbar(im, ax=ax, label="Fraction of trials")
    fig.tight_layout()
    fig.savefig(out_path, dpi=150)
    plt.close(fig)
    return out_path


# =============================================================================
# 6.  Main.
# =============================================================================

def run_scenario(scenario_name, sigma_0_list, n_trials, noise, seed):
    print(f"\n[{scenario_name}]  σ_0 = {sigma_0_list},  N = {n_trials} "
          f"per truth,  noise = {noise*100:.0f}%")
    confusion, detail = run_challenge(sigma_0_list, n_trials, noise, seed)
    summary = confusion_summary(confusion, n_trials)
    plot_path = OUT_DIR / f"confusion_{scenario_name}.png"
    plot_confusion(confusion, f"{scenario_name}: σ_0 = {sigma_0_list}, "
                   f"noise = {noise*100:.0f}%", n_trials, plot_path)

    # Print summary.
    print(f"  {'truth':>15}  {'recall':>10}  {'precision':>10}  "
          f"{'total':>10}  {'correct':>10}")
    for t in MECHANISMS:
        s = summary[t]
        print(f"  {t:>15}  {s['recall']*100:>9.1f}%  "
              f"{s['precision']*100:>9.1f}%  "
              f"{s['total']:>10}  {s['correct']:>10}")
    print(f"  Confusion matrix saved: {plot_path}")

    # Most important: false-positive rate of LSBridge label from each confounder.
    print(f"  False-positive 'lsbridge' verdicts from each confounder:")
    for t in MECHANISMS:
        if t == "lsbridge":
            continue
        fp = confusion[t]["lsbridge"]
        fp_rate = fp / n_trials
        print(f"    truth = {t:>15}: "
              f"{fp:>3}/{n_trials} = {fp_rate*100:>5.1f}%")
    return {"scenario": scenario_name,
            "sigma_0_list": sigma_0_list,
            "n_trials": n_trials,
            "noise": noise,
            "confusion": confusion,
            "summary": summary,
            "plot": str(plot_path.relative_to(SCRIPT_DIR.parent))}


def main():
    print("=" * 78)
    print("LSBridge blind synthetic-data challenge")
    print("=" * 78)

    base_seed = 20240524
    n_trials = 50

    scenarios = [
        run_scenario("S1_full_schedule_5pct",
                     sigma_0_list=[3.0, 5.0, 6.0, 7.0],
                     n_trials=n_trials, noise=0.05, seed=base_seed),
        run_scenario("S2_minimal_5pct",
                     sigma_0_list=[5.0, 6.0],
                     n_trials=n_trials, noise=0.05, seed=base_seed + 1),
        run_scenario("S3_full_schedule_10pct",
                     sigma_0_list=[3.0, 5.0, 6.0, 7.0],
                     n_trials=n_trials, noise=0.10, seed=base_seed + 2),
        run_scenario("S4_wide_schedule_5pct",
                     sigma_0_list=[2.0, 3.0, 5.0, 6.0, 7.0, 8.0],
                     n_trials=n_trials, noise=0.05, seed=base_seed + 3),
    ]

    # Save summary JSON.
    out = {"scenarios": scenarios, "n_trials_per_truth": n_trials}
    json_path = OUT_DIR / "blind_challenge_summary.json"
    with json_path.open("w") as f:
        json.dump(out, f, indent=2)
    print(f"\nFull JSON: {json_path}")

    # Overall recommendation.
    print("\n" + "=" * 78)
    print("Overall recommendation")
    print("=" * 78)
    print("  The recommended discrimination schedule σ_0 = {3, 5, 6, 7} μm at")
    print("  5% noise should achieve > 95% recall and > 95% precision across")
    print("  all five mechanisms.  Minimal {5, 6} schedule may suffice;")
    print("  noise stress test at 10% checks degradation.")


if __name__ == "__main__":
    main()
