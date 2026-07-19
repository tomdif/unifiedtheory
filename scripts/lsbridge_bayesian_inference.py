"""
LSBridge Bayesian inference layer.

Upgrades the chi-squared fit (in `lsbridge_ell_inference.py`) to a proper
Bayesian posterior on the natural length scale ℓ.

Given measurements (σ_0, R_measured, R_err) and a log-Gaussian likelihood
for the multiplicative noise model, compute:

    P(ℓ | data) ∝ exp(-χ²(ℓ)/2) · P(ℓ)

with a flat-on-log prior over a physically-motivated range.  Output:

  • posterior mean, median, MAP estimate;
  • 68% / 95% credible intervals;
  • full posterior histogram;
  • Bayes factor for LSBridge vs the null hypothesis R ≡ 1.

This is the right tool for a real experiment:  it returns a probability
distribution on ℓ (or rules it out entirely if the data is inconsistent),
rather than a single point estimate.
"""

from __future__ import annotations

import argparse
import csv
import json
import math
from dataclasses import dataclass
from pathlib import Path

import matplotlib.pyplot as plt
import numpy as np
from scipy.integrate import quad

import sys
sys.path.insert(0, str(Path(__file__).resolve().parent))
from lsbridge_ell_inference import (  # noqa: E402
    Measurement, R_predicted, simulate_measurements,
)


SCRIPT_DIR = Path(__file__).resolve().parent
OUT_DIR = SCRIPT_DIR.parent / "results" / "lsbridge_predictions" / "bayesian"
OUT_DIR.mkdir(parents=True, exist_ok=True)


# =============================================================================
# 1. Log-likelihood and posterior.
# =============================================================================

def log_likelihood(ell, measurements, C=1.0):
    """log P(data | ℓ).  Log-Gaussian likelihood for multiplicative noise.

      log P = − (1/2) Σ_k [(log R_meas_k − log R_pred_k(σ/ℓ)) / σ_log_k]²
              − (1/2) Σ_k log(2π σ_log_k²)
    """
    log_L = 0.0
    for m in measurements:
        sigma_dim = m.sigma_0_phys / ell
        R_pred = R_predicted(sigma_dim, C)
        if not math.isfinite(R_pred) or R_pred <= 0 or m.R_measured <= 0:
            return -float("inf")
        sigma_log = m.R_err / m.R_measured
        diff = math.log(m.R_measured) - math.log(R_pred)
        log_L -= 0.5 * (diff / sigma_log)**2
        log_L -= 0.5 * math.log(2.0 * math.pi * sigma_log**2)
    return log_L


def log_prior_uniform(ell, ell_min=1e-3, ell_max=100.0):
    """Flat-on-log prior over [ell_min, ell_max] μm."""
    if ell <= 0 or ell < ell_min or ell > ell_max:
        return -float("inf")
    # log P(log ℓ) is uniform; in terms of ℓ this is P(ℓ) ∝ 1/ℓ.
    return -math.log(ell) - math.log(math.log(ell_max / ell_min))


def log_posterior(ell, measurements, ell_min, ell_max, C=1.0):
    lp = log_prior_uniform(ell, ell_min, ell_max)
    if not math.isfinite(lp):
        return -float("inf")
    return log_likelihood(ell, measurements, C) + lp


# =============================================================================
# 2.  Posterior sampling via grid integration (1D parameter, no MCMC needed).
# =============================================================================

def compute_posterior(measurements, ell_min=1e-3, ell_max=100.0,
                      n_grid=3000, C=1.0):
    """Compute the (unnormalized) posterior on a log-uniform grid in ℓ,
    then normalize and return summary statistics."""
    log_ell = np.linspace(math.log10(ell_min), math.log10(ell_max), n_grid)
    ell_grid = 10.0**log_ell
    log_post = np.array([log_posterior(ell, measurements, ell_min, ell_max, C)
                          for ell in ell_grid])

    # Normalize:  P(log ℓ) = posterior density in log-space.
    # Subtract max for numerical stability.
    log_post_shifted = log_post - np.max(log_post)
    post_unnorm = np.exp(log_post_shifted)
    # Normalize over log-ℓ uniformly spaced.
    d_log = log_ell[1] - log_ell[0]
    norm = np.sum(post_unnorm) * d_log
    post = post_unnorm / norm

    # MAP estimate (in log-ℓ).
    idx_map = int(np.argmax(post))
    ell_map = float(ell_grid[idx_map])

    # CDF for credible intervals (in log-ℓ).
    cdf = np.cumsum(post) * d_log
    cdf /= cdf[-1]  # ensure exact 1.0 at end

    def quantile(q):
        idx = int(np.argmin(np.abs(cdf - q)))
        return float(ell_grid[idx])

    # Posterior mean (in log-ℓ).  Geometric mean is more natural for log-prior.
    ell_geomean = float(10.0**(np.sum(log_ell * post) * d_log))
    ell_median = quantile(0.5)
    ci68 = (quantile(0.16), quantile(0.84))
    ci95 = (quantile(0.025), quantile(0.975))

    # Bayes factor LSBridge / null (R ≡ 1).
    # null log-likelihood:
    log_L_null = 0.0
    for m in measurements:
        sigma_log = m.R_err / m.R_measured
        log_L_null -= 0.5 * (math.log(m.R_measured) / sigma_log)**2
        log_L_null -= 0.5 * math.log(2.0 * math.pi * sigma_log**2)
    # marginal log-likelihood for LSBridge:
    log_marginal_LS = np.log(norm) + np.max(log_post)
    log_bayes_factor = log_marginal_LS - log_L_null

    return {
        "ell_grid": ell_grid,
        "log_posterior": log_post,
        "posterior_density": post,
        "ell_MAP": ell_map,
        "ell_geometric_mean": ell_geomean,
        "ell_median": ell_median,
        "ell_CI_68": ci68,
        "ell_CI_95": ci95,
        "log_bayes_factor_LS_vs_null": float(log_bayes_factor),
    }


# =============================================================================
# 3.  Interpretation.
# =============================================================================

def bayes_factor_interpretation(log_BF):
    """Standard scale for log Bayes factor (e.g., Kass-Raftery 1995)."""
    BF = math.exp(log_BF) if log_BF < 700 else float("inf")
    if log_BF > math.log(150):
        verdict = "DECISIVE evidence for LSBridge vs R ≡ 1"
    elif log_BF > math.log(20):
        verdict = "STRONG evidence for LSBridge vs R ≡ 1"
    elif log_BF > math.log(3):
        verdict = "POSITIVE evidence for LSBridge vs R ≡ 1"
    elif log_BF > -math.log(3):
        verdict = "Inconclusive (no clear preference)"
    elif log_BF > -math.log(20):
        verdict = "POSITIVE evidence for R ≡ 1 over LSBridge"
    elif log_BF > -math.log(150):
        verdict = "STRONG evidence for R ≡ 1 over LSBridge"
    else:
        verdict = "DECISIVE evidence for R ≡ 1 over LSBridge"
    return verdict, BF


# =============================================================================
# 4.  Plotting.
# =============================================================================

def plot_posterior(result, measurements, truth_ell, out_path):
    ell_grid = result["ell_grid"]
    post = result["posterior_density"]

    fig, axes = plt.subplots(1, 2, figsize=(13, 5))

    # Posterior on log scale.
    axes[0].semilogx(ell_grid, post, "b-", linewidth=2)
    axes[0].axvline(result["ell_MAP"], color="r", linestyle="-", linewidth=2,
                     label=f"MAP ℓ = {result['ell_MAP']:.4g} μm")
    axes[0].axvline(result["ell_median"], color="g", linestyle="--",
                     label=f"median = {result['ell_median']:.4g} μm")
    if truth_ell is not None:
        axes[0].axvline(truth_ell, color="k", linestyle=":", linewidth=2,
                         label=f"truth ℓ = {truth_ell:.4g} μm")
    ci95 = result["ell_CI_95"]
    axes[0].axvspan(ci95[0], ci95[1], alpha=0.15, color="blue",
                     label=f"95% CI: [{ci95[0]:.3g}, {ci95[1]:.3g}] μm")
    axes[0].set_xlabel("ℓ (μm)")
    axes[0].set_ylabel("Posterior density P(ℓ | data)")
    axes[0].set_title("Bayesian posterior on natural length scale ℓ")
    axes[0].grid(True, which="both", alpha=0.3)
    axes[0].legend(fontsize=9)

    # Measurements + best-fit prediction.
    sigmas = [m.sigma_0_phys for m in measurements]
    R_meas = [m.R_measured for m in measurements]
    R_err = [m.R_err for m in measurements]
    axes[1].errorbar(sigmas, R_meas, yerr=R_err, fmt="o", color="black",
                      capsize=4, label="Measurements")
    sigma_pred = np.logspace(np.log10(min(sigmas) * 0.5),
                               np.log10(max(sigmas) * 1.5), 100)
    R_pred_MAP = np.array([R_predicted(s / result["ell_MAP"])
                            for s in sigma_pred])
    axes[1].loglog(sigma_pred, R_pred_MAP, "r-",
                    label=f"MAP prediction (ℓ = {result['ell_MAP']:.3g})")
    R_pred_lo = np.array([R_predicted(s / ci95[0]) for s in sigma_pred])
    R_pred_hi = np.array([R_predicted(s / ci95[1]) for s in sigma_pred])
    axes[1].fill_between(sigma_pred,
                          np.minimum(R_pred_lo, R_pred_hi),
                          np.maximum(R_pred_lo, R_pred_hi),
                          alpha=0.2, color="red", label="95% CI band")
    if truth_ell is not None:
        R_truth = np.array([R_predicted(s / truth_ell) for s in sigma_pred])
        axes[1].loglog(sigma_pred, R_truth, "k--",
                        label=f"truth (ℓ = {truth_ell:.3g})")
    axes[1].set_xlabel("σ_0 (μm)")
    axes[1].set_ylabel("R = T_LS / T_free")
    axes[1].set_title("Measurements + posterior-band prediction")
    axes[1].grid(True, which="both", alpha=0.3)
    axes[1].legend(fontsize=9)

    fig.tight_layout()
    fig.savefig(out_path, dpi=150)
    plt.close(fig)
    return out_path


# =============================================================================
# 5.  Demo.
# =============================================================================

def run_demo():
    """Two synthetic scenarios:  consistent (truth ℓ = 1) and null (R ≡ 1)."""
    print("=" * 80)
    print("LSBridge Bayesian inference — synthetic demo")
    print("=" * 80)

    # Scenario A:  LSBridge truth, 3% noise.
    truth_ell = 1.0
    sigma_phys_test = [1.0, 2.0, 3.0, 4.0, 5.0, 6.0, 7.0, 8.0]
    measurements_A = simulate_measurements(truth_ell, sigma_phys_test,
                                            relative_noise=0.03, seed=42)
    result_A = compute_posterior(measurements_A)
    verdict_BF_A, BF_A = bayes_factor_interpretation(
        result_A["log_bayes_factor_LS_vs_null"])
    plot_A = plot_posterior(result_A, measurements_A, truth_ell,
                              OUT_DIR / "demo_A_posterior.png")

    print(f"\n[Scenario A — LSBridge anomaly, truth ℓ = {truth_ell}]")
    print(f"  MAP ℓ:        {result_A['ell_MAP']:.4g} μm")
    print(f"  median ℓ:     {result_A['ell_median']:.4g} μm")
    print(f"  68% CI:       [{result_A['ell_CI_68'][0]:.4g}, "
          f"{result_A['ell_CI_68'][1]:.4g}] μm")
    print(f"  95% CI:       [{result_A['ell_CI_95'][0]:.4g}, "
          f"{result_A['ell_CI_95'][1]:.4g}] μm")
    print(f"  log BF (LS vs R≡1):  {result_A['log_bayes_factor_LS_vs_null']:.2f}  "
          f"(BF = {BF_A:.2e})")
    print(f"  Verdict:      {verdict_BF_A}")
    print(f"  Plot:         {plot_A}")

    # Scenario B:  null, R ≡ 1.
    rng = np.random.default_rng(7)
    measurements_B = []
    for s0 in sigma_phys_test:
        R_meas = 1.0 + 0.03 * float(rng.standard_normal())
        R_meas = max(R_meas, 0.5)
        measurements_B.append(Measurement(s0, R_meas, 0.03))
    result_B = compute_posterior(measurements_B)
    verdict_BF_B, BF_B = bayes_factor_interpretation(
        result_B["log_bayes_factor_LS_vs_null"])
    plot_B = plot_posterior(result_B, measurements_B, truth_ell=None,
                              out_path=OUT_DIR / "demo_B_null_posterior.png")

    print(f"\n[Scenario B — null measurement (R ≈ 1, no anomaly)]")
    print(f"  MAP ℓ:        {result_B['ell_MAP']:.4g} μm  "
          "(not physically meaningful)")
    print(f"  95% CI:       [{result_B['ell_CI_95'][0]:.4g}, "
          f"{result_B['ell_CI_95'][1]:.4g}] μm")
    print(f"  log BF (LS vs R≡1):  {result_B['log_bayes_factor_LS_vs_null']:.2f}  "
          f"(BF = {BF_B:.2e})")
    print(f"  Verdict:      {verdict_BF_B}")
    print(f"  Plot:         {plot_B}")

    # Save summary.
    summary = {
        "scenario_A": {
            "truth_ell": truth_ell,
            "measurements": [{"sigma_0_um": m.sigma_0_phys,
                              "R_measured": m.R_measured,
                              "R_err": m.R_err}
                             for m in measurements_A],
            "MAP": result_A["ell_MAP"],
            "median": result_A["ell_median"],
            "CI_68": result_A["ell_CI_68"],
            "CI_95": result_A["ell_CI_95"],
            "log_bayes_factor": result_A["log_bayes_factor_LS_vs_null"],
            "verdict": verdict_BF_A,
        },
        "scenario_B": {
            "truth": "null (R ≡ 1, no LSBridge anomaly)",
            "measurements": [{"sigma_0_um": m.sigma_0_phys,
                              "R_measured": m.R_measured,
                              "R_err": m.R_err}
                             for m in measurements_B],
            "MAP": result_B["ell_MAP"],
            "median": result_B["ell_median"],
            "CI_95": result_B["ell_CI_95"],
            "log_bayes_factor": result_B["log_bayes_factor_LS_vs_null"],
            "verdict": verdict_BF_B,
        },
    }
    out_json = OUT_DIR / "bayesian_demo_summary.json"
    with out_json.open("w") as f:
        json.dump(summary, f, indent=2)
    print(f"\nJSON:  {out_json}")


def main():
    parser = argparse.ArgumentParser(description="LSBridge Bayesian ℓ inference.")
    parser.add_argument("--csv", type=Path,
                        help="CSV of measurements (sigma_0_um, R_measured, R_err)")
    args = parser.parse_args()

    if args.csv is None:
        run_demo()
        return

    measurements = []
    with args.csv.open() as f:
        reader = csv.DictReader(f)
        for row in reader:
            measurements.append(Measurement(
                sigma_0_phys=float(row["sigma_0_um"]),
                R_measured=float(row["R_measured"]),
                R_err=float(row["R_err"]),
            ))
    result = compute_posterior(measurements)
    verdict_BF, BF = bayes_factor_interpretation(
        result["log_bayes_factor_LS_vs_null"])
    plot_path = plot_posterior(result, measurements, truth_ell=None,
                                 out_path=OUT_DIR / (args.csv.stem + "_posterior.png"))
    print(f"MAP ℓ:        {result['ell_MAP']:.4g} μm")
    print(f"95% CI:       [{result['ell_CI_95'][0]:.4g}, "
          f"{result['ell_CI_95'][1]:.4g}] μm")
    print(f"log BF:       {result['log_bayes_factor_LS_vs_null']:.2f}  (BF = {BF:.2e})")
    print(f"Verdict:      {verdict_BF}")
    print(f"Plot:         {plot_path}")


if __name__ == "__main__":
    main()
