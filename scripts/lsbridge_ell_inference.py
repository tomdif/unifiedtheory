"""
LSBridge parameter-inference layer.

The LSBridge framework predicts dimensionless `R(σ_0) = T_LS/T_free`.
The free parameter `ℓ` (natural length scale) sets `σ_dim = σ_phys / ℓ`.

This script inverts the inference problem:  given a set of measured
(σ_0_phys, T_measured) pairs from a photonic waveguide experiment,
either:
  (a) fit `ℓ` to the data and report best-fit + confidence interval,  OR
  (b) rule out a range of `ℓ` values when the fit is poor.

Two modes:
  • simulate:  generate synthetic measurements at a chosen `truth_ell`,
    add experimental noise, run the fit to demonstrate recovery.
  • fit:       load real measurements from a CSV and report the fit.

Universal predicted curve (proved in LohmillerSlotineGaussianWidthDynamics):
    R_pred(σ_dim) = T_LS,dim(σ_dim) / T_free,dim(σ_dim)
                  = (∫_{σ_dim}^{2σ_dim} (e^s/(C·s)) ds) / (√3 · σ_dim²).
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
from scipy.optimize import minimize_scalar


SCRIPT_DIR = Path(__file__).resolve().parent
OUT_DIR = SCRIPT_DIR.parent / "results" / "lsbridge_predictions" / "ell_inference"
OUT_DIR.mkdir(parents=True, exist_ok=True)


@dataclass
class Measurement:
    """A single experimental data point."""
    sigma_0_phys: float       # physical initial width (μm in photonic units)
    R_measured: float          # ratio T_measured / T_free_predicted
    R_err: float               # 1σ error on R_measured


# =============================================================================
# 1. The predicted R(σ_dim) curve.
# =============================================================================

def R_predicted(sigma_dim: float, C: float = 1.0) -> float:
    """R_pred(σ_dim) = T_LS(σ_dim) / T_free(σ_dim).
    Both in dimensionless units (ℏ/m = 1 OR D = 1 for photonic).

    For very large σ_dim the integrand exp(σ) overflows; return +∞ so
    χ² rejects that ℓ.  For very small σ_dim the integral is computed
    accurately by scipy.quad."""
    if sigma_dim <= 0:
        return float("inf")
    if sigma_dim > 100.0:
        # exp(200) overflows double precision; this ℓ is excluded.
        return float("inf")
    try:
        T_LS = quad(lambda s: math.exp(s) / (C * s), sigma_dim, 2.0 * sigma_dim)[0]
    except (OverflowError, ValueError):
        return float("inf")
    T_free = math.sqrt(3.0) * sigma_dim**2
    return T_LS / T_free


# =============================================================================
# 2. Inference: χ²(ℓ) over a grid of candidate ℓ values.
# =============================================================================

def chi_squared(ell: float, measurements: list[Measurement],
                C: float = 1.0) -> float:
    """χ²(ℓ) on the LOG scale (R varies over many decades; noise is
    multiplicative in time measurements).

      χ² = Σ [(log R_meas − log R_pred(σ/ℓ)) / σ_log]²
    where σ_log ≈ R_err / R_measured  (relative error)."""
    chi2 = 0.0
    for m in measurements:
        sigma_dim = m.sigma_0_phys / ell
        R_pred = R_predicted(sigma_dim, C)
        if not math.isfinite(R_pred) or R_pred <= 0 or m.R_measured <= 0:
            return float("inf")
        log_R_meas = math.log(m.R_measured)
        log_R_pred = math.log(R_pred)
        sigma_log = m.R_err / m.R_measured  # relative error → log-space σ.
        chi2 += ((log_R_meas - log_R_pred) / sigma_log)**2
    return chi2


def fit_ell(measurements: list[Measurement],
            ell_range_um=(1e-3, 1e3), n_grid: int = 400,
            C: float = 1.0) -> dict:
    """Two-stage fit:  coarse grid scan to find the best decade, then
    continuous optimization within for a precise best-fit ℓ.

    Returns best ℓ, χ²_min, and a 1σ confidence interval estimated
    from a finer grid sweep around the optimum."""
    # Stage 1: coarse grid.
    log_ell_grid = np.linspace(np.log10(ell_range_um[0]),
                               np.log10(ell_range_um[1]), n_grid)
    ell_grid = 10.0**log_ell_grid
    chi2_values = np.array([chi_squared(ell, measurements, C)
                            for ell in ell_grid])
    idx_best = int(np.argmin(chi2_values))
    ell_coarse = float(ell_grid[idx_best])

    # Stage 2: continuous optimization in a neighborhood of ell_coarse.
    log_coarse = math.log10(ell_coarse)
    bracket_lo = max(log_ell_grid[0], log_coarse - 0.5)
    bracket_hi = min(log_ell_grid[-1], log_coarse + 0.5)
    result = minimize_scalar(
        lambda log_ell: chi_squared(10.0**log_ell, measurements, C),
        bracket=(bracket_lo, log_coarse, bracket_hi),
        method="brent",
        options={"xtol": 1e-8},
    )
    ell_best = 10.0**float(result.x)
    chi2_min = float(result.fun)

    # Stage 3: fine grid around best to estimate the 1σ region.
    fine_log = np.linspace(math.log10(ell_best) - 1.0,
                            math.log10(ell_best) + 1.0, 2001)
    fine_ell = 10.0**fine_log
    fine_chi2 = np.array([chi_squared(ell, measurements, C)
                          for ell in fine_ell])
    # 1σ confidence interval:  Δχ² = 1.
    threshold = chi2_min + 1.0
    above = fine_chi2 <= threshold
    if above.any():
        lo_idx = int(np.argmax(above))
        hi_idx = len(above) - 1 - int(np.argmax(above[::-1]))
        ell_lo = float(fine_ell[lo_idx])
        ell_hi = float(fine_ell[hi_idx])
    else:
        ell_lo = ell_hi = ell_best

    # Plausibility check:  is the best-fit chi² consistent with the data?
    # Use reduced χ² = χ²/dof.  With 1 fitted parameter, dof = n - 1.
    # Reduced χ² ~ 1 indicates a good fit.  Threshold: reduced χ² < 5.
    n_data = len(measurements)
    dof = max(1, n_data - 1)
    reduced_chi2 = chi2_min / dof
    is_consistent = reduced_chi2 < 5.0

    return {
        "ell_best_um": ell_best,
        "chi2_min": chi2_min,
        "reduced_chi2": reduced_chi2,
        "dof": dof,
        "n_data_points": n_data,
        "ell_lower_1sigma_um": ell_lo,
        "ell_upper_1sigma_um": ell_hi,
        "ell_grid_um": ell_grid.tolist(),
        "chi2_grid": chi2_values.tolist(),
        "model_consistent_with_data": is_consistent,
    }


# =============================================================================
# 3. Falsification verdict.
# =============================================================================

def falsification_verdict(fit_result: dict, n_data: int) -> dict:
    """
    Reach a clear verdict.

      • model_consistent      ⇒ within fit window, ℓ constrained.
      • ell_at_grid_boundary  ⇒ best-fit hit the grid edge; widen the
                                grid or interpret as "no good ℓ exists."
      • model_in_tension      ⇒ χ²_min way above expected; theory in
                                serious tension with the data even at
                                its best-fit ℓ.
    """
    chi2 = fit_result["chi2_min"]
    reduced = fit_result["reduced_chi2"]
    if not fit_result["model_consistent_with_data"]:
        return {
            "verdict": "FALSIFIED_or_BAD_MODEL",
            "chi2_min": chi2,
            "reduced_chi2": reduced,
            "n_data_points": n_data,
            "interpretation": (
                f"reduced χ² = {reduced:.2f} ≫ 1  "
                f"(χ²_min = {chi2:.2f}, dof = {fit_result['dof']}).  "
                "No ℓ in the search range makes the LSBridge prediction "
                "consistent with the measurements.  Either the theory is "
                "falsified or the experiment has unmodelled systematics."
            ),
        }
    return {
        "verdict": "CONSISTENT_FIT",
        "chi2_min": chi2,
        "reduced_chi2": reduced,
        "n_data_points": n_data,
        "ell_best_um": fit_result["ell_best_um"],
        "ell_1sigma_range_um": [
            fit_result["ell_lower_1sigma_um"],
            fit_result["ell_upper_1sigma_um"],
        ],
        "interpretation": (
            f"reduced χ² = {reduced:.2f} at ℓ = {fit_result['ell_best_um']:.4g} "
            f"μm.  LSBridge is consistent with the data;  the natural "
            f"length scale is bracketed at 1σ to "
            f"[{fit_result['ell_lower_1sigma_um']:.4g}, "
            f"{fit_result['ell_upper_1sigma_um']:.4g}] μm."
        ),
    }


# =============================================================================
# 4. Simulation:  generate synthetic measurements at a chosen truth_ell.
# =============================================================================

def simulate_measurements(truth_ell_um: float,
                          sigma_0_phys_list,
                          relative_noise: float = 0.10,
                          C: float = 1.0,
                          seed: int = 42) -> list[Measurement]:
    """Generate noisy R_measured at the chosen true ℓ."""
    rng = np.random.default_rng(seed)
    measurements = []
    for sigma_phys in sigma_0_phys_list:
        sigma_dim = sigma_phys / truth_ell_um
        R_true = R_predicted(sigma_dim, C)
        # Multiplicative noise (typical for time measurements).
        noise = rng.normal(0.0, relative_noise)
        R_meas = R_true * (1.0 + noise)
        # Force a small positive lower bound.
        R_meas = max(R_meas, 1e-3 * R_true)
        R_err = R_true * relative_noise
        measurements.append(Measurement(sigma_phys, R_meas, R_err))
    return measurements


# =============================================================================
# 5. Plotting.
# =============================================================================

def plot_chi2_curve(fit_result, measurements, truth_ell, out_path):
    fig, axes = plt.subplots(1, 2, figsize=(14, 5))

    ell_grid = np.array(fit_result["ell_grid_um"])
    chi2 = np.array(fit_result["chi2_grid"])
    ell_best = fit_result["ell_best_um"]
    chi2_min = fit_result["chi2_min"]

    axes[0].semilogx(ell_grid, chi2, "b-")
    axes[0].axhline(chi2_min + 1.0, color="g", linestyle="--",
                    label="Δχ² = 1 (1σ)")
    axes[0].axvline(ell_best, color="r", linestyle="-", linewidth=2,
                    label=f"Best fit ℓ = {ell_best:.4g} μm")
    if truth_ell is not None:
        axes[0].axvline(truth_ell, color="k", linestyle=":", linewidth=2,
                        label=f"Truth ℓ = {truth_ell:.4g} μm")
    axes[0].set_xlabel("Candidate ℓ (μm)")
    axes[0].set_ylabel("χ²(ℓ)")
    axes[0].set_title("Profile of χ² vs ℓ — best fit + 1σ range")
    axes[0].set_yscale("log")
    axes[0].grid(True, which="both", alpha=0.3)
    axes[0].legend()

    sigmas = [m.sigma_0_phys for m in measurements]
    R_meas = [m.R_measured for m in measurements]
    R_err = [m.R_err for m in measurements]
    axes[1].errorbar(sigmas, R_meas, yerr=R_err, fmt="o", color="black",
                     label="Measurements", capsize=4)
    sigma_pred = np.logspace(np.log10(min(sigmas) * 0.5),
                              np.log10(max(sigmas) * 2.0), 100)
    R_at_best = np.array([R_predicted(s / ell_best) for s in sigma_pred])
    axes[1].loglog(sigma_pred, R_at_best, "r-",
                   label=f"Best-fit prediction (ℓ = {ell_best:.3g} μm)")
    if truth_ell is not None:
        R_at_truth = np.array([R_predicted(s / truth_ell) for s in sigma_pred])
        axes[1].loglog(sigma_pred, R_at_truth, "k--",
                       label=f"Truth (ℓ = {truth_ell:.3g} μm)")
    axes[1].set_xlabel("σ_0 (μm)")
    axes[1].set_ylabel("R = T_LS / T_free")
    axes[1].set_title("Measurements vs predicted curve")
    axes[1].grid(True, which="both", alpha=0.3)
    axes[1].legend()

    fig.tight_layout()
    fig.savefig(out_path, dpi=150)
    plt.close(fig)
    return out_path


# =============================================================================
# 6. CLI.
# =============================================================================

def _print_demo_block(title, measurements, fit_result, verdict,
                       truth_ell, plot_path, json_path):
    print("=" * 78)
    print(title)
    print("=" * 78)
    if truth_ell is not None:
        print(f"  Truth ℓ:  {truth_ell} μm")
    print(f"  Measurements (σ_0, R_measured ± err):")
    for m in measurements:
        print(f"    σ_0 = {m.sigma_0_phys:>5.2f} μm:  "
              f"R = {m.R_measured:>10.4e} ± {m.R_err:>10.4e}")
    print()
    print(f"  Best-fit ℓ:    {fit_result['ell_best_um']:.4g} μm")
    print(f"  1σ range:      [{fit_result['ell_lower_1sigma_um']:.4g}, "
          f"{fit_result['ell_upper_1sigma_um']:.4g}] μm")
    print(f"  χ²_min:        {fit_result['chi2_min']:.3f}")
    print(f"  Reduced χ²:    {fit_result['reduced_chi2']:.3f}  "
          f"(dof = {fit_result['dof']})")
    print(f"  Data points:   {len(measurements)}")
    print(f"  Verdict:       {verdict['verdict']}")
    print(f"  Interpretation:")
    print(f"    {verdict['interpretation']}")
    print()
    print(f"  Plot:  {plot_path}")
    print(f"  JSON:  {json_path}")
    print()


def run_simulation_demo():
    """Two synthetic scenarios: (A) anomaly present, fit recovers ℓ.
                                (B) no anomaly, model is falsified."""
    # Scenario A:  LSBridge truth at ℓ = 1.0 μm with realistic noise.
    # Use σ_0 ∈ [1, 8] μm (moderate range — the exponential growth at
    # higher σ_0 makes the χ² landscape highly non-quadratic).
    truth_ell = 1.0
    sigma_phys_test = [1.0, 2.0, 3.0, 4.0, 5.0, 6.0, 7.0, 8.0]
    measurements_A = simulate_measurements(truth_ell, sigma_phys_test,
                                            relative_noise=0.03, seed=42)
    fit_A = fit_ell(measurements_A, ell_range_um=(1e-3, 100.0))
    verdict_A = falsification_verdict(fit_A, len(measurements_A))
    plot_A = OUT_DIR / "demo_A_consistent.png"
    plot_chi2_curve(fit_A, measurements_A, truth_ell, plot_A)
    json_A = OUT_DIR / "demo_A_consistent.json"
    with json_A.open("w") as f:
        json.dump({
            "scenario": "A — LSBridge anomaly present, fit recovers ℓ",
            "truth_ell_um": truth_ell,
            "measurements": [{"sigma_0_um": m.sigma_0_phys,
                              "R_measured": m.R_measured,
                              "R_err": m.R_err}
                             for m in measurements_A],
            "fit": {k: v for k, v in fit_A.items()
                    if k not in {"ell_grid_um", "chi2_grid"}},
            "verdict": verdict_A,
        }, f, indent=2)
    _print_demo_block("Scenario A:  LSBridge anomaly present  (truth ℓ = 1.0 μm)",
                       measurements_A, fit_A, verdict_A, truth_ell,
                       plot_A, json_A)

    # Scenario B:  NO anomaly — R_measured ≈ 1 for all σ_0 (free Schrödinger
    # spreading matches the data).  Demonstrates falsification path.
    rng = np.random.default_rng(7)
    measurements_B = []
    for s0 in sigma_phys_test:
        R_meas = 1.0 + 0.03 * float(rng.standard_normal())  # ≈ 1 ± 3%
        R_meas = max(R_meas, 0.5)
        measurements_B.append(Measurement(s0, R_meas, 0.03))
    fit_B = fit_ell(measurements_B, ell_range_um=(1e-3, 100.0))
    verdict_B = falsification_verdict(fit_B, len(measurements_B))
    plot_B = OUT_DIR / "demo_B_no_anomaly_falsifies.png"
    plot_chi2_curve(fit_B, measurements_B, truth_ell=None, out_path=plot_B)
    json_B = OUT_DIR / "demo_B_no_anomaly_falsifies.json"
    with json_B.open("w") as f:
        json.dump({
            "scenario": ("B — no anomaly measured (R_measured ≈ 1 for "
                         "all σ_0); LSBridge falsified"),
            "measurements": [{"sigma_0_um": m.sigma_0_phys,
                              "R_measured": m.R_measured,
                              "R_err": m.R_err}
                             for m in measurements_B],
            "fit": {k: v for k, v in fit_B.items()
                    if k not in {"ell_grid_um", "chi2_grid"}},
            "verdict": verdict_B,
        }, f, indent=2)
    _print_demo_block("Scenario B:  NO anomaly measured (R ≈ 1)",
                       measurements_B, fit_B, verdict_B, None,
                       plot_B, json_B)


def run_csv_fit(csv_path: Path):
    """Fit from a CSV with columns sigma_0_um, R_measured, R_err."""
    measurements = []
    with csv_path.open() as f:
        reader = csv.DictReader(f)
        for row in reader:
            measurements.append(Measurement(
                sigma_0_phys=float(row["sigma_0_um"]),
                R_measured=float(row["R_measured"]),
                R_err=float(row["R_err"]),
            ))
    fit_result = fit_ell(measurements)
    verdict = falsification_verdict(fit_result, len(measurements))
    plot_path = OUT_DIR / (csv_path.stem + "_fit.png")
    plot_chi2_curve(fit_result, measurements, truth_ell=None,
                     out_path=plot_path)

    print(f"Fit from {csv_path}:")
    print(f"  Best ℓ:   {fit_result['ell_best_um']:.4g} μm")
    print(f"  χ²_min:   {fit_result['chi2_min']:.3f}")
    print(f"  Verdict:  {verdict['verdict']}")
    print(f"  {verdict['interpretation']}")
    print(f"Plot:  {plot_path}")


def main():
    parser = argparse.ArgumentParser(description="LSBridge ℓ parameter inference.")
    parser.add_argument("--csv", type=Path,
                        help="CSV of measurements (sigma_0_um, R_measured, R_err)")
    args = parser.parse_args()

    if args.csv:
        run_csv_fit(args.csv)
    else:
        run_simulation_demo()


if __name__ == "__main__":
    main()
