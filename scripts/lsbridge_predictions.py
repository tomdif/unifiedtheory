"""
LSBridge prediction extraction layer.

Numerical simulation of the LSBridge Gaussian-width ODE and comparison with
free Schrödinger spreading.  Produces:
  - σ(t) curves for both models at multiple σ_0, C
  - Doubling-time tables (LSBridge vs free Schrödinger)
  - Ratio T_LS / T_free as a function of σ_0
  - Phase portraits (σ, σ̇) for the LSBridge dynamics
  - JSON summary of all numerical predictions

Based on the proved theorems in:
  UnifiedTheory/LayerB/LohmillerSlotineGaussianWidthDynamics.lean
  UnifiedTheory/LayerB/LohmillerSlotineBackreaction.lean (Part 14)
"""

from __future__ import annotations

import json
import math
from pathlib import Path

import matplotlib.pyplot as plt
import numpy as np
from scipy.integrate import quad, solve_ivp


SCRIPT_DIR = Path(__file__).resolve().parent
OUT_DIR = SCRIPT_DIR.parent / "results" / "lsbridge_predictions"
OUT_DIR.mkdir(parents=True, exist_ok=True)


# =============================================================================
# 1.  THE TWO ODEs
# =============================================================================

def lsbridge_rhs(t: float, sigma: np.ndarray, C: float) -> np.ndarray:
    """σ̇ = C · σ · exp(−σ).  From the LSBridge first integral."""
    s = sigma[0]
    if s <= 0:
        return np.array([0.0])
    return np.array([C * s * math.exp(-s)])


def free_schrodinger_sigma(t: np.ndarray, sigma_0: float,
                           hbar: float = 1.0, m: float = 1.0) -> np.ndarray:
    """
    Free-Schrödinger Gaussian width: σ(t) = σ₀ · √(1 + (ℏt/(2mσ₀²))²).
    Closed-form solution to σ̈ = ℏ²/(m²σ³).
    """
    return sigma_0 * np.sqrt(1.0 + (hbar * t / (2.0 * m * sigma_0**2))**2)


def free_schrodinger_doubling_time(sigma_0: float, hbar: float = 1.0,
                                   m: float = 1.0) -> float:
    """
    Time for free-Schrödinger σ to double from σ_0 to 2σ_0.
    Solve: 2σ_0 = σ_0 · √(1 + (ℏt/(2mσ_0²))²)
         ⇒ 4 = 1 + (ℏt/(2mσ_0²))²
         ⇒ t = 2mσ_0² · √3 / ℏ.
    """
    return 2.0 * m * sigma_0**2 * math.sqrt(3.0) / hbar


def lsbridge_doubling_time(sigma_0: float, C: float) -> float:
    """
    LSBridge doubling time:  T = ∫_{σ_0}^{2σ_0} (e^σ / (C · σ)) dσ.
    Numerical integration via scipy.quad.
    """
    integrand = lambda s: math.exp(s) / (C * s)
    T, _ = quad(integrand, sigma_0, 2.0 * sigma_0)
    return T


# =============================================================================
# 2.  σ(t) CURVES (LSBridge vs Free)
# =============================================================================

def compute_sigma_curves(sigma_0_list, C, t_max=10.0, n_points=500):
    """For each σ_0 in the list, integrate both LSBridge and free Schrödinger."""
    t = np.linspace(0.0, t_max, n_points)
    results = {}
    for s0 in sigma_0_list:
        sol = solve_ivp(
            lsbridge_rhs, (0.0, t_max), [s0],
            args=(C,), t_eval=t,
            rtol=1e-10, atol=1e-12,
            method="RK45",
        )
        sigma_LS = sol.y[0]
        sigma_free = free_schrodinger_sigma(t, s0)
        results[s0] = {"t": t, "LS": sigma_LS, "free": sigma_free}
    return results


def plot_sigma_curves(curves, C, out_path):
    fig, axes = plt.subplots(1, 2, figsize=(12, 5))
    colors = plt.cm.viridis(np.linspace(0.1, 0.9, len(curves)))
    for (s0, data), col in zip(curves.items(), colors):
        axes[0].plot(data["t"], data["LS"], color=col,
                     label=f"σ₀ = {s0:.2f}")
        axes[1].plot(data["t"], data["free"], color=col,
                     label=f"σ₀ = {s0:.2f}")
    axes[0].set_title(f"LSBridge backreaction:  σ̇ = C·σ·exp(−σ),  C = {C}")
    axes[0].set_xlabel("t")
    axes[0].set_ylabel("σ(t)")
    axes[0].legend(loc="lower right", fontsize=8)
    axes[0].grid(True, alpha=0.3)
    axes[1].set_title("Free Schrödinger:  σ(t) = σ₀·√(1+(ℏt/(2mσ₀²))²)")
    axes[1].set_xlabel("t")
    axes[1].set_ylabel("σ(t)")
    axes[1].legend(loc="lower right", fontsize=8)
    axes[1].grid(True, alpha=0.3)
    fig.tight_layout()
    fig.savefig(out_path, dpi=150)
    plt.close(fig)
    return out_path


# =============================================================================
# 3.  DOUBLING-TIME TABLE
# =============================================================================

def build_doubling_table(sigma_0_list, C_list):
    rows = []
    for s0 in sigma_0_list:
        T_free = free_schrodinger_doubling_time(s0)
        for C in C_list:
            T_LS = lsbridge_doubling_time(s0, C)
            # Proved bounds (Part 7-8):
            T_lower = math.exp(s0) / (2 * C)
            T_upper = math.exp(2 * s0) / C
            rows.append({
                "sigma_0": s0,
                "C": C,
                "T_LS_numerical": T_LS,
                "T_LS_lower_bound": T_lower,
                "T_LS_upper_bound": T_upper,
                "T_free": T_free,
                "ratio_T_LS_over_T_free": T_LS / T_free,
                "ratio_lower_bound": T_lower / T_free,
            })
    return rows


def plot_doubling_ratio(table_rows, C_list, out_path):
    """Plot T_LS / T_free as a function of σ_0 for each C."""
    fig, ax = plt.subplots(figsize=(8, 6))
    for C in C_list:
        rows = [r for r in table_rows if r["C"] == C]
        s_vals = [r["sigma_0"] for r in rows]
        ratios = [r["ratio_T_LS_over_T_free"] for r in rows]
        ax.semilogy(s_vals, ratios, "o-", label=f"C = {C}")
    ax.set_xlabel("σ₀ (initial width, natural units)")
    ax.set_ylabel("T_LS / T_free  (log scale)")
    ax.set_title("LSBridge backreaction:  doubling-time enhancement over free Schrödinger")
    ax.grid(True, which="both", alpha=0.3)
    ax.legend()
    ax.axhline(1.0, color="k", linestyle="--", alpha=0.5,
               label="parity (T_LS = T_free)")
    fig.tight_layout()
    fig.savefig(out_path, dpi=150)
    plt.close(fig)
    return out_path


# =============================================================================
# 4.  PHASE PORTRAIT (σ, σ̇)
# =============================================================================

def plot_phase_portrait(C, sigma_max=6.0, out_path=None):
    """Phase portrait of σ̇ = C·σ·exp(−σ).  Vector field + sample trajectories."""
    sigma_vals = np.linspace(0.05, sigma_max, 80)
    sigma_prime = C * sigma_vals * np.exp(-sigma_vals)

    fig, axes = plt.subplots(1, 2, figsize=(13, 5))

    # Left: σ̇(σ) curve, marking the maximum at σ = 1.
    axes[0].plot(sigma_vals, sigma_prime, "b-", linewidth=2,
                 label=f"σ̇ = C·σ·exp(−σ),  C = {C}")
    sigma_star = 1.0
    sigma_prime_max = C / math.e
    axes[0].plot(sigma_star, sigma_prime_max, "ro", markersize=10,
                 label=f"max at σ = 1, σ̇_max = C/e ≈ {sigma_prime_max:.4f}")
    axes[0].axvline(1.0, color="r", linestyle="--", alpha=0.4)
    axes[0].axhline(sigma_prime_max, color="r", linestyle="--", alpha=0.4)
    axes[0].set_xlabel("σ (Gaussian width)")
    axes[0].set_ylabel("σ̇ (spreading rate)")
    axes[0].set_title("LSBridge spreading rate vs width — optimal at σ = 1")
    axes[0].grid(True, alpha=0.3)
    axes[0].legend()

    # Right: σ(t) trajectories starting from different σ_0.
    t_max = 50.0
    t_eval = np.linspace(0.0, t_max, 500)
    start_σ = [0.2, 0.5, 1.0, 1.5, 2.0, 3.0, 4.0]
    for s0 in start_σ:
        sol = solve_ivp(lsbridge_rhs, (0.0, t_max), [s0],
                        args=(C,), t_eval=t_eval,
                        rtol=1e-10, atol=1e-12)
        axes[1].plot(sol.t, sol.y[0], label=f"σ₀ = {s0}")
    axes[1].set_xlabel("t")
    axes[1].set_ylabel("σ(t)")
    axes[1].set_title(f"LSBridge σ(t) for various σ₀ (C = {C})")
    axes[1].grid(True, alpha=0.3)
    axes[1].legend(loc="lower right", fontsize=8)

    fig.tight_layout()
    if out_path:
        fig.savefig(out_path, dpi=150)
    plt.close(fig)
    return out_path


# =============================================================================
# 5.  MAIN — RUN EVERYTHING
# =============================================================================

def main():
    C_default = 1.0
    sigma_0_curves = [0.5, 1.0, 1.5, 2.0, 3.0, 5.0]
    sigma_0_table = [0.5, 1.0, 2.0, 3.0, 5.0, 7.0, 10.0]
    C_table = [0.1, 1.0, 10.0]

    # σ(t) curves.
    curves = compute_sigma_curves(sigma_0_curves, C_default, t_max=30.0)
    p1 = plot_sigma_curves(curves, C_default,
                            OUT_DIR / "sigma_curves_LSbridge_vs_free.png")

    # Doubling-time table.
    table = build_doubling_table(sigma_0_table, C_table)
    p2 = plot_doubling_ratio(table, C_table,
                              OUT_DIR / "doubling_time_ratio.png")

    # Phase portrait (default C = 1.0).
    p3 = plot_phase_portrait(C_default,
                              out_path=OUT_DIR / "phase_portrait.png")

    # Optimal-width verification: σ*(C) = 1 always; max rate = C/e.
    optimal_data = []
    for C in [0.1, 0.5, 1.0, 2.0, 10.0]:
        sigma_test = np.linspace(0.01, 5.0, 1000)
        rates = C * sigma_test * np.exp(-sigma_test)
        idx_max = int(np.argmax(rates))
        optimal_data.append({
            "C": C,
            "optimal_sigma_numerical": float(sigma_test[idx_max]),
            "optimal_sigma_proved": 1.0,
            "max_rate_numerical": float(rates[idx_max]),
            "max_rate_proved": C / math.e,
        })

    # Save summary JSON.
    summary = {
        "lsbridge_predictions_summary": {
            "ode": "σ̇ = C · σ · exp(−σ)  (from LSBridge backreaction conservation law)",
            "free_schrodinger_ode": "σ̈ = ℏ²/(m²σ³)  with closed form σ(t) = σ₀√(1+(ℏt/(2mσ₀²))²)",
            "proved_bounds": {
                "doubling_time_lower": "T ≥ exp(σ_0)/(2C)",
                "doubling_time_upper": "T ≤ exp(2σ_0)/C",
                "spreading_rate_max": "σ̇ ≤ C/e, attained at σ = 1",
            },
            "C_default": C_default,
            "plots": {
                "sigma_curves": str(p1.relative_to(SCRIPT_DIR.parent)),
                "doubling_ratio": str(p2.relative_to(SCRIPT_DIR.parent)),
                "phase_portrait": str(p3.relative_to(SCRIPT_DIR.parent)),
            },
            "doubling_table": table,
            "optimal_width_data": optimal_data,
        },
    }
    json_path = OUT_DIR / "summary.json"
    with json_path.open("w") as f:
        json.dump(summary, f, indent=2)

    # Console report.
    print("=" * 78)
    print("LSBridge prediction extraction — summary")
    print("=" * 78)
    print()
    print(f"Output directory: {OUT_DIR}")
    print()
    print("Plots generated:")
    print(f"  - {p1.name}")
    print(f"  - {p2.name}")
    print(f"  - {p3.name}")
    print()
    print("Doubling-time table (subset):")
    print(f"  {'σ_0':>6}  {'C':>6}  {'T_LS':>15}  {'T_free':>10}  "
          f"{'T_LS/T_free':>14}  {'lower_bnd':>12}  {'upper_bnd':>12}")
    for r in table:
        print(f"  {r['sigma_0']:>6.2f}  {r['C']:>6.2f}  "
              f"{r['T_LS_numerical']:>15.4e}  {r['T_free']:>10.4e}  "
              f"{r['ratio_T_LS_over_T_free']:>14.4e}  "
              f"{r['T_LS_lower_bound']:>12.4e}  "
              f"{r['T_LS_upper_bound']:>12.4e}")
    print()
    print("Optimal-width verification:  σ* = 1, max rate = C/e")
    print(f"  {'C':>6}  {'σ*_num':>10}  {'σ*_proved':>10}  "
          f"{'rate_max_num':>14}  {'rate_max_proved':>15}")
    for r in optimal_data:
        print(f"  {r['C']:>6.2f}  {r['optimal_sigma_numerical']:>10.4f}  "
              f"{r['optimal_sigma_proved']:>10.4f}  "
              f"{r['max_rate_numerical']:>14.6f}  "
              f"{r['max_rate_proved']:>15.6f}")
    print()
    print(f"Full numerical data: {json_path}")
    print()
    print("=" * 78)


if __name__ == "__main__":
    main()
