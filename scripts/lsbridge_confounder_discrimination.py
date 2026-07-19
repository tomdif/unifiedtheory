"""
LSBridge vs experimental confounders — discrimination tool.

An experimentalist observing anomalously slow Gaussian-beam spreading in
a photonic waveguide array could attribute it to several alternative
mechanisms beyond LSBridge backreaction.  This script compares the
predicted `R(σ_0) = T_measured / T_free` curves for:

  1.  LSBridge backreaction (proved theorems).
  2.  Linear loss (no spreading effect, R ≡ 1).
  3.  Kerr nonlinearity (self-focusing — R < 1 at small σ_0).
  4.  Anderson localization (R → ∞ above localization length ξ_loc).
  5.  Next-nearest-neighbor hopping (small modification, R ≈ 1+ε).

Output:  per-mechanism R(σ_0) curves + a "fingerprint discrimination"
table showing which σ_0 ranges uniquely identify LSBridge.
"""

from __future__ import annotations

import json
import math
from pathlib import Path

import matplotlib.pyplot as plt
import numpy as np
from scipy.integrate import quad


SCRIPT_DIR = Path(__file__).resolve().parent
OUT_DIR = SCRIPT_DIR.parent / "results" / "lsbridge_predictions" / "confounders"
OUT_DIR.mkdir(parents=True, exist_ok=True)


# =============================================================================
# 1. R(σ_0) predictions for each mechanism.
# =============================================================================

def R_lsbridge(sigma_0: float, C: float = 1.0) -> float:
    """R from the proved LSBridge bounds.
    Numerical integral of e^σ/(Cσ) over [σ_0, 2σ_0], divided by free."""
    integ = quad(lambda s: math.exp(s) / (C * s), sigma_0, 2.0 * sigma_0)[0]
    return integ / (math.sqrt(3.0) * sigma_0**2)


def R_linear_loss(sigma_0: float) -> float:
    """Linear loss attenuates uniformly — width evolution is unaffected.
    Hence R ≡ 1 by construction."""
    return 1.0


def R_kerr_self_focusing(sigma_0: float, kerr_strength: float = 0.5) -> float:
    """Negative Kerr (self-focusing) predicts ACCELERATED spreading
    (or self-focusing if strong enough).  For a Gaussian, the
    nonlinear contribution to σ̈ goes like  +n_2·I_0·σ_0²/σ³  (focusing,
    sign chosen so kerr_strength > 0 means accelerated spread).

    Free σ̈ = ℏ²/(m²σ³);  Kerr σ̈ = ℏ²·(1 + kerr_strength·σ_0²)/(m²σ³).
    Effective spreading speed grows, so doubling time shrinks:
        T_kerr ≈ T_free / √(1 + kerr_strength · σ_0²)
    For self-focusing (effective negative diffraction),  R < 1  for
    moderate σ_0 and decreases with σ_0.

    Approximation:  R_kerr(σ_0) = 1 / √(1 + kerr_strength · σ_0²)."""
    return 1.0 / math.sqrt(1.0 + kerr_strength * sigma_0**2)


def R_anderson_localization(sigma_0: float, xi_loc: float = 50.0) -> float:
    """Anderson localization caps spreading at width ξ_loc.  For σ_0 > ξ_loc,
    the wavepacket cannot spread beyond its localization length — doubling
    is impossible.  For σ_0 << ξ_loc, ordinary spreading dominates.
    Approximation:
        R_AL(σ_0) ≈ 1                 if 2σ_0 < ξ_loc
        R_AL(σ_0) ≈ exp((2σ_0/ξ_loc)²)  if 2σ_0 ≥ ξ_loc (sharp blow-up)
    """
    if 2.0 * sigma_0 < xi_loc:
        return 1.0
    arg = ((2.0 * sigma_0 - xi_loc) / (0.2 * xi_loc))**2
    if arg > 700.0:  # exp(700) overflows; clamp.
        return 1e300
    return math.exp(arg)


def R_nnn_hopping(sigma_0: float, eps: float = 0.05) -> float:
    """Next-nearest-neighbor hopping modifies effective dispersion by a
    small relative factor (1 + ε).  Doubling time scales by 1/(1+ε)²
    approximately.  Predicts R = 1/(1+ε)² ≈ 1 − 2ε constant in σ_0."""
    return 1.0 / (1.0 + eps)**2


# =============================================================================
# 2.  Plot all mechanisms on a single axis.
# =============================================================================

def plot_mechanisms(out_path, sigma_range=(0.5, 12.0), n=300):
    sigma = np.linspace(sigma_range[0], sigma_range[1], n)
    r_ls = np.array([R_lsbridge(s) for s in sigma])
    r_loss = np.array([R_linear_loss(s) for s in sigma])
    r_kerr_small = np.array([R_kerr_self_focusing(s, kerr_strength=0.1) for s in sigma])
    r_kerr_large = np.array([R_kerr_self_focusing(s, kerr_strength=1.0) for s in sigma])
    r_AL_small = np.array([R_anderson_localization(s, xi_loc=10.0) for s in sigma])
    r_AL_large = np.array([R_anderson_localization(s, xi_loc=20.0) for s in sigma])
    r_nnn = np.array([R_nnn_hopping(s, eps=0.05) for s in sigma])

    fig, ax = plt.subplots(figsize=(11, 7))
    ax.semilogy(sigma, r_ls, "r-", linewidth=2.5, label="LSBridge backreaction")
    ax.semilogy(sigma, r_loss, "k-", linewidth=1.5, alpha=0.6, label="Linear loss (R ≡ 1)")
    ax.semilogy(sigma, r_kerr_small, "b--", linewidth=1.5,
                label="Kerr self-focusing (weak, n₂σ₀² = 0.1)")
    ax.semilogy(sigma, r_kerr_large, "b:", linewidth=1.5,
                label="Kerr self-focusing (strong, n₂σ₀² = 1.0)")
    ax.semilogy(sigma, r_AL_small, "g--", linewidth=1.5,
                label="Anderson localization (ξ_loc = 10 μm)")
    ax.semilogy(sigma, r_AL_large, "g:", linewidth=1.5,
                label="Anderson localization (ξ_loc = 20 μm)")
    ax.semilogy(sigma, r_nnn, "m-.", linewidth=1.5,
                label="Next-nearest-neighbor hopping (ε = 0.05)")
    ax.axhline(1.0, color="gray", linestyle=":", alpha=0.5)
    ax.set_xlabel("σ_0  (μm, assuming natural length ℓ = 1 μm)")
    ax.set_ylabel("R(σ_0) = T_measured / T_free  (log scale)")
    ax.set_title("LSBridge vs experimental confounders — R(σ_0) fingerprints")
    ax.grid(True, which="both", alpha=0.3)
    ax.legend(loc="upper left", fontsize=9)
    fig.tight_layout()
    fig.savefig(out_path, dpi=150)
    plt.close(fig)
    return out_path


# =============================================================================
# 3.  Discrimination table:  ratio LSBridge / confounder per σ_0.
# =============================================================================

def discrimination_ratios(sigma_0_list):
    rows = []
    for s in sigma_0_list:
        r_ls = R_lsbridge(s)
        r_loss = R_linear_loss(s)
        r_kerr_weak = R_kerr_self_focusing(s, 0.1)
        r_kerr_strong = R_kerr_self_focusing(s, 1.0)
        r_AL_10 = R_anderson_localization(s, 10.0)
        r_AL_20 = R_anderson_localization(s, 20.0)
        r_nnn = R_nnn_hopping(s, 0.05)
        rows.append({
            "sigma_0_um": s,
            "LSBridge": r_ls,
            "linear_loss": r_loss,
            "kerr_weak": r_kerr_weak,
            "kerr_strong": r_kerr_strong,
            "AL_xi=10um": r_AL_10,
            "AL_xi=20um": r_AL_20,
            "nnn_hopping": r_nnn,
            "LSBridge_over_loss": r_ls / r_loss,
            "LSBridge_over_kerr_weak": r_ls / r_kerr_weak,
            "LSBridge_over_AL_10": r_ls / r_AL_10,
            "LSBridge_over_AL_20": r_ls / r_AL_20,
        })
    return rows


def print_discrimination_table(rows):
    print(f"\n{'σ_0 (μm)':>10} | {'LSBridge':>12} | {'loss':>8} | "
          f"{'kerr_w':>10} | {'AL ξ=10':>12} | {'AL ξ=20':>12} | {'nnn':>8}")
    print("-" * 90)
    for r in rows:
        print(f"{r['sigma_0_um']:>10.2f} | {r['LSBridge']:>12.4e} | "
              f"{r['linear_loss']:>8.4f} | {r['kerr_weak']:>10.4f} | "
              f"{r['AL_xi=10um']:>12.4e} | {r['AL_xi=20um']:>12.4e} | "
              f"{r['nnn_hopping']:>8.4f}")


# =============================================================================
# 4.  Identify the "uniquely-LSBridge" σ_0 windows.
# =============================================================================

def find_unique_lsbridge_windows(sigma_range=(0.5, 12.0), n=600):
    """A σ_0 is 'uniquely LSBridge' if R_LS(σ_0) differs from every confounder
    R by more than 5× (factor) AND is itself > 5×."""
    sigma = np.linspace(sigma_range[0], sigma_range[1], n)
    windows_5x = []
    windows_50x = []
    for s in sigma:
        r_ls = R_lsbridge(s)
        if r_ls < 5.0:
            continue
        # All confounders we want to distinguish from:
        confounders = [
            R_linear_loss(s),
            R_kerr_self_focusing(s, 0.1),
            R_kerr_self_focusing(s, 1.0),
            R_anderson_localization(s, 10.0),
            R_anderson_localization(s, 20.0),
            R_nnn_hopping(s, 0.05),
        ]
        max_confounder = max(confounders)
        if r_ls > 5.0 * max_confounder:
            windows_5x.append(s)
        if r_ls > 50.0 * max_confounder:
            windows_50x.append(s)
    return {
        "5x_above_all_confounders": [round(s, 3) for s in windows_5x],
        "50x_above_all_confounders": [round(s, 3) for s in windows_50x],
        "5x_window_min_sigma": float(windows_5x[0]) if windows_5x else None,
        "5x_window_max_sigma": float(windows_5x[-1]) if windows_5x else None,
        "50x_window_min_sigma": float(windows_50x[0]) if windows_50x else None,
        "50x_window_max_sigma": float(windows_50x[-1]) if windows_50x else None,
    }


# =============================================================================
# 5.  Anderson localization vs LSBridge — special discrimination.
# =============================================================================
#
# Both Anderson localization (σ_0 ≳ ξ_loc) and LSBridge predict R ≫ 1 at
# large σ_0.  They are distinguished by:
#   (a) AL has a SHARP THRESHOLD at σ_0 ~ ξ_loc.
#   (b) LSBridge has a SMOOTH exp(σ_0)/σ_0² growth from R ~ 1.
# Below ξ_loc, AL predicts R = 1 (free spreading); LSBridge predicts a
# monotonically growing R(σ_0).
# =============================================================================

def AL_vs_lsbridge_discrimination(xi_loc_list=(5.0, 10.0, 20.0, 50.0),
                                   sigma_range=(0.5, 20.0)):
    out = []
    for xi in xi_loc_list:
        # Below threshold: R_AL ≈ 1, R_LS smoothly grows.
        # The SLOPE of R(σ_0) discriminates: LSBridge has slope > 0 always,
        # AL has slope 0 until threshold, then sharp blow-up.
        sigma_test = np.linspace(sigma_range[0], min(sigma_range[1], 0.9 * xi), 50)
        # In the sub-threshold region, LSBridge predicts R > 1 monotonically;
        # AL predicts R = 1.  Find where LSBridge first exceeds 1.5.
        for s in sigma_test:
            if R_lsbridge(s) > 1.5:
                out.append({
                    "xi_loc_um": xi,
                    "first_LSBridge_signal_below_threshold": s,
                    "interpretation": (
                        f"σ_0 ≈ {s:.2f} μm shows R > 1.5 for LSBridge "
                        f"but R = 1 for Anderson localization (ξ = {xi} μm).  "
                        "Measurement in this regime distinguishes the two."
                    ),
                })
                break
        else:
            out.append({
                "xi_loc_um": xi,
                "first_LSBridge_signal_below_threshold": None,
                "interpretation": (
                    f"Anderson localization (ξ = {xi}) threshold below the "
                    "LSBridge slowdown regime; both predict large R, "
                    "so discrimination requires fitting the full R(σ_0) curve."
                ),
            })
    return out


# =============================================================================
# 6.  Main.
# =============================================================================

def main():
    print("=" * 78)
    print("LSBridge vs experimental confounders — discrimination map")
    print("=" * 78)

    # Single-plot comparison.
    plot_path = plot_mechanisms(OUT_DIR / "mechanism_comparison.png")
    print(f"\nMechanism comparison plot:  {plot_path}")

    # Discrimination table.
    sigma_check = [1.0, 2.0, 3.0, 4.0, 5.0, 6.0, 7.0, 8.0, 10.0]
    rows = discrimination_ratios(sigma_check)
    print_discrimination_table(rows)

    # Uniquely-LSBridge σ_0 windows.
    print("\n" + "=" * 78)
    print("Uniquely-LSBridge σ_0 windows (σ_0 where R_LS exceeds every")
    print("confounder by ≥ 5× or ≥ 50×):")
    print("=" * 78)
    windows = find_unique_lsbridge_windows()
    print(f"\n  5× discrimination:  σ_0 ∈ "
          f"[{windows['5x_window_min_sigma']}, "
          f"{windows['5x_window_max_sigma']}] μm "
          f"(N = {len(windows['5x_above_all_confounders'])} sampled points)")
    print(f"  50× discrimination: σ_0 ∈ "
          f"[{windows['50x_window_min_sigma']}, "
          f"{windows['50x_window_max_sigma']}] μm "
          f"(N = {len(windows['50x_above_all_confounders'])} sampled points)")

    # Anderson-localization-specific discrimination.
    print("\n" + "=" * 78)
    print("Anderson localization vs LSBridge discrimination")
    print("=" * 78)
    al_data = AL_vs_lsbridge_discrimination()
    for entry in al_data:
        print(f"  ξ_loc = {entry['xi_loc_um']:.1f} μm: "
              f"{entry['interpretation']}")

    # Save full summary JSON.
    summary = {
        "mechanism_R_values": rows,
        "uniquely_lsbridge_windows": windows,
        "anderson_localization_discrimination": al_data,
        "plot": str(plot_path.relative_to(SCRIPT_DIR.parent)),
        "interpretation": (
            "LSBridge backreaction predicts a smooth exp(σ_0)/σ_0² growth "
            "in R(σ_0) starting from R(1) ≈ 1.77, while ALL plausible "
            "confounders give either R ≡ 1 (linear loss, NNN hopping), "
            "R < 1 (Kerr self-focusing), or a sharp threshold (Anderson "
            "localization).  Fitting the SHAPE of R(σ_0) — not just one "
            "data point — uniquely identifies LSBridge if the shape "
            "matches across multiple σ_0."
        ),
    }
    out_json = OUT_DIR / "confounder_summary.json"
    with out_json.open("w") as f:
        json.dump(summary, f, indent=2)
    print(f"\nFull JSON: {out_json}")


if __name__ == "__main__":
    main()
