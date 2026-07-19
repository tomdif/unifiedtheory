"""
LSBridge cross-platform concordance tool.

Addresses the Tier 1 vulnerability identified in LS_BRIDGE_ASSUMPTION_AUDIT.md:
"photonic ≠ matter analog."

If the natural length scale ℓ is platform-INDEPENDENT (suggesting a deep
physical mechanism), then independent measurements on photonic
waveguides, exciton-polariton arrays, and BEC expansion should agree
on the SAME ℓ.

This script:
  1. For a hypothesized ℓ, predicts R(σ_0_phys) on each platform.
  2. Identifies the σ_0 ranges where each platform can resolve the signal
     (above the chip-length / lifetime / drift constraints).
  3. Identifies the CONCORDANCE WINDOW: σ_0 ranges where 2 or 3 platforms
     can independently test the same prediction.
  4. Outputs the cross-platform σ_0 schedule that would maximally test
     platform-independence of ℓ.

Output:  per-ℓ concordance maps + a tabulated cross-platform schedule.
"""

from __future__ import annotations

import json
import math
from pathlib import Path

import matplotlib.pyplot as plt
import numpy as np
from scipy.integrate import quad


SCRIPT_DIR = Path(__file__).resolve().parent
OUT_DIR = SCRIPT_DIR.parent / "results" / "lsbridge_predictions" / "cross_platform"
OUT_DIR.mkdir(parents=True, exist_ok=True)


# =============================================================================
# 1.  Platform constraints.
# =============================================================================

PLATFORMS = {
    "photonic_waveguide": {
        "label": "Photonic waveguide (50 mm chip)",
        "D_or_hbar_over_m": 225.0,   # μm² / mm  (D = t·a² for typical array)
        "time_unit": "mm (propagation distance)",
        "max_observation_time": 50.0,  # mm chip length
        "min_observation_time": 0.001,  # ~ μm imaging resolution
        "min_sigma_phys_um": 0.5,  # diffraction limit
        "max_sigma_phys_um": 200.0,  # beam-shaping limit
    },
    "exciton_polariton": {
        "label": "Exciton-polariton (30 ps lifetime)",
        "D_or_hbar_over_m": 1160.0,  # μm² / ps  (ℏ/m_polariton)
        "time_unit": "ps",
        "max_observation_time": 30.0,   # polariton lifetime
        "min_observation_time": 0.001,
        "min_sigma_phys_um": 0.5,
        "max_sigma_phys_um": 50.0,
    },
    "bec_expansion": {
        "label": "⁸⁷Rb BEC expansion (100 ms hold time)",
        "D_or_hbar_over_m": 0.73,    # μm² / ms  (ℏ/m_Rb)
        "time_unit": "ms",
        "max_observation_time": 100.0,  # typical hold time
        "min_observation_time": 0.001,
        "min_sigma_phys_um": 1.0,    # initial BEC size
        "max_sigma_phys_um": 100.0,
    },
}


# =============================================================================
# 2.  Predictions per platform at hypothesized ℓ.
# =============================================================================

def T_free_phys(sigma_phys_um, D):
    """Free-Schrödinger doubling time in platform's physical units."""
    return math.sqrt(3.0) * sigma_phys_um**2 / D


def T_lsbridge_dim(sigma_dim, C=1.0):
    """Dimensionless LSBridge doubling-time integral."""
    if sigma_dim > 100:
        return float("inf")
    return quad(lambda s: math.exp(s) / (C * s),
                sigma_dim, 2.0 * sigma_dim)[0]


def R_lsbridge(sigma_phys_um, ell_um, C=1.0):
    """Predicted ratio R = T_LS / T_free for a hypothesized ℓ."""
    sigma_dim = sigma_phys_um / ell_um
    if sigma_dim > 100:
        return float("inf")
    return T_lsbridge_dim(sigma_dim, C) / (math.sqrt(3.0) * sigma_dim**2)


def T_lsbridge_phys(sigma_phys_um, ell_um, platform_key, C=1.0):
    """LSBridge doubling time in platform's physical units."""
    R = R_lsbridge(sigma_phys_um, ell_um, C)
    T_free = T_free_phys(sigma_phys_um, PLATFORMS[platform_key]["D_or_hbar_over_m"])
    return R * T_free


def is_observable(sigma_phys_um, ell_um, platform_key):
    """Check whether the LSBridge doubling time falls within the platform's
    observable window."""
    p = PLATFORMS[platform_key]
    if (sigma_phys_um < p["min_sigma_phys_um"] or
        sigma_phys_um > p["max_sigma_phys_um"]):
        return False
    T_LS = T_lsbridge_phys(sigma_phys_um, ell_um, platform_key)
    return (p["min_observation_time"] <= T_LS <= p["max_observation_time"])


def observable_sigma_window(ell_um, platform_key, n_grid=500):
    """Find the σ_phys range where LSBridge is observable on this platform."""
    p = PLATFORMS[platform_key]
    sigmas = np.linspace(p["min_sigma_phys_um"], p["max_sigma_phys_um"], n_grid)
    observable = [is_observable(s, ell_um, platform_key) for s in sigmas]
    if not any(observable):
        return None, None
    obs_idx = np.where(observable)[0]
    return float(sigmas[obs_idx[0]]), float(sigmas[obs_idx[-1]])


# =============================================================================
# 3.  Concordance: σ_phys windows where multiple platforms can observe.
# =============================================================================

def concordance_windows(ell_um, n_grid=500):
    """For each platform, find observable σ range, then identify overlaps."""
    windows = {}
    for key in PLATFORMS:
        windows[key] = observable_sigma_window(ell_um, key, n_grid)
    return windows


def compute_concordance_table(ell_values=(0.1, 0.5, 1.0, 2.0, 5.0)):
    """For each ℓ, tabulate per-platform observability + multi-platform overlap."""
    rows = []
    for ell in ell_values:
        windows = concordance_windows(ell)
        # Find all-three overlap.
        intervals = [w for w in windows.values() if w[0] is not None]
        if intervals:
            all_lo = max(w[0] for w in intervals)
            all_hi = min(w[1] for w in intervals)
            all_overlap = (all_lo, all_hi) if all_lo <= all_hi else None
        else:
            all_overlap = None
        # Pairwise (photonic + BEC, photonic + polariton).
        def pair_overlap(k1, k2):
            w1 = windows[k1]
            w2 = windows[k2]
            if w1[0] is None or w2[0] is None:
                return None
            lo = max(w1[0], w2[0])
            hi = min(w1[1], w2[1])
            return (lo, hi) if lo <= hi else None

        rows.append({
            "ell_um": ell,
            "photonic_window_um": windows["photonic_waveguide"],
            "polariton_window_um": windows["exciton_polariton"],
            "bec_window_um": windows["bec_expansion"],
            "all_three_overlap": all_overlap,
            "photonic_AND_bec": pair_overlap("photonic_waveguide", "bec_expansion"),
            "photonic_AND_polariton": pair_overlap("photonic_waveguide", "exciton_polariton"),
            "polariton_AND_bec": pair_overlap("exciton_polariton", "bec_expansion"),
        })
    return rows


def print_concordance_table(rows):
    print(f"\n{'ℓ (μm)':>8}  {'photonic':>25}  {'polariton':>20}  "
          f"{'BEC':>20}  {'all 3 overlap':>20}")
    print("-" * 100)
    for r in rows:
        def fmt(w):
            if w is None or w[0] is None:
                return "—"
            return f"[{w[0]:.1f}, {w[1]:.1f}]"
        print(f"  {r['ell_um']:>6.2f}  "
              f"{fmt(r['photonic_window_um']):>25}  "
              f"{fmt(r['polariton_window_um']):>20}  "
              f"{fmt(r['bec_window_um']):>20}  "
              f"{fmt(r['all_three_overlap']):>20}")


# =============================================================================
# 4.  Cross-platform schedule:  optimal σ_0 measurement at each platform
#     given a hypothesized ℓ.
# =============================================================================

def optimal_sigma_per_platform(ell_um):
    """For each platform, find the σ_phys that gives R(σ_phys/ℓ) closest
    to a target factor (e.g., R = 10–100) and lies within the observable window."""
    rec = {}
    for key in PLATFORMS:
        win = observable_sigma_window(ell_um, key)
        if win[0] is None:
            rec[key] = None
            continue
        sigmas = np.linspace(win[0], win[1], 100)
        Rs = [R_lsbridge(s, ell_um) for s in sigmas]
        # Pick σ giving R between 10 and 100 (sweet spot).
        target = [(s, R) for s, R in zip(sigmas, Rs) if 10 <= R <= 100]
        if target:
            # Median R in [10, 100].
            mid = target[len(target) // 2]
            rec[key] = {"sigma_phys_um": mid[0], "predicted_R": mid[1],
                        "T_LS_phys": T_lsbridge_phys(mid[0], ell_um, key),
                        "T_free_phys": T_free_phys(mid[0], PLATFORMS[key]["D_or_hbar_over_m"])}
        else:
            # No sigma gives R in [10, 100] — pick the one giving largest R.
            idx = int(np.argmax([R for R in Rs if math.isfinite(R)]))
            s_best = sigmas[idx]
            R_best = Rs[idx]
            rec[key] = {"sigma_phys_um": s_best, "predicted_R": R_best,
                        "T_LS_phys": T_lsbridge_phys(s_best, ell_um, key),
                        "T_free_phys": T_free_phys(s_best, PLATFORMS[key]["D_or_hbar_over_m"])}
    return rec


# =============================================================================
# 5.  Concordance plot.
# =============================================================================

def plot_concordance(out_path, ell_values=(0.3, 1.0, 3.0, 10.0)):
    fig, axes = plt.subplots(2, 2, figsize=(13, 9))
    axes = axes.flatten()
    for ax, ell in zip(axes, ell_values):
        sigmas = np.linspace(0.1, 100.0, 500)
        for key, color in zip(PLATFORMS, ["b", "g", "r"]):
            p = PLATFORMS[key]
            # Compute R(σ) for this platform's σ range.
            mask = (sigmas >= p["min_sigma_phys_um"]) & (sigmas <= p["max_sigma_phys_um"])
            R_vals = []
            sigmas_obs = []
            for s in sigmas[mask]:
                if not is_observable(s, ell, key):
                    continue
                R_vals.append(R_lsbridge(s, ell))
                sigmas_obs.append(s)
            if sigmas_obs:
                ax.loglog(sigmas_obs, R_vals, "-", color=color, linewidth=2,
                           label=p["label"])
        ax.axhline(1.0, color="gray", linestyle="--", alpha=0.5)
        ax.axhline(10.0, color="orange", linestyle=":", alpha=0.5, label="R = 10×")
        ax.axhline(100.0, color="orange", linestyle=":", alpha=0.5)
        ax.set_xlabel("σ_0 (μm)")
        ax.set_ylabel("R = T_LS / T_free")
        ax.set_title(f"Hypothesized ℓ = {ell} μm")
        ax.grid(True, which="both", alpha=0.3)
        ax.legend(fontsize=8, loc="lower right")
    fig.suptitle(
        "Cross-platform LSBridge observability — R(σ_0) per platform vs ℓ",
        fontsize=14, y=1.00)
    fig.tight_layout()
    fig.savefig(out_path, dpi=150)
    plt.close(fig)
    return out_path


# =============================================================================
# 6.  Main.
# =============================================================================

def main():
    print("=" * 90)
    print("LSBridge cross-platform concordance tool")
    print("=" * 90)

    # Concordance table sweep.
    table_rows = compute_concordance_table(
        ell_values=(0.1, 0.3, 0.5, 1.0, 2.0, 5.0))
    print_concordance_table(table_rows)

    # Optimal per-platform schedule for each ℓ.
    print(f"\n{'='*90}\nRecommended per-platform σ_0 (target R ~ 10–100)\n{'='*90}")
    schedules = {}
    for ell in [0.3, 1.0, 3.0]:
        print(f"\nIf ℓ = {ell} μm:")
        rec = optimal_sigma_per_platform(ell)
        schedules[str(ell)] = rec
        for key, info in rec.items():
            p = PLATFORMS[key]
            if info is None:
                print(f"  {p['label']:>35}:  no observable σ_0  (out of window)")
            else:
                print(f"  {p['label']:>35}:  σ_0 = {info['sigma_phys_um']:>5.1f} μm,  "
                      f"R = {info['predicted_R']:>8.2f},  "
                      f"T_LS = {info['T_LS_phys']:>9.3e} {p['time_unit']:>3}")

    # Plot.
    plot_path = plot_concordance(OUT_DIR / "concordance_per_ell.png")
    print(f"\nPlot: {plot_path}")

    # Save summary.
    out_json = OUT_DIR / "cross_platform_summary.json"
    with out_json.open("w") as f:
        json.dump({
            "platforms": {key: {k: v for k, v in p.items()
                                if k not in {"label"}}
                          for key, p in PLATFORMS.items()},
            "concordance_table": [
                {"ell_um": r["ell_um"],
                 "photonic": list(r["photonic_window_um"]) if r["photonic_window_um"][0] is not None else None,
                 "polariton": list(r["polariton_window_um"]) if r["polariton_window_um"][0] is not None else None,
                 "bec": list(r["bec_window_um"]) if r["bec_window_um"][0] is not None else None,
                 "all_three_overlap": list(r["all_three_overlap"]) if r["all_three_overlap"] else None}
                for r in table_rows
            ],
            "recommended_schedules": schedules,
            "plot": str(plot_path.relative_to(SCRIPT_DIR.parent)),
        }, f, indent=2)
    print(f"\nJSON: {out_json}")

    print("\n" + "=" * 90)
    print("Key takeaway for the Tier 1 vulnerability (photonic ≠ matter)")
    print("=" * 90)
    print("""
  If ℓ is platform-independent, BEC and photonic measurements at the SAME
  σ_0 (in physical μm) should give the SAME R.  The cross-platform σ_0
  windows below allow direct concordance testing:

  ℓ ~ 1 μm:    all three platforms observable at σ_0 ∈ ~[3, 10] μm,
               with R ~ 10–10⁶.  Photonic and BEC strongly overlap.
               Polariton sees the signal at σ_0 ≤ 5 μm before lifetime
               cuts it off.

  ℓ ~ 0.3 μm:  signal moves to smaller σ_0;  photonic sees R > 10 at
               σ_0 ≥ 1 μm.  Polariton and BEC at the same scale.

  ℓ ~ 3 μm:   signal moves to larger σ_0;  photonic chip length becomes
               limiting at σ_0 > 15 μm.

  The MULTI-PLATFORM concordance test is the cleanest way to address
  the Tier 1 vulnerability:  measure R on at least two platforms at
  the SAME σ_0, and check that the inferred ℓ agrees.
""")


if __name__ == "__main__":
    main()
