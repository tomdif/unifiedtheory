"""
LSBridge experimental regimes / falsifiability map.

Maps the dimensionless LSBridge ODE  σ̇ = C · σ · exp(−σ)  to three
candidate experimental platforms, identifies the parameter regimes
where the predicted slowdown is large enough to be measurable, and
generates platform-specific width-vs-propagation curves.

Platforms (per user-supplied recommendation):
  1. Photonic waveguide / quantum-walk arrays
  2. Exciton-polariton propagation
  3. Quasi-1D ultracold atom (BEC) expansion

Observable to test:
    R(σ_0) := T_doubling,measured / T_doubling,free.

If LSBridge backreaction is real, R(σ_0) ≈ 1 near the crossover scale
σ_0 ~ 1 (in dimensionless units), and R(σ_0) → exp(σ_0)/σ_0² (huge)
for broad packets.

References:
  - Predictions encoded in scripts/lsbridge_predictions.py.
  - Bounds proved in UnifiedTheory.LayerB.LohmillerSlotineGaussianWidthDynamics.
"""

from __future__ import annotations

import json
import math
from pathlib import Path

import matplotlib.pyplot as plt
import numpy as np
from scipy.integrate import quad


SCRIPT_DIR = Path(__file__).resolve().parent
OUT_DIR = SCRIPT_DIR.parent / "results" / "lsbridge_predictions" / "experimental_regimes"
OUT_DIR.mkdir(parents=True, exist_ok=True)


# =============================================================================
# 1.  The two doubling times.
# =============================================================================

def lsbridge_doubling_time_dimless(sigma_0: float, C: float = 1.0) -> float:
    """T_LS = ∫_{σ_0}^{2σ_0} (e^σ / (C·σ)) dσ.   Dimensionless."""
    return quad(lambda s: math.exp(s) / (C * s), sigma_0, 2.0 * sigma_0)[0]


def free_schrodinger_doubling_time_dimless(sigma_0: float) -> float:
    """In free-Schrödinger natural units (ℏ/m = 1):  t_double = √3 · σ_0²."""
    return math.sqrt(3.0) * sigma_0**2


def observable_R(sigma_0: float, C: float = 1.0) -> float:
    """The proposed dimensionless observable:  R(σ_0) = T_LS / T_free."""
    return lsbridge_doubling_time_dimless(sigma_0, C) / \
        free_schrodinger_doubling_time_dimless(sigma_0)


# =============================================================================
# 2.  Platform parameter database.
# =============================================================================
#
# All platforms admit the SAME dimensionless ODE after rescaling.
# The translation from dimensionless σ to physical wavepacket width
# involves a platform-specific natural length scale ℓ.  The translation
# from dimensionless t to physical time involves a platform-specific
# spreading-rate constant Γ = ℏ/(m_eff · ℓ²) (or analog).
# =============================================================================

PLATFORMS = {
    "photonic_waveguide_array": {
        "label": "Photonic waveguide array (e.g., femtosecond-laser-written glass)",
        "spatial_units": "μm",
        "time_units": "mm (propagation distance z)",
        # Typical parameters for 1D coupled waveguide arrays:
        "lattice_spacing_a_um": 15.0,
        "hopping_t_per_mm": 1.0,
        # Effective diffraction coefficient D = t·a²  (units: μm²/mm).
        # In free-particle analog,  D plays the role of ℏ/m.
        "diffraction_coef_D_um2_per_mm": 15.0**2 * 1.0,
        # Probe scale & realistic initial widths:
        "ell_natural_um": 1.0,        # natural length unit (assumption)
        "sigma_0_range_um": [1.0, 5.0, 10.0, 25.0, 50.0, 100.0, 200.0],
        "max_propagation_mm": 200.0,   # typical array length
        "comment": (
            "Photonic waveguide arrays implement a discrete Schrödinger "
            "equation along the transverse coordinate as the beam propagates. "
            "Beam profile imaging allows direct measurement of σ(z). "
            "Broad initial Gaussians (σ_0 ~ 50-200 μm) are routine."
        ),
    },
    "exciton_polariton": {
        "label": "Exciton-polariton propagation (semiconductor microcavity)",
        "spatial_units": "μm",
        "time_units": "ps",
        # Polariton effective mass: ~ 10⁻⁴ × electron mass ≈ 9.1e-35 kg.
        "m_eff_kg": 9.1e-35,
        # hbar / m_eff for polaritons:  ~ ℏ/(10⁻⁴ m_e) ~ 10⁻⁴ · ℏ/m_e.
        # ℏ/m_e ≈ 1.16e-4 m²/s = 116 μm²/ns.
        # So ℏ/m_polariton ≈ 116 / 1e-4 = 1.16e6 μm²/ns = 1160 μm²/ps.
        "hbar_over_m_um2_per_ps": 1160.0,
        # Polariton lifetime is ~10-100 ps; observable window.
        "lifetime_ps": 30.0,
        # Polariton coherence length / spot size — typically a few μm.
        "ell_natural_um": 1.0,
        "sigma_0_range_um": [1.0, 2.0, 5.0, 10.0, 20.0, 50.0],
        "max_time_ps": 30.0,
        "comment": (
            "Polariton wavepackets propagate in engineered cavity potentials "
            "with very small effective mass (~ 10⁻⁴ m_e) and lifetimes "
            "~ 10-100 ps.  Direct space-time imaging is standard.  Broad "
            "initial spots σ_0 > 10 μm are accessible with shaped pumping."
        ),
    },
    "bec_expansion_1d": {
        "label": "Quasi-1D ⁸⁷Rb BEC expansion (after trap release)",
        "spatial_units": "μm",
        "time_units": "ms",
        # ⁸⁷Rb mass:
        "m_Rb87_kg": 1.443e-25,
        # ℏ/m_Rb87 in μm²/ms:
        # ℏ = 1.0546e-34 J·s, m = 1.443e-25 kg
        # ℏ/m = 7.31e-10 m²/s = 7.31e-10 × 10¹² μm²/s × 10⁻³ s/ms = 7.31e-1 μm²/ms ≈ 0.73 μm²/ms.
        "hbar_over_m_um2_per_ms": 0.73,
        # Typical initial BEC widths after release: ~ 1-100 μm.
        "ell_natural_um": 1.0,
        "sigma_0_range_um": [1.0, 2.0, 5.0, 10.0, 25.0, 50.0, 100.0],
        "max_time_ms": 100.0,
        "comment": (
            "BEC expansion in a quasi-1D geometry (after release from a "
            "highly anisotropic trap) directly tests free-particle spreading "
            "in the matter-wave regime.  Standard absorption imaging gives "
            "the cloud width vs time.  Caveat: residual interactions and "
            "trap-release imperfections need to be controlled."
        ),
    },
}


# =============================================================================
# 3.  Per-platform regime analysis.
# =============================================================================

def physical_doubling_times(platform_key: str, sigma_0_um_list,
                            assume_C_natural: float = 1.0):
    """
    For a given platform, compute LSBridge and free doubling times.

    The LSBridge dimensionless σ is taken to be σ_phys / ℓ_natural,
    where ℓ_natural is a platform-specific length scale (the "lattice"
    of the underlying LSBridge substrate, an unknown to be fit).

    Free Schrödinger time scale:  T_free = √3 · σ_0² / (ℏ/m_eff)
        for matter, OR  T_free = √3 · σ_0² / D  for photonic D.
    """
    p = PLATFORMS[platform_key]
    ell = p["ell_natural_um"]

    if platform_key == "photonic_waveguide_array":
        D = p["diffraction_coef_D_um2_per_mm"]   # μm²/mm
        # T_free in mm units.
        def T_free_phys(sigma_um):
            return math.sqrt(3.0) * sigma_um**2 / D
    elif platform_key == "exciton_polariton":
        hbar_m = p["hbar_over_m_um2_per_ps"]
        def T_free_phys(sigma_um):
            return math.sqrt(3.0) * sigma_um**2 / hbar_m
    elif platform_key == "bec_expansion_1d":
        hbar_m = p["hbar_over_m_um2_per_ms"]
        def T_free_phys(sigma_um):
            return math.sqrt(3.0) * sigma_um**2 / hbar_m
    else:
        raise ValueError(f"Unknown platform {platform_key}")

    rows = []
    for sigma_um in sigma_0_um_list:
        sigma_dimless = sigma_um / ell
        T_LS_dimless = lsbridge_doubling_time_dimless(sigma_dimless,
                                                       C=assume_C_natural)
        T_free_dimless = free_schrodinger_doubling_time_dimless(sigma_dimless)
        # In physical units, the rescaling factor is the same on both sides
        # of the ratio, so R(σ_0) is identical to the dimensionless ratio.
        R = T_LS_dimless / T_free_dimless

        T_free_phys_val = T_free_phys(sigma_um)
        # LSBridge physical time inherits the same prefactor (since both
        # ODEs use the same time-rescaling on the platform side):
        T_LS_phys_val = T_free_phys_val * R

        rows.append({
            "sigma_0_um": sigma_um,
            "sigma_0_dimless": sigma_dimless,
            "T_free_phys": T_free_phys_val,
            "T_LS_phys": T_LS_phys_val,
            "R_observable": R,
            "T_LS_lower_bound_dimless": math.exp(sigma_dimless) / (2.0 * assume_C_natural),
            "T_LS_upper_bound_dimless": math.exp(2.0 * sigma_dimless) / assume_C_natural,
        })
    return rows


def regime_thresholds(rows, R_thresholds=(2.0, 5.0, 10.0, 100.0, 1000.0)):
    """For each R threshold, find the minimum σ_0 reaching that ratio."""
    out = {}
    for thr in R_thresholds:
        min_sigma = None
        for r in rows:
            if r["R_observable"] >= thr:
                min_sigma = r["sigma_0_um"]
                break
        out[f"R≥{thr}"] = min_sigma
    return out


# =============================================================================
# 4.  Plots.
# =============================================================================

def plot_platform_doubling_times(platform_key, rows, out_path):
    p = PLATFORMS[platform_key]
    sigmas = [r["sigma_0_um"] for r in rows]
    T_LS = [r["T_LS_phys"] for r in rows]
    T_free = [r["T_free_phys"] for r in rows]

    fig, axes = plt.subplots(1, 2, figsize=(13, 5))

    axes[0].loglog(sigmas, T_free, "b-o", label="Free Schrödinger (standard)")
    axes[0].loglog(sigmas, T_LS, "r-s", label="LSBridge backreaction")
    axes[0].set_xlabel(f"Initial width σ_0 ({p['spatial_units']})")
    axes[0].set_ylabel(f"Doubling time ({p['time_units']})")
    axes[0].set_title(f"{p['label']}\nDoubling time vs initial width")
    axes[0].legend()
    axes[0].grid(True, which="both", alpha=0.3)

    R = [r["R_observable"] for r in rows]
    axes[1].loglog(sigmas, R, "g-^", linewidth=2)
    axes[1].axhline(1.0, color="k", linestyle="--", alpha=0.4)
    for thr in [5.0, 10.0, 100.0]:
        axes[1].axhline(thr, color="orange", linestyle=":", alpha=0.4,
                        label=f"R = {thr}×" if thr == 5.0 else None)
    axes[1].set_xlabel(f"Initial width σ_0 ({p['spatial_units']})")
    axes[1].set_ylabel("R(σ_0) = T_LS / T_free")
    axes[1].set_title("Predicted doubling-time slowdown ratio")
    axes[1].legend()
    axes[1].grid(True, which="both", alpha=0.3)

    fig.tight_layout()
    fig.savefig(out_path, dpi=150)
    plt.close(fig)
    return out_path


def plot_observable_R_universal(out_path):
    """The universal R(σ_0) curve — same shape on every platform, since
    the rescaling factors cancel."""
    sigmas = np.linspace(0.1, 12.0, 200)
    R_values = np.array([observable_R(s, C=1.0) for s in sigmas])

    fig, ax = plt.subplots(figsize=(10, 6))
    ax.semilogy(sigmas, R_values, "b-", linewidth=2,
                label="R(σ_0) = T_LS / T_free (numerical)")
    # Proved bounds:
    R_lower = np.array([math.exp(s) / (2.0 * math.sqrt(3.0) * s**2) for s in sigmas])
    R_upper = np.array([math.exp(2.0 * s) / (math.sqrt(3.0) * s**2) for s in sigmas])
    ax.semilogy(sigmas, R_lower, "g--", alpha=0.6,
                label="Lower bound: exp(σ₀)/(2·√3·σ₀²)")
    ax.semilogy(sigmas, R_upper, "r--", alpha=0.6,
                label="Upper bound: exp(2σ₀)/(√3·σ₀²)")
    ax.axhline(1.0, color="k", linestyle="--", alpha=0.5, label="R = 1 (parity)")
    ax.axhline(5.0, color="orange", linestyle=":", alpha=0.6)
    ax.axhline(10.0, color="orange", linestyle=":", alpha=0.6)
    ax.axhline(100.0, color="orange", linestyle=":", alpha=0.6)
    ax.set_xlabel("σ_0 (dimensionless LSBridge initial width)")
    ax.set_ylabel("R(σ_0) = T_LS / T_free   (log scale)")
    ax.set_title("LSBridge universal observable — slowdown ratio vs initial width")
    ax.grid(True, which="both", alpha=0.3)
    ax.legend(loc="upper left")
    fig.tight_layout()
    fig.savefig(out_path, dpi=150)
    plt.close(fig)
    return out_path


# =============================================================================
# 5.  Main.
# =============================================================================

def main():
    summary = {"platforms": {}, "universal_R_curve_data": None}

    for key in PLATFORMS:
        p = PLATFORMS[key]
        rows = physical_doubling_times(key, p["sigma_0_range_um"])
        thresholds = regime_thresholds(rows)
        plot_path = OUT_DIR / f"{key}_regimes.png"
        plot_platform_doubling_times(key, rows, plot_path)
        summary["platforms"][key] = {
            "label": p["label"],
            "comment": p["comment"],
            "spatial_units": p["spatial_units"],
            "time_units": p["time_units"],
            "ell_natural_um": p["ell_natural_um"],
            "rows": rows,
            "minimum_sigma_for_R_threshold_um": thresholds,
            "plot": str(plot_path.relative_to(SCRIPT_DIR.parent)),
        }

    universal_plot = OUT_DIR / "universal_R_curve.png"
    plot_observable_R_universal(universal_plot)
    summary["universal_R_curve_data"] = {
        "plot": str(universal_plot.relative_to(SCRIPT_DIR.parent)),
        "description": (
            "R(σ_0) is universal across platforms because the platform "
            "rescaling factors cancel in the ratio T_LS/T_free.  Only "
            "the natural length scale ℓ (which sets dimensionless σ = "
            "σ_phys/ℓ) is platform-dependent."
        ),
    }

    summary_path = OUT_DIR / "experimental_regimes_summary.json"
    with summary_path.open("w") as f:
        json.dump(summary, f, indent=2)

    # Console summary.
    print("=" * 90)
    print("LSBridge experimental regimes — falsifiability map")
    print("=" * 90)
    print()
    print("Universal observable:  R(σ_0) = T_doubling,measured / T_doubling,free")
    print()
    print("Predicted (proved bounds + numerical):")
    sigma_check_points = [0.5, 1.0, 2.0, 5.0, 10.0]
    for s in sigma_check_points:
        R = observable_R(s)
        print(f"  σ_0 = {s:>5.1f}  ⇒  R = {R:>10.4e}    "
              f"(bounds [{math.exp(s)/(2*math.sqrt(3)*s**2):.2e}, "
              f"{math.exp(2*s)/(math.sqrt(3)*s**2):.2e}])")
    print()

    for key in PLATFORMS:
        p = PLATFORMS[key]
        platform_summary = summary["platforms"][key]
        print(f"[{key}]  {p['label']}")
        print(f"  Natural length ℓ = {p['ell_natural_um']} {p['spatial_units']}")
        print(f"  Per-row table (σ_0, σ_dimless, T_free, T_LS, R):")
        print(f"  {'σ_0':>10}  {'σ_dim':>8}  {'T_free':>12}  "
              f"{'T_LS':>12}  {'R':>12}")
        for r in platform_summary["rows"]:
            unit_s = p["spatial_units"]
            unit_t = p["time_units"]
            print(f"  {r['sigma_0_um']:>6.1f} {unit_s:>3}  "
                  f"{r['sigma_0_dimless']:>8.2f}  "
                  f"{r['T_free_phys']:>9.3e} {unit_t:>2}  "
                  f"{r['T_LS_phys']:>9.3e} {unit_t:>2}  "
                  f"{r['R_observable']:>12.4e}")
        print(f"  Regime thresholds (minimum σ_0 to reach R≥):")
        for thr_label, thr_val in platform_summary["minimum_sigma_for_R_threshold_um"].items():
            print(f"    {thr_label:>10}:  σ_0 ≥ {thr_val} {p['spatial_units']}"
                  if thr_val else f"    {thr_label:>10}:  not reachable in test range")
        print()

    print(f"All plots:   {OUT_DIR}")
    print(f"Summary JSON: {summary_path}")


if __name__ == "__main__":
    main()
