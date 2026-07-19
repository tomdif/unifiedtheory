"""
Phase 2 — σ_0 sweep at fixed (τ, N).

Tests whether the Gaussian/sech mode discrimination is stronger at narrow σ_0,
where the sech source term 1/ξ² is larger.

Reuses run_pde() from lsbridge_phase2_pde_shape_fidelity.py.
"""

from __future__ import annotations

import json
import math
import sys
import time
from pathlib import Path

import matplotlib.pyplot as plt
import numpy as np

SCRIPT_DIR = Path(__file__).resolve().parent
sys.path.insert(0, str(SCRIPT_DIR))
from lsbridge_phase2_pde_shape_fidelity import run_pde   # noqa: E402

OUT_DIR = SCRIPT_DIR.parent / "results" / "lsbridge_predictions" / "phase2_pde_shape_fidelity"
OUT_DIR.mkdir(parents=True, exist_ok=True)


def free_schrodinger_sigma(t, sigma_0):
    """σ²(t) = σ_0² · (1 + (t/(2σ_0²))²), ℏ = m = 1."""
    return sigma_0 * math.sqrt(1.0 + (t / (2.0 * sigma_0**2))**2)


def reduced_gaussian_sigma_ode(t, sigma_0, C=1.0):
    """σ̇ = C·σ·exp(−σ), ICσ(0) = σ_0.  Return σ(t) at the requested t."""
    from scipy.integrate import solve_ivp
    sol = solve_ivp(lambda tt, s: [C * s[0] * math.exp(-s[0])],
                    (0.0, t), [sigma_0], rtol=1e-10, atol=1e-12)
    return float(sol.y[0][-1])


def reduced_sech_curved_sigma(t, sigma_0):
    """Solve sech ODE  ξ·ξ_pp + ξ_p²·(ξ−1) = 1/ξ  from (ξ_0=σ_0·√12/π, ξ_p(0)=0).
       Return σ_sech(t) = ξ(t)·π/√12."""
    from scipy.integrate import solve_ivp
    xi_0 = sigma_0 * math.sqrt(12.0) / math.pi
    def rhs(tt, y):
        xi, xip = y
        if xi <= 0:
            return [0.0, 0.0]
        xi_pp = 1.0 / xi**2 - xip**2 * (xi - 1.0) / xi
        return [xip, xi_pp]
    sol = solve_ivp(rhs, (0.0, t), [xi_0, 0.0], rtol=1e-10, atol=1e-12)
    xi_t = float(sol.y[0][-1])
    return xi_t * math.pi / math.sqrt(12.0)


def main():
    sigma_0_list = [0.3, 0.5, 0.7, 1.0, 1.5, 2.0]
    tau_rel  = 0.05
    N        = 2048
    L        = 80.0
    t_max    = 1.0
    dt_cap   = 5e-4
    sample_dt = 0.1
    aperture_W = 2.0

    print("=" * 84)
    print(f"Phase 2 σ_0 sweep at τ_rel={tau_rel}, N={N}, t_max={t_max}")
    print("=" * 84)
    print(f"  σ_0 ∈ {sigma_0_list}")
    print()

    rows = []
    for s0 in sigma_0_list:
        for ic in ["gaussian", "sech"]:
            t0 = time.time()
            print(f"  σ_0={s0:>4.2f}  IC={ic:<8} ...", end="", flush=True)
            r = run_pde(ic_kind=ic, sigma_0=s0, tau_rel=tau_rel,
                        N=N, L=L, t_max=t_max, dt_cap=dt_cap,
                        sample_dt=sample_dt, aperture_W=aperture_W)
            elapsed = time.time() - t0
            tag = " BLOWUP" if r["blowup"] else ""
            print(f"  {elapsed:5.1f}s  σ_init={r['sigma'][0]:.3f}  "
                  f"σ_end={r['sigma'][-1]:.3f}  "
                  f"F={r['F_G'][-1] if ic == 'gaussian' else r['F_S'][-1]:.3f}  "
                  f"normdrift={abs(r['norm'][-1]/r['norm'][0]-1):.2e}{tag}")
            rows.append(r)

    # Compare PDE vs reduced ODE vs free Schrödinger.
    print()
    print(f"{'σ_0':>6}  {'PDE σ_G':>9}  {'PDE σ_S':>9}  {'σ_S/σ_G':>9}  "
          f"{'free σ':>8}  {'red.ODE σ_G':>13}  {'red.ODE σ_S':>13}  "
          f"{'red ratio':>10}")
    print("-" * 100)
    summary_rows = []
    for s0 in sigma_0_list:
        rG = next(r for r in rows if r["sigma_0"] == s0 and r["ic"] == "gaussian")
        rS = next(r for r in rows if r["sigma_0"] == s0 and r["ic"] == "sech")
        # Use the LAST sample for both (they were both run to t_max=1.0).
        sG_end = float(rG["sigma"][-1])
        sS_end = float(rS["sigma"][-1])
        pde_ratio = sS_end / max(sG_end, 1e-12)
        s_free = free_schrodinger_sigma(rG["t_reached"], s0)
        s_red_G = reduced_gaussian_sigma_ode(rG["t_reached"], s0, C=1.0)
        s_red_S = reduced_sech_curved_sigma(rG["t_reached"], s0)
        red_ratio = s_red_S / max(s_red_G, 1e-12)
        summary_rows.append({
            "sigma_0": s0,
            "t":       rG["t_reached"],
            "pde_sigma_G": sG_end,
            "pde_sigma_S": sS_end,
            "pde_ratio_S_over_G": pde_ratio,
            "free_sigma": s_free,
            "reduced_ode_sigma_G_with_C1": s_red_G,
            "reduced_ode_sigma_S": s_red_S,
            "reduced_ratio_S_over_G": red_ratio,
            "norm_drift_G": abs(rG["norm"][-1]/rG["norm"][0]-1),
            "norm_drift_S": abs(rS["norm"][-1]/rS["norm"][0]-1),
            "F_G_end": float(rG["F_G"][-1]),
            "F_S_end": float(rS["F_S"][-1]),
        })
        print(f"{s0:>6.2f}  {sG_end:>9.4f}  {sS_end:>9.4f}  "
              f"{pde_ratio:>9.4f}  {s_free:>8.4f}  "
              f"{s_red_G:>13.4f}  {s_red_S:>13.4f}  {red_ratio:>10.4f}")

    # Plot.
    fig, axes = plt.subplots(1, 2, figsize=(13, 5))
    s0arr = np.array([r["sigma_0"] for r in summary_rows])

    axes[0].plot(s0arr, [r["pde_ratio_S_over_G"] for r in summary_rows], "ro-",
                  label="PDE σ_S/σ_G",   linewidth=2, markersize=8)
    axes[0].plot(s0arr, [r["reduced_ratio_S_over_G"] for r in summary_rows], "b--",
                  label="reduced-ODE σ_S/σ_G", linewidth=2)
    axes[0].axhline(1.0,  color="grey", linestyle=":", label="no discrimination")
    axes[0].axhline(1.10, color="green", linestyle=":", label="pass threshold (1.10)")
    axes[0].set_xlabel("initial σ_0")
    axes[0].set_ylabel("σ_S / σ_G   at  t = 1.0")
    axes[0].set_title(f"Mode discrimination vs σ_0  (τ_rel = {tau_rel})")
    axes[0].grid(True, alpha=0.3)
    axes[0].legend()
    axes[0].set_xscale("log")

    axes[1].plot(s0arr, [r["pde_sigma_G"] for r in summary_rows],     "bo-",
                  label="PDE Gaussian σ", linewidth=2)
    axes[1].plot(s0arr, [r["pde_sigma_S"] for r in summary_rows],     "ro-",
                  label="PDE sech σ",     linewidth=2)
    axes[1].plot(s0arr, [r["free_sigma"] for r in summary_rows],      "k--",
                  label="free σ_free(t=1)", linewidth=1.5)
    axes[1].plot(s0arr, [r["reduced_ode_sigma_G_with_C1"] for r in summary_rows], "b:",
                  label="reduced ODE Gauss (C=1)", linewidth=1.5)
    axes[1].plot(s0arr, [r["reduced_ode_sigma_S"] for r in summary_rows], "r:",
                  label="reduced ODE sech", linewidth=1.5)
    axes[1].plot(s0arr, s0arr,                                                  "grey",
                  linestyle="-.", linewidth=1, label="identity (no spreading)")
    axes[1].set_xlabel("initial σ_0")
    axes[1].set_ylabel("σ(t=1.0)")
    axes[1].set_title(f"Width at t=1 vs σ_0  (τ_rel = {tau_rel})")
    axes[1].grid(True, alpha=0.3)
    axes[1].legend(fontsize=8)
    axes[1].set_xscale("log")
    axes[1].set_yscale("log")

    fig.tight_layout()
    plot_path = OUT_DIR / f"sigma0_sweep_tau{tau_rel:.3f}.png"
    fig.savefig(plot_path, dpi=150)
    plt.close(fig)
    print()
    print(f"Plot: {plot_path}")

    # JSON.
    out = {
        "tau_rel": tau_rel,
        "N": N,
        "t_max": t_max,
        "sigma_0_list": sigma_0_list,
        "summary": summary_rows,
    }
    json_path = OUT_DIR / f"sigma0_sweep_tau{tau_rel:.3f}.json"
    with json_path.open("w") as f:
        json.dump(out, f, indent=2)
    print(f"JSON: {json_path}")


if __name__ == "__main__":
    main()
