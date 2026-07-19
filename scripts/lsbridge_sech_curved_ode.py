"""
Phase 1 — sech-curved width-ODE reproducer (Lean-derived, NOT heuristic).

Replaces the retracted heuristic ODE from `lsbridge_sech_width_dynamics.py`
with the actual Lean-derived sech-curved width ODE proved in
UnifiedTheory/LayerB/LohmillerSlotineBackreaction.lean Part 17:

    ξ·ξ_pp + ξ_prime²·(ξ − 1) = ℏ²/(m²·ξ)               (sech, Lean Part 17)

For comparison, the Gaussian-curved ODE shares the same structural LHS
but with ZERO source term:

    σ·σ_pp + σ_prime²·(σ − 1) = 0                        (Gaussian, Lean Part 12)

Setting ℏ = m = 1 (these set the natural scale and are absorbed into ℓ),
the sech ODE becomes ξ·ξ_pp + ξ_prime²·(ξ − 1) = 1/ξ.

In state-space form with y = (ξ, ξ_prime):
    sech:      y[0]' = y[1],  y[1]' = 1/y[0]² − y[1]²·(y[0]−1)/y[0]
    Gaussian:  y[0]' = y[1],  y[1]' =      0  − y[1]²·(y[0]−1)/y[0]

Numerical witnesses of the proved theorems:
  (a) sech_curved_rejects_frozen:  initialize ξ_prime(0) = 0; sech
      acceleration is 1/ξ² ≠ 0 (frozen forbidden), Gaussian acceleration
      is 0 (frozen admissible).
  (b) sech_curved_distinct_from_gaussian_curved:  with identical ICs
      ξ(0) = 1, ξ_prime(0) = 0.1, the two trajectories diverge.

Output:
  • Frozen-test table (initial accelerations for both ODEs).
  • Trajectory plots for ξ(t), σ(t) at matched ICs.
  • JSON summary with the numerical verdict.

Phase 1 only: tests reduced ODE behavior.  Does NOT touch the full PDE
(which has the 1/|ψ|² singularity that Phase 2 must reckon with).
"""

from __future__ import annotations

import json
import math
from pathlib import Path

import matplotlib.pyplot as plt
import numpy as np
from scipy.integrate import solve_ivp


SCRIPT_DIR = Path(__file__).resolve().parent
OUT_DIR = SCRIPT_DIR.parent / "results" / "lsbridge_predictions" / "sech_curved_ode"
OUT_DIR.mkdir(parents=True, exist_ok=True)


# =============================================================================
# 1.  The two Lean-derived ODEs in state-space form.
# =============================================================================

def gaussian_curved_rhs(t, y):
    """Gaussian-curved: σ·σ_pp + σ_prime²·(σ − 1) = 0."""
    sigma, sigma_p = y
    if sigma <= 0:
        return [0.0, 0.0]
    sigma_pp = -sigma_p**2 * (sigma - 1.0) / sigma
    return [sigma_p, sigma_pp]


def sech_curved_rhs(t, y):
    """Sech-curved (Lean Part 17, ℏ = m = 1):
       ξ·ξ_pp + ξ_prime²·(ξ − 1) = 1/ξ."""
    xi, xi_p = y
    if xi <= 0:
        return [0.0, 0.0]
    xi_pp = 1.0 / xi**2 - xi_p**2 * (xi - 1.0) / xi
    return [xi_p, xi_pp]


# =============================================================================
# 2.  Initial-acceleration witness — the frozen-state test.
# =============================================================================

def initial_acceleration(rhs_fn, width_0):
    """Acceleration at t = 0 for IC (width = width_0, width_prime = 0).

    For a true frozen state both width_prime AND width_pp must vanish.
    Phase 1 witness of sech_curved_rejects_frozen and the Gaussian
    frozen-admissibility theorem."""
    _, ddot = rhs_fn(0.0, [width_0, 0.0])
    return ddot


def frozen_state_table(widths):
    """Compare initial accelerations at width_prime = 0 across widths."""
    rows = []
    for w in widths:
        a_g = initial_acceleration(gaussian_curved_rhs, w)
        a_s = initial_acceleration(sech_curved_rhs, w)
        rows.append({
            "width_0": w,
            "gaussian_initial_accel": a_g,
            "sech_initial_accel": a_s,
            "gaussian_admits_frozen": abs(a_g) < 1e-12,
            "sech_rejects_frozen": abs(a_s) > 1e-12,
        })
    return rows


# =============================================================================
# 3.  Trajectory integration.
# =============================================================================

def integrate(rhs_fn, y0, t_max=20.0, n_points=400):
    t = np.linspace(0.0, t_max, n_points)
    sol = solve_ivp(rhs_fn, (0.0, t_max), y0, t_eval=t,
                    method="RK45", rtol=1e-10, atol=1e-12)
    return sol.t, sol.y[0], sol.y[1], sol.success


# =============================================================================
# 4.  Plot:  ξ(t) vs σ(t) at matched ICs + frozen-state demo.
# =============================================================================

def plot_trajectories(out_path):
    fig, axes = plt.subplots(1, 3, figsize=(16, 5))

    # Panel A:  matched-IC trajectories (width_prime ≠ 0).
    t_max = 8.0
    ic_list = [(1.0, 0.10), (1.0, 0.20), (2.0, 0.10)]
    colors_g = plt.cm.Blues(np.linspace(0.4, 0.9, len(ic_list)))
    colors_s = plt.cm.Reds(np.linspace(0.4, 0.9, len(ic_list)))
    for (w0, wp0), cg, cs in zip(ic_list, colors_g, colors_s):
        t, g, _, _ = integrate(gaussian_curved_rhs, [w0, wp0], t_max=t_max)
        axes[0].plot(t, g, "-", color=cg,
                     label=f"Gaussian σ_0={w0}, σ'_0={wp0}", linewidth=1.6)
        t, s, _, _ = integrate(sech_curved_rhs, [w0, wp0], t_max=t_max)
        axes[0].plot(t, s, "--", color=cs,
                     label=f"Sech ξ_0={w0}, ξ'_0={wp0}", linewidth=1.6)
    axes[0].set_xlabel("t")
    axes[0].set_ylabel("width(t)")
    axes[0].set_title("Matched-IC trajectories\n(Gaussian solid, sech dashed)")
    axes[0].legend(fontsize=8, loc="best")
    axes[0].grid(True, alpha=0.3)

    # Panel B:  frozen-IC test (width_prime = 0).
    t_max_frozen = 5.0
    for w0, col_g, col_s in [(0.5, "tab:blue", "tab:red"),
                              (1.0, "navy",     "darkred"),
                              (2.0, "steelblue", "firebrick")]:
        t, g, _, _ = integrate(gaussian_curved_rhs, [w0, 0.0], t_max=t_max_frozen)
        axes[1].plot(t, g, "-", color=col_g,
                     label=f"Gaussian σ_0={w0}", linewidth=1.6)
        t, s, _, _ = integrate(sech_curved_rhs, [w0, 0.0], t_max=t_max_frozen)
        axes[1].plot(t, s, "--", color=col_s,
                     label=f"Sech ξ_0={w0}", linewidth=1.6)
    axes[1].set_xlabel("t")
    axes[1].set_ylabel("width(t)")
    axes[1].set_title("Frozen-state IC (width'(0) = 0)\nGaussian stays put · sech accelerates")
    axes[1].legend(fontsize=8, loc="best")
    axes[1].grid(True, alpha=0.3)

    # Panel C:  initial acceleration vs width_0.
    widths = np.linspace(0.3, 4.0, 60)
    a_g = np.array([initial_acceleration(gaussian_curved_rhs, w) for w in widths])
    a_s = np.array([initial_acceleration(sech_curved_rhs, w) for w in widths])
    axes[2].plot(widths, a_g, "b-",  label="Gaussian: width''(0) = 0", linewidth=2)
    axes[2].plot(widths, a_s, "r--", label="Sech: width''(0) = 1/ξ²", linewidth=2)
    axes[2].axhline(0.0, color="k", linewidth=0.6)
    axes[2].set_xlabel("width₀ (with width'(0) = 0)")
    axes[2].set_ylabel("initial width''(0)")
    axes[2].set_title("Frozen-state acceleration\nGaussian = 0 (admissible) · sech ≠ 0 (rejected)")
    axes[2].legend(fontsize=9, loc="best")
    axes[2].grid(True, alpha=0.3)
    axes[2].set_yscale("symlog", linthresh=1e-2)

    fig.tight_layout()
    fig.savefig(out_path, dpi=150)
    plt.close(fig)
    return out_path


# =============================================================================
# 5.  Divergence metric: how fast do matched-IC trajectories separate?
# =============================================================================

def divergence_at_t(width_0, width_p0, t_eval=5.0):
    t_g, g, _, _ = integrate(gaussian_curved_rhs, [width_0, width_p0],
                              t_max=t_eval, n_points=int(50 * t_eval))
    t_s, s, _, _ = integrate(sech_curved_rhs, [width_0, width_p0],
                              t_max=t_eval, n_points=int(50 * t_eval))
    g_end, s_end = float(g[-1]), float(s[-1])
    return {
        "width_0": width_0,
        "width_p0": width_p0,
        "t_eval": t_eval,
        "gaussian_width_at_t": g_end,
        "sech_width_at_t": s_end,
        "abs_diff": abs(g_end - s_end),
        "rel_diff": abs(g_end - s_end) / max(abs(g_end), abs(s_end), 1e-9),
    }


# =============================================================================
# 6.  Main.
# =============================================================================

def main():
    print("=" * 78)
    print("Phase 1 — Lean-derived sech-curved width ODE reproducer")
    print("=" * 78)
    print("""
Lean theorems being numerically witnessed:
  • gaussian_curved_leading_order_sigma_ode  (Part 12)  — Gaussian: source = 0.
  • sech_curved_leading_order_sigma_ode      (Part 17)  — sech: source = 1/ξ.
  • sech_curved_rejects_frozen               (Part 17)  — frozen state forbidden.
  • sech_curved_distinct_from_gaussian_curved (Part 17) — ODEs are non-equivalent.
""")

    # --- (a) Frozen-state numerical witness. ---
    print("[Frozen-state test:  width_prime(0) = 0 for both ODEs]")
    rows = frozen_state_table([0.5, 1.0, 1.5, 2.0, 3.0])
    print(f"{'width_0':>9}  {'Gaussian a(0)':>16}  {'Sech a(0)':>16}  "
          f"{'G admits frozen?':>18}  {'Sech rejects frozen?':>22}")
    for r in rows:
        print(f"{r['width_0']:>9.3f}  {r['gaussian_initial_accel']:>16.4e}  "
              f"{r['sech_initial_accel']:>16.4e}  "
              f"{str(r['gaussian_admits_frozen']):>18}  "
              f"{str(r['sech_rejects_frozen']):>22}")
    all_g_admit = all(r["gaussian_admits_frozen"] for r in rows)
    all_s_reject = all(r["sech_rejects_frozen"] for r in rows)
    print()
    if all_g_admit and all_s_reject:
        print("VERDICT (frozen test):  PASS")
        print("  Gaussian admits frozen state for all tested widths.")
        print("  Sech rejects frozen state for all tested widths (a(0) = 1/ξ² > 0).")
        print("  Numerical reproduction of sech_curved_rejects_frozen.")
    else:
        print("VERDICT (frozen test):  FAIL — Lean/numerical inconsistency.")

    # --- (b) Trajectory divergence at matched ICs. ---
    print()
    print("[Trajectory divergence at matched non-frozen ICs]")
    div_rows = [divergence_at_t(w0, wp0, t_eval=5.0)
                for w0, wp0 in [(1.0, 0.1), (1.0, 0.2), (2.0, 0.1), (0.5, 0.1)]]
    print(f"{'w_0':>6}  {'w_p0':>6}  {'t':>5}  {'Gauss w(t)':>12}  "
          f"{'Sech w(t)':>12}  {'|diff|':>10}  {'rel.diff':>10}")
    for d in div_rows:
        print(f"{d['width_0']:>6.2f}  {d['width_p0']:>6.2f}  {d['t_eval']:>5.1f}  "
              f"{d['gaussian_width_at_t']:>12.5f}  {d['sech_width_at_t']:>12.5f}  "
              f"{d['abs_diff']:>10.3e}  {d['rel_diff']:>10.3e}")
    significant = all(d["rel_diff"] > 0.02 for d in div_rows)
    print()
    if significant:
        print("VERDICT (divergence):  PASS")
        print("  Sech and Gaussian trajectories diverge at matched ICs.")
        print("  Numerical reproduction of sech_curved_distinct_from_gaussian_curved.")
    else:
        print("VERDICT (divergence):  WEAK — relative deviations < 2%.")

    # --- (c) Plots. ---
    plot_path = plot_trajectories(OUT_DIR / "gaussian_vs_sech_curved_odes.png")
    print()
    print(f"Plot saved: {plot_path}")

    # --- (d) JSON summary. ---
    summary = {
        "ode_gaussian": "sigma * sigma_pp + sigma_prime**2 * (sigma - 1) = 0",
        "ode_sech":     "xi * xi_pp + xi_prime**2 * (xi - 1) = 1/xi  (hbar = m = 1)",
        "frozen_test_rows": rows,
        "divergence_rows": div_rows,
        "verdict_frozen_test": "PASS" if (all_g_admit and all_s_reject) else "FAIL",
        "verdict_divergence": "PASS" if significant else "WEAK",
        "lean_theorems_witnessed": [
            "gaussian_curved_leading_order_sigma_ode",
            "sech_curved_leading_order_sigma_ode",
            "sech_curved_rejects_frozen",
            "sech_curved_distinct_from_gaussian_curved",
        ],
        "phase": "Phase 1 (reduced-ODE only; no PDE; no regularizer)",
    }
    json_path = OUT_DIR / "phase1_sech_curved_summary.json"
    with json_path.open("w") as f:
        json.dump(summary, f, indent=2)
    print(f"JSON saved: {json_path}")
    print()
    print("Next step in user's roadmap:  Phase 2 (full 1D PDE with sigma_0 sweep,")
    print("sech IC, shape fidelity, regularizer sensitivity).  Phase 2 is gated by")
    print("the 1/|psi|^2 singularity in the LSBridge PDE — see Phase 2 spec.")


if __name__ == "__main__":
    main()
