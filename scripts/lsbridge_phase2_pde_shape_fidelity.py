"""
Phase 2 — full 1D PDE: Gaussian vs sech shape fidelity + tail-mask sensitivity.

Tests whether the Gaussian/sech narrow-width discrimination predicted by the
reduced ODEs (Phase 1) survives in the full matter-coupled curved Schrödinger
PDE on a finite-difference grid.

Physics:  LSBridge coupling is matter-coupled (a² = |ψ|² = ρ).  Where ρ → 0
there is no matter, hence no coupling — the equation reduces to free
Schrödinger.  A "tail-mask" formulation makes this physical insight explicit:

    i ∂_t ψ = − (1/2) · M(ρ; τ) · ∂_xx ψ
where
    M(ρ; τ) = 1/ρ        when ρ > τ      (LSBridge coupling, dense matter)
            = 1          when ρ ≤ τ      (free Schrödinger, dilute tails)

τ is a tail-mask threshold.  Earlier attempt (using i∂_t ψ = −1/(2(ρ+ε))∂_xx ψ
with additive ε) failed CFL catastrophically:  the regularized tails behave
as free Schrödinger with effective coefficient 1/(2ε), forcing dt < dx²·2ε.
The tail-mask formulation removes that source of stiffness entirely.

τ-sweep:  {0.01·peak_0, 0.05·peak_0, 0.10·peak_0, 0.20·peak_0}
          (relative to the initial peak density, peak_0 ≈ 0.4 for σ_0 = 1)
N-sweep:  {1024, 2048}
IC:       Gaussian (σ_0 = 1) and sech (matched initial σ ≈ 1)

Adaptive dt:  dt = min(5e−4, 0.4 · dx² · 2 · τ_abs).  Guarantees CFL.

Metrics tracked vs t:
  • σ(t), F_G(t), F_S(t), η(t, W), norm(t).

Pass condition (user's spec, adapted):
  σ_S/σ_G separation > 1.10 persists across ≥3 τ values and ≥2 grid
  resolutions, with Gaussian and sech fidelity ≥ 0.90 (no mode collapse),
  and norm conservation drift < 5%.

Usage:
    python3 lsbridge_phase2_pde_shape_fidelity.py --mode pilot   # ~1 min
    python3 lsbridge_phase2_pde_shape_fidelity.py --mode full    # ~10 min
"""

from __future__ import annotations

import argparse
import json
import math
import time
from pathlib import Path

import matplotlib.pyplot as plt
import numpy as np


SCRIPT_DIR = Path(__file__).resolve().parent
OUT_DIR = SCRIPT_DIR.parent / "results" / "lsbridge_predictions" / "phase2_pde_shape_fidelity"
OUT_DIR.mkdir(parents=True, exist_ok=True)


# =============================================================================
# 1.  Grid, ICs, PDE RHS, RK4.
# =============================================================================

def make_grid(L=80.0, N=2048):
    dx = L / N
    x = np.linspace(-L/2, L/2 - dx, N)
    return x, dx


def gaussian_psi(x, sigma_0):
    """Real, normalized Gaussian.  ⟨x²⟩ = σ_0², ∫|ψ|² = 1."""
    psi = np.exp(-x**2 / (4 * sigma_0**2)) / (2 * np.pi * sigma_0**2)**0.25
    return psi.astype(np.complex128)


def sech_psi(x, sigma_0):
    """Real, normalized sech profile with measured-σ matching σ_0.
       |ψ|² = (1/(2ξ))·sech²(x/ξ), ⟨x²⟩ = ξ²·π²/12, set ξ = σ_0·√12/π."""
    xi = sigma_0 * math.sqrt(12.0) / math.pi
    rho = (1.0 / (2.0 * xi)) / np.cosh(x / xi)**2
    psi = np.sqrt(rho).astype(np.complex128)
    return psi


def laplacian(psi, dx):
    return (np.roll(psi, -1) - 2.0 * psi + np.roll(psi, 1)) / dx**2


def rhs_lsbridge_masked(psi, dx, tau_abs):
    """Tail-masked LSBridge RHS.
       i∂_t ψ = −(1/2)·M(ρ;τ)·∂_xx ψ where M = 1/ρ if ρ>τ, else 1.
       (Returns ∂_t ψ.)"""
    rho = np.abs(psi)**2
    inv = np.where(rho > tau_abs, 1.0 / np.maximum(rho, tau_abs), 1.0)
    return 0.5j * inv * laplacian(psi, dx)


def rk4_step(psi, dx, dt, tau_abs):
    k1 = rhs_lsbridge_masked(psi,             dx, tau_abs)
    k2 = rhs_lsbridge_masked(psi + 0.5*dt*k1, dx, tau_abs)
    k3 = rhs_lsbridge_masked(psi + 0.5*dt*k2, dx, tau_abs)
    k4 = rhs_lsbridge_masked(psi + dt*k3,     dx, tau_abs)
    return psi + (dt / 6.0) * (k1 + 2.0*k2 + 2.0*k3 + k4)


# =============================================================================
# 2.  Metrics extracted from ψ(t).
# =============================================================================

def measure_sigma(psi, x, dx):
    rho = np.abs(psi)**2
    norm = float(np.sum(rho) * dx)
    if norm < 1e-12 or not math.isfinite(norm):
        return float("nan"), float("nan")
    mean_x = float(np.sum(x * rho) * dx) / norm
    var_x  = float(np.sum((x - mean_x)**2 * rho) * dx) / norm
    return math.sqrt(max(var_x, 0.0)), norm


def gaussian_density_template(x, sigma):
    return np.exp(-x**2 / (2.0 * sigma**2)) / math.sqrt(2.0 * math.pi * sigma**2)


def sech_density_template(x, sigma):
    xi = sigma * math.sqrt(12.0) / math.pi
    return (1.0 / (2.0 * xi)) / np.cosh(x / xi)**2


def density_fidelity(psi, x, dx, template):
    """Cosine similarity of density profiles. 1.0 = exact match."""
    rho = np.abs(psi)**2
    t   = template
    num = float(np.sum(rho * t) * dx)
    den = math.sqrt(float(np.sum(rho * rho) * dx) *
                    float(np.sum(t * t) * dx))
    if den < 1e-15:
        return float("nan")
    return num / den


def aperture_coupling(psi, x, dx, W):
    rho = np.abs(psi)**2
    mask = np.abs(x) < W
    return float(np.sum(rho[mask]) * dx)


# =============================================================================
# 3.  Single PDE run with metric logging.
# =============================================================================

def run_pde(ic_kind, sigma_0, tau_rel, N, L, t_max, dt_cap, sample_dt, aperture_W):
    """Run the tail-masked LSBridge PDE.
       tau_rel:  threshold relative to initial peak density (peak·tau_rel).
       dt is adaptive:  dt = min(dt_cap, 0.4·dx²·2·tau_abs)."""
    x, dx = make_grid(L, N)
    if ic_kind == "gaussian":
        psi = gaussian_psi(x, sigma_0)
    elif ic_kind == "sech":
        psi = sech_psi(x, sigma_0)
    else:
        raise ValueError(ic_kind)
    peak_init = float(np.max(np.abs(psi)**2))
    tau_abs   = tau_rel * peak_init
    dt        = min(dt_cap, 0.4 * dx**2 * 2.0 * tau_abs)
    dt        = max(dt, 1e-7)  # absolute floor to keep step count finite

    sigma_init, norm_init = measure_sigma(psi, x, dx)
    times    = [0.0]
    sigmas   = [sigma_init]
    norms    = [norm_init]
    f_G_list = [density_fidelity(psi, x, dx,
                                  gaussian_density_template(x, sigma_init))]
    f_S_list = [density_fidelity(psi, x, dx,
                                  sech_density_template(x, sigma_init))]
    eta_list = [aperture_coupling(psi, x, dx, aperture_W)]

    n_steps = int(round(t_max / dt))
    next_sample = sample_dt
    t = 0.0
    blowup = False
    for step in range(n_steps):
        psi = rk4_step(psi, dx, dt, tau_abs)
        t = (step + 1) * dt
        if not np.all(np.isfinite(psi)):
            blowup = True
            break
        if t >= next_sample - 1e-12:
            s, nrm = measure_sigma(psi, x, dx)
            if not math.isfinite(s) or not math.isfinite(nrm):
                blowup = True
                break
            times.append(t)
            sigmas.append(s)
            norms.append(nrm)
            f_G_list.append(density_fidelity(psi, x, dx,
                                              gaussian_density_template(x, s)))
            f_S_list.append(density_fidelity(psi, x, dx,
                                              sech_density_template(x, s)))
            eta_list.append(aperture_coupling(psi, x, dx, aperture_W))
            next_sample += sample_dt

    return {
        "ic": ic_kind,
        "sigma_0": sigma_0,
        "tau_rel": tau_rel,
        "tau_abs": tau_abs,
        "peak_init": peak_init,
        "N": N,
        "L": L,
        "t_max_requested": t_max,
        "t_reached": float(times[-1]),
        "dt": dt,
        "dt_cap": dt_cap,
        "n_steps_run": step + 1 if not blowup else step,
        "sample_dt": sample_dt,
        "aperture_W": aperture_W,
        "blowup": blowup,
        "times":  np.asarray(times),
        "sigma":  np.asarray(sigmas),
        "norm":   np.asarray(norms),
        "F_G":    np.asarray(f_G_list),
        "F_S":    np.asarray(f_S_list),
        "eta":    np.asarray(eta_list),
    }


# =============================================================================
# 4.  Run a config matrix and aggregate.
# =============================================================================

def run_config_matrix(tau_list, N_list, ic_list, sigma_0=1.0, L=80.0,
                       t_max=3.0, dt_cap=5e-4, sample_dt=0.1, aperture_W=2.0):
    rows = []
    for tau in tau_list:
        for N in N_list:
            for ic in ic_list:
                t0 = time.time()
                print(f"  τ_rel={tau:>6.3f}  N={N}  IC={ic:<8} ...",
                      end="", flush=True)
                r = run_pde(ic_kind=ic, sigma_0=sigma_0, tau_rel=tau,
                            N=N, L=L, t_max=t_max, dt_cap=dt_cap,
                            sample_dt=sample_dt, aperture_W=aperture_W)
                elapsed = time.time() - t0
                tag = " BLOWUP" if r["blowup"] else ""
                print(f"  done in {elapsed:5.1f}s  dt={r['dt']:.2e}  "
                      f"(t={r['t_reached']:.2f}, σ={r['sigma'][-1]:.3f}, "
                      f"F_G={r['F_G'][-1]:.3f}, F_S={r['F_S'][-1]:.3f}, "
                      f"η={r['eta'][-1]:.3f}, "
                      f"normdrift={abs(r['norm'][-1]/r['norm'][0]-1.0):.2e}){tag}")
                rows.append(r)
    return rows


# =============================================================================
# 5.  Plot: 4-panel summary at one ε, one N.
# =============================================================================

def plot_summary_for_eps_N(rows, tau, N, out_path):
    pair = [r for r in rows if r["tau_rel"] == tau and r["N"] == N]
    if len(pair) != 2:
        return None
    r_G = next((r for r in pair if r["ic"] == "gaussian"), None)
    r_S = next((r for r in pair if r["ic"] == "sech"), None)
    if r_G is None or r_S is None:
        return None

    fig, axes = plt.subplots(2, 2, figsize=(13, 9))

    # Panel A: σ(t) for both ICs.
    axes[0, 0].plot(r_G["times"], r_G["sigma"], "b-", linewidth=2,
                     label="Gaussian IC")
    axes[0, 0].plot(r_S["times"], r_S["sigma"], "r--", linewidth=2,
                     label="Sech IC (matched initial σ)")
    axes[0, 0].set_xlabel("t")
    axes[0, 0].set_ylabel("σ(t)")
    axes[0, 0].set_title("Width σ(t)")
    axes[0, 0].grid(True, alpha=0.3)
    axes[0, 0].legend()

    # Panel B: σ_S(t) / σ_G(t).
    # Interpolate to common grid in case sample arrays differ.
    t_common = np.minimum(r_G["times"][-1], r_S["times"][-1])
    t_grid = np.linspace(0.0, t_common, 50)
    sG = np.interp(t_grid, r_G["times"], r_G["sigma"])
    sS = np.interp(t_grid, r_S["times"], r_S["sigma"])
    ratio = sS / np.maximum(sG, 1e-12)
    axes[0, 1].plot(t_grid, ratio, "k-", linewidth=2)
    axes[0, 1].axhline(1.0, color="grey", linestyle=":")
    axes[0, 1].set_xlabel("t")
    axes[0, 1].set_ylabel("σ_sech / σ_Gaussian")
    axes[0, 1].set_title("Width ratio (mode-discrimination metric)")
    axes[0, 1].grid(True, alpha=0.3)

    # Panel C: shape fidelity.
    axes[1, 0].plot(r_G["times"], r_G["F_G"], "b-",
                     label="Gaussian IC, Gaussian template", linewidth=2)
    axes[1, 0].plot(r_S["times"], r_S["F_S"], "r--",
                     label="Sech IC, sech template", linewidth=2)
    axes[1, 0].plot(r_G["times"], r_G["F_S"], "b:",
                     label="Gaussian IC, sech template", linewidth=1)
    axes[1, 0].plot(r_S["times"], r_S["F_G"], "r:",
                     label="Sech IC, Gaussian template", linewidth=1)
    axes[1, 0].axhline(0.95, color="grey", linestyle=":",
                        label="0.95 fidelity floor")
    axes[1, 0].set_xlabel("t")
    axes[1, 0].set_ylabel("density fidelity")
    axes[1, 0].set_title("Shape fidelity")
    axes[1, 0].grid(True, alpha=0.3)
    axes[1, 0].legend(fontsize=8)
    axes[1, 0].set_ylim(0.0, 1.05)

    # Panel D: aperture coupling.
    axes[1, 1].plot(r_G["times"], r_G["eta"], "b-",
                     label=f"η_G(t), W = {r_G['aperture_W']}", linewidth=2)
    axes[1, 1].plot(r_S["times"], r_S["eta"], "r--",
                     label=f"η_S(t), W = {r_S['aperture_W']}", linewidth=2)
    axes[1, 1].set_xlabel("t")
    axes[1, 1].set_ylabel("∫_{|x|<W} |ψ|² dx")
    axes[1, 1].set_title("Narrow-aperture coupling")
    axes[1, 1].grid(True, alpha=0.3)
    axes[1, 1].legend()

    fig.suptitle(f"Phase 2 PDE (tail-masked): Gaussian vs sech, "
                  f"τ_rel = {tau:.3f}, N = {N}",
                  fontsize=14, y=1.0)
    fig.tight_layout()
    fig.savefig(out_path, dpi=150)
    plt.close(fig)
    return out_path


# =============================================================================
# 6.  Robustness table + verdict.
# =============================================================================

def robustness_table(rows, sep_threshold=1.1, fidelity_floor=0.90,
                      norm_drift_max=0.05):
    tbl = []
    tau_set = sorted({r["tau_rel"] for r in rows}, reverse=True)
    N_set   = sorted({r["N"]       for r in rows})
    pass_count = 0
    tau_pass_set = set()
    N_pass_set = set()
    for tau in tau_set:
        for N in N_set:
            pair = [r for r in rows if r["tau_rel"] == tau and r["N"] == N]
            r_G = next((r for r in pair if r["ic"] == "gaussian"), None)
            r_S = next((r for r in pair if r["ic"] == "sech"), None)
            if r_G is None or r_S is None:
                continue
            t_common = min(r_G["t_reached"], r_S["t_reached"])
            sG_end = float(np.interp(t_common, r_G["times"], r_G["sigma"]))
            sS_end = float(np.interp(t_common, r_S["times"], r_S["sigma"]))
            ratio  = sS_end / max(sG_end, 1e-12)
            F_G_end = float(r_G["F_G"][-1])
            F_S_end = float(r_S["F_S"][-1])
            norm_drift_G = abs(r_G["norm"][-1] / r_G["norm"][0] - 1.0)
            norm_drift_S = abs(r_S["norm"][-1] / r_S["norm"][0] - 1.0)
            cond_sep = ratio >= sep_threshold
            cond_fid = F_G_end >= fidelity_floor and F_S_end >= fidelity_floor
            cond_no_blowup = (not r_G["blowup"]) and (not r_S["blowup"])
            cond_norm = max(norm_drift_G, norm_drift_S) <= norm_drift_max
            passed = cond_sep and cond_fid and cond_no_blowup and cond_norm
            if passed:
                pass_count += 1
                tau_pass_set.add(tau)
                N_pass_set.add(N)
            tbl.append({
                "tau_rel": tau,
                "N":   N,
                "t_reached": t_common,
                "sigma_G": sG_end,
                "sigma_S": sS_end,
                "ratio_S_over_G": ratio,
                "F_G_end": F_G_end,
                "F_S_end": F_S_end,
                "norm_drift_G": norm_drift_G,
                "norm_drift_S": norm_drift_S,
                "blowup_G": r_G["blowup"],
                "blowup_S": r_S["blowup"],
                "separation_above_threshold": cond_sep,
                "fidelity_above_floor":       cond_fid,
                "no_blowup":                  cond_no_blowup,
                "norm_drift_ok":              cond_norm,
                "config_passes":              passed,
            })
    verdict = {
        "n_tau_with_pass": len(tau_pass_set),
        "n_N_with_pass":   len(N_pass_set),
        "n_configs_passing": pass_count,
        "n_configs_total":   len(tbl),
        "pass_tau_threshold": len(tau_pass_set) >= 3,
        "pass_N_threshold":   len(N_pass_set)   >= 2,
        "pass_overall": (len(tau_pass_set) >= 3 and len(N_pass_set) >= 2),
        "sep_threshold":   sep_threshold,
        "fidelity_floor":  fidelity_floor,
        "norm_drift_max":  norm_drift_max,
    }
    return tbl, verdict


def print_table(tbl):
    print()
    print(f"{'τ_rel':>7}  {'N':>5}  {'t':>5}  {'σ_G':>7}  {'σ_S':>7}  "
          f"{'σ_S/σ_G':>8}  {'F_G':>6}  {'F_S':>6}  "
          f"{'normdriftG':>11}  {'pass?':>6}")
    print("-" * 95)
    for r in tbl:
        flag = "YES" if r["config_passes"] else "no"
        bg = " (G blew up)" if r["blowup_G"] else ""
        bs = " (S blew up)" if r["blowup_S"] else ""
        print(f"{r['tau_rel']:>7.3f}  {r['N']:>5d}  {r['t_reached']:>5.2f}  "
              f"{r['sigma_G']:>7.3f}  {r['sigma_S']:>7.3f}  "
              f"{r['ratio_S_over_G']:>8.3f}  {r['F_G_end']:>6.3f}  "
              f"{r['F_S_end']:>6.3f}  "
              f"{r['norm_drift_G']:>11.2e}  {flag:>6}{bg}{bs}")


# =============================================================================
# 7.  Main.
# =============================================================================

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--mode", choices=["pilot", "full"], default="pilot")
    args = ap.parse_args()

    print("=" * 84)
    print(f"Phase 2 — full PDE shape-fidelity + regularizer-sensitivity   ({args.mode})")
    print("=" * 84)

    sigma_0 = 1.0
    if args.mode == "pilot":
        tau_list = [0.05, 0.20]
        N_list   = [2048]
        t_max    = 1.0
        dt_cap   = 5e-4
        sample_dt = 0.1
    else:
        tau_list = [0.01, 0.05, 0.10, 0.20]
        N_list   = [1024, 2048]
        t_max    = 2.0
        dt_cap   = 5e-4
        sample_dt = 0.1
    ic_list = ["gaussian", "sech"]

    print(f"  σ_0 = {sigma_0}    L = 80    t_max = {t_max}    dt_cap = {dt_cap}")
    print(f"  τ_rel ∈ {tau_list} (× initial peak)    N ∈ {N_list}    IC ∈ {ic_list}")
    print(f"  metrics: σ(t), F_G(t), F_S(t), η(t, W=2), norm(t)")
    print(f"  PDE: i∂_t ψ = −(1/2)·M(ρ;τ)·∂_xx ψ,  M = 1/ρ if ρ>τ, else 1")
    print()

    rows = run_config_matrix(tau_list, N_list, ic_list,
                              sigma_0=sigma_0, t_max=t_max,
                              dt_cap=dt_cap, sample_dt=sample_dt,
                              aperture_W=2.0)

    tbl, verdict = robustness_table(rows,
                                     sep_threshold=1.10,
                                     fidelity_floor=0.90,
                                     norm_drift_max=0.05)
    print_table(tbl)

    print()
    print(f"PASS thresholds:  σ_S/σ_G ≥ {verdict['sep_threshold']},  "
          f"F_{{G,S}} ≥ {verdict['fidelity_floor']},  "
          f"normdrift ≤ {verdict['norm_drift_max']},  no blowup")
    print(f"  τ-values with at least one passing config: {verdict['n_tau_with_pass']}/{len(tau_list)}")
    print(f"  N-values with at least one passing config: {verdict['n_N_with_pass']}/{len(N_list)}")
    if verdict["pass_overall"]:
        print("  OVERALL VERDICT: PASS — Gaussian/sech split persists across required τ, N coverage.")
    else:
        print("  OVERALL VERDICT: NOT PASS — does not hit ≥3 τ AND ≥2 N at chosen thresholds.")
    print()

    plots = []
    for tau in sorted({r['tau_rel'] for r in rows}, reverse=True):
        for N in sorted({r['N'] for r in rows}):
            p = OUT_DIR / f"summary_tau{tau:.3f}_N{N}.png"
            res = plot_summary_for_eps_N(rows, tau, N, p)
            if res is not None:
                plots.append(str(res))
    print(f"Plots: {len(plots)} files in {OUT_DIR}")
    for pth in plots:
        print(f"  {Path(pth).name}")

    summary = {
        "mode": args.mode,
        "method": "tail_masked",
        "config": {
            "sigma_0": sigma_0,
            "L": 80.0,
            "t_max": t_max,
            "dt_cap": dt_cap,
            "sample_dt": sample_dt,
            "tau_list_rel": tau_list,
            "N_list": N_list,
            "ic_list": ic_list,
            "aperture_W": 2.0,
        },
        "table": tbl,
        "verdict": verdict,
    }
    summary_path = OUT_DIR / f"phase2_tailmasked_{args.mode}_summary.json"

    def _np_to_py(obj):
        import numpy as _np
        if isinstance(obj, _np.bool_):
            return bool(obj)
        if isinstance(obj, _np.integer):
            return int(obj)
        if isinstance(obj, _np.floating):
            return float(obj)
        if isinstance(obj, _np.ndarray):
            return obj.tolist()
        return obj
    with summary_path.open("w") as f:
        json.dump(summary, f, indent=2, default=_np_to_py)
    print(f"JSON: {summary_path.name}")


if __name__ == "__main__":
    main()
