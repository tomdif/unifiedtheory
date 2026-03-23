#!/usr/bin/env python3
"""
Density convergence scan for m_mu/m_tau.

Physics:
  The lepton mass ratio r = m_mu/m_tau should converge to the physical value
  as the sprinkling density rho -> infinity (continuum limit). This script
  runs the lepton_gpu computation at multiple densities to verify convergence.

  If r stabilizes as rho increases, the prediction is robust and not an
  artifact of finite-density discretization effects.

  Expected behavior from prior runs:
    rho = 5K:  k* ~ 9.5  (r ~ 0.06 at k=0)
    rho = 10K: k* ~ 6.6  (r ~ 0.06 at k=0)
    rho = 20K: r should approach expt 0.0595
    rho = 50K: convergence check (slow, ~30 min/seed)

Requirements: pip install numpy scipy torch
Usage:
    python density_scan.py           # rho=5K,10K,20K,50K, 10 seeds
    python density_scan.py --quick   # rho=5K,10K, 5 seeds
    python density_scan.py --full    # rho=5K,10K,20K,50K, 20 seeds
"""

import sys, os
import numpy as np
import time

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from lepton_gpu import run_lepton_gpu, DEVICE

# ============================================================
# Constants
# ============================================================

EXP_MU_TAU = 0.0595  # experimental m_mu / m_tau


# ============================================================
# Main
# ============================================================

if __name__ == "__main__":
    if "--quick" in sys.argv:
        rhos = [5000, 10000]
        n_seeds = 5
        n_sample = 200
    elif "--full" in sys.argv:
        rhos = [5000, 10000, 20000, 50000]
        n_seeds = 20
        n_sample = 400
    else:
        rhos = [5000, 10000, 20000, 50000]
        n_seeds = 10
        n_sample = 300

    print("=" * 90)
    print("  DENSITY CONVERGENCE SCAN: m_mu/m_tau vs rho")
    print(f"  Densities: {rhos}")
    print(f"  {n_seeds} seeds, {n_sample} samples/length")
    print(f"  Device: {DEVICE}")
    print(f"  Experiment: m_mu/m_tau = {EXP_MU_TAU}")
    print("=" * 90)

    summary = {}
    all_timings = {}

    for rho in rhos:
        expected_N = rho  # box_size=1 => N ~ rho
        expected_L = 1.7 * rho ** 0.25
        print(f"\n{'='*70}")
        print(f"  rho = {rho}  (expected N ~ {expected_N}, L_max ~ {expected_L:.0f})")
        print(f"{'='*70}")

        results = []
        t_rho_start = time.time()

        for seed_idx in range(n_seeds):
            seed = seed_idx * 137
            r = run_lepton_gpu(rho=rho, n_sample=n_sample, seed=seed)
            results.append(r)

            print(f"  seed={seed_idx:>2d}: r = {r['r_mu_tau']:.5f}  "
                  f"L_max={r['L_max']:>2d}  N={r['N']:>6d}  "
                  f"t={r['time']:.0f}s  "
                  f"(cset={r.get('t_causet',0):.0f} "
                  f"dp={r.get('t_dp',0):.0f} "
                  f"paths={r.get('t_pathcount',0):.1f} "
                  f"hol={r.get('t_holonomy',0):.0f})",
                  flush=True)

            # Running average every 5 seeds
            if (seed_idx + 1) % 5 == 0 and len(results) >= 3:
                rs = [x['r_mu_tau'] for x in results]
                m, s = np.mean(rs), np.std(rs) / np.sqrt(len(rs))
                print(f"    --- running ({len(rs)} seeds): "
                      f"r = {m:.5f} +/- {s:.5f}  "
                      f"({m/EXP_MU_TAU:.2f}x expt) ---", flush=True)

        t_rho = time.time() - t_rho_start

        # Statistics for this density
        rs = [x['r_mu_tau'] for x in results if x['r_mu_tau'] > 0]
        Ls = [x['L_max'] for x in results]
        Ns = [x['N'] for x in results]
        times = [x['time'] for x in results]

        if rs:
            m = np.mean(rs)
            s = np.std(rs) / np.sqrt(len(rs))
            ci95 = 1.96 * s
            summary[rho] = {
                'mean': m,
                'sem': s,
                'std': np.std(rs),
                'n': len(rs),
                'ci95': ci95,
                'L_max_avg': np.mean(Ls),
                'N_avg': np.mean(Ns),
            }
            all_timings[rho] = {
                'per_seed': np.mean(times),
                'total': t_rho,
            }

            print(f"\n  >>> rho={rho}: r = {m:.5f} +/- {s:.5f}  "
                  f"(95% CI: [{m-ci95:.5f}, {m+ci95:.5f}])")
            print(f"      expt = {EXP_MU_TAU}, ratio = {m/EXP_MU_TAU:.3f}x")
            print(f"      avg L_max = {np.mean(Ls):.1f}, avg N = {np.mean(Ns):.0f}")
            print(f"      total time: {t_rho:.0f}s ({np.mean(times):.0f}s/seed)")
        else:
            print(f"\n  >>> rho={rho}: ALL FAILED")

    # ----------------------------------------------------------
    # Convergence table
    # ----------------------------------------------------------
    print(f"\n{'='*90}")
    print(f"  CONVERGENCE TABLE")
    print(f"{'='*90}")
    print(f"  {'rho':>8s}  {'N_avg':>8s}  {'L_max':>6s}  "
          f"{'r':>10s}  {'SEM':>10s}  {'95% CI':>22s}  "
          f"{'ratio':>8s}  {'t/seed':>8s}")
    print(f"  {'-'*88}")

    for rho in rhos:
        if rho in summary:
            s = summary[rho]
            t = all_timings[rho]
            lo = s['mean'] - s['ci95']
            hi = s['mean'] + s['ci95']
            print(f"  {rho:>8d}  {s['N_avg']:>8.0f}  {s['L_max_avg']:>6.1f}  "
                  f"{s['mean']:>10.5f}  {s['sem']:>10.5f}  "
                  f"[{lo:>9.5f}, {hi:>9.5f}]  "
                  f"{s['mean']/EXP_MU_TAU:>7.3f}x  "
                  f"{t['per_seed']:>7.0f}s")
        else:
            print(f"  {rho:>8d}  {'FAILED':>8s}")

    print(f"  {'Expt':>8s}  {'':>8s}  {'':>6s}  {EXP_MU_TAU:>10.5f}")
    print(f"{'='*90}")

    # Convergence analysis
    if len(summary) >= 2:
        rho_vals = sorted(summary.keys())
        r_vals = [summary[r]['mean'] for r in rho_vals]

        print(f"\n  CONVERGENCE ANALYSIS:")
        for i in range(1, len(rho_vals)):
            r_prev = summary[rho_vals[i-1]]['mean']
            r_curr = summary[rho_vals[i]]['mean']
            delta = r_curr - r_prev
            pct = abs(delta / r_prev) * 100 if r_prev > 0 else 0
            direction = "+" if delta > 0 else ""
            print(f"    rho {rho_vals[i-1]:>6d} -> {rho_vals[i]:>6d}: "
                  f"delta r = {direction}{delta:.5f} ({pct:.1f}%)")

        if len(rho_vals) >= 3:
            # Check if converging: is |delta| decreasing?
            deltas = [abs(summary[rho_vals[i]]['mean'] - summary[rho_vals[i-1]]['mean'])
                      for i in range(1, len(rho_vals))]
            if all(deltas[i] <= deltas[i-1] * 1.5 for i in range(1, len(deltas))):
                print(f"    --> Convergent behavior: changes are decreasing")
            else:
                print(f"    --> Non-monotonic convergence (may need more seeds)")

    print(f"\n  If r -> {EXP_MU_TAU} as rho increases, the lepton mass ratio")
    print(f"  is a parameter-free prediction of causal set + fiber geometry.")
    print(f"{'='*90}")
