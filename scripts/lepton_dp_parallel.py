#!/usr/bin/env python3
"""
Parallelized version of lepton_dp_guided.py.
Runs all seeds concurrently across all CPU cores.
"""

import sys, numpy as np, time
from multiprocessing import Pool, cpu_count

# Import everything from the DP-guided script
sys.path.insert(0, '.')
from scripts.lepton_dp_guided import run_lepton_dp_guided, EXP_MU_TAU


def run_seed(args):
    rho, n_sample, seed = args
    return run_lepton_dp_guided(rho=rho, beta_weak=4.0,
                                 n_sample_per_length=n_sample,
                                 seed=seed * 137)


if __name__ == "__main__":
    ncpu = cpu_count()

    if "--quick" in sys.argv:
        rhos = [5000, 10000]
        n_seeds = 5
        n_sample = 300
    elif "--20k" in sys.argv:
        rhos = [20000]
        n_seeds = 10
        n_sample = 500
    elif "--full" in sys.argv:
        rhos = [5000, 10000, 20000]
        n_seeds = 10
        n_sample = 500
    else:
        rhos = [5000, 10000, 20000]
        n_seeds = 5
        n_sample = 500

    print(f"Using {ncpu} cores")
    print("=" * 70)
    print("  PARALLELIZED DP-GUIDED LEPTON MASS RATIOS (count-weighted, k=0)")
    print(f"  {n_seeds} seeds/rho, {n_sample} samples/length")
    print("=" * 70)

    for rho in rhos:
        t0 = time.time()
        args = [(rho, n_sample, s) for s in range(n_seeds)]

        with Pool(min(ncpu, n_seeds)) as pool:
            results = pool.map(run_seed, args)

        for r in results:
            seed = r.get('seed', '?')
            print(f"  rho={rho}, "
                  f"|c|=({r['c_weak_mag'][0]:.4f},{r['c_weak_mag'][1]:.4f}), "
                  f"r={r['r_mu_tau']:.5f}, L_max={r['L_max']}, "
                  f"t={r['time']:.1f}s", flush=True)

        mu_taus = [r['r_mu_tau'] for r in results if r.get('total_weight', 0) > 0]
        if mu_taus:
            mean = np.mean(mu_taus)
            sem = np.std(mu_taus) / np.sqrt(len(mu_taus))
            print(f"\n  >>> rho={rho}: r_mu_tau = {mean:.5f} +/- {sem:.5f} "
                  f"(expt: {EXP_MU_TAU}, factor {mean/EXP_MU_TAU:.2f}x) "
                  f"[{time.time()-t0:.0f}s total]\n")

    print("=" * 70)
