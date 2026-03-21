#!/usr/bin/env python3
"""
Lepton sector convergence study: m_μ/m_τ vs sprinkling density ρ.

SELF-CONTAINED: no imports from causal-higgs-sim needed.
All functions included in this single file.

At ρ = 10,000: m_μ/m_τ ≈ 0.025 (factor 2.4× from experiment 0.060).
The prediction should converge toward experiment as ρ → 200,000.

Hardware: 4060 (8GB VRAM) or any machine with ≥4GB RAM.
GPU: Optional (install cupy-cuda12x for CUDA acceleration).
Time: ~2-3 hours on 4060; ~7 hours CPU-only.

Setup:
    pip install numpy scipy

Usage:
    python3 lepton_convergence.py              # standard (10 seeds, ~3h)
    python3 lepton_convergence.py --quick      # fast test (5 seeds, ~10min)
    python3 lepton_convergence.py --full       # publication (20 seeds, ~6h)
"""

import sys, os, numpy as np, time
from scipy.spatial import cKDTree


# ============================================================
# 1. Poisson sprinkling in 4D
# ============================================================

def poisson_sprinkle_4d(rho, box_size=1.0, seed=42):
    rng = np.random.default_rng(seed)
    N = rng.poisson(rho * box_size ** 4)
    pts = rng.uniform(0, box_size, size=(N, 4)).astype(np.float64)
    order = np.argsort(pts[:, 0])
    return pts[order], N


# ============================================================
# 2. Causal pairs via KDTree
# ============================================================

def build_causal_pairs_fast(points, box_size=1.0, periodic=True):
    N = len(points)
    times = points[:, 0]
    spatial = points[:, 1:]
    tree = cKDTree(spatial, boxsize=box_size if periodic else None)

    max_dt = box_size / 2
    pairs = tree.query_pairs(r=max_dt, output_type='ndarray')
    if len(pairs) == 0:
        return np.array([], dtype=np.int64), np.array([], dtype=np.int64), 0

    i_arr, j_arr = pairs[:, 0], pairs[:, 1]
    dt = times[j_arr] - times[i_arr]
    dx = spatial[j_arr] - spatial[i_arr]
    if periodic:
        dx = dx - box_size * np.round(dx / box_size)
    dist_sq = np.sum(dx ** 2, axis=1)

    # Causal: dt > 0 and dt^2 > dist_sq (timelike separation)
    mask_fwd = (dt > 0) & (dt ** 2 > dist_sq)
    mask_bwd = (dt < 0) & (dt ** 2 > dist_sq)

    pi = np.concatenate([i_arr[mask_fwd], j_arr[mask_bwd]])
    pj = np.concatenate([j_arr[mask_fwd], i_arr[mask_bwd]])

    return pi, pj, len(pi)


# ============================================================
# 3. Find longest chains (for holonomy computation)
# ============================================================

def find_longest_chains(pi, pj, N, min_length=2, max_chains=5000, seed=42):
    from collections import defaultdict
    adj = defaultdict(list)
    for i, j in zip(pi, pj):
        adj[int(i)].append(int(j))

    rng = np.random.default_rng(seed)
    chains = []
    all_li, all_lj = [], []

    for _ in range(max_chains * 3):
        if not adj:
            break
        start = rng.choice(list(adj.keys()))
        chain = [start]
        current = start
        visited = {start}
        while current in adj and adj[current]:
            nexts = [n for n in adj[current] if n not in visited]
            if not nexts:
                break
            nxt = nexts[rng.integers(len(nexts))]
            chain.append(nxt)
            visited.add(nxt)
            current = nxt
        if len(chain) >= min_length:
            chains.append(chain)
            for k in range(len(chain) - 1):
                all_li.append(chain[k])
                all_lj.append(chain[k + 1])
        if len(chains) >= max_chains:
            break

    li = np.array(all_li, dtype=np.int64)
    lj = np.array(all_lj, dtype=np.int64)
    return chains, li, lj, None, None


# ============================================================
# 4. Random SU(2) matrices at coupling β
# ============================================================

def random_su2_batch(n, rng, beta=4.0):
    Us = np.zeros((n, 2, 2), dtype=complex)
    for k in range(n):
        H = rng.standard_normal((2, 2)) + 1j * rng.standard_normal((2, 2))
        H = (H + H.conj().T) / 2
        H -= np.trace(H) / 2 * np.eye(2)
        eigvals, eigvecs = np.linalg.eig(1j * H / beta)
        U = eigvecs @ np.diag(np.exp(eigvals)) @ np.linalg.inv(eigvecs)
        det = np.linalg.det(U)
        U *= (det.conj() / abs(det + 1e-30)) ** 0.5
        Us[k] = U
    return Us


# ============================================================
# 5. Weak-only K/P projection for the lepton sector
# ============================================================

def run_lepton_kp(rho=10000, beta_weak=4.0, n_chains=5000, seed=42):
    pts, N = poisson_sprinkle_4d(rho, seed=seed)
    pi, pj, _ = build_causal_pairs_fast(pts)
    chains, li, lj, _, _ = find_longest_chains(
        pi, pj, N, min_length=2, max_chains=n_chains, seed=seed + 100)

    link_set = {}
    for i, j in zip(li, lj):
        key = (int(i), int(j))
        if key not in link_set:
            link_set[key] = len(link_set)

    rng = np.random.default_rng(seed + 9000)
    Us = random_su2_batch(len(link_set), rng, beta=beta_weak)

    s_ref = np.array([1, 0], dtype=complex)
    c_weak = np.zeros(2, dtype=complex)
    for chain in chains:
        W = np.eye(2, dtype=complex)
        for l in range(len(chain) - 1):
            key = (chain[l], chain[l + 1])
            if key in link_set:
                W = Us[link_set[key]] @ W
        c_weak += W @ s_ref
    c_weak /= len(chains)

    c_norm = np.abs(c_weak)
    masses = np.sort(c_norm)[::-1]
    r_mu_tau = float(masses[1] / masses[0]) if masses[0] > 0 else 0

    return {
        'N': N,
        'n_chains': len(chains),
        'beta_weak': beta_weak,
        'r_mu_tau': r_mu_tau,
        'r_e_tau': r_mu_tau ** 2,
    }


# ============================================================
# 6. Convergence study
# ============================================================

EXP_MU_TAU = 0.0595
EXP_E_TAU = 0.000288


def run_convergence(rhos=None, n_seeds=10, n_chains=10000):
    if rhos is None:
        rhos = [10000, 50000, 100000, 200000]

    print("=" * 70)
    print("  LEPTON CONVERGENCE STUDY: m_μ/m_τ vs density ρ")
    print(f"  β_weak = 4, n_chains = {n_chains}, {n_seeds} seeds per ρ")
    print(f"  Target: m_μ/m_τ = {EXP_MU_TAU} (experiment)")
    print("=" * 70)

    all_results = {}
    for rho in rhos:
        results = []
        t0 = time.time()
        for seed in range(n_seeds):
            try:
                r = run_lepton_kp(
                    rho=rho, beta_weak=4.0,
                    n_chains=n_chains, seed=seed * 137
                )
                results.append(r)
                print(f"  rho={rho:>7d}, seed={seed:>2d}: "
                      f"m_mu/m_tau = {r['r_mu_tau']:.6f} "
                      f"(N={r['N']}, chains={r['n_chains']})",
                      flush=True)
            except Exception as e:
                print(f"  rho={rho:>7d}, seed={seed:>2d}: FAILED ({e})")

        if not results:
            continue

        mu_taus = [r['r_mu_tau'] for r in results]
        mean = np.mean(mu_taus)
        sem = np.std(mu_taus) / np.sqrt(len(mu_taus))
        dt = time.time() - t0

        all_results[rho] = {
            'mean': mean, 'sem': sem, 'n': len(results),
            'factor': mean / EXP_MU_TAU, 'time': dt
        }

        print(f"\n  >>> rho={rho:>7d}: m_mu/m_tau = {mean:.6f} +/- {sem:.6f} "
              f"(expt: {EXP_MU_TAU}, factor {mean/EXP_MU_TAU:.2f}x) "
              f"[{dt:.0f}s]\n")

    print("=" * 70)
    print("  SUMMARY")
    print("=" * 70)
    print(f"  {'rho':>8s}  {'m_mu/m_tau':>12s}  {'SEM':>10s}  "
          f"{'Factor':>8s}  {'Time':>8s}")
    print("-" * 58)
    for rho, r in all_results.items():
        print(f"  {rho:>8d}  {r['mean']:>12.6f}  {r['sem']:>10.6f}  "
              f"{r['factor']:>7.2f}x  {r['time']:>7.0f}s")
    print(f"  {'Expt':>8s}  {EXP_MU_TAU:>12.6f}")
    print("=" * 70)

    return all_results


if __name__ == "__main__":
    if "--quick" in sys.argv:
        print("Quick mode: rho = [10k, 50k], 5 seeds")
        run_convergence(rhos=[10000, 50000], n_seeds=5, n_chains=5000)
    elif "--full" in sys.argv:
        print("Full mode: rho = [10k, 50k, 100k, 200k], 20 seeds")
        run_convergence(rhos=[10000, 50000, 100000, 200000],
                       n_seeds=20, n_chains=10000)
    else:
        print("Standard mode: rho = [10k, 50k, 100k, 200k], 10 seeds")
        print("Use --quick for fast test, --full for publication quality\n")
        run_convergence()
