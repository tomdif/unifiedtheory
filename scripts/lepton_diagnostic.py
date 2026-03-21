#!/usr/bin/env python3
"""
Diagnostic: WHY isn't m_μ/m_τ converging?

Checks:
1. Are chains getting LONGER at higher ρ? (They should)
2. Is |c_weak| going to zero? (Random walk washout)
3. Is the ratio m_μ/m_τ = |c_weak[1]|/|c_weak[0]| saturating?
4. Memory profile at each ρ

Also: uses reduced search radius to avoid OOM at high ρ.
"""

import sys, numpy as np, time
from scipy.spatial import cKDTree
from collections import defaultdict


def poisson_sprinkle_4d(rho, box_size=1.0, seed=42):
    rng = np.random.default_rng(seed)
    N = rng.poisson(rho * box_size ** 4)
    pts = rng.uniform(0, box_size, size=(N, 4)).astype(np.float64)
    order = np.argsort(pts[:, 0])
    return pts[order], N


def build_causal_pairs_fast(points, box_size=1.0, rho=10000):
    """Causal pairs with ADAPTIVE search radius to avoid OOM."""
    N = len(points)
    times = points[:, 0]
    spatial = points[:, 1:]

    # Adaptive radius: discreteness scale ~ rho^{-1/4}
    # Use a multiple of this as the search radius
    disc_scale = rho ** (-0.25)
    search_radius = min(box_size / 2, 10 * disc_scale)

    tree = cKDTree(spatial, boxsize=box_size)
    pairs = tree.query_pairs(r=search_radius, output_type='ndarray')

    if len(pairs) == 0:
        return np.array([], dtype=np.int64), np.array([], dtype=np.int64), 0

    i_arr, j_arr = pairs[:, 0], pairs[:, 1]
    dt = times[j_arr] - times[i_arr]
    dx = spatial[j_arr] - spatial[i_arr]
    dx = dx - box_size * np.round(dx / box_size)
    dist_sq = np.sum(dx ** 2, axis=1)

    mask_fwd = (dt > 0) & (dt ** 2 > dist_sq)
    mask_bwd = (dt < 0) & (dt ** 2 > dist_sq)
    pi = np.concatenate([i_arr[mask_fwd], j_arr[mask_bwd]])
    pj = np.concatenate([j_arr[mask_fwd], i_arr[mask_bwd]])

    return pi, pj, len(pi)


def find_longest_chains(pi, pj, N, min_length=2, max_chains=5000, seed=42):
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
    return chains, li, lj


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


def run_diagnostic(rho, beta_weak=4.0, n_chains=5000, seed=42):
    t0 = time.time()

    pts, N = poisson_sprinkle_4d(rho, seed=seed)
    t_sprinkle = time.time() - t0

    pi, pj, n_pairs = build_causal_pairs_fast(pts, rho=rho)
    t_pairs = time.time() - t0 - t_sprinkle

    chains, li, lj = find_longest_chains(
        pi, pj, N, min_length=2, max_chains=n_chains, seed=seed + 100)
    t_chains = time.time() - t0 - t_sprinkle - t_pairs

    chain_lengths = [len(c) for c in chains]

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

    total_time = time.time() - t0

    return {
        'rho': rho,
        'N': N,
        'n_pairs': n_pairs,
        'n_chains': len(chains),
        'n_links': len(link_set),
        'chain_length_mean': np.mean(chain_lengths) if chain_lengths else 0,
        'chain_length_max': max(chain_lengths) if chain_lengths else 0,
        'chain_length_median': np.median(chain_lengths) if chain_lengths else 0,
        'c_weak_0': complex(c_weak[0]),
        'c_weak_1': complex(c_weak[1]),
        'c_weak_mag_0': float(c_norm[0]),
        'c_weak_mag_1': float(c_norm[1]),
        'c_weak_total': float(np.linalg.norm(c_weak)),
        'r_mu_tau': r_mu_tau,
        'time_sprinkle': t_sprinkle,
        'time_pairs': t_pairs,
        'time_chains': t_chains,
        'time_total': total_time,
        'mem_pts_mb': N * 4 * 8 / 1e6,
        'mem_pairs_mb': n_pairs * 16 / 1e6,
    }


if __name__ == "__main__":
    print("=" * 80)
    print("  LEPTON DIAGNOSTIC: Why isn't m_μ/m_τ converging?")
    print("=" * 80)

    rhos = [5000, 10000, 20000, 50000, 100000]
    if "--small" in sys.argv:
        rhos = [5000, 10000, 20000]

    for rho in rhos:
        print(f"\n--- rho = {rho} ---")
        results = []
        for seed in range(5):
            r = run_diagnostic(rho, seed=seed * 137)
            results.append(r)
            print(f"  seed={seed}: N={r['N']}, pairs={r['n_pairs']}, "
                  f"chains={r['n_chains']}, "
                  f"chain_len={r['chain_length_mean']:.1f} "
                  f"(max {r['chain_length_max']}), "
                  f"|c_w|=({r['c_weak_mag_0']:.5f},{r['c_weak_mag_1']:.5f}), "
                  f"r={r['r_mu_tau']:.5f}, "
                  f"mem={r['mem_pts_mb']+r['mem_pairs_mb']:.0f}MB, "
                  f"t={r['time_total']:.1f}s",
                  flush=True)

        means = {k: np.mean([r[k] for r in results])
                 for k in ['chain_length_mean', 'chain_length_max',
                           'c_weak_mag_0', 'c_weak_mag_1', 'c_weak_total',
                           'r_mu_tau']}
        print(f"\n  MEAN: chain_len={means['chain_length_mean']:.1f}, "
              f"max_chain={means['chain_length_max']:.0f}, "
              f"|c_w|=({means['c_weak_mag_0']:.5f},{means['c_weak_mag_1']:.5f}), "
              f"|c_w|_total={means['c_weak_total']:.5f}, "
              f"r_mu_tau={means['r_mu_tau']:.5f}")

        if means['c_weak_total'] < 0.01:
            print("  *** WARNING: |c_weak| → 0 (random walk washout!)")
        if means['chain_length_mean'] < 5:
            print("  *** WARNING: chains too short for holonomy to build up")

    print("\n" + "=" * 80)
    print("  KEY DIAGNOSTICS:")
    print("  - If chain_length_mean does NOT grow with rho: chain finding is bottleneck")
    print("  - If |c_weak| → 0 at all rho: random walk washout (beta too low)")
    print("  - If |c_weak[0]| and |c_weak[1]| both shrink equally: no hierarchy")
    print("  - If r_mu_tau is flat: the mechanism saturates, need different approach")
    print("=" * 80)
