#!/usr/bin/env python3
"""
Lepton mass ratios with DAG longest-path chains.

The greedy random-walk chain finder gives chains of length 2-3,
which is too short for SU(2) holonomy at β=4 to accumulate meaningful
perpendicular projection. The fix: use longest-path on the causal DAG.

Algorithm:
  1. Build causal DAG (adjacency list, already time-ordered)
  2. Topological sort (trivial: time-ordering IS a topological sort)
  3. Dynamic programming: for each node, longest path ending at that node
  4. Backtrack to extract the actual chains

Expected longest chain (Brightwell-Georgiou):
  L_max ≈ 1.7 × ρ^{1/4}
  ρ=10k: ~17 links. ρ=50k: ~25 links. ρ=200k: ~40 links.

These are long enough for the K/P perpendicular fraction to reach ~0.06.

Requirements: pip install numpy scipy
Usage:
    python3 lepton_longest_path.py              # standard
    python3 lepton_longest_path.py --quick      # fast test
"""

import sys, numpy as np, time
from scipy.spatial import cKDTree
from collections import defaultdict


# ============================================================
# 1. Poisson sprinkling (same as before)
# ============================================================

def poisson_sprinkle_4d(rho, box_size=1.0, seed=42):
    rng = np.random.default_rng(seed)
    N = rng.poisson(rho * box_size ** 4)
    pts = rng.uniform(0, box_size, size=(N, 4)).astype(np.float64)
    order = np.argsort(pts[:, 0])
    return pts[order], N


# ============================================================
# 2. Causal pairs with adaptive radius
# ============================================================

def build_causal_pairs(points, box_size=1.0, rho=10000):
    N = len(points)
    times = points[:, 0]
    spatial = points[:, 1:]

    disc_scale = rho ** (-0.25)
    search_radius = min(box_size / 2, 15 * disc_scale)

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


# ============================================================
# 3. DAG longest-path via dynamic programming
# ============================================================

def find_longest_chains_dag(pi, pj, N, n_chains=5000):
    """
    Find the longest chains in the causal DAG via dynamic programming.

    Algorithm:
      - Build adjacency list (forward edges only, already time-ordered)
      - DP: dp[j] = max(dp[i] + 1) for all i → j
      - Backtrack from the nodes with largest dp values

    Returns the top n_chains longest chains.
    """
    # Build forward adjacency list
    adj = defaultdict(list)
    in_nodes = set()
    for i, j in zip(pi, pj):
        adj[int(i)].append(int(j))
        in_nodes.add(int(i))
        in_nodes.add(int(j))

    if not in_nodes:
        return [], np.array([]), np.array([])

    all_nodes = sorted(in_nodes)  # already time-ordered from sprinkling
    node_set = set(all_nodes)

    # DP: longest path ending at each node
    dp = {}        # dp[node] = length of longest path ending here
    parent = {}    # parent[node] = predecessor on longest path

    for node in all_nodes:
        dp[node] = 1
        parent[node] = -1

    for node in all_nodes:
        if node in adj:
            for nxt in adj[node]:
                if nxt in node_set and dp.get(node, 1) + 1 > dp.get(nxt, 1):
                    dp[nxt] = dp[node] + 1
                    parent[nxt] = node

    # Find the top endpoints (nodes with largest dp values)
    endpoints = sorted(dp.keys(), key=lambda x: dp[x], reverse=True)

    # Backtrack to extract chains
    chains = []
    used_endpoints = set()
    all_li, all_lj = [], []

    for end in endpoints:
        if len(chains) >= n_chains:
            break
        if end in used_endpoints:
            continue

        # Backtrack
        chain = []
        node = end
        while node != -1:
            chain.append(node)
            node = parent.get(node, -1)
        chain.reverse()

        if len(chain) >= 3:  # only keep chains with ≥ 3 nodes (≥ 2 links)
            chains.append(chain)
            used_endpoints.add(end)
            for k in range(len(chain) - 1):
                all_li.append(chain[k])
                all_lj.append(chain[k + 1])

    li = np.array(all_li, dtype=np.int64) if all_li else np.array([], dtype=np.int64)
    lj = np.array(all_lj, dtype=np.int64) if all_lj else np.array([], dtype=np.int64)

    return chains, li, lj


# ============================================================
# 4. Random SU(2) matrices
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
# 5. Lepton K/P projection with longest-path chains
# ============================================================

def run_lepton_longest_path(rho=10000, beta_weak=4.0, n_chains=5000, seed=42):
    t0 = time.time()

    pts, N = poisson_sprinkle_4d(rho, seed=seed)
    t1 = time.time()

    pi, pj, n_pairs = build_causal_pairs(pts, rho=rho)
    t2 = time.time()

    chains, li, lj = find_longest_chains_dag(pi, pj, N, n_chains=n_chains)
    t3 = time.time()

    if not chains:
        return {'N': N, 'n_chains': 0, 'r_mu_tau': 0, 'chain_len_mean': 0,
                'chain_len_max': 0, 'time': time.time() - t0}

    chain_lengths = [len(c) for c in chains]

    # Build link set
    link_set = {}
    for i, j in zip(li, lj):
        key = (int(i), int(j))
        if key not in link_set:
            link_set[key] = len(link_set)

    rng = np.random.default_rng(seed + 9000)
    Us = random_su2_batch(len(link_set), rng, beta=beta_weak)

    # K/P projection
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
        'N': N,
        'n_pairs': n_pairs,
        'n_chains': len(chains),
        'n_links': len(link_set),
        'chain_len_mean': np.mean(chain_lengths),
        'chain_len_max': max(chain_lengths),
        'chain_len_median': np.median(chain_lengths),
        'c_weak_mag': (float(c_norm[0]), float(c_norm[1])),
        'c_weak_total': float(np.linalg.norm(c_weak)),
        'r_mu_tau': r_mu_tau,
        'r_e_tau': r_mu_tau ** 2,
        'time_sprinkle': t1 - t0,
        'time_pairs': t2 - t1,
        'time_chains': t3 - t2,
        'time_total': total_time,
    }


# ============================================================
# 6. Convergence study
# ============================================================

EXP_MU_TAU = 0.0595

if __name__ == "__main__":
    if "--quick" in sys.argv:
        rhos = [5000, 10000, 20000]
        n_seeds = 3
        n_chains = 2000
    elif "--full" in sys.argv:
        rhos = [5000, 10000, 20000, 50000]
        n_seeds = 10
        n_chains = 5000
    else:
        rhos = [5000, 10000, 20000, 50000]
        n_seeds = 5
        n_chains = 5000

    print("=" * 80)
    print("  LEPTON MASS RATIOS WITH DAG LONGEST-PATH CHAINS")
    print(f"  beta_weak = 4, {n_seeds} seeds per rho")
    print(f"  Brightwell-Georgiou: L_max ~ 1.7 * rho^(1/4)")
    print("=" * 80)

    for rho in rhos:
        expected_L = 1.7 * rho ** 0.25
        print(f"\n--- rho = {rho} (expected L_max ~ {expected_L:.0f}) ---")

        results = []
        for seed in range(n_seeds):
            r = run_lepton_longest_path(rho=rho, beta_weak=4.0,
                                         n_chains=n_chains, seed=seed * 137)
            results.append(r)
            print(f"  seed={seed}: N={r['N']}, chains={r['n_chains']}, "
                  f"chain_len={r['chain_len_mean']:.1f} "
                  f"(max {r['chain_len_max']}), "
                  f"|c_w|=({r['c_weak_mag'][0]:.5f},{r['c_weak_mag'][1]:.5f}), "
                  f"r_mu_tau={r['r_mu_tau']:.5f}, "
                  f"t={r['time_total']:.1f}s",
                  flush=True)

        if results:
            mu_taus = [r['r_mu_tau'] for r in results if r['n_chains'] > 0]
            chain_lens = [r['chain_len_mean'] for r in results if r['n_chains'] > 0]
            max_lens = [r['chain_len_max'] for r in results if r['n_chains'] > 0]

            if mu_taus:
                mean = np.mean(mu_taus)
                sem = np.std(mu_taus) / np.sqrt(len(mu_taus))
                print(f"\n  >>> rho={rho}: m_mu/m_tau = {mean:.5f} +/- {sem:.5f} "
                      f"(expt: {EXP_MU_TAU}, factor {mean/EXP_MU_TAU:.2f}x)")
                print(f"      chain_len = {np.mean(chain_lens):.1f} "
                      f"(max {np.mean(max_lens):.0f})")

    print("\n" + "=" * 80)
    print("  KEY: If chain_len_max grows with rho AND r_mu_tau increases,")
    print("  the lepton undershoot is an algorithm artifact, not a physics gap.")
    print("=" * 80)
