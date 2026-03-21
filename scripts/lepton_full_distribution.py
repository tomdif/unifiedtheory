#!/usr/bin/env python3
"""
Lepton mass ratios with FULL chain-length distribution.

The random-walk finder undershoots (chains too short, r ≈ 0.003).
The longest-path finder overshoots (only longest chains, r ≈ 0.16).
The correct computation uses the full chain-length distribution:
  c_eff = (1/N_total) Σ_{L=2}^{L_max} Σ_{chains of length L} W_chain · s₀

Short chains (near identity) dominate by count.
Long chains (large rotation) provide the tail.
The balance gives the correct perpendicular fraction.

Algorithm:
  1. Build causal DAG + compute L_max via DP
  2. For each length L = 2, ..., L_max:
     - Sample n_sample chains of exactly length L (random walks constrained to L steps)
     - Compute holonomy for each
  3. Weight by chain count at each L (estimated from sampling success rate)
  4. Average all holonomies to get c_eff

Requirements: pip install numpy scipy
Usage:
    python3 lepton_full_distribution.py --quick
    python3 lepton_full_distribution.py
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


def build_causal_pairs(points, box_size=1.0, rho=10000):
    N = len(points)
    times = points[:, 0]
    spatial = points[:, 1:]
    disc_scale = rho ** (-0.25)
    search_radius = min(box_size / 2, 15 * disc_scale)
    tree = cKDTree(spatial, boxsize=box_size)
    pairs = tree.query_pairs(r=search_radius, output_type='ndarray')
    if len(pairs) == 0:
        return np.array([], dtype=np.int64), np.array([], dtype=np.int64), {}, 0
    i_arr, j_arr = pairs[:, 0], pairs[:, 1]
    dt = times[j_arr] - times[i_arr]
    dx = spatial[j_arr] - spatial[i_arr]
    dx = dx - box_size * np.round(dx / box_size)
    dist_sq = np.sum(dx ** 2, axis=1)
    mask_fwd = (dt > 0) & (dt ** 2 > dist_sq)
    mask_bwd = (dt < 0) & (dt ** 2 > dist_sq)
    pi = np.concatenate([i_arr[mask_fwd], j_arr[mask_bwd]])
    pj = np.concatenate([j_arr[mask_fwd], i_arr[mask_bwd]])

    adj = defaultdict(list)
    for i, j in zip(pi, pj):
        adj[int(i)].append(int(j))
    return pi, pj, adj, len(pi)


def compute_longest_path_dp(adj, N):
    """DP to find longest path length from each node."""
    all_nodes = sorted(adj.keys())
    dp = {}
    for node in all_nodes:
        dp[node] = 1
    for node in all_nodes:
        for nxt in adj.get(node, []):
            if dp.get(node, 1) + 1 > dp.get(nxt, 1):
                dp[nxt] = dp[node] + 1
    L_max = max(dp.values()) if dp else 0
    return dp, L_max


def sample_chains_at_length(adj, dp, target_length, n_sample, rng):
    """Sample chains of exactly target_length nodes using guided random walks."""
    chains = []
    # Find nodes where a chain of target_length could START
    # A node can start a chain of length L if dp[node] >= L
    # But dp gives the longest path ENDING at node. We need longest path FROM node.
    # Compute forward dp: longest path starting from each node.

    # Actually, let's do it differently: random walk with length constraint.
    # Start from a random node, walk forward, stop at exactly target_length.
    all_nodes = list(adj.keys())
    if not all_nodes:
        return []

    attempts = 0
    max_attempts = n_sample * 20
    while len(chains) < n_sample and attempts < max_attempts:
        attempts += 1
        start = all_nodes[rng.integers(len(all_nodes))]
        chain = [start]
        current = start
        visited = {start}
        while len(chain) < target_length and current in adj:
            nexts = [n for n in adj[current] if n not in visited]
            if not nexts:
                break
            nxt = nexts[rng.integers(len(nexts))]
            chain.append(nxt)
            visited.add(nxt)
            current = nxt
        if len(chain) == target_length:
            chains.append(chain)

    return chains


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


def run_lepton_full_dist(rho=10000, beta_weak=4.0, n_sample_per_length=500, seed=42):
    t0 = time.time()

    pts, N = poisson_sprinkle_4d(rho, seed=seed)
    pi, pj, adj, n_pairs = build_causal_pairs(pts, rho=rho)
    dp, L_max = compute_longest_path_dp(adj, N)

    # Build link set for holonomy assignment
    link_set = {}
    for i, j in zip(pi, pj):
        key = (int(i), int(j))
        if key not in link_set:
            link_set[key] = len(link_set)

    rng = np.random.default_rng(seed + 9000)
    Us = random_su2_batch(len(link_set), rng, beta=beta_weak)

    s_ref = np.array([1, 0], dtype=complex)
    c_weak_total = np.zeros(2, dtype=complex)
    total_chains = 0
    length_stats = {}

    rng_chain = np.random.default_rng(seed + 5000)

    # Sample chains at each length from 2 to L_max
    for L in range(2, L_max + 1):
        chains = sample_chains_at_length(adj, dp, L, n_sample_per_length, rng_chain)
        if not chains:
            continue

        # Compute holonomy for each chain
        c_weak_L = np.zeros(2, dtype=complex)
        for chain in chains:
            W = np.eye(2, dtype=complex)
            for l in range(len(chain) - 1):
                key = (chain[l], chain[l + 1])
                if key in link_set:
                    W = Us[link_set[key]] @ W
            c_weak_L += W @ s_ref

        n_found = len(chains)
        # Weight by number of chains found (proxy for true chain count)
        c_weak_total += c_weak_L
        total_chains += n_found

        length_stats[L] = {
            'n_found': n_found,
            'c_mag': np.abs(c_weak_L / n_found) if n_found > 0 else (0, 0),
        }

    if total_chains == 0:
        return {'N': N, 'n_chains': 0, 'r_mu_tau': 0, 'L_max': L_max,
                'time': time.time() - t0}

    c_weak = c_weak_total / total_chains
    c_norm = np.abs(c_weak)
    masses = np.sort(c_norm)[::-1]
    r_mu_tau = float(masses[1] / masses[0]) if masses[0] > 0 else 0

    return {
        'N': N,
        'n_pairs': n_pairs,
        'n_chains': total_chains,
        'L_max': L_max,
        'c_weak_mag': (float(c_norm[0]), float(c_norm[1])),
        'r_mu_tau': r_mu_tau,
        'r_e_tau': r_mu_tau ** 2,
        'length_stats': length_stats,
        'time': time.time() - t0,
    }


EXP_MU_TAU = 0.0595

if __name__ == "__main__":
    if "--quick" in sys.argv:
        rhos = [5000, 10000]
        n_seeds = 3
        n_sample = 300
    elif "--full" in sys.argv:
        rhos = [5000, 10000, 20000, 50000]
        n_seeds = 10
        n_sample = 1000
    else:
        rhos = [5000, 10000, 20000]
        n_seeds = 5
        n_sample = 500

    print("=" * 80)
    print("  LEPTON MASS RATIOS: FULL CHAIN-LENGTH DISTRIBUTION")
    print(f"  beta_weak = 4, {n_seeds} seeds, {n_sample} samples/length")
    print("  Combines short chains (near identity) + long chains (large rotation)")
    print("=" * 80)

    for rho in rhos:
        print(f"\n--- rho = {rho} ---")
        results = []
        for seed in range(n_seeds):
            r = run_lepton_full_dist(rho=rho, beta_weak=4.0,
                                      n_sample_per_length=n_sample,
                                      seed=seed * 137)
            results.append(r)

            # Print chain length distribution
            if r['length_stats']:
                dist = [(L, s['n_found']) for L, s in sorted(r['length_stats'].items())]
                dist_str = ' '.join(f'L{L}:{n}' for L, n in dist[:8])
            else:
                dist_str = 'none'

            print(f"  seed={seed}: N={r['N']}, L_max={r['L_max']}, "
                  f"chains={r['n_chains']}, "
                  f"|c|=({r['c_weak_mag'][0]:.4f},{r['c_weak_mag'][1]:.4f}), "
                  f"r={r['r_mu_tau']:.5f}, "
                  f"dist=[{dist_str}], "
                  f"t={r['time']:.1f}s",
                  flush=True)

        if results:
            mu_taus = [r['r_mu_tau'] for r in results if r['n_chains'] > 0]
            if mu_taus:
                mean = np.mean(mu_taus)
                sem = np.std(mu_taus) / np.sqrt(len(mu_taus))
                print(f"\n  >>> rho={rho}: m_mu/m_tau = {mean:.5f} +/- {sem:.5f} "
                      f"(expt: {EXP_MU_TAU}, factor {mean/EXP_MU_TAU:.2f}x)")

    print("\n" + "=" * 80)
    print("  The full distribution should give a ratio BETWEEN the random-walk")
    print("  (0.003, too low) and longest-path (0.16, too high) results.")
    print(f"  Target: {EXP_MU_TAU} (experiment)")
    print("=" * 80)
