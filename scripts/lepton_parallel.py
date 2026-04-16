#!/usr/bin/env python3
"""
Parallelized lepton mass ratio computation.
Uses all CPU cores to run seeds concurrently.
"""

import sys, os, numpy as np, time
from multiprocessing import Pool, cpu_count
from scipy.spatial import cKDTree
from collections import defaultdict


def poisson_sprinkle_4d(rho, box_size=1.0, seed=42):
    rng = np.random.default_rng(seed)
    N = rng.poisson(rho * box_size ** 4)
    pts = rng.uniform(0, box_size, size=(N, 4)).astype(np.float64)
    return pts[np.argsort(pts[:, 0])], N


def build_causal_pairs(points, box_size=1.0, rho=10000):
    N = len(points)
    times, spatial = points[:, 0], points[:, 1:]
    r = min(box_size / 2, 15 * rho ** (-0.25))
    tree = cKDTree(spatial, boxsize=box_size)
    pairs = tree.query_pairs(r=r, output_type='ndarray')
    if len(pairs) == 0:
        return np.array([]), np.array([]), {}, 0
    i, j = pairs[:, 0], pairs[:, 1]
    dt = times[j] - times[i]
    dx = spatial[j] - spatial[i]
    dx -= box_size * np.round(dx / box_size)
    d2 = np.sum(dx**2, axis=1)
    mf, mb = (dt > 0) & (dt**2 > d2), (dt < 0) & (dt**2 > d2)
    pi = np.concatenate([i[mf], j[mb]])
    pj = np.concatenate([j[mf], i[mb]])
    adj = defaultdict(list)
    for a, b in zip(pi, pj):
        adj[int(a)].append(int(b))
    return pi, pj, adj, len(pi)


def compute_longest_path_dp(adj):
    all_nodes = sorted(adj.keys())
    dp = {n: 1 for n in all_nodes}
    for node in all_nodes:
        for nxt in adj.get(node, []):
            if nxt in dp and dp[node] + 1 > dp.get(nxt, 1):
                dp[nxt] = dp[node] + 1
    return dp, max(dp.values()) if dp else 0


def sample_chains_at_length(adj, target_length, n_sample, rng):
    all_nodes = list(adj.keys())
    if not all_nodes:
        return []
    chains, attempts = [], 0
    while len(chains) < n_sample and attempts < n_sample * 20:
        attempts += 1
        start = all_nodes[rng.integers(len(all_nodes))]
        chain = [start]
        current, visited = start, {start}
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


def run_single_seed(args):
    """Run one seed — designed for multiprocessing Pool."""
    rho, beta_weak, n_sample, seed = args
    t0 = time.time()

    pts, N = poisson_sprinkle_4d(rho, seed=seed)
    pi, pj, adj, n_pairs = build_causal_pairs(pts, rho=rho)
    dp, L_max = compute_longest_path_dp(adj)

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
    rng_chain = np.random.default_rng(seed + 5000)

    for L in range(2, L_max + 1):
        chains = sample_chains_at_length(adj, L, n_sample, rng_chain)
        if not chains:
            continue
        for chain in chains:
            W = np.eye(2, dtype=complex)
            for l in range(len(chain) - 1):
                key = (chain[l], chain[l + 1])
                if key in link_set:
                    W = Us[link_set[key]] @ W
            c_weak_total += W @ s_ref
        total_chains += len(chains)

    if total_chains == 0:
        return {'seed': seed, 'rho': rho, 'r_mu_tau': 0, 'N': N,
                'n_chains': 0, 'L_max': L_max, 'time': time.time() - t0}

    c_weak = c_weak_total / total_chains
    c_norm = np.abs(c_weak)
    masses = np.sort(c_norm)[::-1]
    r = float(masses[1] / masses[0]) if masses[0] > 0 else 0

    return {'seed': seed, 'rho': rho, 'r_mu_tau': r, 'N': N,
            'n_chains': total_chains, 'L_max': L_max, 'time': time.time() - t0}


EXP = 0.0595

if __name__ == "__main__":
    ncpu = cpu_count()
    print(f"Using {ncpu} cores")

    if "--quick" in sys.argv:
        rhos = [5000, 10000]
        n_seeds = 5
        n_sample = 300
    elif "--full" in sys.argv:
        rhos = [5000, 10000, 20000]
        n_seeds = 10
        n_sample = 500
    else:
        rhos = [5000, 10000, 20000]
        n_seeds = 5
        n_sample = 500

    print("=" * 70)
    print("  PARALLELIZED LEPTON MASS RATIOS (count-weighted, k=0)")
    print(f"  {n_seeds} seeds/rho, {n_sample} samples/length, {ncpu} cores")
    print("=" * 70)

    for rho in rhos:
        t0 = time.time()
        args = [(rho, 4.0, n_sample, s * 137) for s in range(n_seeds)]

        with Pool(min(ncpu, n_seeds)) as pool:
            results = pool.map(run_single_seed, args)

        mu_taus = [r['r_mu_tau'] for r in results if r['n_chains'] > 0]
        for r in results:
            print(f"  rho={rho}, seed={r['seed']//137}: "
                  f"r={r['r_mu_tau']:.5f} L_max={r['L_max']} "
                  f"chains={r['n_chains']} t={r['time']:.1f}s", flush=True)

        if mu_taus:
            mean = np.mean(mu_taus)
            sem = np.std(mu_taus) / np.sqrt(len(mu_taus))
            print(f"\n  >>> rho={rho}: r_mu_tau = {mean:.5f} +/- {sem:.5f} "
                  f"(expt: {EXP}, factor {mean/EXP:.2f}x) "
                  f"[{time.time()-t0:.0f}s total]\n")

    print("=" * 70)
