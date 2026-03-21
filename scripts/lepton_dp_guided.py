#!/usr/bin/env python3
"""
Lepton mass ratios with DP-GUIDED chain sampling + TRUE chain-count weighting.

v1 sampled 200 chains at every length L=2..L_max with equal weight.
This overcounts long chains (rare in the DAG) relative to short ones (abundant).

v2 fix: count the actual number of paths of each length L in the DAG via DP,
then weight the holonomy contribution at each L by that count.

  c_eff = (1/N_total) * sum_L  count(L) * <W_chain>_L * s_ref

where count(L) = total number of causal chains of length L in the DAG,
and <W_chain>_L is the average holonomy over sampled chains at length L.

Algorithm:
  1. Build causal DAG, compute forward DP (longest path from each node)
  2. Count paths at each length via DP: pathcount[node][l] = # paths of length l ending at node
  3. Sample n_sample chains at each L using forward-DP guidance
  4. Weight holonomy at each L by pathcount total at that L

Requirements: pip install numpy scipy
Usage:
    python3 lepton_dp_guided.py --quick      # fast test (~2 min)
    python3 lepton_dp_guided.py              # standard (~15 min)
    python3 lepton_dp_guided.py --full       # publication (~1 hr)
"""

import sys, numpy as np, time
from scipy.spatial import cKDTree
from collections import defaultdict


# ============================================================
# 1. Poisson sprinkling
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
        return {}, 0
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
    return adj, len(pi)


# ============================================================
# 3. Forward and backward DP
# ============================================================

def compute_dp(adj):
    """
    Compute both backward DP (longest path ending at node)
    and forward DP (longest path starting from node).
    """
    all_nodes = sorted(adj.keys())
    # Also collect all destination nodes
    all_dest = set()
    for v in adj.values():
        all_dest.update(v)
    all_in_graph = sorted(set(all_nodes) | all_dest)

    # Backward DP: dp_back[node] = longest path ending at node
    dp_back = {n: 1 for n in all_in_graph}
    for node in all_in_graph:
        if node in adj:
            for nxt in adj[node]:
                if dp_back[node] + 1 > dp_back.get(nxt, 1):
                    dp_back[nxt] = dp_back[node] + 1

    # Forward DP: dp_fwd[node] = longest path starting from node
    # Process in REVERSE topological order
    dp_fwd = {n: 1 for n in all_in_graph}
    for node in reversed(all_in_graph):
        if node in adj:
            for nxt in adj[node]:
                candidate = 1 + dp_fwd.get(nxt, 1)
                if candidate > dp_fwd[node]:
                    dp_fwd[node] = candidate

    L_max = max(dp_back.values()) if dp_back else 0
    return dp_back, dp_fwd, L_max, all_in_graph


def count_paths_by_length(adj, all_in_graph, L_max):
    """
    Count the number of directed paths of each length L in the DAG.

    pathcount[node][l] = number of paths of exactly l nodes ending at node.
    Total paths of length l = sum over all nodes of pathcount[node][l].

    Uses floats to avoid integer overflow (counts can be astronomical).
    Returns dict: L -> total_count.
    """
    # pathcount[node] = dict of {length: count}
    # Initialize: every node has exactly 1 path of length 1 (itself)
    pathcount = {n: {1: 1.0} for n in all_in_graph}

    # Process in topological order (already sorted by time)
    for node in all_in_graph:
        if node in adj:
            for nxt in adj[node]:
                if nxt not in pathcount:
                    pathcount[nxt] = {1: 1.0}
                for l, cnt in pathcount[node].items():
                    new_l = l + 1
                    if new_l > L_max:
                        continue
                    pathcount[nxt][new_l] = pathcount[nxt].get(new_l, 0.0) + cnt

    # Aggregate: total paths at each length
    total_by_length = {}
    for node in all_in_graph:
        for l, cnt in pathcount.get(node, {}).items():
            if l >= 2:  # only count chains with at least 2 nodes
                total_by_length[l] = total_by_length.get(l, 0.0) + cnt

    return total_by_length


# ============================================================
# 4. DP-guided chain sampling
# ============================================================

def sample_chains_guided(adj, dp_fwd, target_length, n_sample, rng, all_nodes):
    """
    Sample chains of exactly target_length using forward DP guidance.

    At each step, only follow neighbors with dp_fwd >= remaining steps needed.
    This guarantees we can reach the target length if such a path exists.
    """
    # Find valid start nodes: need dp_fwd[start] >= target_length
    valid_starts = [n for n in all_nodes if dp_fwd.get(n, 1) >= target_length]
    if not valid_starts:
        return []

    chains = []
    attempts = 0
    max_attempts = n_sample * 10

    while len(chains) < n_sample and attempts < max_attempts:
        attempts += 1
        start = valid_starts[rng.integers(len(valid_starts))]
        chain = [start]
        current = start
        visited = {start}
        success = True

        for step in range(target_length - 1):
            remaining = target_length - len(chain)
            # Filter neighbors: must not be visited AND must have enough forward reach
            candidates = []
            if current in adj:
                for nxt in adj[current]:
                    if nxt not in visited and dp_fwd.get(nxt, 1) >= remaining:
                        candidates.append(nxt)

            if not candidates:
                success = False
                break

            nxt = candidates[rng.integers(len(candidates))]
            chain.append(nxt)
            visited.add(nxt)
            current = nxt

        if success and len(chain) == target_length:
            chains.append(chain)

    return chains


# ============================================================
# 5. Random SU(2) matrices
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
# 6. Main: lepton K/P with DP-guided full distribution
# ============================================================

def run_lepton_dp_guided(rho=10000, beta_weak=4.0, n_sample_per_length=500, seed=42):
    t0 = time.time()

    pts, N = poisson_sprinkle_4d(rho, seed=seed)
    adj, n_pairs = build_causal_pairs(pts, rho=rho)
    dp_back, dp_fwd, L_max, all_nodes = compute_dp(adj)

    # Count true number of paths at each length
    path_counts = count_paths_by_length(adj, all_nodes, L_max)

    # Build link set for holonomy
    link_set = {}
    for src, dests in adj.items():
        for dst in dests:
            key = (src, dst)
            if key not in link_set:
                link_set[key] = len(link_set)

    rng_su2 = np.random.default_rng(seed + 9000)
    Us = random_su2_batch(len(link_set), rng_su2, beta=beta_weak)

    s_ref = np.array([1, 0], dtype=complex)
    c_weak_weighted = np.zeros(2, dtype=complex)
    total_weight = 0.0
    length_stats = {}

    rng_chain = np.random.default_rng(seed + 5000)

    for L in range(2, L_max + 1):
        chains = sample_chains_guided(adj, dp_fwd, L, n_sample_per_length,
                                       rng_chain, all_nodes)
        true_count = path_counts.get(L, 0.0)

        if not chains or true_count == 0:
            length_stats[L] = {'n_found': 0, 'true_count': true_count,
                               'c_perp': 0.0, 'c_para': 0.0, 'weight': 0.0}
            continue

        # Compute average holonomy for sampled chains at this length
        c_weak_L = np.zeros(2, dtype=complex)
        for chain in chains:
            W = np.eye(2, dtype=complex)
            for l in range(len(chain) - 1):
                key = (chain[l], chain[l + 1])
                if key in link_set:
                    W = Us[link_set[key]] @ W
            c_weak_L += W @ s_ref

        n_found = len(chains)
        c_avg = c_weak_L / n_found  # average holonomy at this length

        # Weight by true chain count: contribution = count(L) * <W>_L
        c_weak_weighted += true_count * c_avg
        total_weight += true_count

        length_stats[L] = {
            'n_found': n_found,
            'true_count': true_count,
            'c_perp': float(np.abs(c_avg[1])),
            'c_para': float(np.abs(c_avg[0])),
            'weight': true_count,
        }

    if total_weight == 0:
        return {'N': N, 'n_chains': 0, 'r_mu_tau': 0, 'L_max': L_max,
                'time': time.time() - t0, 'length_stats': {}}

    c_weak = c_weak_weighted / total_weight
    c_norm = np.abs(c_weak)
    masses = np.sort(c_norm)[::-1]
    r_mu_tau = float(masses[1] / masses[0]) if masses[0] > 0 else 0

    return {
        'N': N,
        'n_pairs': n_pairs,
        'total_weight': total_weight,
        'L_max': L_max,
        'c_weak_mag': (float(c_norm[0]), float(c_norm[1])),
        'c_weak_total': float(np.linalg.norm(c_weak)),
        'r_mu_tau': r_mu_tau,
        'r_e_tau': r_mu_tau ** 2,
        'length_stats': length_stats,
        'time': time.time() - t0,
    }


# ============================================================
# 7. Convergence study
# ============================================================

EXP_MU_TAU = 0.0595

if __name__ == "__main__":
    if "--quick" in sys.argv:
        rhos = [5000, 10000]
        n_seeds = 3
        n_sample = 200
    elif "--full" in sys.argv:
        rhos = [5000, 10000, 20000, 50000]
        n_seeds = 10
        n_sample = 1000
    else:
        rhos = [5000, 10000, 20000]
        n_seeds = 5
        n_sample = 500

    print("=" * 80)
    print("  LEPTON MASS RATIOS: DP-GUIDED CHAIN SAMPLING")
    print(f"  beta_weak = 4, {n_seeds} seeds, {n_sample} samples/length")
    print("  Forward DP guarantees sampling at ALL lengths up to L_max")
    print("=" * 80)

    all_summary = {}
    for rho in rhos:
        expected_L = 1.7 * rho ** 0.25
        print(f"\n--- rho = {rho} (expected L_max ~ {expected_L:.0f}) ---")
        results = []
        for seed in range(n_seeds):
            r = run_lepton_dp_guided(rho=rho, beta_weak=4.0,
                                      n_sample_per_length=n_sample,
                                      seed=seed * 137)
            results.append(r)

            # Chain length distribution summary
            if r['length_stats']:
                dist = [(L, s['n_found']) for L, s in sorted(r['length_stats'].items())
                        if s['n_found'] > 0]
                dist_str = ' '.join(f'L{L}:{n}' for L, n in dist)
            else:
                dist_str = 'none'

            print(f"  seed={seed}: N={r['N']}, L_max={r['L_max']}, "
                  f"|c|=({r['c_weak_mag'][0]:.4f},{r['c_weak_mag'][1]:.4f}), "
                  f"r={r['r_mu_tau']:.5f}, "
                  f"dist=[{dist_str}], "
                  f"t={r['time']:.1f}s",
                  flush=True)

        if results:
            mu_taus = [r['r_mu_tau'] for r in results if r.get('total_weight', 0) > 0]
            if mu_taus:
                mean = np.mean(mu_taus)
                sem = np.std(mu_taus) / np.sqrt(len(mu_taus))
                all_summary[rho] = (mean, sem)
                print(f"\n  >>> rho={rho}: m_mu/m_tau = {mean:.5f} +/- {sem:.5f} "
                      f"(expt: {EXP_MU_TAU}, factor {mean/EXP_MU_TAU:.2f}x)")

            # Print per-length holonomy buildup (averaged across seeds)
            all_lengths = set()
            for r in results:
                all_lengths.update(r['length_stats'].keys())
            if all_lengths:
                print(f"\n  Per-length holonomy buildup (weighted by true chain count):")
                print(f"    {'L':>3s}  {'sampled':>8s}  {'true_count':>12s}  {'wt_frac':>8s}  "
                      f"{'|c_para|':>10s}  {'|c_perp|':>10s}  {'ratio':>10s}")
                for L in sorted(all_lengths):
                    stats = [r['length_stats'].get(L, {'n_found': 0, 'c_perp': 0,
                             'c_para': 0, 'true_count': 0, 'weight': 0})
                             for r in results]
                    n_avg = np.mean([s['n_found'] for s in stats])
                    if n_avg < 0.5:
                        continue
                    true_count = np.mean([s.get('true_count', 0) for s in stats])
                    total_wt = np.mean([sum(s2.get('true_count', 0)
                                       for s2 in r['length_stats'].values())
                                       for r in results])
                    wt_frac = true_count / total_wt if total_wt > 0 else 0
                    c_perp = np.mean([s.get('c_perp', 0) for s in stats])
                    c_para = np.mean([s.get('c_para', 0) for s in stats])
                    ratio = c_perp / c_para if c_para > 1e-10 else 0
                    print(f"    {L:>3d}  {n_avg:>8.0f}  {true_count:>12.0f}  {wt_frac:>7.1%}  "
                          f"{c_para:>10.5f}  {c_perp:>10.5f}  {ratio:>10.5f}")

    print("\n" + "=" * 80)
    print("  SUMMARY")
    print("=" * 80)
    print(f"  {'rho':>8s}  {'m_mu/m_tau':>12s}  {'SEM':>10s}  {'Factor':>8s}")
    print("-" * 46)
    for rho, (mean, sem) in all_summary.items():
        print(f"  {rho:>8d}  {mean:>12.5f}  {sem:>10.5f}  {mean/EXP_MU_TAU:>7.2f}x")
    print(f"  {'Expt':>8s}  {EXP_MU_TAU:>12.5f}")
    print("=" * 80)
    print("\n  KEY: True chain-count weighting means short chains (near identity)")
    print("  dominate by count, while long chains provide the perpendicular tail.")
    print("  The weighted average should be much closer to expt than equal-weight.")
    print("=" * 80)
