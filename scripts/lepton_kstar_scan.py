#!/usr/bin/env python3
"""
Fine k-scan to pin down k* where r_amplitude = 0.0595 (experiment).

From the coarse scan: r crosses 0.0595 between k=5 (r=0.027) and k=10 (r=0.073).
This script does a fine scan in k = [5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]
with more seeds to reduce error bars.

Also runs at rho=5000 and rho=10000 to check if k* is density-independent
(which it should be if it's a physical momentum scale).

Requirements: pip install numpy scipy
Usage:
    python3 lepton_kstar_scan.py --quick    # rho=5000 only, 5 seeds
    python3 lepton_kstar_scan.py            # rho=5000+10000, 10 seeds
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


def build_causal_graph(points, box_size=1.0, rho=10000):
    N = len(points)
    times = points[:, 0]
    spatial = points[:, 1:]
    disc_scale = rho ** (-0.25)
    search_radius = min(box_size / 2, 15 * disc_scale)
    tree = cKDTree(spatial, boxsize=box_size)
    pairs = tree.query_pairs(r=search_radius, output_type='ndarray')
    if len(pairs) == 0:
        return {}, {}, 0
    i_arr, j_arr = pairs[:, 0], pairs[:, 1]
    dt = times[j_arr] - times[i_arr]
    dx = spatial[j_arr] - spatial[i_arr]
    dx = dx - box_size * np.round(dx / box_size)
    dist_sq = np.sum(dx ** 2, axis=1)
    mask_fwd = (dt > 0) & (dt ** 2 > dist_sq)
    mask_bwd = (dt < 0) & (dt ** 2 > dist_sq)
    pi = np.concatenate([i_arr[mask_fwd], j_arr[mask_bwd]])
    pj = np.concatenate([j_arr[mask_fwd], i_arr[mask_bwd]])
    dt_fwd = np.abs(np.concatenate([dt[mask_fwd], dt[mask_bwd]]))
    dsq_fwd = np.concatenate([dist_sq[mask_fwd], dist_sq[mask_bwd]])
    tau = np.sqrt(dt_fwd ** 2 - dsq_fwd)

    adj = defaultdict(list)
    link_tau = {}
    for idx in range(len(pi)):
        i, j = int(pi[idx]), int(pj[idx])
        adj[i].append(j)
        link_tau[(i, j)] = float(tau[idx])
    return adj, link_tau, len(pi)


def compute_forward_dp(adj):
    all_nodes = sorted(adj.keys())
    all_dest = set()
    for v in adj.values():
        all_dest.update(v)
    all_in_graph = sorted(set(all_nodes) | all_dest)

    dp_fwd = {n: 1 for n in all_in_graph}
    for node in reversed(all_in_graph):
        if node in adj:
            for nxt in adj[node]:
                candidate = 1 + dp_fwd.get(nxt, 1)
                if candidate > dp_fwd[node]:
                    dp_fwd[node] = candidate

    dp_back = {n: 1 for n in all_in_graph}
    for node in all_in_graph:
        if node in adj:
            for nxt in adj[node]:
                if dp_back[node] + 1 > dp_back.get(nxt, 1):
                    dp_back[nxt] = dp_back[node] + 1

    L_max = max(dp_back.values()) if dp_back else 0
    return dp_fwd, L_max, all_in_graph


def count_paths_by_length(adj, all_in_graph, L_max):
    pathcount = {n: {1: 1.0} for n in all_in_graph}
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
    total_by_length = {}
    for node in all_in_graph:
        for l, cnt in pathcount.get(node, {}).items():
            if l >= 2:
                total_by_length[l] = total_by_length.get(l, 0.0) + cnt
    return total_by_length


def sample_chains_guided(adj, dp_fwd, target_length, n_sample, rng, all_nodes):
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


def precompute_causet(rho, seed, n_sample_per_length):
    """Build the causal set once, return everything needed for k-scan."""
    pts, N = poisson_sprinkle_4d(rho, seed=seed)
    adj, link_tau, n_pairs = build_causal_graph(pts, rho=rho)
    dp_fwd, L_max, all_nodes = compute_forward_dp(adj)
    path_counts = count_paths_by_length(adj, all_nodes, L_max)

    # Build link set
    link_set = {}
    for src, dests in adj.items():
        for dst in dests:
            key = (src, dst)
            if key not in link_set:
                link_set[key] = len(link_set)

    rng_su2 = np.random.default_rng(seed + 9000)
    Us = random_su2_batch(len(link_set), rng_su2, beta=4.0)

    # Sample chains at each length (reuse across k values)
    rng_chain = np.random.default_rng(seed + 5000)
    s_ref = np.array([1, 0], dtype=complex)

    chain_data = []  # list of (true_count, holonomies, actions) per length
    for L in range(2, L_max + 1):
        chains = sample_chains_guided(adj, dp_fwd, L, n_sample_per_length,
                                       rng_chain, all_nodes)
        true_count = path_counts.get(L, 0.0)
        if not chains or true_count == 0:
            continue

        holonomies = []
        actions = []
        for chain in chains:
            W = np.eye(2, dtype=complex)
            S = 0.0
            for l in range(len(chain) - 1):
                key = (chain[l], chain[l + 1])
                if key in link_set:
                    W = Us[link_set[key]] @ W
                if key in link_tau:
                    S += link_tau[key]
            holonomies.append(W @ s_ref)
            actions.append(S)

        chain_data.append({
            'L': L,
            'true_count': true_count,
            'holonomies': np.array(holonomies),  # shape (n_found, 2)
            'actions': np.array(actions),          # shape (n_found,)
        })

    return N, L_max, chain_data


def evaluate_k(chain_data, k_val):
    """Given precomputed chain data, evaluate r_mu_tau at momentum k."""
    c_weighted = np.zeros(2, dtype=complex)
    total_weight = 0.0

    for cd in chain_data:
        phases = np.exp(1j * k_val * cd['actions'])  # shape (n_found,)
        # amplitude-weighted holonomy: sum of phase * holonomy
        weighted_hol = (phases[:, None] * cd['holonomies']).mean(axis=0)
        c_weighted += cd['true_count'] * weighted_hol
        total_weight += cd['true_count']

    if total_weight == 0:
        return 0.0
    c = c_weighted / total_weight
    cn = np.abs(c)
    m = np.sort(cn)[::-1]
    return float(m[1] / m[0]) if m[0] > 0 else 0.0


EXP_MU_TAU = 0.0595

if __name__ == "__main__":
    if "--quick" in sys.argv:
        rhos = [5000]
        n_seeds = 5
        n_sample = 200
    else:
        rhos = [5000, 10000]
        n_seeds = 10
        n_sample = 300

    # Fine k grid around the crossing region
    k_values = [4, 5, 6, 7, 7.5, 8, 8.5, 9, 9.5, 10, 11, 12, 14, 16, 20]

    print("=" * 90)
    print("  FINE k-SCAN: PINNING DOWN k* WHERE r_amplitude = 0.0595")
    print(f"  k = {k_values}")
    print(f"  beta_weak = 4, {n_seeds} seeds, {n_sample} samples/length")
    print("=" * 90)

    for rho in rhos:
        print(f"\n{'='*90}")
        print(f"  rho = {rho}")
        print(f"{'='*90}")

        # Precompute all causets (expensive part — done once per seed)
        print(f"\n  Precomputing {n_seeds} causal sets...", flush=True)
        precomputed = []
        for seed_idx in range(n_seeds):
            t0 = time.time()
            N, L_max, chain_data = precompute_causet(
                rho, seed=seed_idx * 137, n_sample_per_length=n_sample)
            dt = time.time() - t0
            print(f"    seed={seed_idx}: N={N}, L_max={L_max}, "
                  f"lengths={len(chain_data)}, t={dt:.1f}s", flush=True)
            precomputed.append(chain_data)

        # Scan k values (fast — just reweighting)
        print(f"\n  {'k':>6s}  {'r_amplitude':>12s}  {'SEM':>10s}  "
              f"{'factor':>8s}  {'status':>12s}")
        print(f"  {'-'*58}")

        best_k = None
        best_diff = float('inf')

        for k_val in k_values:
            rs = []
            for chain_data in precomputed:
                r = evaluate_k(chain_data, k_val)
                rs.append(r)

            mean = np.mean(rs)
            sem = np.std(rs) / np.sqrt(len(rs))
            diff = abs(mean - EXP_MU_TAU)

            if diff < best_diff:
                best_diff = diff
                best_k = k_val

            status = ""
            if diff / EXP_MU_TAU < 0.05:
                status = "*** MATCH ***"
            elif diff / EXP_MU_TAU < 0.1:
                status = "** CLOSE **"
            elif diff / EXP_MU_TAU < 0.2:
                status = "* near *"

            print(f"  {k_val:>6.1f}  {mean:>10.5f}+/-{sem:>6.4f}  "
                  f"{mean/EXP_MU_TAU:>7.2f}x  {status}", flush=True)

        print(f"\n  Best k: {best_k} (r = {best_diff + EXP_MU_TAU:.5f} or "
              f"{EXP_MU_TAU - best_diff:.5f}, diff = {best_diff:.5f})")

        # If we have a good candidate, do a super-fine scan around it
        if best_k is not None and best_diff / EXP_MU_TAU < 0.3:
            fine_ks = np.arange(best_k - 1.5, best_k + 1.6, 0.25)
            fine_ks = [round(k, 2) for k in fine_ks if k > 0]
            print(f"\n  --- Super-fine scan around k={best_k} ---")
            print(f"  {'k':>6s}  {'r_amplitude':>12s}  {'SEM':>10s}  "
                  f"{'factor':>8s}")
            print(f"  {'-'*42}")

            for k_val in fine_ks:
                rs = [evaluate_k(cd, k_val) for cd in precomputed]
                mean = np.mean(rs)
                sem = np.std(rs) / np.sqrt(len(rs))
                marker = " <--" if abs(mean - EXP_MU_TAU) / EXP_MU_TAU < 0.1 else ""
                print(f"  {k_val:>6.2f}  {mean:>10.5f}+/-{sem:>6.4f}  "
                      f"{mean/EXP_MU_TAU:>7.2f}x{marker}", flush=True)

    print(f"\n{'='*90}")
    print(f"  If k* is consistent across rho values, the amplitude phase")
    print(f"  exp(i*k*S) with S = sum(proper times) is the correct K/P")
    print(f"  prescription. k* = physical momentum scale in Planck units.")
    print(f"  Target: r = {EXP_MU_TAU}")
    print(f"{'='*90}")
