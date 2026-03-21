#!/usr/bin/env python3
"""
Lepton mass ratios with AMPLITUDE-WEIGHTED holonomy sum.

The missing physics: the K/P Yukawa matrix element is not just the holonomy
sum, but the amplitude-weighted holonomy sum:

  c_eff = (1/Z) * sum_gamma  z(gamma) * U_gamma * s_0

where z(gamma) = exp(i * k * S(gamma)) is the propagation amplitude,
S(gamma) = sum of proper times along the chain, and k is the momentum scale.

The amplitude phase decorrelates long chains (random walk in phase),
providing a physical mechanism for chain weighting that is neither
equal-count nor pure combinatorial.

For a causal link (i,j) with time separation dt and spatial separation dx,
the proper time is tau = sqrt(dt^2 - |dx|^2). The chain action is
S(gamma) = sum_{links} tau_l.

The momentum scale k sets how fast the phase winds. We scan k to find
the value that gives the experimental ratio r = 0.0595.

Requirements: pip install numpy scipy
Usage:
    python3 lepton_amplitude.py --quick       # k-scan at rho=5000
    python3 lepton_amplitude.py               # k-scan at rho=5000,10000
    python3 lepton_amplitude.py --full        # k-scan + convergence
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
# 2. Causal pairs with proper time computation
# ============================================================

def build_causal_graph(points, box_size=1.0, rho=10000):
    """Build causal DAG and compute proper time for each link."""
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
    # Proper time for each causal link: tau = sqrt(dt^2 - |dx|^2)
    dt_fwd = np.abs(np.concatenate([dt[mask_fwd], dt[mask_bwd]]))
    dsq_fwd = np.concatenate([dist_sq[mask_fwd], dist_sq[mask_bwd]])
    tau = np.sqrt(dt_fwd ** 2 - dsq_fwd)

    adj = defaultdict(list)
    link_tau = {}  # (i,j) -> proper time
    for idx in range(len(pi)):
        i, j = int(pi[idx]), int(pj[idx])
        adj[i].append(j)
        link_tau[(i, j)] = float(tau[idx])

    return adj, link_tau, len(pi)


# ============================================================
# 3. Forward DP
# ============================================================

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

    # Also compute backward dp for L_max
    dp_back = {n: 1 for n in all_in_graph}
    for node in all_in_graph:
        if node in adj:
            for nxt in adj[node]:
                if dp_back[node] + 1 > dp_back.get(nxt, 1):
                    dp_back[nxt] = dp_back[node] + 1

    L_max = max(dp_back.values()) if dp_back else 0
    return dp_fwd, L_max, all_in_graph


# ============================================================
# 4. Count paths by length (for diagnostics)
# ============================================================

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


# ============================================================
# 5. DP-guided chain sampling
# ============================================================

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


# ============================================================
# 6. Random SU(2) matrices
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
# 7. Amplitude-weighted holonomy computation
# ============================================================

def run_amplitude_weighted(rho=10000, beta_weak=4.0, k_momentum=1.0,
                            n_sample_per_length=300, seed=42):
    """
    Compute lepton mass ratio with amplitude-weighted holonomy:
      c_eff = (1/Z) * sum_gamma  exp(i*k*S(gamma)) * U_gamma * s_0
    where S(gamma) = sum of proper times along the chain.
    """
    t0 = time.time()

    pts, N = poisson_sprinkle_4d(rho, seed=seed)
    adj, link_tau, n_pairs = build_causal_graph(pts, rho=rho)
    dp_fwd, L_max, all_nodes = compute_forward_dp(adj)
    path_counts = count_paths_by_length(adj, all_nodes, L_max)

    # Build link set for holonomy assignment
    link_set = {}
    for src, dests in adj.items():
        for dst in dests:
            key = (src, dst)
            if key not in link_set:
                link_set[key] = len(link_set)

    rng_su2 = np.random.default_rng(seed + 9000)
    Us = random_su2_batch(len(link_set), rng_su2, beta=beta_weak)

    s_ref = np.array([1, 0], dtype=complex)
    rng_chain = np.random.default_rng(seed + 5000)

    # Three computations in parallel:
    # 1. Count-weighted (no amplitude) - baseline
    # 2. Amplitude-weighted with phase exp(i*k*S)
    # 3. |amplitude|-weighted (magnitude only, no phase)
    c_count = np.zeros(2, dtype=complex)
    c_amplitude = np.zeros(2, dtype=complex)
    c_magweight = np.zeros(2, dtype=complex)
    Z_count = 0.0
    Z_amplitude = 0.0 + 0j
    Z_magweight = 0.0
    length_stats = {}

    for L in range(2, L_max + 1):
        chains = sample_chains_guided(adj, dp_fwd, L, n_sample_per_length,
                                       rng_chain, all_nodes)
        true_count = path_counts.get(L, 0.0)
        if not chains or true_count == 0:
            length_stats[L] = {'n_found': 0, 'true_count': true_count}
            continue

        n_found = len(chains)

        # Compute holonomy AND action for each sampled chain
        c_L_count = np.zeros(2, dtype=complex)
        c_L_amp = np.zeros(2, dtype=complex)
        c_L_mag = np.zeros(2, dtype=complex)
        phases = []
        actions = []

        for chain in chains:
            W = np.eye(2, dtype=complex)
            S = 0.0  # chain action = sum of proper times
            for l in range(len(chain) - 1):
                key = (chain[l], chain[l + 1])
                if key in link_set:
                    W = Us[link_set[key]] @ W
                if key in link_tau:
                    S += link_tau[key]

            holonomy = W @ s_ref
            phase = np.exp(1j * k_momentum * S)
            mag = np.exp(-abs(k_momentum) * S * 0)  # magnitude = 1 for unitary phase

            c_L_count += holonomy
            c_L_amp += phase * holonomy
            c_L_mag += holonomy  # same as count for now

            phases.append(float(np.angle(phase)))
            actions.append(S)

        # Average over samples, then weight by true chain count
        avg_count = c_L_count / n_found
        avg_amp = c_L_amp / n_found

        c_count += true_count * avg_count
        c_amplitude += true_count * avg_amp
        Z_count += true_count
        Z_amplitude += true_count  # normalization is by total chain count

        # Per-length diagnostics
        c_avg_count = c_L_count / n_found
        c_avg_amp = c_L_amp / n_found
        length_stats[L] = {
            'n_found': n_found,
            'true_count': true_count,
            'action_mean': np.mean(actions),
            'action_std': np.std(actions),
            'phase_mean': np.mean(phases),
            'phase_std': np.std(phases),
            # Count-weighted holonomy at this L
            'count_para': float(np.abs(c_avg_count[0])),
            'count_perp': float(np.abs(c_avg_count[1])),
            # Amplitude-weighted holonomy at this L
            'amp_para': float(np.abs(c_avg_amp[0])),
            'amp_perp': float(np.abs(c_avg_amp[1])),
        }

    if Z_count == 0:
        return {'N': N, 'r_count': 0, 'r_amplitude': 0, 'L_max': L_max,
                'time': time.time() - t0, 'length_stats': {}}

    # Finalize both computations
    c_count /= Z_count
    c_amplitude /= Z_count  # same normalization

    cn_count = np.abs(c_count)
    cn_amp = np.abs(c_amplitude)

    m_count = np.sort(cn_count)[::-1]
    m_amp = np.sort(cn_amp)[::-1]

    r_count = float(m_count[1] / m_count[0]) if m_count[0] > 0 else 0
    r_amp = float(m_amp[1] / m_amp[0]) if m_amp[0] > 0 else 0

    return {
        'N': N,
        'n_pairs': n_pairs,
        'L_max': L_max,
        'k_momentum': k_momentum,
        'r_count': r_count,        # count-weighted (no phase)
        'r_amplitude': r_amp,       # amplitude-weighted (with phase)
        'c_count_mag': (float(cn_count[0]), float(cn_count[1])),
        'c_amp_mag': (float(cn_amp[0]), float(cn_amp[1])),
        'length_stats': length_stats,
        'time': time.time() - t0,
    }


# ============================================================
# 8. Main: k-scan and convergence
# ============================================================

EXP_MU_TAU = 0.0595

if __name__ == "__main__":
    if "--quick" in sys.argv:
        rhos = [5000]
        n_seeds = 3
        n_sample = 200
        k_values = [0, 1, 2, 5, 10, 20, 50, 100]
    elif "--full" in sys.argv:
        rhos = [5000, 10000, 20000]
        n_seeds = 5
        n_sample = 500
        k_values = [0, 1, 2, 5, 10, 15, 20, 30, 50, 75, 100, 150, 200]
    else:
        rhos = [5000, 10000]
        n_seeds = 3
        n_sample = 300
        k_values = [0, 1, 2, 5, 10, 20, 50, 100, 200]

    print("=" * 90)
    print("  LEPTON MASS RATIOS: AMPLITUDE-WEIGHTED HOLONOMY")
    print(f"  c_eff = (1/Z) * sum_gamma exp(i*k*S(gamma)) * U_gamma * s_0")
    print(f"  S(gamma) = sum of proper times along chain")
    print(f"  Scanning k = {k_values}")
    print(f"  beta_weak = 4, {n_seeds} seeds, {n_sample} samples/length")
    print("=" * 90)

    for rho in rhos:
        print(f"\n{'='*90}")
        print(f"  rho = {rho}")
        print(f"{'='*90}")

        # First run k=0 (count-weighted baseline) and show chain structure
        print(f"\n  --- Chain structure (k=0 baseline) ---")
        r0 = run_amplitude_weighted(rho=rho, k_momentum=0, n_sample_per_length=n_sample,
                                     seed=0)
        print(f"  L_max={r0['L_max']}, r_count={r0['r_count']:.5f}")
        print(f"    {'L':>3s}  {'count':>12s}  {'wt%':>6s}  {'<S>':>8s}  "
              f"{'count_r':>8s}  {'amp_r':>8s}")
        total_ct = sum(s.get('true_count', 0) for s in r0['length_stats'].values())
        for L in sorted(r0['length_stats'].keys()):
            s = r0['length_stats'][L]
            if s['n_found'] == 0:
                continue
            wt = s['true_count'] / total_ct * 100 if total_ct > 0 else 0
            cr = s['count_perp'] / s['count_para'] if s['count_para'] > 1e-10 else 0
            ar = s['amp_perp'] / s['amp_para'] if s['amp_para'] > 1e-10 else 0
            print(f"    {L:>3d}  {s['true_count']:>12.0f}  {wt:>5.1f}%  "
                  f"{s['action_mean']:>8.4f}  {cr:>8.4f}  {ar:>8.4f}")

        # k-scan
        print(f"\n  --- k-scan ---")
        print(f"  {'k':>6s}  {'r_count':>10s}  {'r_amplitude':>12s}  "
              f"{'factor_c':>9s}  {'factor_a':>9s}  {'time':>6s}")
        print(f"  {'-'*60}")

        for k_val in k_values:
            results = []
            for seed in range(n_seeds):
                r = run_amplitude_weighted(rho=rho, k_momentum=k_val,
                                            n_sample_per_length=n_sample,
                                            seed=seed * 137)
                results.append(r)

            rc_mean = np.mean([r['r_count'] for r in results])
            ra_mean = np.mean([r['r_amplitude'] for r in results])
            ra_sem = np.std([r['r_amplitude'] for r in results]) / np.sqrt(len(results))
            avg_time = np.mean([r['time'] for r in results])

            marker = ""
            if abs(ra_mean - EXP_MU_TAU) / EXP_MU_TAU < 0.2:
                marker = " <-- CLOSE!"
            if abs(ra_mean - EXP_MU_TAU) / EXP_MU_TAU < 0.1:
                marker = " <-- MATCH!"

            print(f"  {k_val:>6.0f}  {rc_mean:>10.5f}  "
                  f"{ra_mean:>10.5f}+/-{ra_sem:>6.4f}  "
                  f"{rc_mean/EXP_MU_TAU:>8.2f}x  "
                  f"{ra_mean/EXP_MU_TAU:>8.2f}x  "
                  f"{avg_time:>5.0f}s{marker}",
                  flush=True)

    print(f"\n{'='*90}")
    print(f"  INTERPRETATION:")
    print(f"  k=0: count-weighted baseline (no amplitude phase)")
    print(f"  k>0: amplitude phase exp(i*k*S) decorrelates long chains")
    print(f"  If there exists k* where r_amplitude = {EXP_MU_TAU}, the amplitude")
    print(f"  phase is the missing physics. k* then determines the momentum scale.")
    print(f"  Target: {EXP_MU_TAU} (experiment)")
    print(f"{'='*90}")
