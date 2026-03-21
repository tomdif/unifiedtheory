#!/usr/bin/env python3
"""
Cabibbo angle: 20 seeds at rho=10K for publishable error bars.

From quick run (3 seeds, rho=5K):
  k=0:   |V_us| = 0.217 ± 0.103 (0.97x expt), theta_C = 12.8 deg
  k=9.5: |V_us| = 0.257 ± 0.079 (1.14x expt), theta_C = 15.0 deg

With 20 seeds, SEM ≈ σ/√20 ≈ 0.023 → tight enough to confirm or reject.

Also diagnoses the Wolfenstein hierarchy problem:
  |V_us| ~ λ ≈ 0.22
  |V_cb| ~ λ² ≈ 0.04
  |V_ub| ~ λ³ ≈ 0.004
Per-length breakdown shows if chain length drives the hierarchy.

Requirements: pip install numpy scipy
Usage:
    python3 cabibbo_20seed.py
"""

import sys, numpy as np, time
from scipy.spatial import cKDTree
from collections import defaultdict


def poisson_sprinkle_4d(rho, box_size=1.0, seed=42):
    rng = np.random.default_rng(seed)
    N = rng.poisson(rho * box_size ** 4)
    pts = rng.uniform(0, box_size, size=(N, 4)).astype(np.float64)
    return pts[np.argsort(pts[:, 0])], N


def build_causal_graph(points, box_size=1.0, rho=10000):
    N = len(points)
    times, spatial = points[:, 0], points[:, 1:]
    r = min(box_size / 2, 15 * rho ** (-0.25))
    tree = cKDTree(spatial, boxsize=box_size)
    pairs = tree.query_pairs(r=r, output_type='ndarray')
    if len(pairs) == 0:
        return {}, {}, 0
    i, j = pairs[:, 0], pairs[:, 1]
    dt = times[j] - times[i]
    dx = spatial[j] - spatial[i]
    dx -= box_size * np.round(dx / box_size)
    d2 = np.sum(dx**2, axis=1)
    mf, mb = (dt > 0) & (dt**2 > d2), (dt < 0) & (dt**2 > d2)
    pi = np.concatenate([i[mf], j[mb]])
    pj = np.concatenate([j[mf], i[mb]])
    dt_fwd = np.abs(np.concatenate([dt[mf], dt[mb]]))
    dsq_fwd = np.concatenate([d2[mf], d2[mb]])
    tau = np.sqrt(dt_fwd**2 - dsq_fwd)

    adj = defaultdict(list)
    link_tau = {}
    for idx in range(len(pi)):
        a, b = int(pi[idx]), int(pj[idx])
        adj[a].append(b)
        link_tau[(a, b)] = float(tau[idx])
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
                c = 1 + dp_fwd.get(nxt, 1)
                if c > dp_fwd[node]:
                    dp_fwd[node] = c

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
    total = {}
    for node in all_in_graph:
        for l, cnt in pathcount.get(node, {}).items():
            if l >= 2:
                total[l] = total.get(l, 0.0) + cnt
    return total


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
            candidates = [nxt for nxt in adj.get(current, [])
                          if nxt not in visited and dp_fwd.get(nxt, 1) >= remaining]
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


def random_su3_batch(n, rng, beta=6.0):
    Us = np.zeros((n, 3, 3), dtype=complex)
    for k in range(n):
        H = rng.standard_normal((3, 3)) + 1j * rng.standard_normal((3, 3))
        H = (H + H.conj().T) / 2
        H -= np.trace(H) / 3 * np.eye(3)
        eigvals, eigvecs = np.linalg.eig(1j * H / beta)
        U = eigvecs @ np.diag(np.exp(eigvals)) @ np.linalg.inv(eigvecs)
        det = np.linalg.det(U)
        U *= (det.conj() / abs(det + 1e-30)) ** (1/3)
        Us[k] = U
    return Us


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


def compute_ckm(rho=10000, beta_color=6.0, beta_weak=4.0,
                k_momentum=0.0, n_sample_per_length=200, seed=42):
    t0 = time.time()
    pts, N = poisson_sprinkle_4d(rho, seed=seed)
    adj, link_tau, n_pairs = build_causal_graph(pts, rho=rho)
    dp_fwd, L_max, all_nodes = compute_forward_dp(adj)
    path_counts = count_paths_by_length(adj, all_nodes, L_max)

    link_set = {}
    for src, dests in adj.items():
        for dst in dests:
            key = (src, dst)
            if key not in link_set:
                link_set[key] = len(link_set)
    n_links = len(link_set)

    rng_c = np.random.default_rng(seed + 5000)
    rng_w = np.random.default_rng(seed + 9000)
    rng_u1 = np.random.default_rng(seed + 7000)

    Us_color = random_su3_batch(n_links, rng_c, beta_color)
    Us_weak = random_su2_batch(n_links, rng_w, beta_weak)
    u1_angles = rng_u1.uniform(0, 2 * np.pi / beta_weak, n_links)

    Y_uR, Y_dR, Y_Q = -2/3, 1/3, 1/6

    s_weak_ref = np.array([1, 0], dtype=complex)
    color_sections = [np.array([1, 0, 0], dtype=complex),
                      np.array([0, 1, 0], dtype=complex),
                      np.array([0, 0, 1], dtype=complex)]

    rng_chain = np.random.default_rng(seed + 3000)

    Y_up = np.zeros((3, 3), dtype=complex)
    Y_down = np.zeros((3, 3), dtype=complex)
    total_weight = 0.0

    # Per-length CKM diagnostics
    length_ckm = {}

    for L in range(2, L_max + 1):
        chains = sample_chains_guided(adj, dp_fwd, L, n_sample_per_length,
                                       rng_chain, all_nodes)
        true_count = path_counts.get(L, 0.0)
        if not chains or true_count == 0:
            continue

        n_found = len(chains)
        Y_up_L = np.zeros((3, 3), dtype=complex)
        Y_down_L = np.zeros((3, 3), dtype=complex)

        for chain in chains:
            W_color = np.eye(3, dtype=complex)
            W_weak = np.eye(2, dtype=complex)
            theta_chain = 0.0
            S_chain = 0.0

            for l in range(len(chain) - 1):
                key = (chain[l], chain[l + 1])
                if key in link_set:
                    idx = link_set[key]
                    W_color = Us_color[idx] @ W_color
                    W_weak = Us_weak[idx] @ W_weak
                    theta_chain += u1_angles[idx]
                if key in link_tau:
                    S_chain += link_tau[key]

            weak_proj = W_weak @ s_weak_ref
            phase_u = np.exp(1j * (Y_uR - Y_Q) * theta_chain)
            phase_d = np.exp(1j * (Y_dR - Y_Q) * theta_chain)
            amp_phase = np.exp(1j * k_momentum * S_chain)

            w_up = weak_proj[0] * phase_u * amp_phase
            w_down = weak_proj[1] * phase_d * amp_phase

            rotated = [W_color @ s for s in color_sections]
            for a in range(3):
                for b in range(3):
                    Y_up_L[a, b] += w_up * np.conj(rotated[a][0]) * rotated[b][0]
                    Y_down_L[a, b] += w_down * np.conj(rotated[a][0]) * rotated[b][0]

        avg_up = Y_up_L / n_found
        avg_down = Y_down_L / n_found

        # Per-length CKM (from just this length's chains)
        try:
            M_u_L = avg_up.conj().T @ avg_up
            M_d_L = avg_down.conj().T @ avg_down
            ev_u, Vu = np.linalg.eigh(M_u_L)
            ev_d, Vd = np.linalg.eigh(M_d_L)
            V_L = np.abs(Vu.conj().T @ Vd)[::-1, ::-1]
            length_ckm[L] = {
                'V_us': V_L[0, 1], 'V_cb': V_L[1, 2], 'V_ub': V_L[0, 2],
                'true_count': true_count, 'n_found': n_found
            }
        except Exception:
            length_ckm[L] = {'V_us': 0, 'V_cb': 0, 'V_ub': 0,
                             'true_count': true_count, 'n_found': n_found}

        Y_up += true_count * avg_up
        Y_down += true_count * avg_down
        total_weight += true_count

    if total_weight == 0:
        return None

    Y_up /= total_weight
    Y_down /= total_weight

    M_up = Y_up.conj().T @ Y_up
    M_down = Y_down.conj().T @ Y_down

    eigvals_u, V_u = np.linalg.eigh(M_up)
    eigvals_d, V_d = np.linalg.eigh(M_down)

    V_ckm = V_u.conj().T @ V_d
    V_abs = np.abs(V_ckm)[::-1, ::-1]

    return {
        'V_abs': V_abs,
        'V_ud': V_abs[0, 0], 'V_us': V_abs[0, 1], 'V_ub': V_abs[0, 2],
        'V_cd': V_abs[1, 0], 'V_cs': V_abs[1, 1], 'V_cb': V_abs[1, 2],
        'V_td': V_abs[2, 0], 'V_ts': V_abs[2, 1], 'V_tb': V_abs[2, 2],
        'theta_C': np.arcsin(min(V_abs[0, 1], 1.0)) * 180 / np.pi,
        'N': N, 'L_max': L_max,
        'length_ckm': length_ckm,
        'time': time.time() - t0,
    }


EXP_CKM = {
    'V_ud': 0.974, 'V_us': 0.225, 'V_ub': 0.004,
    'V_cd': 0.225, 'V_cs': 0.974, 'V_cb': 0.042,
    'V_td': 0.009, 'V_ts': 0.042, 'V_tb': 0.999,
}

if __name__ == "__main__":
    rho = 10000
    n_seeds = 20
    n_sample = 200
    k_momentum = 0.0  # k=0 first; k=9.5 can be tested after

    if "--k9" in sys.argv:
        k_momentum = 9.5

    print("=" * 80)
    print(f"  CABIBBO ANGLE: 20 SEEDS AT rho={rho}, k={k_momentum}")
    print(f"  Target: |V_us| = 0.225 (theta_C = 13.0 deg)")
    print(f"  Target SEM: sigma/sqrt(20) ~ 0.023")
    print("=" * 80)

    all_results = []
    all_Vus, all_Vcb, all_Vub, all_theta = [], [], [], []

    for seed_idx in range(n_seeds):
        r = compute_ckm(rho=rho, k_momentum=k_momentum,
                        n_sample_per_length=n_sample, seed=seed_idx * 137)
        if r is None:
            print(f"  seed={seed_idx:>2d}: FAILED", flush=True)
            continue

        all_results.append(r)
        all_Vus.append(r['V_us'])
        all_Vcb.append(r['V_cb'])
        all_Vub.append(r['V_ub'])
        all_theta.append(r['theta_C'])

        print(f"  seed={seed_idx:>2d}: |V_us|={r['V_us']:.4f} "
              f"|V_cb|={r['V_cb']:.4f} |V_ub|={r['V_ub']:.4f} "
              f"theta_C={r['theta_C']:.1f} deg "
              f"|V_ud|={r['V_ud']:.3f} |V_tb|={r['V_tb']:.3f} "
              f"L_max={r['L_max']} t={r['time']:.0f}s",
              flush=True)

        # Running statistics every 5 seeds
        if (seed_idx + 1) % 5 == 0 and len(all_Vus) >= 3:
            n = len(all_Vus)
            m = np.mean(all_Vus)
            s = np.std(all_Vus) / np.sqrt(n)
            print(f"    --- running ({n} seeds): |V_us| = {m:.4f} +/- {s:.4f} "
                  f"(factor {m/0.225:.2f}x) ---", flush=True)

    print(f"\n{'='*80}")
    print(f"  FINAL RESULTS ({len(all_Vus)} seeds)")
    print(f"{'='*80}")

    if all_Vus:
        n = len(all_Vus)
        for name, vals, exp in [('|V_us|', all_Vus, 0.225),
                                 ('|V_cb|', all_Vcb, 0.042),
                                 ('|V_ub|', all_Vub, 0.004),
                                 ('theta_C', all_theta, 13.0)]:
            m = np.mean(vals)
            s = np.std(vals) / np.sqrt(n)
            ci95 = 1.96 * s
            unit = ' deg' if name == 'theta_C' else ''
            print(f"  {name:>8s} = {m:.4f} +/- {s:.4f} "
                  f"(95% CI: [{m-ci95:.4f}, {m+ci95:.4f}]) "
                  f"expt: {exp}{unit} factor: {m/exp:.2f}x")

        # Wolfenstein hierarchy check
        print(f"\n  Wolfenstein hierarchy (expt: lambda ~ 0.22):")
        m_us = np.mean(all_Vus)
        m_cb = np.mean(all_Vcb)
        m_ub = np.mean(all_Vub)
        if m_us > 0:
            print(f"    |V_us| = {m_us:.4f} ~ lambda")
            print(f"    |V_cb| = {m_cb:.4f} ~ lambda^{np.log(m_cb)/np.log(m_us):.1f} "
                  f"(expt: lambda^2 = {0.225**2:.4f})")
            print(f"    |V_ub| = {m_ub:.4f} ~ lambda^{np.log(m_ub)/np.log(m_us):.1f} "
                  f"(expt: lambda^3 = {0.225**3:.4f})")

        # Per-length CKM breakdown (averaged across seeds)
        if all_results:
            all_lengths = set()
            for r in all_results:
                all_lengths.update(r['length_ckm'].keys())
            if all_lengths:
                print(f"\n  Per-length CKM elements (averaged):")
                print(f"    {'L':>3s}  {'count':>12s}  {'|V_us|':>8s}  "
                      f"{'|V_cb|':>8s}  {'|V_ub|':>8s}")
                for L in sorted(all_lengths):
                    stats = [r['length_ckm'].get(L, {'V_us': 0, 'V_cb': 0,
                             'V_ub': 0, 'true_count': 0})
                             for r in all_results]
                    tc = np.mean([s['true_count'] for s in stats])
                    vus = np.mean([s['V_us'] for s in stats])
                    vcb = np.mean([s['V_cb'] for s in stats])
                    vub = np.mean([s['V_ub'] for s in stats])
                    if tc > 0:
                        print(f"    {L:>3d}  {tc:>12.0f}  {vus:>8.4f}  "
                              f"{vcb:>8.4f}  {vub:>8.4f}")

    print(f"\n{'='*80}")
    print(f"  Experimental CKM (Wolfenstein):")
    print(f"    |V_us| = 0.225 (lambda)")
    print(f"    |V_cb| = 0.042 (lambda^2)")
    print(f"    |V_ub| = 0.004 (lambda^3)")
    print(f"{'='*80}")
