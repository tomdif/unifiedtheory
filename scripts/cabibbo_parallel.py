#!/usr/bin/env python3
"""
Cabibbo angle: parallelized 20-seed CPU runner with U(1)-off control.

Per-seed worker is pure numpy/scipy (avoids torch fork/MPS issues across procs).
Outer loop uses multiprocessing.Pool for seed-level parallelism.

Audit-driven additions vs cabibbo_20seed.py / cabibbo_gpu.py:
  - --u1-off : zeros all U(1) link angles. If V_us collapses to ~0, the U(1)
               phase IS the load-bearing piece for the up/down split, and the
               April-19 SU(2) unitarity retraction (commit 5699b18) does not
               bleed into the CKM derivation. If V_us stays >0.1, we have an
               artifact (probably finite-N row-0 vs row-1 sampling asymmetry).
  - --u1-only : zeros weak holonomy (Us_weak = I). Reverse control — V_us
                must come from somewhere; isolating U(1) tells us if the
                weak sector is needed at all.
  - per-length CKM dict, full results JSON output for downstream analysis.
  - vectorized chain-index assembly (was the Python-loop bottleneck).

Usage:
    python3 cabibbo_parallel.py --quick                # 5 seeds, rho=5K, 1 wave
    python3 cabibbo_parallel.py                        # 20 seeds, rho=10K
    python3 cabibbo_parallel.py --u1-off               # control
    python3 cabibbo_parallel.py --k9                   # k_momentum=9.5
    python3 cabibbo_parallel.py --workers 14           # explicit pool size
"""

import sys, os, json, argparse, time
import numpy as np
from scipy.spatial import cKDTree
from collections import defaultdict
import multiprocessing as mp


# ============================================================
# Causal set construction (CPU-only, per seed)
# ============================================================

def poisson_sprinkle_4d(rho, box_size=1.0, seed=42):
    rng = np.random.default_rng(seed)
    N = rng.poisson(rho * box_size ** 4)
    pts = rng.uniform(0, box_size, size=(N, 4)).astype(np.float64)
    return pts[np.argsort(pts[:, 0])], N


def build_causal_graph(points, box_size=1.0, rho=10000):
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


# ============================================================
# Vectorized SU(N) generation (numpy, CPU)
# ============================================================

def random_su3_vec(n, seed, beta=6.0):
    """Batched SU(3) via Cayley map + det-projection. Pure numpy."""
    rng = np.random.default_rng(seed)
    H = (rng.standard_normal((n, 3, 3)) + 1j * rng.standard_normal((n, 3, 3)))
    H = (H + H.conj().swapaxes(-1, -2)) / 2
    tr = np.trace(H, axis1=-2, axis2=-1) / 3.0
    H -= tr[:, None, None] * np.eye(3)
    iH_b = (1j * H) / beta
    eye3 = np.eye(3, dtype=complex)
    A = eye3 + iH_b
    B = eye3 - iH_b
    U = np.linalg.solve(B, A)              # batched solve, vectorized
    det = np.linalg.det(U)
    phase = (det.conj() / (np.abs(det) + 1e-12)) ** (1.0 / 3.0)
    U *= phase[:, None, None]
    return U


def random_su2_vec(n, seed, beta=4.0):
    """Batched SU(2) via quaternion parameterization."""
    rng = np.random.default_rng(seed)
    q = rng.standard_normal((n, 4)) / beta
    q[:, 0] += 1.0
    q /= np.linalg.norm(q, axis=1, keepdims=True).clip(min=1e-12)
    a0, a1, a2, a3 = q[:, 0], q[:, 1], q[:, 2], q[:, 3]
    U = np.empty((n, 2, 2), dtype=complex)
    U[:, 0, 0] = a0 + 1j * a3
    U[:, 0, 1] = a2 + 1j * a1
    U[:, 1, 0] = -a2 + 1j * a1
    U[:, 1, 1] = a0 - 1j * a3
    return U


# ============================================================
# Per-length holonomy: vectorized
# ============================================================

def chain_yukawa_vectorized(chains_arr, link_idx_lookup, Us_color, Us_weak,
                            u1_angles, link_tau_arr, k_mom,
                            Y_uR, Y_dR, Y_Q):
    """
    chains_arr: (n_chains, L) int array of node IDs (all chains same L)
    link_idx_lookup: dict (i,j) -> link index
    Returns Y_up_L, Y_down_L (3x3 complex)
    """
    n_chains, L = chains_arr.shape
    n_steps = L - 1

    # Build (n_chains, n_steps) link index array — one-shot dict lookup
    src = chains_arr[:, :-1].ravel()
    dst = chains_arr[:, 1:].ravel()
    link_ids = np.empty(src.size, dtype=np.int64)
    valid = np.empty(src.size, dtype=bool)
    for k in range(src.size):
        key = (int(src[k]), int(dst[k]))
        idx = link_idx_lookup.get(key, -1)
        link_ids[k] = idx
        valid[k] = idx >= 0
    link_ids = link_ids.reshape(n_chains, n_steps)
    valid = valid.reshape(n_chains, n_steps)

    # Replace invalid links with index 0 (will be masked via identity matrix)
    safe_ids = np.where(valid, link_ids, 0)

    # Sequential matmul along chain length, batched across chains
    eye3 = np.eye(3, dtype=complex)
    eye2 = np.eye(2, dtype=complex)
    W_color = np.broadcast_to(eye3, (n_chains, 3, 3)).copy()
    W_weak = np.broadcast_to(eye2, (n_chains, 2, 2)).copy()

    theta_chain = np.zeros(n_chains)
    S_chain = np.zeros(n_chains)

    for li in range(n_steps):
        ids_li = safe_ids[:, li]
        valid_li = valid[:, li]
        # Masked matmul: where invalid, use identity
        c_step = np.where(valid_li[:, None, None], Us_color[ids_li], eye3)
        w_step = np.where(valid_li[:, None, None], Us_weak[ids_li], eye2)
        W_color = np.einsum('cij,cjk->cik', c_step, W_color)
        W_weak = np.einsum('cij,cjk->cik', w_step, W_weak)
        theta_chain += np.where(valid_li, u1_angles[ids_li], 0.0)
        S_chain += np.where(valid_li, link_tau_arr[ids_li], 0.0)

    # Weak projection on s_ref = (1, 0)
    weak_proj = W_weak[:, :, 0]    # = W_weak @ [1,0]
    w_up_weak = weak_proj[:, 0]
    w_down_weak = weak_proj[:, 1]

    phase_u = np.exp(1j * (Y_uR - Y_Q) * theta_chain)
    phase_d = np.exp(1j * (Y_dR - Y_Q) * theta_chain)
    amp = np.exp(1j * k_mom * S_chain)

    w_up = w_up_weak * phase_u * amp
    w_down = w_down_weak * phase_d * amp

    # Row-0 trick: Y[a,b] = sum_c w_c * conj(W_color[c,0,a]) * W_color[c,0,b]
    row0 = W_color[:, 0, :]                 # (n_chains, 3)
    Y_up_L = np.einsum('c,ca,cb->ab', w_up, row0.conj(), row0)
    Y_down_L = np.einsum('c,ca,cb->ab', w_down, row0.conj(), row0)
    return Y_up_L, Y_down_L


# ============================================================
# Per-seed worker
# ============================================================

def compute_ckm_one_seed(args):
    (seed, rho, beta_color, beta_weak, k_mom, n_sample,
     u1_off, weak_off) = args
    t0 = time.time()

    pts, N = poisson_sprinkle_4d(rho, seed=seed)
    adj, link_tau, n_pairs = build_causal_graph(pts, rho=rho)
    if n_pairs == 0:
        return None
    dp_fwd, L_max, all_nodes = compute_forward_dp(adj)
    path_counts = count_paths_by_length(adj, all_nodes, L_max)

    link_idx_lookup = {}
    for src, dests in adj.items():
        for dst in dests:
            key = (src, dst)
            if key not in link_idx_lookup:
                link_idx_lookup[key] = len(link_idx_lookup)
    n_links = len(link_idx_lookup)

    Us_color = random_su3_vec(n_links, seed + 5000, beta_color)
    if weak_off:
        Us_weak = np.broadcast_to(np.eye(2, dtype=complex), (n_links, 2, 2)).copy()
    else:
        Us_weak = random_su2_vec(n_links, seed + 9000, beta_weak)

    rng_u1 = np.random.default_rng(seed + 7000)
    if u1_off:
        u1_angles = np.zeros(n_links)
    else:
        u1_angles = rng_u1.uniform(0, 2 * np.pi / beta_weak, n_links)

    # Pack link_tau as a flat array indexed by link_id
    link_tau_arr = np.zeros(n_links)
    for key, lid in link_idx_lookup.items():
        link_tau_arr[lid] = link_tau.get(key, 0.0)

    Y_uR, Y_dR, Y_Q = -2/3, 1/3, 1/6

    rng_chain = np.random.default_rng(seed + 3000)
    Y_up = np.zeros((3, 3), dtype=complex)
    Y_down = np.zeros((3, 3), dtype=complex)
    total_weight = 0.0
    length_ckm = {}

    for L in range(2, L_max + 1):
        chains = sample_chains_guided(adj, dp_fwd, L, n_sample, rng_chain, all_nodes)
        true_count = path_counts.get(L, 0.0)
        if not chains or true_count == 0:
            continue
        chains_arr = np.array(chains, dtype=np.int64)
        n_found = len(chains)
        Y_up_L, Y_down_L = chain_yukawa_vectorized(
            chains_arr, link_idx_lookup, Us_color, Us_weak,
            u1_angles, link_tau_arr, k_mom, Y_uR, Y_dR, Y_Q)
        avg_up = Y_up_L / n_found
        avg_down = Y_down_L / n_found

        try:
            M_u_L = avg_up.conj().T @ avg_up
            M_d_L = avg_down.conj().T @ avg_down
            ev_u, Vu = np.linalg.eigh(M_u_L)
            ev_d, Vd = np.linalg.eigh(M_d_L)
            V_L = np.abs(Vu.conj().T @ Vd)[::-1, ::-1]
            length_ckm[L] = {
                'V_us': float(V_L[0, 1]), 'V_cb': float(V_L[1, 2]),
                'V_ub': float(V_L[0, 2]),
                'true_count': float(true_count), 'n_found': n_found,
            }
        except Exception:
            length_ckm[L] = {'V_us': 0.0, 'V_cb': 0.0, 'V_ub': 0.0,
                             'true_count': float(true_count), 'n_found': n_found}

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
        'seed': seed,
        'V_us': float(V_abs[0, 1]),
        'V_cb': float(V_abs[1, 2]),
        'V_ub': float(V_abs[0, 2]),
        'V_ud': float(V_abs[0, 0]),
        'V_tb': float(V_abs[2, 2]),
        'theta_C': float(np.arcsin(min(V_abs[0, 1], 1.0)) * 180 / np.pi),
        'V_abs': V_abs.tolist(),
        'N': int(N), 'n_links': int(n_links), 'L_max': int(L_max),
        'length_ckm': {int(k): v for k, v in length_ckm.items()},
        'time': float(time.time() - t0),
        'u1_off': bool(u1_off),
        'weak_off': bool(weak_off),
    }


# ============================================================
# Driver
# ============================================================

def summarize(results, label):
    valid = [r for r in results if r is not None]
    if not valid:
        print(f"  {label}: ALL SEEDS FAILED")
        return
    n = len(valid)
    Vus = np.array([r['V_us'] for r in valid])
    Vcb = np.array([r['V_cb'] for r in valid])
    Vub = np.array([r['V_ub'] for r in valid])
    theta = np.array([r['theta_C'] for r in valid])
    print(f"\n  ===== {label} ({n} seeds) =====")
    for name, vals, exp in [('|V_us|', Vus, 0.225),
                             ('|V_cb|', Vcb, 0.042),
                             ('|V_ub|', Vub, 0.004),
                             ('theta_C', theta, 13.0)]:
        m = vals.mean()
        s = vals.std(ddof=1) / np.sqrt(n) if n > 1 else float('nan')
        ci95 = 1.96 * s if n > 1 else float('nan')
        unit = ' deg' if name == 'theta_C' else ''
        print(f"    {name:>8s} = {m:.4f} +/- {s:.4f} "
              f"(95% CI: [{m-ci95:.4f}, {m+ci95:.4f}]) "
              f"expt: {exp}{unit} factor: {m/exp:.2f}x")


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--quick', action='store_true', help='5 seeds, rho=5K')
    parser.add_argument('--rho', type=int, default=None)
    parser.add_argument('--seeds', type=int, default=None)
    parser.add_argument('--n-sample', type=int, default=200)
    parser.add_argument('--k', type=float, default=0.0)
    parser.add_argument('--k9', action='store_true', help='shortcut for k=9.5')
    parser.add_argument('--workers', type=int, default=None)
    parser.add_argument('--u1-off', action='store_true', help='zero U(1) angles')
    parser.add_argument('--weak-off', action='store_true', help='zero weak SU(2)')
    parser.add_argument('--out', type=str, default=None, help='JSON output path')
    parser.add_argument('--beta-color', type=float, default=6.0)
    parser.add_argument('--beta-weak', type=float, default=4.0)
    args = parser.parse_args()

    if args.k9:
        args.k = 9.5
    if args.quick:
        rho = args.rho or 5000
        n_seeds = args.seeds or 5
    else:
        rho = args.rho or 10000
        n_seeds = args.seeds or 20

    n_workers = args.workers or min(mp.cpu_count(), n_seeds)

    label_bits = [f"rho={rho}", f"k={args.k}", f"seeds={n_seeds}",
                  f"workers={n_workers}"]
    if args.u1_off:
        label_bits.append("U(1) OFF")
    if args.weak_off:
        label_bits.append("WEAK OFF")
    label = " ".join(label_bits)

    print("=" * 80)
    print(f"  CABIBBO PARALLEL: {label}")
    print(f"  Target: |V_us| = 0.225 (theta_C = 13.0 deg)")
    print("=" * 80, flush=True)

    seed_args = [(i * 137, rho, args.beta_color, args.beta_weak, args.k,
                  args.n_sample, args.u1_off, args.weak_off)
                 for i in range(n_seeds)]

    t_start = time.time()
    results = []
    with mp.get_context('spawn').Pool(n_workers) as pool:
        for r in pool.imap_unordered(compute_ckm_one_seed, seed_args):
            results.append(r)
            if r is None:
                print("  seed FAILED", flush=True)
                continue
            print(f"  seed={r['seed']:>5d}: |V_us|={r['V_us']:.4f} "
                  f"|V_cb|={r['V_cb']:.4f} |V_ub|={r['V_ub']:.4f} "
                  f"theta_C={r['theta_C']:.1f} L_max={r['L_max']} "
                  f"n_links={r['n_links']} t={r['time']:.0f}s",
                  flush=True)

    elapsed = time.time() - t_start
    print(f"\n  Wallclock: {elapsed:.0f}s ({elapsed/60:.1f} min)", flush=True)
    summarize(results, label)

    if args.out:
        with open(args.out, 'w') as f:
            json.dump({
                'label': label, 'rho': rho, 'k': args.k, 'n_seeds': n_seeds,
                'u1_off': args.u1_off, 'weak_off': args.weak_off,
                'wallclock_sec': elapsed,
                'results': results,
            }, f, indent=2)
        print(f"  Wrote {args.out}", flush=True)


if __name__ == "__main__":
    mp.freeze_support()
    main()
