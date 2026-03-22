#!/usr/bin/env python3
"""
GPU-accelerated Cabibbo angle computation.

Bottlenecks in CPU version (17 min/seed at rho=10K):
1. random_su3_batch: Python loop with np.linalg.eig per matrix → PyTorch batched
2. Holonomy loop: Python loop over chains × links → PyTorch batched matmul
3. Path counting DP: dict-of-dicts → numpy arrays

Expected speedup: ~10× (17 min → ~2 min per seed)

Requirements: pip install numpy scipy torch
Usage:
    python3 cabibbo_gpu.py --quick       # 5 seeds, rho=5K
    python3 cabibbo_gpu.py               # 20 seeds, rho=10K
    python3 cabibbo_gpu.py --k9          # 20 seeds, rho=10K, k=9.5
"""

import sys, numpy as np, time, torch
from scipy.spatial import cKDTree
from collections import defaultdict

DEVICE = torch.device('cuda' if torch.cuda.is_available() else 'cpu')
print(f"Using device: {DEVICE}", flush=True)


# ============================================================
# 1. Causal set (CPU — graph ops don't benefit from GPU)
# ============================================================

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


# ============================================================
# 2. GPU-accelerated SU(N) generation
# ============================================================

def random_su3_fast(n, seed, beta=6.0):
    """Generate n random SU(3) matrices on GPU via Cayley map. float32 only.

    Cayley approximation: U = (I + iH/beta)(I - iH/beta)^{-1}
    Maps Hermitian traceless matrices to SU(3) without matrix_exp.
    Uses torch.linalg.solve instead of explicit inverse for numerical stability.
    ~10x less memory than complex128 matrix_exp (float32 vs float64, no exp workspace).
    """
    rng = torch.Generator(device=DEVICE).manual_seed(seed)
    # Random Hermitian traceless matrix in float32
    H_real = torch.randn(n, 3, 3, device=DEVICE, generator=rng, dtype=torch.float32)
    H_imag = torch.randn(n, 3, 3, device=DEVICE, generator=rng, dtype=torch.float32)
    H = torch.complex(H_real, H_imag)  # complex64
    H = (H + H.conj().transpose(-2, -1)) / 2  # Hermitian
    trace = torch.diagonal(H, dim1=-2, dim2=-1).sum(-1, keepdim=True).unsqueeze(-1)
    eye3 = torch.eye(3, dtype=torch.complex64, device=DEVICE).unsqueeze(0)
    H = H - (trace / 3) * eye3  # traceless

    # Cayley map: U = (I + iH/beta) @ (I - iH/beta)^{-1}
    # Rewrite as: U = A @ B^{-1} where A = I + iH/beta, B = I - iH/beta
    # Solve B^T X^T = A^T then U = X, i.e. U = solve(B, A) via batched solve
    iH_beta = (1j * H) / beta
    A = eye3 + iH_beta
    B = eye3 - iH_beta
    # U = A @ B^{-1} = (B^{-T} @ A^T)^T  — use solve for stability
    U = torch.linalg.solve(B, A)

    # Project to SU(3): U *= (det(U)*/|det(U)|)^{1/3}
    det = torch.linalg.det(U)
    phase = (det.conj() / (det.abs() + 1e-8)) ** (1.0 / 3.0)
    U = U * phase.unsqueeze(-1).unsqueeze(-1)

    return U


def random_su2_fast(n, seed, beta=4.0):
    """Batched SU(2) via quaternion parameterization. float32 only.

    SU(2) = unit quaternions: U = a0*I + i*(a1*s1 + a2*s2 + a3*s3)
    Sample a 4-vector from N(0, 1/beta), bias toward identity, normalize.
    Uses ONLY real float32 arithmetic until final complex64 matrix assembly.
    """
    rng = torch.Generator(device=DEVICE).manual_seed(seed)
    q = torch.randn(n, 4, device=DEVICE, generator=rng, dtype=torch.float32) / beta
    q[:, 0] += 1.0  # bias toward identity

    norm = q.norm(dim=1, keepdim=True).clamp(min=1e-8)
    q = q / norm
    a0, a1, a2, a3 = q[:, 0], q[:, 1], q[:, 2], q[:, 3]

    U = torch.zeros(n, 2, 2, dtype=torch.complex64, device=DEVICE)
    U[:, 0, 0] = torch.complex(a0, a3)
    U[:, 0, 1] = torch.complex(a2, a1)
    U[:, 1, 0] = torch.complex(-a2, a1)
    U[:, 1, 1] = torch.complex(a0, -a3)
    return U


# ============================================================
# 3. GPU-accelerated holonomy computation
# ============================================================

def compute_holonomies_gpu(chains, link_indices, Us_color, Us_weak,
                            u1_angles, link_taus, k_momentum,
                            Y_uR, Y_dR, Y_Q, s_weak_ref, color_sections):
    """
    Compute holonomies for all chains at a given length on GPU.

    chains: list of chains (each chain is a list of node IDs)
    link_indices: dict (i,j) -> index into Us arrays
    Returns: Y_up_L, Y_down_L (3x3 complex matrices)
    """
    n_chains = len(chains)
    if n_chains == 0:
        return (torch.zeros(3, 3, dtype=torch.complex64, device=DEVICE),
                torch.zeros(3, 3, dtype=torch.complex64, device=DEVICE))

    chain_len = len(chains[0])  # all chains same length at this L
    n_links_per_chain = chain_len - 1

    # Build index arrays for all chains' links
    color_idx = torch.zeros(n_chains, n_links_per_chain, dtype=torch.long, device=DEVICE)
    weak_idx = torch.zeros(n_chains, n_links_per_chain, dtype=torch.long, device=DEVICE)
    theta_vals = torch.zeros(n_chains, n_links_per_chain, dtype=torch.float32, device=DEVICE)
    tau_vals = torch.zeros(n_chains, n_links_per_chain, dtype=torch.float32, device=DEVICE)
    valid_mask = torch.zeros(n_chains, n_links_per_chain, dtype=torch.bool, device=DEVICE)

    for ci, chain in enumerate(chains):
        for li in range(n_links_per_chain):
            key = (chain[li], chain[li + 1])
            if key in link_indices:
                idx = link_indices[key]
                color_idx[ci, li] = idx
                weak_idx[ci, li] = idx
                theta_vals[ci, li] = u1_angles[idx]
                tau_vals[ci, li] = link_taus.get(key, 0.0)
                valid_mask[ci, li] = True

    # Compute chain holonomies via sequential matmul (link by link)
    # Color: (n_chains, 3, 3)
    W_color = torch.eye(3, dtype=torch.complex64, device=DEVICE).unsqueeze(0).expand(n_chains, -1, -1).clone()
    W_weak = torch.eye(2, dtype=torch.complex64, device=DEVICE).unsqueeze(0).expand(n_chains, -1, -1).clone()

    for li in range(n_links_per_chain):
        c_mats = Us_color[color_idx[:, li]]  # (n_chains, 3, 3)
        w_mats = Us_weak[weak_idx[:, li]]    # (n_chains, 2, 2)
        # Only apply where valid
        mask3 = valid_mask[:, li].view(-1, 1, 1).expand_as(c_mats)
        mask2 = valid_mask[:, li].view(-1, 1, 1).expand_as(w_mats)
        eye3 = torch.eye(3, dtype=torch.complex64, device=DEVICE).unsqueeze(0).expand_as(c_mats)
        eye2 = torch.eye(2, dtype=torch.complex64, device=DEVICE).unsqueeze(0).expand_as(w_mats)
        c_mats = torch.where(mask3, c_mats, eye3)
        w_mats = torch.where(mask2, w_mats, eye2)
        W_color = torch.bmm(c_mats, W_color)
        W_weak = torch.bmm(w_mats, W_weak)

    # Weak projection: (n_chains, 2)
    weak_proj = torch.matmul(W_weak, s_weak_ref)  # (n_chains, 2)
    w_up_weak = weak_proj[:, 0]    # (n_chains,)
    w_down_weak = weak_proj[:, 1]  # (n_chains,)

    # U(1) phases
    theta_chain = theta_vals.sum(dim=1)  # (n_chains,)
    phase_u = torch.exp(1j * torch.tensor(Y_uR - Y_Q, device=DEVICE) * theta_chain.to(torch.complex64))
    phase_d = torch.exp(1j * torch.tensor(Y_dR - Y_Q, device=DEVICE) * theta_chain.to(torch.complex64))

    # Amplitude phase
    S_chain = tau_vals.sum(dim=1)  # (n_chains,)
    amp_phase = torch.exp(1j * k_momentum * S_chain.to(torch.complex64))

    # Full weights
    w_up = w_up_weak * phase_u * amp_phase      # (n_chains,)
    w_down = w_down_weak * phase_d * amp_phase   # (n_chains,)

    # Color rotation of sections: (n_chains, 3, 3) @ (3, 3) -> project first component
    # rotated[a] = W_color @ section[a], take [0] component
    # For Y[a,b] = sum_chains w * conj(rot_a[0]) * rot_b[0]
    # rot_a[0] = (W_color @ section_a)[0] = W_color[0, a]
    # So Y[a,b] = sum_chains w * conj(W_color[0,a]) * W_color[0,b]

    row0 = W_color[:, 0, :]  # (n_chains, 3) — first row of color holonomy

    # Y_up[a,b] = sum_c w_up[c] * conj(row0[c,a]) * row0[c,b]
    # = (w_up * conj(row0))^T @ row0 (outer product sum)
    weighted_up = (w_up.unsqueeze(-1) * row0.conj())  # (n_chains, 3)
    weighted_down = (w_down.unsqueeze(-1) * row0.conj())  # (n_chains, 3)

    Y_up_L = torch.einsum('ca,cb->ab', weighted_up, row0)
    Y_down_L = torch.einsum('ca,cb->ab', weighted_down, row0)

    return Y_up_L, Y_down_L


# ============================================================
# 4. Main CKM computation
# ============================================================

def compute_ckm_gpu(rho=10000, beta_color=6.0, beta_weak=4.0,
                     k_momentum=0.0, n_sample_per_length=200, seed=42):
    t0 = time.time()

    # CPU: causal set construction
    pts, N = poisson_sprinkle_4d(rho, seed=seed)
    adj, link_tau, n_pairs = build_causal_graph(pts, rho=rho)
    dp_fwd, L_max, all_nodes = compute_forward_dp(adj)
    path_counts = count_paths_by_length(adj, all_nodes, L_max)
    t_graph = time.time() - t0

    # Build link set
    link_set = {}
    for src, dests in adj.items():
        for dst in dests:
            key = (src, dst)
            if key not in link_set:
                link_set[key] = len(link_set)
    n_links = len(link_set)

    # GPU: generate gauge fields
    t1 = time.time()
    Us_color = random_su3_fast(n_links, seed + 5000, beta_color)
    Us_weak = random_su2_fast(n_links, seed + 9000, beta_weak)
    t_gauge = time.time() - t1

    # U(1) angles (CPU, small)
    rng_u1 = np.random.default_rng(seed + 7000)
    u1_angles_np = rng_u1.uniform(0, 2 * np.pi / beta_weak, n_links)

    Y_uR, Y_dR, Y_Q = -2/3, 1/3, 1/6

    s_weak_ref = torch.tensor([1, 0], dtype=torch.complex64, device=DEVICE)
    color_sections = [torch.tensor([1, 0, 0], dtype=torch.complex64, device=DEVICE),
                      torch.tensor([0, 1, 0], dtype=torch.complex64, device=DEVICE),
                      torch.tensor([0, 0, 1], dtype=torch.complex64, device=DEVICE)]

    rng_chain = np.random.default_rng(seed + 3000)

    Y_up_total = torch.zeros(3, 3, dtype=torch.complex64, device=DEVICE)
    Y_down_total = torch.zeros(3, 3, dtype=torch.complex64, device=DEVICE)
    total_weight = 0.0

    t2 = time.time()
    for L in range(2, L_max + 1):
        chains = sample_chains_guided(adj, dp_fwd, L, n_sample_per_length,
                                       rng_chain, all_nodes)
        true_count = path_counts.get(L, 0.0)
        if not chains or true_count == 0:
            continue

        n_found = len(chains)
        Y_up_L, Y_down_L = compute_holonomies_gpu(
            chains, link_set, Us_color, Us_weak,
            u1_angles_np, link_tau, k_momentum,
            Y_uR, Y_dR, Y_Q, s_weak_ref, color_sections)

        Y_up_total += true_count * (Y_up_L / n_found)
        Y_down_total += true_count * (Y_down_L / n_found)
        total_weight += true_count

    t_holonomy = time.time() - t2

    if total_weight == 0:
        return None

    Y_up = (Y_up_total / total_weight).cpu().numpy()
    Y_down = (Y_down_total / total_weight).cpu().numpy()

    M_up = Y_up.conj().T @ Y_up
    M_down = Y_down.conj().T @ Y_down

    eigvals_u, V_u = np.linalg.eigh(M_up)
    eigvals_d, V_d = np.linalg.eigh(M_down)

    V_ckm = V_u.conj().T @ V_d
    V_abs = np.abs(V_ckm)[::-1, ::-1]

    total_time = time.time() - t0

    return {
        'V_abs': V_abs,
        'V_ud': V_abs[0, 0], 'V_us': V_abs[0, 1], 'V_ub': V_abs[0, 2],
        'V_cd': V_abs[1, 0], 'V_cs': V_abs[1, 1], 'V_cb': V_abs[1, 2],
        'V_td': V_abs[2, 0], 'V_ts': V_abs[2, 1], 'V_tb': V_abs[2, 2],
        'theta_C': np.arcsin(min(V_abs[0, 1], 1.0)) * 180 / np.pi,
        'N': N, 'L_max': L_max, 'n_links': n_links,
        'time_total': total_time,
        'time_graph': t_graph,
        'time_gauge': t_gauge,
        'time_holonomy': t_holonomy,
    }


# ============================================================
# 5. Main
# ============================================================

if __name__ == "__main__":
    if "--quick" in sys.argv:
        rho = 5000
        n_seeds = 5
    else:
        rho = 10000
        n_seeds = 20

    k_momentum = 9.5 if "--k9" in sys.argv else 0.0
    n_sample = 200

    print("=" * 80)
    print(f"  CABIBBO ANGLE (GPU): {n_seeds} SEEDS AT rho={rho}, k={k_momentum}")
    print(f"  Device: {DEVICE}")
    print(f"  Target: |V_us| = 0.225 (theta_C = 13.0 deg)")
    print("=" * 80)

    all_Vus, all_Vcb, all_Vub, all_theta = [], [], [], []

    for seed_idx in range(n_seeds):
        r = compute_ckm_gpu(rho=rho, k_momentum=k_momentum,
                             n_sample_per_length=n_sample, seed=seed_idx * 137)
        if r is None:
            print(f"  seed={seed_idx:>2d}: FAILED", flush=True)
            continue

        all_Vus.append(r['V_us'])
        all_Vcb.append(r['V_cb'])
        all_Vub.append(r['V_ub'])
        all_theta.append(r['theta_C'])

        print(f"  seed={seed_idx:>2d}: |V_us|={r['V_us']:.4f} "
              f"|V_cb|={r['V_cb']:.4f} |V_ub|={r['V_ub']:.4f} "
              f"theta_C={r['theta_C']:.1f} deg "
              f"t={r['time_total']:.0f}s "
              f"(graph={r['time_graph']:.0f}s gauge={r['time_gauge']:.1f}s "
              f"hol={r['time_holonomy']:.0f}s)",
              flush=True)

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

        m_us = np.mean(all_Vus)
        m_cb = np.mean(all_Vcb)
        m_ub = np.mean(all_Vub)
        if m_us > 0.01:
            print(f"\n  Wolfenstein hierarchy:")
            print(f"    |V_us| = {m_us:.4f} ~ lambda")
            print(f"    |V_cb| = {m_cb:.4f} ~ lambda^{np.log(max(m_cb,1e-6))/np.log(m_us):.1f} "
                  f"(expt: lambda^2 = {0.225**2:.4f})")
            print(f"    |V_ub| = {m_ub:.4f} ~ lambda^{np.log(max(m_ub,1e-6))/np.log(m_us):.1f} "
                  f"(expt: lambda^3 = {0.225**3:.4f})")

    print(f"\n{'='*80}")
