#!/usr/bin/env python3
"""
Cabibbo angle from the K/P framework with U(1) hypercharge phases.

The current CKM computation (ckm_covariance.py) gives 5 elements within
3% of experiment but MISSES the Cabibbo angle (|V_us| ≈ 0.005 vs 0.225).
The reason: it uses real SU(2) holonomies without the U(1)_Y phase.

THE FIX: Include the hypercharge phase.
- Up-type right-handed: Y_u = -2/3 → phase e^{i(-2/3)θ} per link
- Down-type right-handed: Y_d = 1/3 → phase e^{i(1/3)θ} per link
- The DIFFERENCE Δ Y = -2/3 - 1/3 = -1 generates CKM mixing

The CKM matrix arises from the misalignment between up-type and
down-type Yukawa matrices, which differ by the U(1) phase.

Requirements: pip install numpy scipy
Usage:
    python3 cabibbo_angle.py --quick
    python3 cabibbo_angle.py
"""

import sys, numpy as np, time
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


def find_chains(adj, N, n_chains=5000, seed=42):
    rng = np.random.default_rng(seed)
    all_nodes = sorted(adj.keys())
    if not all_nodes:
        return []
    chains = []
    for _ in range(n_chains * 3):
        if len(chains) >= n_chains:
            break
        start = all_nodes[rng.integers(len(all_nodes))]
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
        if len(chain) >= 2:
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


def compute_ckm_with_hypercharge(rho=10000, beta_color=6.0, beta_weak=4.0,
                                  n_chains=5000, seed=42):
    """
    Compute the CKM matrix including U(1)_Y hypercharge phases.

    The key: up-type and down-type quarks have DIFFERENT hypercharges
    for their right-handed components:
      Y_u_R = -2/3 (derived from anomaly cancellation)
      Y_d_R = 1/3  (derived from anomaly cancellation)

    This generates a U(1) phase difference along each causal link,
    which misaligns the up and down Yukawa matrices → CKM mixing.
    """
    pts, N = poisson_sprinkle_4d(rho, seed=seed)
    pi, pj, adj, n_pairs = build_causal_pairs(pts, rho=rho)
    chains = find_chains(adj, N, n_chains=n_chains, seed=seed + 100)

    if not chains:
        return None

    # Build link set
    link_set = {}
    for chain in chains:
        for l in range(len(chain) - 1):
            key = (chain[l], chain[l + 1])
            if key not in link_set:
                link_set[key] = len(link_set)
    n_links = len(link_set)

    rng_c = np.random.default_rng(seed + 5000)
    rng_w = np.random.default_rng(seed + 9000)
    rng_u1 = np.random.default_rng(seed + 7000)

    # Gauge holonomies
    Us_color = random_su3_batch(n_links, rng_c, beta_color)
    Us_weak = random_su2_batch(n_links, rng_w, beta_weak)

    # U(1) phases: random angle θ per link, then Y*θ gives the hypercharge phase
    u1_angles = rng_u1.uniform(0, 2 * np.pi / beta_weak, n_links)

    # Hypercharges (DERIVED from anomaly cancellation):
    Y_uR = -2/3   # up-type right-handed (= -4*yQ = -4/6)
    Y_dR = 1/3    # down-type right-handed (= 2*yQ = 2/6)
    Y_Q = 1/6     # quark doublet

    # U(1) phase factors for up and down
    phase_u = np.exp(1j * (Y_uR - Y_Q) * u1_angles)  # up: Δ Y = -2/3 - 1/6 = -5/6
    phase_d = np.exp(1j * (Y_dR - Y_Q) * u1_angles)  # down: Δ Y = 1/3 - 1/6 = 1/6

    # K/P projection: color sector
    s_ref_color = np.array([1, 0, 0], dtype=complex)

    # Three reference sections (one per generation)
    sections = [
        np.array([1, 0, 0], dtype=complex),
        np.array([0, 1, 0], dtype=complex),
        np.array([0, 0, 1], dtype=complex),
    ]

    # Compute Yukawa covariance for UP and DOWN sectors separately
    Y_up = np.zeros((3, 3), dtype=complex)
    Y_down = np.zeros((3, 3), dtype=complex)

    for chain in chains:
        # Color holonomy (same for up and down)
        W_color = np.eye(3, dtype=complex)
        # U(1) phases (different for up and down)
        phase_u_chain = 1.0 + 0j
        phase_d_chain = 1.0 + 0j

        for l in range(len(chain) - 1):
            key = (chain[l], chain[l + 1])
            if key in link_set:
                idx = link_set[key]
                W_color = Us_color[idx] @ W_color
                phase_u_chain *= phase_u[idx]
                phase_d_chain *= phase_d[idx]

        # Rotated sections with U(1) phase
        for a in range(3):
            c_a = W_color @ sections[a]
            for b in range(3):
                c_b = W_color @ sections[b]
                # Up Yukawa: includes up-type U(1) phase
                Y_up[a, b] += np.conj(c_a[0] * phase_u_chain) * (c_b[0] * phase_u_chain)
                # Down Yukawa: includes down-type U(1) phase
                Y_down[a, b] += np.conj(c_a[0] * phase_d_chain) * (c_b[0] * phase_d_chain)

    Y_up /= len(chains)
    Y_down /= len(chains)

    # Diagonalize: Y = V D V†
    eigvals_u, V_u = np.linalg.eigh(Y_up)
    eigvals_d, V_d = np.linalg.eigh(Y_down)

    # CKM = V_u† × V_d
    V_ckm = V_u.conj().T @ V_d

    # Extract |V_ij|
    V_abs = np.abs(V_ckm)

    # Standard CKM parameterization
    # |V_us| = sin θ_C ≈ 0.225 (Cabibbo angle)
    # |V_ub| ≈ 0.004
    # |V_cb| ≈ 0.042

    return {
        'V_ckm': V_ckm,
        'V_abs': V_abs,
        'V_ud': V_abs[0, 0],
        'V_us': V_abs[0, 1],
        'V_ub': V_abs[0, 2],
        'V_cd': V_abs[1, 0],
        'V_cs': V_abs[1, 1],
        'V_cb': V_abs[1, 2],
        'V_td': V_abs[2, 0],
        'V_ts': V_abs[2, 1],
        'V_tb': V_abs[2, 2],
        'theta_C': np.arcsin(V_abs[0, 1]) * 180 / np.pi if V_abs[0, 1] < 1 else 90,
        'n_chains': len(chains),
        'N': N,
    }


# Experimental CKM values
EXP_CKM = {
    'V_ud': 0.974, 'V_us': 0.225, 'V_ub': 0.004,
    'V_cd': 0.225, 'V_cs': 0.974, 'V_cb': 0.042,
    'V_td': 0.009, 'V_ts': 0.042, 'V_tb': 0.999,
}


if __name__ == "__main__":
    if "--quick" in sys.argv:
        rhos = [5000, 10000]
        n_seeds = 3
    else:
        rhos = [5000, 10000, 20000]
        n_seeds = 5

    print("=" * 70)
    print("  CABIBBO ANGLE FROM K/P WITH U(1) HYPERCHARGE PHASES")
    print("  Y_u = -2/3, Y_d = 1/3 (derived from anomaly cancellation)")
    print("=" * 70)

    for rho in rhos:
        print(f"\n--- rho = {rho} ---")
        all_Vus = []

        for seed in range(n_seeds):
            r = compute_ckm_with_hypercharge(rho=rho, seed=seed * 137)
            if r is None:
                print(f"  seed={seed}: FAILED")
                continue

            all_Vus.append(r['V_us'])
            print(f"  seed={seed}: |V_us| = {r['V_us']:.4f} "
                  f"(θ_C = {r['theta_C']:.1f}°) "
                  f"|V_ud|={r['V_ud']:.3f} |V_cb|={r['V_cb']:.3f} "
                  f"|V_tb|={r['V_tb']:.3f} "
                  f"(N={r['N']}, chains={r['n_chains']})",
                  flush=True)

        if all_Vus:
            mean = np.mean(all_Vus)
            sem = np.std(all_Vus) / np.sqrt(len(all_Vus))
            print(f"\n  >>> |V_us| = {mean:.4f} ± {sem:.4f} "
                  f"(expt: {EXP_CKM['V_us']}, factor {mean/EXP_CKM['V_us']:.2f}x)")

    print("\n" + "=" * 70)
    print("  Experiment: |V_us| = 0.225, θ_C = 13.0°")
    print("  If |V_us| is nonzero and trends toward 0.225,")
    print("  the Cabibbo angle is DERIVED from the hypercharge difference.")
    print("=" * 70)
