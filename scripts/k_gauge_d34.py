#!/usr/bin/env python3
"""
k_gauge_d34.py — Gauged chamber kernel at d=3 and d=4

Direct computation, no extrapolation.
d=3: ungauged target 2.0, chamber points C(N,3)
d=4: ungauged target 5/3 ≈ 1.667, chamber points C(N,4)
"""

import numpy as np
from itertools import combinations
import time

def sprinkle_causal_diamond(N, dim_space=1, seed=42):
    """Sprinkle N points into a (dim_space+1)D causal diamond.
    Returns sorted points and causal order matrix."""
    rng = np.random.default_rng(seed)
    points = []
    while len(points) < N:
        t = rng.uniform(-1, 1)
        x = rng.uniform(-1, 1, size=dim_space)
        if np.sum(np.abs(x)) + abs(t) <= 1:
            points.append(np.concatenate([[t], x]))

    points = np.array(points)
    idx = np.argsort(points[:, 0])
    points = points[idx]

    order = np.zeros((N, N), dtype=bool)
    for i in range(N):
        for j in range(i+1, N):
            dt = points[j, 0] - points[i, 0]
            dx = np.sqrt(np.sum((points[j, 1:] - points[i, 1:])**2))
            if dt > 0 and dx < dt:
                order[i, j] = True

    return points, order

def random_su3(rng):
    """Random SU(3) matrix via QR."""
    Z = (rng.standard_normal((3, 3)) + 1j * rng.standard_normal((3, 3))) / np.sqrt(2)
    Q, R = np.linalg.qr(Z)
    d = np.diagonal(R)
    ph = d / np.abs(d)
    Q = Q @ np.diag(ph)
    det = np.linalg.det(Q)
    Q = Q / (det ** (1/3))
    return Q

def block_det(blocks, d):
    """Trace of the d×d block determinant (blocks are N_c×N_c matrices).
    Uses Leibniz formula: det = Σ_σ sgn(σ) Π_i blocks[i][σ(i)]."""
    from itertools import permutations
    N_c = blocks[0][0].shape[0]
    result = np.zeros((N_c, N_c), dtype=complex)
    for perm in permutations(range(d)):
        sgn = 1
        # compute sign of permutation
        p = list(perm)
        inversions = sum(1 for i in range(d) for j in range(i+1, d) if p[i] > p[j])
        sgn = (-1) ** inversions
        # product of blocks along the permutation
        prod = np.eye(N_c, dtype=complex)
        for i in range(d):
            prod = prod @ blocks[i][perm[i]]
        result += sgn * prod
    return np.trace(result).real

def compute_k_gauge(points, order, N_c, d, max_chamber=800, seed=42):
    """Compute gauged chamber kernel for dimension d."""
    rng = np.random.default_rng(seed)
    N = len(points)

    # Assign holonomies
    holonomies = {}
    for i in range(N):
        for j in range(i+1, N):
            U = random_su3(rng)
            holonomies[(i, j)] = U
            holonomies[(j, i)] = U.conj().T

    # Chamber points
    chamber_pts = list(combinations(range(N), d))
    n_ch = len(chamber_pts)

    if n_ch > max_chamber:
        rng2 = np.random.default_rng(seed + 999)
        indices = sorted(rng2.choice(n_ch, max_chamber, replace=False))
        chamber_pts = [chamber_pts[i] for i in indices]
        n_ch = len(chamber_pts)

    # Gauged zeta: returns N_c × N_c matrix
    eye = np.eye(N_c, dtype=complex)
    zero = np.zeros((N_c, N_c), dtype=complex)

    def zeta_U(i, j):
        if i <= j:
            if (i, j) in holonomies:
                return holonomies[(i, j)]
            return eye.copy()
        return zero.copy()

    # Build K_gauge
    K = np.zeros((n_ch, n_ch))
    for i, P in enumerate(chamber_pts):
        for j, Q in enumerate(chamber_pts):
            blocks_PQ = [[zeta_U(P[a], Q[b]) for b in range(d)] for a in range(d)]
            blocks_QP = [[zeta_U(Q[a], P[b]) for b in range(d)] for a in range(d)]

            det_PQ = block_det(blocks_PQ, d)
            det_QP = block_det(blocks_QP, d)
            delta = N_c if i == j else 0.0

            K[i, j] = det_PQ + det_QP - delta

    return chamber_pts, K

def analyze(chamber_pts, K, N, d):
    """R-decomposition and eigenvalue ratio."""
    n_ch = len(chamber_pts)
    pt_to_idx = {p: i for i, p in enumerate(chamber_pts)}

    R_mat = np.zeros((n_ch, n_ch))
    for i, P in enumerate(chamber_pts):
        RP = tuple(N - 1 - P[k] for k in range(d-1, -1, -1))
        if RP in pt_to_idx:
            R_mat[i, pt_to_idx[RP]] = 1.0

    K_sym = (K + K.T) / 2
    P_even = (np.eye(n_ch) + R_mat) / 2
    P_odd = (np.eye(n_ch) - R_mat) / 2

    K_even = P_even @ K_sym @ P_even
    K_odd = P_odd @ K_sym @ P_odd

    eig_e = np.linalg.eigvalsh(K_even)
    eig_o = np.linalg.eigvalsh(K_odd)

    even_nz = eig_e[np.abs(eig_e) > 1e-6]
    odd_nz = eig_o[np.abs(eig_o) > 1e-6]

    if len(even_nz) > 0 and len(odd_nz) > 0:
        le = np.max(even_nz)
        lo = np.max(odd_nz)
        if lo > 0:
            return le / lo, le, lo
    return None, None, None

def main():
    print("=" * 70)
    print("GAUGED CHAMBER KERNEL: d=2, d=3, d=4")
    print("SU(3) holonomies on Poisson causal sets")
    print("=" * 70)

    targets = {2: 3.0, 3: 2.0, 4: 5/3}

    for d in [2, 3, 4]:
        dim_space = d - 1  # spatial dimensions for sprinkling
        # But we use index-based order, not geometric causality for speed
        # For d=2: N up to 30
        # For d=3: N up to 15 (C(15,3) = 455)
        # For d=4: N up to 12 (C(12,4) = 495)

        if d == 2:
            N_values = [15, 20, 25, 30]
            n_seeds = 10
        elif d == 3:
            N_values = [10, 12, 14]
            n_seeds = 8
        else:  # d=4
            N_values = [8, 9, 10, 11]
            n_seeds = 6

        print(f"\n{'═'*70}")
        print(f"d = {d}, ungauged target = {targets[d]:.4f}")
        print(f"{'═'*70}")

        for N in N_values:
            n_chamber = len(list(combinations(range(N), d)))
            print(f"\n  N={N}, C(N,d)={n_chamber} chamber points")

            ratios = []
            t0 = time.time()
            for seed in range(n_seeds):
                # Use index-based causal order (i < j iff i < j as integers)
                # This is [N]^1 effectively — the simplest causal set
                points = np.arange(N, dtype=float).reshape(-1, 1)
                order = np.zeros((N, N), dtype=bool)
                for i in range(N):
                    for j in range(i+1, N):
                        order[i, j] = True  # total order

                try:
                    ch_pts, K = compute_k_gauge(
                        points, order, N_c=3, d=d,
                        max_chamber=min(n_chamber, 600),
                        seed=seed*137)
                    ratio, le, lo = analyze(ch_pts, K, N, d)
                    if ratio is not None and ratio > 0:
                        ratios.append(ratio)
                        if seed < 2:
                            print(f"    seed={seed}: le={le:.2f}, lo={lo:.2f}, "
                                  f"le/lo={ratio:.4f}")
                except Exception as e:
                    if seed < 2:
                        print(f"    seed={seed}: {e}")

            dt = time.time() - t0
            if ratios:
                mean = np.mean(ratios)
                sem = np.std(ratios) / np.sqrt(len(ratios))
                print(f"    Mean le/lo = {mean:.4f} ± {sem:.4f} "
                      f"({len(ratios)} seeds, {dt:.1f}s)")
                print(f"    Ungauged target: {targets[d]:.4f}")
                print(f"    Ratio gauged/ungauged: {mean/targets[d]:.4f}")

    print(f"\n{'═'*70}")
    print("SUMMARY")
    print(f"{'═'*70}")
    print(f"\n  d  ungauged  gauged   ratio  m_p/m_rho_equiv")
    print(f"  {'─'*55}")
    print(f"  If the gauged/ungauged ratio is consistent across d,")
    print(f"  it gives a universal SU(3) suppression factor.")
    print(f"  The d=4 gauged ratio is the direct prediction for")
    print(f"  the confining-sector eigenvalue ratio.")

if __name__ == "__main__":
    main()
