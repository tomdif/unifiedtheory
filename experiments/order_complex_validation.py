#!/usr/bin/env python3
"""
T² validation for the ORDER COMPLEX of a Poisson causal set.
Start SMALL — the order complex explodes combinatorially.
"""

import numpy as np
from collections import defaultdict
import time


def poisson_sprinkling(rho, dim, seed):
    rng = np.random.RandomState(seed)
    N = rng.poisson(rho)
    points = rng.uniform(0, 1, size=(N, dim))
    return points


def causal_order_periodic(points, dim):
    N = len(points)
    time_order = np.argsort(points[:, 0])
    pts = points[time_order]

    causal = set()
    for i in range(N):
        for j in range(i + 1, N):
            dt = pts[j, 0] - pts[i, 0]
            if dt <= 0:
                continue
            dx = np.abs(pts[j, 1:] - pts[i, 1:])
            dx = np.minimum(dx, 1.0 - dx)
            dist2 = np.sum(dx**2)
            if dist2 <= dt**2:
                causal.add((i, j))

    return causal, pts, N


def build_order_complex_capped(causal, N, max_dim, max_simplices=50000):
    """Order complex with hard cap on simplex count per dimension."""
    adj = defaultdict(set)
    for i, j in causal:
        adj[i].add(j)

    simplices = {0: set((v,) for v in range(N))}
    simplices[1] = set(causal)
    print(f"    0-simplices: {len(simplices[0])}")
    print(f"    1-simplices: {len(simplices[1])}")

    for k in range(2, max_dim + 1):
        t0 = time.time()
        simplices[k] = set()
        for chain in simplices[k - 1]:
            last = chain[-1]
            for nxt in adj[last]:
                if nxt > last:
                    simplices[k].add(chain + (nxt,))
            if len(simplices[k]) > max_simplices:
                break
        elapsed = time.time() - t0
        n_k = len(simplices[k])
        capped = " (CAPPED)" if n_k >= max_simplices else ""
        print(f"    {k}-simplices: {n_k}{capped} ({elapsed:.1f}s)")
        if n_k == 0:
            break

    return simplices


def boundary_matrix(simplices_k, simplices_km1):
    if not simplices_k or not simplices_km1:
        return None

    k_list = sorted(simplices_k)
    km1_list = sorted(simplices_km1)
    km1_idx = {s: i for i, s in enumerate(km1_list)}

    m, n = len(km1_list), len(k_list)
    if m * n > 50_000_000:
        print(f"    Matrix too large ({m}×{n}), skipping")
        return None

    mat = np.zeros((m, n), dtype=float)
    for j, sigma in enumerate(k_list):
        for i in range(len(sigma)):
            face = sigma[:i] + sigma[i + 1:]
            if face in km1_idx:
                mat[km1_idx[face], j] = (-1) ** i
    return mat


def compute_betti(simplices, max_dim):
    betti = {}
    ranks = {}

    for k in range(max_dim + 1):
        if k > 0 and k in simplices and (k - 1) in simplices:
            t0 = time.time()
            mat = boundary_matrix(simplices[k], simplices[k - 1])
            if mat is not None and mat.size > 0:
                ranks[k] = np.linalg.matrix_rank(mat, tol=1e-10)
            else:
                ranks[k] = 0
            elapsed = time.time() - t0
            print(f"    rank(∂_{k}) = {ranks[k]} ({elapsed:.1f}s)")
        else:
            ranks[k] = 0

    for k in range(max_dim + 1):
        n_k = len(simplices.get(k, set()))
        rank_dk = ranks.get(k, 0)
        rank_dkp1 = ranks.get(k + 1, 0)
        betti[k] = n_k - rank_dk - rank_dkp1

    return betti


def run_test(dim, max_dim, expected, rho, seed):
    print(f"\n--- T^{dim}, ρ={rho}, seed={seed} ---")
    t0 = time.time()

    points = poisson_sprinkling(rho, dim, seed)
    N = len(points)
    print(f"  N = {N}")

    if N < 3:
        print("  Too few points")
        return

    causal, pts, N = causal_order_periodic(points, dim)
    print(f"  Causal relations: {len(causal)}")
    print(f"  Causal density: {len(causal)/N:.1f} relations/event")

    print(f"  Building order complex...")
    simplices = build_order_complex_capped(causal, N, max_dim)

    print(f"  Computing Betti numbers...")
    betti = compute_betti(simplices, max_dim)

    all_match = True
    for k in range(max_dim + 1):
        exp = expected[k] if k < len(expected) else "?"
        match = "✓" if betti[k] == exp else "✗"
        if betti[k] != exp:
            all_match = False
        print(f"    β_{k} = {betti[k]}  (expect {exp}) {match}")

    elapsed = time.time() - t0
    print(f"  {'PASS' if all_match else 'FAIL'} ({elapsed:.1f}s)")


if __name__ == "__main__":
    print("=" * 65)
    print("ORDER COMPLEX VALIDATION")
    print("Using ALL causal relations (not just links)")
    print("=" * 65)

    # T² = T^2: β₀=1, β₁=2, β₂=1
    # Start VERY small to avoid combinatorial explosion
    for rho in [15, 20, 30, 50]:
        for seed in [42, 123]:
            run_test(dim=2, max_dim=2, expected=[1, 2, 1],
                     rho=rho, seed=seed)
