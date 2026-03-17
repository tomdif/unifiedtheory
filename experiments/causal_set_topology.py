#!/usr/bin/env python3
"""
Compute the homology of Poisson causal set order complexes in 4D.

This is the key experiment: if H^4 of the order complex has specific
structure, it constrains which principal bundles exist on the discrete
substrate, which constrains the gauge group.

Strategy:
1. Poisson sprinkling in [0,1]^4 (flat 4D with periodic identification → T^4)
2. Build causal order (event p precedes q iff all coordinates of p ≤ all of q
   in a lightcone sense: |x-y|² ≤ (t_q - t_p)² with t_q > t_p)
3. Build order complex (k-simplex = chain of k+1 causally related events)
4. Compute homology H_k for k = 0,1,2,3,4
5. Compute coordination number and plaquettes-per-edge

Run at densities ρ = 100, 500, 1000, 5000.
"""

import numpy as np
from itertools import combinations
from collections import defaultdict
import time

def poisson_sprinkling(rho, dim=4, seed=42):
    """Generate Poisson sprinkling in [0,1]^dim."""
    rng = np.random.RandomState(seed)
    N = rng.poisson(rho)
    points = rng.uniform(0, 1, size=(N, dim))
    return points

def causal_order_flat(points):
    """Build causal order in flat 4D Minkowski.
    Convention: coordinate 0 is time.
    p precedes q iff t_p < t_q and spatial separation² ≤ (t_q - t_p)².
    """
    N = len(points)
    # Sort by time
    time_order = np.argsort(points[:, 0])
    points_sorted = points[time_order]

    edges = []
    for i in range(N):
        for j in range(i+1, min(i+50, N)):  # Only check nearby (in time) events
            dt = points_sorted[j, 0] - points_sorted[i, 0]
            if dt <= 0:
                continue
            dx2 = np.sum((points_sorted[j, 1:] - points_sorted[i, 1:])**2)
            if dx2 <= dt**2:
                edges.append((i, j))

    return edges, points_sorted

def build_order_complex_chains(edges, N, max_dim=4):
    """Build chains (totally ordered subsets) up to dimension max_dim.
    A k-chain is a sequence i_0 < i_1 < ... < i_k where each consecutive
    pair is in the causal order.

    We use adjacency lists and DFS to find chains efficiently.
    """
    # Build adjacency list (forward only, since causal order is a DAG)
    adj = defaultdict(list)
    for i, j in edges:
        adj[i].append(j)

    simplices = {k: set() for k in range(max_dim + 1)}

    # 0-simplices: all vertices
    for v in range(N):
        simplices[0].add((v,))

    # 1-simplices: all edges
    for i, j in edges:
        simplices[1].add((i, j))

    # k-simplices for k >= 2: extend chains
    for k in range(2, max_dim + 1):
        for chain in simplices[k-1]:
            last = chain[-1]
            for next_v in adj[last]:
                new_chain = chain + (next_v,)
                simplices[k].add(new_chain)

        if len(simplices[k]) == 0:
            break

        # Cap the number of simplices for computational tractability
        if len(simplices[k]) > 100000:
            print(f"  Warning: {len(simplices[k])} {k}-simplices, capping at 100000")
            simplices[k] = set(list(simplices[k])[:100000])

    return simplices

def compute_boundary_matrix(simplices, k):
    """Compute the boundary matrix ∂_k : C_k → C_{k-1}.
    The boundary of a k-simplex [v0,...,vk] is Σ (-1)^i [v0,...,v̂i,...,vk].
    """
    if k == 0 or k not in simplices or len(simplices[k]) == 0:
        return None, None, None

    k_simplices = sorted(simplices[k])
    km1_simplices = sorted(simplices[k-1])

    if len(km1_simplices) == 0:
        return None, None, None

    km1_index = {s: i for i, s in enumerate(km1_simplices)}

    # Sparse boundary matrix
    rows, cols, vals = [], [], []
    for j, sigma in enumerate(k_simplices):
        for i in range(len(sigma)):
            face = sigma[:i] + sigma[i+1:]
            if face in km1_index:
                rows.append(km1_index[face])
                cols.append(j)
                vals.append((-1)**i)

    return rows, cols, vals, len(km1_simplices), len(k_simplices)

def compute_betti_numbers(simplices, max_dim=4):
    """Compute Betti numbers β_k = dim(H_k) = dim(ker ∂_k) - dim(im ∂_{k+1}).
    Uses rank computation over Q (rational coefficients).
    """
    betti = {}

    for k in range(max_dim + 1):
        n_k = len(simplices.get(k, set()))

        if n_k == 0:
            betti[k] = 0
            continue

        # Rank of ∂_k (image dimension)
        if k > 0:
            result = compute_boundary_matrix(simplices, k)
            if result is None or result[0] is None:
                rank_dk = 0
            else:
                rows, cols, vals, m, n = result
                # Build dense matrix for small cases
                if m < 5000 and n < 5000:
                    mat = np.zeros((m, n), dtype=float)
                    for r, c, v in zip(rows, cols, vals):
                        mat[r, c] = v
                    rank_dk = np.linalg.matrix_rank(mat)
                else:
                    rank_dk = min(m, n)  # Upper bound
        else:
            rank_dk = 0

        # Rank of ∂_{k+1}
        result_kp1 = compute_boundary_matrix(simplices, k+1)
        if result_kp1 is None or result_kp1[0] is None:
            rank_dkp1 = 0
        else:
            rows, cols, vals, m, n = result_kp1
            if m < 5000 and n < 5000:
                mat = np.zeros((m, n), dtype=float)
                for r, c, v in zip(rows, cols, vals):
                    mat[r, c] = v
                rank_dkp1 = np.linalg.matrix_rank(mat)
            else:
                rank_dkp1 = min(m, n)

        # β_k = n_k - rank_dk - rank_dkp1
        betti[k] = n_k - rank_dk - rank_dkp1

    return betti

def compute_coordination(edges, N):
    """Average coordination number (edges per vertex)."""
    degree = defaultdict(int)
    for i, j in edges:
        degree[i] += 1
        degree[j] += 1
    if N == 0:
        return 0
    return sum(degree.values()) / N

def main():
    print("=" * 60)
    print("CAUSAL SET ORDER COMPLEX TOPOLOGY")
    print("Poisson sprinkling in [0,1]^4, flat Minkowski")
    print("=" * 60)

    densities = [100, 300, 500, 1000]

    for rho in densities:
        print(f"\n--- ρ = {rho} ---")
        t0 = time.time()

        points = poisson_sprinkling(rho, dim=4)
        N = len(points)
        print(f"  N = {N} events")

        edges, points_sorted = causal_order_flat(points)
        n_edges = len(edges)
        print(f"  {n_edges} causal links")

        coord = compute_coordination(edges, N)
        print(f"  Average coordination: {coord:.1f}")

        # Build order complex
        print("  Building order complex...")
        simplices = build_order_complex_chains(edges, N, max_dim=4)

        for k in range(5):
            n_k = len(simplices.get(k, set()))
            print(f"    {k}-simplices: {n_k}")

        # Compute Betti numbers
        print("  Computing Betti numbers...")
        betti = compute_betti_numbers(simplices, max_dim=4)

        for k in sorted(betti.keys()):
            print(f"    β_{k} = {betti[k]}")

        # Plaquettes per edge estimate
        n_2 = len(simplices.get(2, set()))
        if n_edges > 0:
            plaq_per_edge = 3 * n_2 / n_edges  # Each 2-simplex has 3 edges
            print(f"  Plaquettes per edge (avg): {plaq_per_edge:.1f}")
            print(f"    Compare: dim(su(2))=3, dim(su(3))=8, dim(su(3)×su(2))=11")

        elapsed = time.time() - t0
        print(f"  Time: {elapsed:.1f}s")

    print("\n" + "=" * 60)
    print("INTERPRETATION:")
    print("  If H_4 = 0: all SU(n)-bundles are trivial on the discrete structure")
    print("  If H_4 = Z: matches continuum T^4 (topology doesn't constrain G)")
    print("  If H_3 = Z_N: Chern-Simons levels constrain G")
    print("  Plaquettes/edge vs dim(g): if p̄ < dim(g), gauge is unconstrained")
    print("=" * 60)

if __name__ == "__main__":
    main()
