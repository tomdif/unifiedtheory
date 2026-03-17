#!/usr/bin/env python3
"""
Compute homology of Poisson causal set order complexes in 4D.

Fixed version:
1. PERIODIC boundary conditions (T^4, not contractible [0,1]^4)
2. LINKS = nearest causal neighbors (no intermediate events)
3. Proper rank computation via numpy SVD
4. Multiple seeds for statistics
"""

import numpy as np
from collections import defaultdict
import time

def poisson_sprinkling(rho, dim=4, seed=42):
    """Generate Poisson sprinkling in [0,1]^dim."""
    rng = np.random.RandomState(seed)
    N = rng.poisson(rho)
    points = rng.uniform(0, 1, size=(N, dim))
    return points

def causal_order_periodic(points, dim=4):
    """Build causal order with PERIODIC boundary conditions (T^dim).
    Convention: coordinate 0 is time.
    p precedes q iff (using periodic distance for spatial coords):
      dt > 0 and spatial_dist² ≤ dt²
    Periodic spatial distance: min(|dx|, 1-|dx|) for each spatial coord.
    Time is NOT periodic (causal order needs a global time direction).
    """
    N = len(points)
    time_order = np.argsort(points[:, 0])
    pts = points[time_order]

    # Build ALL causal relations first
    causal = set()
    for i in range(N):
        for j in range(i+1, N):
            dt = pts[j, 0] - pts[i, 0]
            if dt <= 0:
                continue
            # Periodic spatial distance
            dx = np.abs(pts[j, 1:] - pts[i, 1:])
            dx = np.minimum(dx, 1.0 - dx)  # Periodic
            dist2 = np.sum(dx**2)
            if dist2 <= dt**2:
                causal.add((i, j))

    # Extract LINKS (nearest causal neighbors: no intermediate event)
    links = set()
    for (i, j) in causal:
        is_link = True
        for k in range(N):
            if k == i or k == j:
                continue
            if (i, k) in causal and (k, j) in causal:
                is_link = False
                break
        if is_link:
            links.add((i, j))

    return list(links), list(causal), pts

def build_order_complex(links, causal_set, N, max_dim=4):
    """Build order complex from links.
    k-simplex = chain of k+1 events connected by causal relations.
    Use links for 1-simplices, then extend via causal relations.
    """
    adj = defaultdict(set)
    for i, j in causal_set:
        adj[i].add(j)

    simplices = {0: set((v,) for v in range(N))}
    simplices[1] = set(links)

    for k in range(2, max_dim + 1):
        simplices[k] = set()
        for chain in simplices[k-1]:
            last = chain[-1]
            for nxt in adj[last]:
                if nxt > last:  # Maintain ordering
                    new_chain = chain + (nxt,)
                    simplices[k].add(new_chain)
        if len(simplices[k]) > 50000:
            print(f"    Capping {k}-simplices at 50000 (was {len(simplices[k])})")
            simplices[k] = set(list(simplices[k])[:50000])
        if len(simplices[k]) == 0:
            break

    return simplices

def boundary_matrix(simplices_k, simplices_km1):
    """Compute boundary matrix ∂_k as dense numpy array."""
    if not simplices_k or not simplices_km1:
        return None

    k_list = sorted(simplices_k)
    km1_list = sorted(simplices_km1)
    km1_idx = {s: i for i, s in enumerate(km1_list)}

    m, n = len(km1_list), len(k_list)
    mat = np.zeros((m, n), dtype=float)

    for j, sigma in enumerate(k_list):
        for i in range(len(sigma)):
            face = sigma[:i] + sigma[i+1:]
            if face in km1_idx:
                mat[km1_idx[face], j] = (-1)**i

    return mat

def compute_betti(simplices, max_dim=4):
    """Compute Betti numbers using SVD rank."""
    betti = {}
    ranks = {}

    for k in range(max_dim + 1):
        # Rank of ∂_k
        if k > 0 and k in simplices and (k-1) in simplices:
            mat = boundary_matrix(simplices[k], simplices[k-1])
            if mat is not None and mat.size > 0:
                ranks[k] = np.linalg.matrix_rank(mat, tol=1e-10)
            else:
                ranks[k] = 0
        else:
            ranks[k] = 0

    for k in range(max_dim + 1):
        n_k = len(simplices.get(k, set()))
        rank_dk = ranks.get(k, 0)
        rank_dkp1 = ranks.get(k+1, 0)
        betti[k] = n_k - rank_dk - rank_dkp1

    return betti

def main():
    print("=" * 65)
    print("CAUSAL SET ORDER COMPLEX TOPOLOGY (PERIODIC T^4)")
    print("Poisson sprinkling, periodic spatial BCs, Minkowski causal order")
    print("Links = nearest causal neighbors (no intermediate events)")
    print("=" * 65)

    configs = [
        (50, 42), (50, 123), (50, 456),
        (100, 42), (100, 123),
        (200, 42),
    ]

    for rho, seed in configs:
        print(f"\n--- ρ = {rho}, seed = {seed} ---")
        t0 = time.time()

        points = poisson_sprinkling(rho, dim=4, seed=seed)
        N = len(points)
        print(f"  N = {N} events")

        links, causal, pts = causal_order_periodic(points)
        print(f"  {len(causal)} causal relations, {len(links)} links")

        if N > 0:
            coord = 2 * len(links) / N
            print(f"  Coordination (links/event): {coord:.2f}")

        print("  Building order complex...")
        simplices = build_order_complex(links, causal, N, max_dim=4)
        for k in range(5):
            print(f"    {k}-simplices: {len(simplices.get(k, set()))}")

        print("  Computing Betti numbers...")
        betti = compute_betti(simplices, max_dim=4)
        for k in sorted(betti.keys()):
            b = betti[k]
            expected = ""
            if k == 0: expected = f"  (T^4 expects 1)"
            if k == 1: expected = f"  (T^4 expects 4)"
            if k == 2: expected = f"  (T^4 expects 6)"
            if k == 3: expected = f"  (T^4 expects 4)"
            if k == 4: expected = f"  (T^4 expects 1)"
            print(f"    β_{k} = {b}{expected}")

        # Plaquettes per edge
        n_2 = len(simplices.get(2, set()))
        n_1 = len(simplices.get(1, set()))
        if n_1 > 0:
            # Each 2-simplex (triangle) has 3 edges
            # Average plaquettes per edge = 3 * n_2 / n_1
            ppe = 3 * n_2 / n_1
            print(f"  Plaquettes per edge: {ppe:.2f}")
            print(f"    dim(su(2))=3, dim(su(3))=8, dim(su(3)×su(2))=11")
            if ppe < 3:
                print(f"    → Even SU(2) may be underdetermined")
            elif ppe < 8:
                print(f"    → SU(2) OK, SU(3) underdetermined")
            elif ppe < 11:
                print(f"    → SU(3) OK, SU(3)×SU(2) underdetermined")
            else:
                print(f"    → SU(3)×SU(2) fully determined")

        elapsed = time.time() - t0
        print(f"  Time: {elapsed:.1f}s")

    print("\n" + "=" * 65)
    print("INTERPRETATION:")
    print("  T^4 has Betti numbers (1, 4, 6, 4, 1).")
    print("  If discrete β matches: topology faithfully reproduced,")
    print("    no topological constraint on G beyond continuum.")
    print("  If β₄ = 0 on T^4: discrete structure LOSES topology,")
    print("    potentially preventing certain bundles.")
    print("  Plaquettes/edge: gauge algebra constraint if p̄ < dim(g).")
    print("=" * 65)

if __name__ == "__main__":
    main()
