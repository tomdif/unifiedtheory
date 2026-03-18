#!/usr/bin/env python3
"""
Vietoris-Rips homology of Poisson causal sets.

The ORDER COMPLEX failed (too many simplices, wrong topology).
The LINK COMPLEX failed (triangle-free, no higher topology).

This tries the RIPS COMPLEX at scale k:
- Two events p,q are "k-close" if p ≺ q and |I(p,q)| ≤ k
  (Alexandrov interval has at most k intermediate events)
- k=0: links only (triangle-free, no topology)
- k→∞: all causal pairs (order complex, too many simplices)
- Optimal k: should recover manifold topology

Test on T² first (expect β₀=1, β₁=2, β₂=1).
"""

import numpy as np
from collections import defaultdict
import time


def poisson_sprinkling(rho, dim, seed):
    rng = np.random.RandomState(seed)
    N = rng.poisson(rho)
    return rng.uniform(0, 1, size=(N, dim))


def build_causal_set(points, dim):
    """Build causal order with periodic spatial BCs."""
    N = len(points)
    order = np.argsort(points[:, 0])
    pts = points[order]

    # All causal pairs
    causal = {}  # (i,j) -> number of intermediate events
    for i in range(N):
        for j in range(i+1, N):
            dt = pts[j, 0] - pts[i, 0]
            if dt <= 0:
                continue
            dx = np.abs(pts[j, 1:] - pts[i, 1:])
            dx = np.minimum(dx, 1.0 - dx)
            if np.sum(dx**2) <= dt**2:
                causal[(i,j)] = 0  # will count intermediates later

    # Count intermediate events for each causal pair
    causal_set = set(causal.keys())
    for (i,j) in list(causal.keys()):
        count = 0
        for k in range(i+1, j):
            if (i,k) in causal_set and (k,j) in causal_set:
                count += 1
        causal[(i,j)] = count

    return causal, pts, N


def build_rips_complex(causal, N, k_threshold, max_dim):
    """Build Vietoris-Rips complex at scale k.
    Edge (i,j) included iff (i,j) is causal with ≤ k intermediate events.
    Then take the flag complex (clique complex).
    """
    # Build adjacency from k-close pairs
    adj = defaultdict(set)
    edges = set()
    for (i,j), count in causal.items():
        if count <= k_threshold:
            adj[i].add(j)
            adj[j].add(i)
            edges.add((min(i,j), max(i,j)))

    simplices = {0: set((v,) for v in range(N))}
    simplices[1] = edges

    # Flag complex: k-cliques from adjacency
    for d in range(2, max_dim + 1):
        simplices[d] = set()
        for clique in simplices[d-1]:
            candidates = set(range(N))
            for v in clique:
                candidates &= adj[v]
            for nxt in candidates:
                if nxt > max(clique):
                    new_clique = tuple(sorted(clique + (nxt,)))
                    simplices[d].add(new_clique)
            if len(simplices[d]) > 200000:
                print(f"      Capping {d}-simplices at 200000")
                simplices[d] = set(list(simplices[d])[:200000])
                break
        if not simplices[d]:
            break

    return simplices


def compute_betti(simplices, max_dim):
    """Compute Betti numbers via SVD."""
    ranks = {}
    for k in range(max_dim + 1):
        if k > 0 and k in simplices and (k-1) in simplices and simplices[k]:
            k_list = sorted(simplices[k])
            km1_list = sorted(simplices[k-1])
            km1_idx = {s: i for i, s in enumerate(km1_list)}
            m, n_cols = len(km1_list), len(k_list)
            if m * n_cols > 20_000_000:
                print(f"      ∂_{k}: {m}×{n_cols} too large, skipping")
                ranks[k] = 0
                continue
            mat = np.zeros((m, n_cols))
            for j, sigma in enumerate(k_list):
                for i in range(len(sigma)):
                    face = sigma[:i] + sigma[i+1:]
                    if face in km1_idx:
                        mat[km1_idx[face], j] = (-1)**i
            ranks[k] = np.linalg.matrix_rank(mat, tol=1e-10)
        else:
            ranks[k] = 0

    betti = {}
    for k in range(max_dim + 1):
        n_k = len(simplices.get(k, set()))
        betti[k] = n_k - ranks.get(k, 0) - ranks.get(k+1, 0)
    return betti


def test_T2(rho, seed, max_dim=2):
    """Test on T² for various Rips scales k."""
    print(f"\n  ρ={rho}, seed={seed}")
    points = poisson_sprinkling(rho, 2, seed)
    N = len(points)
    print(f"  N={N}")

    causal, pts, N = build_causal_set(points, 2)
    print(f"  Causal pairs: {len(causal)}")

    # Distribution of interval sizes
    interval_sizes = list(causal.values())
    if interval_sizes:
        print(f"  Interval sizes: min={min(interval_sizes)}, "
              f"median={sorted(interval_sizes)[len(interval_sizes)//2]}, "
              f"max={max(interval_sizes)}")

    # Try various k thresholds
    expected = [1, 2, 1]
    for k in [0, 1, 2, 3, 5, 8, 12, 20]:
        n_edges = sum(1 for (i,j), c in causal.items() if c <= k)
        if n_edges == 0:
            continue

        t0 = time.time()
        simplices = build_rips_complex(causal, N, k, max_dim)
        betti = compute_betti(simplices, max_dim)
        elapsed = time.time() - t0

        n_simp = [len(simplices.get(d, set())) for d in range(max_dim+1)]
        match = all(betti.get(d, -1) == expected[d] for d in range(max_dim+1))
        status = "✓ MATCH" if match else "✗"

        betti_str = ", ".join(f"β{d}={betti.get(d,0)}" for d in range(max_dim+1))
        print(f"    k={k:2d}: edges={n_edges:5d}, "
              f"simpl={n_simp}, "
              f"{betti_str}  {status}  ({elapsed:.1f}s)")

        if match:
            return k  # Return the working scale
        if elapsed > 30:
            print(f"    (stopping k sweep, too slow)")
            break
    return None


def main():
    print("=" * 70)
    print("VIETORIS-RIPS HOMOLOGY ON T²")
    print("Expected: β₀=1, β₁=2, β₂=1")
    print("Rips scale k = max Alexandrov interval size for edge inclusion")
    print("=" * 70)

    for rho in [50, 100, 200]:
        for seed in [42, 123]:
            test_T2(rho, seed)


if __name__ == "__main__":
    main()
