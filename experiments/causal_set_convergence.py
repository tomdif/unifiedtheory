#!/usr/bin/env python3
"""
Convergence test for plaquettes-per-link on Poisson causal sets.

Key question: does p̄ converge or diverge as ρ → ∞?
If it diverges, the gauge constraint direction is dead.
If it converges, p̄_∞(d) is a dimension-dependent constant worth computing.

CRITICAL FIX from previous version:
- Build simplicial complex from LINKS ONLY (not all causal relations)
- Links = nearest causal neighbors (no intermediate event)

Also: T² validation (should give β₀=1, β₁=2, β₂=1).
"""

import numpy as np
from collections import defaultdict
import time
import sys


def poisson_sprinkling(rho, dim, seed):
    """Generate Poisson sprinkling in [0,1]^dim."""
    rng = np.random.RandomState(seed)
    N = rng.poisson(rho)
    points = rng.uniform(0, 1, size=(N, dim))
    return points


def causal_order_periodic(points, dim):
    """Build causal order with periodic spatial BCs.
    Time (coord 0) is NOT periodic. Spatial coords are periodic.
    p ≺ q iff dt > 0 and spatial_dist² ≤ dt² (Minkowski lightcone).
    Returns links (nearest causal neighbors) only.
    """
    N = len(points)
    time_order = np.argsort(points[:, 0])
    pts = points[time_order]

    # Build all causal relations
    causal = set()
    for i in range(N):
        for j in range(i + 1, N):
            dt = pts[j, 0] - pts[i, 0]
            if dt <= 0:
                continue
            dx = np.abs(pts[j, 1:] - pts[i, 1:])
            dx = np.minimum(dx, 1.0 - dx)  # Periodic spatial
            dist2 = np.sum(dx**2)
            if dist2 <= dt**2:
                causal.add((i, j))

    # Extract LINKS: (i,j) is a link iff no k with i≺k≺j
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

    return list(links), pts, N


def build_link_complex(links, N, max_dim):
    """Build simplicial complex from LINKS ONLY.

    A k-simplex = a set of k+1 events that are PAIRWISE connected by links.
    This is the clique complex (flag complex) of the link graph.

    NOT the order complex of the full causal order.
    """
    # Build undirected link adjacency (for clique finding)
    link_adj = defaultdict(set)
    for i, j in links:
        link_adj[i].add(j)
        link_adj[j].add(i)

    # Also keep directed for chain structure
    link_fwd = defaultdict(set)
    for i, j in links:
        link_fwd[i].add(j)

    simplices = {0: set((v,) for v in range(N))}
    # 1-simplices = links (directed, as tuples)
    simplices[1] = set(tuple(sorted(e)) for e in links)

    # k-simplices: extend (k-1)-cliques by vertices adjacent to ALL members
    for k in range(2, max_dim + 1):
        simplices[k] = set()
        for clique in simplices[k - 1]:
            # Find vertices connected to ALL vertices in the clique
            candidates = set(range(N))
            for v in clique:
                candidates &= link_adj[v]
            for nxt in candidates:
                if nxt > max(clique):  # Avoid duplicates
                    new_clique = tuple(sorted(clique + (nxt,)))
                    simplices[k].add(new_clique)
        if len(simplices[k]) > 100000:
            print(f"    Capping {k}-simplices at 100000 (was {len(simplices[k])})")
            simplices[k] = set(list(simplices[k])[:100000])
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
            face = sigma[:i] + sigma[i + 1:]
            if face in km1_idx:
                mat[km1_idx[face], j] = (-1) ** i

    return mat


def compute_betti(simplices, max_dim):
    """Compute Betti numbers using SVD rank."""
    betti = {}
    ranks = {}

    for k in range(max_dim + 1):
        if k > 0 and k in simplices and (k - 1) in simplices:
            mat = boundary_matrix(simplices[k], simplices[k - 1])
            if mat is not None and mat.size > 0:
                ranks[k] = np.linalg.matrix_rank(mat, tol=1e-10)
            else:
                ranks[k] = 0
        else:
            ranks[k] = 0

    for k in range(max_dim + 1):
        n_k = len(simplices.get(k, set()))
        rank_dk = ranks.get(k, 0)
        rank_dkp1 = ranks.get(k + 1, 0)
        betti[k] = n_k - rank_dk - rank_dkp1

    return betti


def run_single(rho, dim, seed, max_dim, verbose=True):
    """Run one sprinkling and return stats."""
    t0 = time.time()
    points = poisson_sprinkling(rho, dim, seed)
    N = len(points)

    if N < 2:
        return None

    links, pts, N = causal_order_periodic(points, dim)
    n_links = len(links)

    if verbose:
        print(f"  N={N}, links={n_links}", end="")

    simplices = build_link_complex(links, N, max_dim)

    n_0 = len(simplices.get(0, set()))
    n_1 = len(simplices.get(1, set()))
    n_2 = len(simplices.get(2, set()))

    # Plaquettes per link (using link-only complex)
    if n_1 > 0:
        # Each 2-simplex (triangle) has 3 edges
        # p̄ = 3 * n_2 / n_1
        p_bar = 3 * n_2 / n_1
    else:
        p_bar = 0.0

    # Links per event
    links_per_event = 2 * n_1 / N if N > 0 else 0

    elapsed = time.time() - t0

    if verbose:
        print(f", 2-simpl={n_2}, p̄={p_bar:.3f}, links/event={links_per_event:.2f}, {elapsed:.1f}s")

    return {
        'N': N, 'n_links': n_links, 'n_1': n_1, 'n_2': n_2,
        'p_bar': p_bar, 'links_per_event': links_per_event,
        'simplices': simplices, 'elapsed': elapsed
    }


def validate_T2():
    """Validate on T² — should give β₀=1, β₁=2, β₂=1."""
    print("=" * 65)
    print("VALIDATION: T² (2D torus)")
    print("Expected: β₀=1, β₁=2, β₂=1")
    print("=" * 65)

    for rho in [100, 200, 400]:
        for seed in [42, 123]:
            print(f"\n  ρ={rho}, seed={seed}:")
            result = run_single(rho, dim=2, seed=seed, max_dim=2, verbose=True)
            if result is None:
                print("    Too few points")
                continue
            betti = compute_betti(result['simplices'], max_dim=2)
            for k in range(3):
                expected = [1, 2, 1][k]
                match = "✓" if betti[k] == expected else "✗"
                print(f"    β_{k} = {betti[k]}  (expect {expected}) {match}")


def convergence_test():
    """Test whether p̄ converges as ρ → ∞."""
    print("\n" + "=" * 65)
    print("CONVERGENCE TEST: p̄ vs ρ on T⁴")
    print("Using LINK-ONLY complex (flag complex of link graph)")
    print("=" * 65)

    densities = [50, 100, 200, 400]
    # Skip 800, 1600 if too slow — O(N³) for link extraction
    seeds = [42, 123, 456]

    results = []
    for rho in densities:
        p_bars = []
        links_per_events = []
        print(f"\n--- ρ = {rho} ---")
        for seed in seeds:
            print(f"  seed={seed}: ", end="")
            sys.stdout.flush()
            result = run_single(rho, dim=4, seed=seed, max_dim=4, verbose=True)
            if result is not None:
                p_bars.append(result['p_bar'])
                links_per_events.append(result['links_per_event'])

        if p_bars:
            mean_p = np.mean(p_bars)
            std_p = np.std(p_bars)
            mean_l = np.mean(links_per_events)
            print(f"  → p̄ = {mean_p:.3f} ± {std_p:.3f}, links/event = {mean_l:.2f}")
            results.append((rho, mean_p, std_p, mean_l))

    print("\n" + "=" * 65)
    print("SUMMARY: p̄ vs ρ")
    print(f"{'ρ':>8}  {'p̄':>8}  {'±σ':>8}  {'links/event':>12}")
    print("-" * 40)
    for rho, mean_p, std_p, mean_l in results:
        print(f"{rho:>8}  {mean_p:>8.3f}  {std_p:>8.3f}  {mean_l:>12.2f}")

    if len(results) >= 3:
        rhos = [r[0] for r in results]
        pbars = [r[1] for r in results]
        # Check if p̄ is roughly linear in ρ (diverging)
        # or flattening (converging)
        ratios = [pbars[i+1]/pbars[i] for i in range(len(pbars)-1)]
        density_ratios = [rhos[i+1]/rhos[i] for i in range(len(rhos)-1)]
        print(f"\nScaling check (ratio of p̄ when ρ doubles):")
        for i in range(len(ratios)):
            print(f"  ρ: {rhos[i]} → {rhos[i+1]}: p̄ ratio = {ratios[i]:.3f} (ρ ratio = {density_ratios[i]:.1f})")
        print(f"\nIf p̄ ratio ≈ ρ ratio: p̄ ~ ρ (DIVERGES, direction dead)")
        print(f"If p̄ ratio ≈ 1: p̄ converges (direction alive)")
        print(f"If p̄ ratio ≈ √(ρ ratio): p̄ ~ √ρ (diverges, but slowly)")

    print("=" * 65)


if __name__ == "__main__":
    validate_T2()
    convergence_test()
