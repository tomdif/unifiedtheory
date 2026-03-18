#!/usr/bin/env python3
"""
TEST: Does the causal set in d=3 spatial dimensions give exactly 3
independent defect propagation channels (= 3 generations)?

THE CONJECTURE: N_g = d. The spatial metric perturbation h_ij is a
d×d symmetric matrix with d eigenvalues. If defects aligned with
different eigenvectors propagate independently, there are d = 3
"generation" channels.

THE TEST:
1. Sprinkle a Poisson causal set in 3+1D Minkowski
2. At each event, compute the link-direction tensor:
   T_ij = Σ_{future links} Δx_i · Δx_j / |Δx|²
   This captures the angular distribution of outgoing links.
3. Diagonalize T_ij → 3 eigenvalues λ₁ ≥ λ₂ ≥ λ₃
4. KEY QUESTION: are the 3 eigenvectors PERSISTENT along causal chains?
   If eigenvector v₁ at event p aligns with eigenvector v₁ at the
   next event q (linked to p), then the eigenvectors define persistent
   "channels" for defect propagation = generations.

If persistent: 3 channels = 3 generations. N_g = d confirmed.
If random: no persistent structure. N_g ≠ d (or the mechanism is different).

Also test in d=2 (should give 2 channels) and d=4 (should give 4).
"""

import numpy as np
from collections import defaultdict


def poisson_sprinkling(rho, dim, seed=42):
    rng = np.random.RandomState(seed)
    N = rng.poisson(rho)
    return rng.uniform(0, 1, size=(N, dim))


def build_links(points, dim):
    """Find links (nearest causal neighbors) with periodic spatial BCs."""
    N = len(points)
    order = np.argsort(points[:, 0])
    pts = points[order]

    # All causal pairs
    causal = set()
    for i in range(N):
        for j in range(i+1, N):
            dt = pts[j, 0] - pts[i, 0]
            if dt <= 0:
                continue
            dx = np.abs(pts[j, 1:] - pts[i, 1:])
            dx = np.minimum(dx, 1.0 - dx)  # Periodic
            if np.sum(dx**2) <= dt**2:
                causal.add((i, j))

    # Extract links (no intermediate event)
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

    return links, pts


def link_direction_tensor(pts, links, event, d_spatial):
    """Compute the link-direction tensor T_ij at a given event.
    T_ij = Σ_{future links from event} Δx_i · Δx_j / |Δx|²
    where Δx is the spatial displacement (periodic). """
    T = np.zeros((d_spatial, d_spatial))
    n_links = 0

    for (i, j) in links:
        if i == event:
            # Future link from event to j
            dx = pts[j, 1:] - pts[i, 1:]
            # Periodic
            dx = np.where(np.abs(dx) > 0.5, dx - np.sign(dx), dx)
            r2 = np.sum(dx**2)
            if r2 > 1e-20:
                T += np.outer(dx, dx) / r2
                n_links += 1

    if n_links > 0:
        T /= n_links

    return T, n_links


def eigenvector_persistence(pts, links, d_spatial, n_chains=100, chain_length=5):
    """Test whether eigenvectors of T_ij persist along causal chains.

    For each chain of linked events p₀ → p₁ → ... → p_k:
    - Compute T_ij at each event
    - Diagonalize to get eigenvectors v₁, v₂, v₃
    - Measure the overlap |v_i(p_{k}) · v_j(p_{k-1})| between consecutive events
    - If persistent: diagonal overlaps ~1, off-diagonal ~0
    - If random: all overlaps ~1/√d (random projection)
    """
    # Build adjacency for future links
    future_links = defaultdict(list)
    for (i, j) in links:
        future_links[i].append(j)

    # Events with enough links
    good_events = [e for e in range(len(pts))
                   if len(future_links[e]) >= d_spatial]

    if len(good_events) < n_chains:
        print(f"  Warning: only {len(good_events)} events with ≥{d_spatial} links")
        n_chains = min(n_chains, len(good_events))

    rng = np.random.RandomState(123)
    diagonal_overlaps = []
    offdiag_overlaps = []

    chains_found = 0
    for _ in range(n_chains * 10):
        if chains_found >= n_chains:
            break

        # Start from a random good event
        start = good_events[rng.randint(len(good_events))]
        chain = [start]

        # Follow links
        current = start
        for _ in range(chain_length):
            neighbors = [j for j in future_links[current]
                        if len(future_links[j]) >= d_spatial]
            if not neighbors:
                break
            current = neighbors[rng.randint(len(neighbors))]
            chain.append(current)

        if len(chain) < 3:
            continue

        chains_found += 1

        # Compute T and eigenvectors along the chain
        prev_evecs = None
        for event in chain:
            T, nl = link_direction_tensor(pts, links, event, d_spatial)
            if nl < d_spatial:
                prev_evecs = None
                continue

            eigenvalues, eigenvectors = np.linalg.eigh(T)
            # Sort by eigenvalue (descending)
            idx = np.argsort(eigenvalues)[::-1]
            eigenvalues = eigenvalues[idx]
            eigenvectors = eigenvectors[:, idx]

            if prev_evecs is not None:
                # Compute overlap matrix |v_i(current) · v_j(previous)|
                overlap = np.abs(eigenvectors.T @ prev_evecs)

                for i in range(d_spatial):
                    diagonal_overlaps.append(overlap[i, i])
                    for j in range(d_spatial):
                        if i != j:
                            offdiag_overlaps.append(overlap[i, j])

            prev_evecs = eigenvectors

    return diagonal_overlaps, offdiag_overlaps


def run_test(d_total, rho, seed=42):
    """Run the generation test in d_total dimensions (d_spatial = d_total - 1)."""
    d_spatial = d_total - 1
    print(f"\n{'='*60}")
    print(f"GENERATION TEST: d_spatial = {d_spatial} ({d_total}D spacetime)")
    print(f"ρ = {rho}, seed = {seed}")
    print(f"{'='*60}")

    points = poisson_sprinkling(rho, d_total, seed)
    N = len(points)
    print(f"  N = {N} events")

    links, pts = build_links(points, d_total)
    print(f"  {len(links)} links")

    if len(links) < 10:
        print("  Too few links, skipping")
        return None

    # Eigenvalue statistics of T_ij
    eigenvalue_lists = [[] for _ in range(d_spatial)]
    n_good = 0

    for event in range(N):
        T, nl = link_direction_tensor(pts, links, event, d_spatial)
        if nl >= d_spatial:
            evals = np.sort(np.linalg.eigvalsh(T))[::-1]
            for k in range(d_spatial):
                eigenvalue_lists[k].append(evals[k])
            n_good += 1

    print(f"  {n_good} events with ≥{d_spatial} links")

    if n_good < 10:
        print("  Too few good events")
        return None

    # Eigenvalue statistics
    print(f"\n  Eigenvalue statistics of link-direction tensor T_ij:")
    means = []
    for k in range(d_spatial):
        vals = np.array(eigenvalue_lists[k])
        means.append(vals.mean())
        print(f"    λ_{k+1}: mean={vals.mean():.4f} ± {vals.std():.4f}")

    # Are eigenvalues degenerate or split?
    if d_spatial >= 2:
        ratio = means[0] / means[-1] if means[-1] > 0 else float('inf')
        print(f"    λ_max/λ_min ratio: {ratio:.3f}")
        print(f"    (Isotropic → ratio=1.0; Anisotropic → ratio>1)")

    # Eigenvector persistence test
    print(f"\n  Eigenvector persistence along causal chains:")
    diag, offdiag = eigenvector_persistence(pts, links, d_spatial,
                                             n_chains=50, chain_length=5)

    if diag and offdiag:
        mean_diag = np.mean(diag)
        mean_offdiag = np.mean(offdiag)
        random_expectation = 1.0 / np.sqrt(d_spatial)

        print(f"    Diagonal overlap ⟨|v_i(p)·v_i(q)|⟩: {mean_diag:.4f}")
        print(f"    Off-diagonal overlap ⟨|v_i(p)·v_j(q)|⟩: {mean_offdiag:.4f}")
        print(f"    Random expectation: {random_expectation:.4f}")
        print()

        if mean_diag > random_expectation * 1.5 and mean_offdiag < mean_diag * 0.8:
            print(f"    → PERSISTENT: eigenvectors define {d_spatial} independent channels")
            print(f"    → N_g = {d_spatial} supported!")
        elif abs(mean_diag - mean_offdiag) < 0.05:
            print(f"    → RANDOM: no persistent structure")
            print(f"    → N_g = d NOT supported by eigenvector persistence")
        else:
            print(f"    → INTERMEDIATE: partial persistence")
            print(f"    → Result inconclusive")

    return {
        'd_spatial': d_spatial,
        'eigenvalue_means': means,
        'diag_overlap': np.mean(diag) if diag else None,
        'offdiag_overlap': np.mean(offdiag) if offdiag else None,
    }


def main():
    print("=" * 60)
    print("N_g = d CONJECTURE TEST")
    print("Does the causal set give d independent defect families?")
    print("=" * 60)

    results = []

    # Test in 2+1D (should give 2 channels)
    r = run_test(d_total=3, rho=100, seed=42)
    if r: results.append(r)

    # Test in 3+1D (should give 3 channels — THE KEY TEST)
    r = run_test(d_total=4, rho=80, seed=42)
    if r: results.append(r)

    # Test in 4+1D (should give 4 channels)
    r = run_test(d_total=5, rho=50, seed=42)
    if r: results.append(r)

    print(f"\n{'='*60}")
    print("SUMMARY")
    print(f"{'='*60}")
    for r in results:
        d = r['d_spatial']
        diag = r.get('diag_overlap')
        offdiag = r.get('offdiag_overlap')
        random_exp = 1.0/np.sqrt(d)
        persist = "YES" if diag and diag > random_exp * 1.5 else "NO"
        print(f"  d={d}: diag={diag:.4f if diag else 0:.4f}, "
              f"offdiag={offdiag:.4f if offdiag else 0:.4f}, "
              f"random={random_exp:.4f}, persistent={persist}")


if __name__ == "__main__":
    main()
