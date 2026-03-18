#!/usr/bin/env python3
"""
SU(3) on a Poisson lattice: measure the string tension as a function
of bare coupling to determine the effective g²(M_P).

On a regular lattice, SU(3) Wilson gauge theory gives:
  String tension σ·a² = -ln(β/18) for β = 6/g² at strong coupling
  σ·a² → 0 as β → β_c (continuum limit)

On a POISSON lattice (random), the local connectivity fluctuates.
The question: what bare coupling g² on the Poisson lattice gives
the same string tension as the continuum SU(3)?

METHOD:
1. Generate a Poisson sprinkling in a 4D box
2. Find links (nearest causal neighbors)
3. For each plaquette (minimal loop of 4 links), assign SU(3) matrices
4. Define the Wilson action: S = Σ_plaq (1/g²)(1 - Re(tr(U_plaq))/3)
5. Measure the Wilson loop expectation ⟨W(R,T)⟩ ~ exp(-σRT)
6. Extract σ as a function of g²
7. Find g² where σ matches the physical value

NOTE: This is a MAJOR computational project. This script sets up
the framework and does a crude strong-coupling estimate. A proper
Monte Carlo simulation would require weeks of compute time.
"""

import numpy as np

def estimate_plaquettes_per_link(rho, dim=4, seed=42):
    """Estimate the number of plaquettes per link on a Poisson causal set.
    This determines the effective lattice structure."""
    from collections import defaultdict

    rng = np.random.RandomState(seed)
    N = rng.poisson(rho)
    points = rng.uniform(0, 1, size=(N, dim))

    order = np.argsort(points[:, 0])
    pts = points[order]

    # Find causal pairs and links
    causal = set()
    for i in range(N):
        for j in range(i+1, N):
            dt = pts[j, 0] - pts[i, 0]
            if dt <= 0: continue
            dx = np.abs(pts[j, 1:] - pts[i, 1:])
            dx = np.minimum(dx, 1.0 - dx)
            if np.sum(dx**2) <= dt**2:
                causal.add((i, j))

    links = set()
    for (i, j) in causal:
        is_link = True
        for k in range(N):
            if k == i or k == j: continue
            if (i, k) in causal and (k, j) in causal:
                is_link = False; break
        if is_link: links.add((i, j))

    # Count triangles (3-cliques in the link graph)
    adj = defaultdict(set)
    for (i, j) in links:
        adj[i].add(j); adj[j].add(i)

    triangles = 0
    for (i, j) in links:
        common = adj[i] & adj[j]
        triangles += len(common)
    triangles //= 3  # Each triangle counted 3 times

    n_links = len(links)
    plaq_per_link = 3 * triangles / n_links if n_links > 0 else 0

    return {
        'N': N, 'n_links': n_links, 'triangles': triangles,
        'plaq_per_link': plaq_per_link,
        'links_per_event': 2 * n_links / N if N > 0 else 0,
    }


def strong_coupling_string_tension(g2, plaq_per_link):
    """Strong coupling estimate of the string tension on the Poisson lattice.

    In strong coupling (large g²), the Wilson loop area law gives:
    σ·a² ≈ -ln(1/(N_c · g²)) for SU(N_c)

    On a lattice with p plaquettes per link, the minimum area
    enclosed by a Wilson loop of perimeter L scales as A ~ L²/p.
    So σ_eff ≈ σ_lattice · p / p_regular where p_regular ≈ 6 for
    a 4D regular lattice.
    """
    N_c = 3
    if g2 <= 0:
        return float('inf')
    beta = 2 * N_c / g2
    # Strong coupling: σa² ≈ -ln(β/(2N_c²))
    arg = beta / (2 * N_c**2)
    if arg <= 0 or arg >= 1:
        return float('inf')
    sigma_a2 = -np.log(arg)
    return sigma_a2


def main():
    print("=" * 60)
    print("SU(3) ON POISSON LATTICE: STRING TENSION ESTIMATE")
    print("=" * 60)

    # First: characterize the Poisson lattice structure
    print("\n--- Poisson lattice structure ---")
    for rho in [50, 100, 200]:
        for seed in [42, 123]:
            r = estimate_plaquettes_per_link(rho, seed=seed)
            print(f"  ρ={rho}: N={r['N']}, links={r['n_links']}, "
                  f"triangles={r['triangles']}, "
                  f"plaq/link={r['plaq_per_link']:.2f}, "
                  f"links/event={r['links_per_event']:.1f}")

    # Strong coupling estimate
    print("\n--- Strong coupling string tension ---")
    print("β = 6/g², σa² ≈ -ln(β/18)")
    print(f"{'g²':>6} {'β':>6} {'σa²':>8}")
    for g2 in [0.5, 1.0, 2.0, 3.0, 4.0, 5.0, 6.0, 8.0, 10.0]:
        beta = 6.0 / g2
        sigma = strong_coupling_string_tension(g2, 6.0)
        print(f"  {g2:>5.1f} {beta:>6.2f} {sigma:>8.4f}")

    # The physical string tension
    print("\n--- Physical matching ---")
    # σ_phys = (440 MeV)² = 0.194 GeV²
    # M_P = 1.22e19 GeV
    # σ in Planck units: σ/M_P² = 0.194/(1.22e19)² = 1.3e-38
    # This is TINY → β must be very close to the critical value
    sigma_phys_planck = 0.194 / (1.22e19)**2
    print(f"  σ_phys = (440 MeV)² = 0.194 GeV²")
    print(f"  σ_phys/M_P² = {sigma_phys_planck:.2e}")
    print(f"  This is incredibly small → the bare coupling must be")
    print(f"  tuned to the WEAK coupling regime (β → ∞, g² → 0)")
    print(f"  which is the continuum limit.")
    print()
    print(f"  The strong-coupling formula σa² = -ln(β/18) gives")
    print(f"  σa² = {sigma_phys_planck:.2e} when β/18 = exp(-{sigma_phys_planck:.2e})")
    print(f"  i.e., β ≈ 18 (to ~38 decimal places)")
    print(f"  This means g² = 6/β ≈ 6/18 = 1/3")
    print()
    print(f"  BUT this is the strong-coupling formula, which is")
    print(f"  NOT valid near the continuum limit (β ~ 6).")
    print()

    # The proper approach: asymptotic scaling
    # In the weak-coupling (continuum) regime:
    # a·Λ_QCD = exp(-1/(2b₀g²)) · (b₀g²)^{-b₁/(2b₀²)} · (1 + O(g²))
    # with b₀ = 11/(16π²), b₁ = 102/(16π²)² for SU(3)
    # σ = (σ/Λ²_QCD) · Λ²_QCD where σ/Λ²_QCD ≈ (2.5)² ≈ 6

    b0 = 11.0 / (16 * np.pi**2)
    b1 = 102.0 / (16 * np.pi**2)**2

    print("--- Asymptotic scaling (weak coupling) ---")
    print(f"  b₀ = 11/(16π²) = {b0:.6f}")
    print(f"  b₁ = 102/(16π²)² = {b1:.8f}")

    # a·Λ_QCD = exp(-1/(2b₀g²)) at leading order
    # σa² = (σ/Λ²) · (a·Λ)² = 6 · exp(-1/(b₀g²))
    # Setting σa² = σ_phys_planck:
    # exp(-1/(b₀g²)) = σ_phys_planck / 6
    # -1/(b₀g²) = ln(σ_phys_planck/6)
    # g² = -1/(b₀ · ln(σ_phys_planck/6))

    log_ratio = np.log(sigma_phys_planck / 6)
    g2_needed = -1 / (b0 * log_ratio)
    beta_needed = 6 / g2_needed

    print(f"  ln(σ_phys/(6·M_P²)) = {log_ratio:.2f}")
    print(f"  g²(M_P) needed = {g2_needed:.6f}")
    print(f"  β needed = {beta_needed:.2f}")
    print(f"  α_s(M_P) = g²/(4π) = {g2_needed/(4*np.pi):.6f}")
    print()

    # Run this g² down to M_Z
    b3 = 7.0  # one-loop beta coeff
    M_P = 1.22e19
    M_Z = 91.19
    t = np.log(M_P / M_Z)
    alpha_s_MP = g2_needed / (4 * np.pi)
    inv_alpha_s_MZ = 1/alpha_s_MP + b3 * t / (2 * np.pi)
    alpha_s_MZ = 1 / inv_alpha_s_MZ

    print(f"  Running to M_Z with b₃ = {b3}:")
    print(f"  α_s(M_P) = {alpha_s_MP:.6f}")
    print(f"  1/α_s(M_Z) = {inv_alpha_s_MZ:.2f}")
    print(f"  α_s(M_Z) = {alpha_s_MZ:.4f}")
    print(f"  MEASURED: α_s(M_Z) = 0.1179")
    print(f"  Ratio: {alpha_s_MZ/0.1179:.4f}")


if __name__ == "__main__":
    main()
