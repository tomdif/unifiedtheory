#!/usr/bin/env python3
"""
S¹ fiber for the 2D prototype (Phase 1).

In the lower-dimensional analog:
  - Base: 2D causal set (1+1 Minkowski)
  - Fiber: S¹ (circle) instead of CP²
  - Sections: Fourier modes e^{inθ} (n = -1, 0, 1) instead of O(1) sections
  - Yukawa: overlap of Higgs with Fourier modes

This tests the mechanism in a simpler setting where:
  - The fiber has only 1 real dimension (vs 4 for CP²)
  - The "sections" are the first 3 Fourier modes
  - The fiber Laplacian is d²/dθ² with eigenvalues n²
"""

import numpy as np


def sprinkle_s1(n_points, seed=42):
    """Random sprinkling on S¹ = [0, 2π) with uniform measure.

    Returns: (n_points,) array of angles θ ∈ [0, 2π)
    """
    rng = np.random.default_rng(seed)
    return rng.uniform(0, 2 * np.pi, size=n_points)


def s1_distance(theta1, theta2):
    """Geodesic distance on S¹."""
    d = np.abs(theta1 - theta2)
    return np.minimum(d, 2 * np.pi - d)


def s1_distance_matrix(thetas):
    """Pairwise distance matrix on S¹."""
    N = len(thetas)
    D = np.zeros((N, N))
    for i in range(N):
        for j in range(i + 1, N):
            d = s1_distance(thetas[i], thetas[j])
            D[i, j] = d
            D[j, i] = d
    return D


def s1_laplacian(thetas, n_neighbors=8):
    """Discrete Laplacian on S¹ from random sprinkling.

    Uses Gaussian-weighted graph Laplacian.
    """
    N = len(thetas)
    D = s1_distance_matrix(thetas)

    k = min(n_neighbors, N - 1)
    sorted_dists = np.sort(D, axis=1)
    sigma = np.median(sorted_dists[:, k])
    if sigma < 1e-10:
        sigma = 0.1

    L = np.zeros((N, N))
    for i in range(N):
        neighbors = np.argsort(D[i])[1:k + 1]
        weights = np.exp(-D[i, neighbors] ** 2 / (2 * sigma ** 2))
        total = np.sum(weights)
        if total > 1e-15:
            for j, w in zip(neighbors, weights):
                L[i, j] = w / total
            L[i, i] = -1.0

    L /= sigma ** 2
    return L, sigma


def fourier_sections(thetas, n_modes=3):
    """Fourier modes on S¹ as the analog of O(1) sections.

    Returns the first n_modes complex exponentials:
      s_k(θ) = e^{ikθ} / √(2π)  for k = 0, 1, ..., n_modes-1

    These are the analogs of the three O(1) sections on CP².
    """
    N = len(thetas)
    sections = np.zeros((n_modes, N), dtype=complex)
    for k in range(n_modes):
        sections[k] = np.exp(1j * k * thetas) / np.sqrt(2 * np.pi)
    return sections


def validate_s1():
    """Validate S¹ fiber implementation."""
    print("=" * 60)
    print("S¹ FIBER VALIDATION")
    print("=" * 60)

    N = 500
    thetas = sprinkle_s1(N, seed=42)
    sections = fourier_sections(thetas, n_modes=3)

    # Check orthogonality: ⟨e^{imθ}, e^{inθ}⟩ = δ_{mn}
    print("\n  Section Gram matrix (expect I₃):")
    G = np.zeros((3, 3), dtype=complex)
    for i in range(3):
        for j in range(3):
            G[i, j] = np.mean(np.conj(sections[i]) * sections[j]) * 2 * np.pi
    for i in range(3):
        row = "   "
        for j in range(3):
            row += f" {G[i, j].real:+.4f}"
        print(row)

    # Laplacian eigenvalues
    L, sigma = s1_laplacian(thetas)
    evals = np.sort(np.linalg.eigvalsh(-L))[:6]
    print(f"\n  Laplacian eigenvalues (first 6):")
    for i, ev in enumerate(evals):
        expected = i ** 2 if i < 4 else "?"
        print(f"    λ_{i} = {ev:.4f} (expect ∝ {expected})")

    print("\n" + "=" * 60)


if __name__ == "__main__":
    validate_s1()
