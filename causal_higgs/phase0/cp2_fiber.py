#!/usr/bin/env python3
"""
CP² fiber geometry for the causal Higgs computation.

CP² = {[z₀:z₁:z₂] : (z₀,z₁,z₂) ∈ ℂ³ \ {0}} / ℂ*

Key structures:
  - Fubini-Study metric: ds² = (|z|²|dz|² - |z̄·dz|²) / |z|⁴
  - O(1) sections: the coordinate functions z₀, z₁, z₂ (normalized)
  - Fiber Laplacian: Δ_FS (discrete approximation from random sprinkling)

The three independent holomorphic sections of O(1) on CP² are exactly
the three generation wavefunctions. Their overlap integrals with the
Higgs field determine the Yukawa matrix.
"""

import numpy as np
from scipy.spatial import KDTree


def random_cp2_point(rng=None):
    """Sample a uniformly random point on CP² using the Fubini-Study measure.

    Method: Sample z ∈ ℂ³ from the standard complex Gaussian,
    then project to CP² by normalizing. The Gaussian measure on ℂ³
    is U(3)-invariant, so the induced measure on CP² is the
    Fubini-Study volume form (up to normalization).

    Returns: z ∈ ℂ³ with |z| = 1 (a representative of [z] ∈ CP²)
    """
    if rng is None:
        rng = np.random.default_rng()
    z = rng.standard_normal(3) + 1j * rng.standard_normal(3)
    z /= np.linalg.norm(z)
    return z


def sprinkle_cp2(n_points, seed=42):
    """Generate a Poisson-like sprinkling of n_points on CP².

    Returns:
        points: (n_points, 3) complex array, each row a unit vector in ℂ³
    """
    rng = np.random.default_rng(seed)
    points = np.zeros((n_points, 3), dtype=complex)
    for i in range(n_points):
        points[i] = random_cp2_point(rng)
    return points


def fubini_study_distance(z1, z2):
    """Fubini-Study distance between two points on CP².

    d_FS([z₁], [z₂]) = arccos(|⟨z₁, z₂⟩|)

    where z₁, z₂ are unit vectors in ℂ³.
    Range: [0, π/2].
    """
    inner = np.abs(np.vdot(z1, z2))
    # Clamp for numerical stability
    inner = min(inner, 1.0)
    return np.arccos(inner)


def fubini_study_distance_matrix(points):
    """Compute the full pairwise FS distance matrix.

    Args:
        points: (N, 3) complex array of unit vectors

    Returns:
        D: (N, N) real array of FS distances
    """
    N = len(points)
    # Gram matrix of absolute inner products
    G = np.abs(points @ points.conj().T)
    np.clip(G, 0, 1, out=G)
    D = np.arccos(G)
    return D


def fiber_laplacian(points, n_neighbors=10):
    """Discrete Laplacian on CP² from a random sprinkling.

    Uses the graph Laplacian with Gaussian weights based on
    Fubini-Study distance. This approximates the Laplace-Beltrami
    operator on (CP², g_FS) as n_points → ∞.

    Method (finite-element / mesh-free):
      For each point p, find its k nearest neighbors {q_j}.
      Weight w_{pq} = exp(-d_FS(p,q)² / (2σ²)) where σ is a
      bandwidth adapted to the local density.
      L_p f = (1/σ²) Σ_j w_{pq_j} (f(q_j) - f(p))

    Args:
        points: (N, 3) complex array of unit vectors on CP²
        n_neighbors: number of nearest neighbors for the graph

    Returns:
        L: (N, N) sparse-like array, the discrete Laplacian matrix
        sigma: the bandwidth parameter used
    """
    N = len(points)
    D = fubini_study_distance_matrix(points)

    # Adaptive bandwidth: median of k-th nearest neighbor distance
    k = min(n_neighbors, N - 1)
    sorted_dists = np.sort(D, axis=1)
    sigma = np.median(sorted_dists[:, k])
    if sigma < 1e-10:
        sigma = 0.1  # fallback

    # Build graph Laplacian with Gaussian weights
    L = np.zeros((N, N))
    for i in range(N):
        # Find k nearest neighbors (excluding self)
        neighbors = np.argsort(D[i])[1:k + 1]
        weights = np.exp(-D[i, neighbors] ** 2 / (2 * sigma ** 2))
        total_weight = np.sum(weights)

        if total_weight > 1e-15:
            for j, w in zip(neighbors, weights):
                L[i, j] = w / total_weight
            L[i, i] = -1.0  # Row sums to zero

    # Scale by 1/σ² to get the correct continuum limit
    L /= sigma ** 2

    return L, sigma


def o1_sections(points):
    """Evaluate the three O(1) sections at each fiber point.

    The sections of O(1) on CP² are the coordinate functions:
      s_k([z]) = z_k / |z|  (k = 0, 1, 2)

    Since our points are already normalized (|z| = 1), the sections
    are simply the components z_0, z_1, z_2.

    These three sections form a basis for H⁰(CP², O(1)) ≅ ℂ³.
    Each section corresponds to one fermion generation.

    Args:
        points: (N, 3) complex array of unit vectors

    Returns:
        sections: (3, N) complex array — sections[k][i] = z_k at point i
    """
    return points.T.copy()  # (3, N)


def section_inner_product(points, s1, s2):
    """Inner product of two sections on CP² using the discrete measure.

    ⟨s₁, s₂⟩ = (1/N) Σᵢ s₁(pᵢ)* s₂(pᵢ)

    This approximates ∫_{CP²} s₁* s₂ dμ_FS as N → ∞.
    """
    return np.mean(np.conj(s1) * s2)


def verify_section_orthogonality(points):
    """Verify that the three O(1) sections are approximately orthogonal.

    By SU(3) invariance, ∫_{CP²} z_j* z_k dμ_FS = (1/3) δ_{jk}.

    Returns:
        G: (3, 3) Gram matrix of section inner products
    """
    sections = o1_sections(points)
    N_g = 3
    G = np.zeros((N_g, N_g), dtype=complex)
    for j in range(N_g):
        for k in range(N_g):
            G[j, k] = section_inner_product(points, sections[j], sections[k])
    return G


def fiber_laplacian_eigendecomposition(points, n_neighbors=10, n_modes=10):
    """Compute the lowest eigenmodes of the fiber Laplacian.

    The first nontrivial eigenmodes of Δ_FS on CP² are the O(1) sections
    themselves (eigenvalue = 6 for the standard normalization of CP²
    with Ricci curvature Ric = 6 g_FS).

    Returns:
        eigenvalues: first n_modes eigenvalues (ascending)
        eigenvectors: (N, n_modes) array of eigenvectors
    """
    L, sigma = fiber_laplacian(points, n_neighbors)
    # L is negative semi-definite; negate to get positive eigenvalues
    eigenvalues, eigenvectors = np.linalg.eigh(-L)

    # Sort ascending (smallest eigenvalue first — should be ~0 for constant mode)
    idx = np.argsort(eigenvalues)
    eigenvalues = eigenvalues[idx[:n_modes]]
    eigenvectors = eigenvectors[:, idx[:n_modes]]

    return eigenvalues, eigenvectors


# ============================================================
# Validation
# ============================================================

def validate_cp2_geometry(n_points=1000, seed=42):
    """Run validation checks on the CP² fiber implementation."""
    print("=" * 60)
    print(f"CP² FIBER VALIDATION (N = {n_points})")
    print("=" * 60)

    points = sprinkle_cp2(n_points, seed)

    # 1. Check normalization
    norms = np.linalg.norm(points, axis=1)
    print(f"\n1. Normalization: |z| = {norms.mean():.6f} ± {norms.std():.2e}")
    assert np.allclose(norms, 1.0), "Points not normalized!"

    # 2. Check section orthogonality
    G = verify_section_orthogonality(points)
    print(f"\n2. Section Gram matrix (expect (1/3)·I₃):")
    for i in range(3):
        row = "   "
        for j in range(3):
            row += f" {G[i, j].real:+.4f}"
            if abs(G[i, j].imag) > 0.001:
                row += f"{G[i, j].imag:+.4f}i"
        print(row)
    expected_diag = 1.0 / 3.0
    diag_error = max(abs(G[i, i].real - expected_diag) for i in range(3))
    offdiag_error = max(abs(G[i, j]) for i in range(3) for j in range(3) if i != j)
    print(f"   Diagonal error: {diag_error:.4f} (expect → 0)")
    print(f"   Off-diagonal max: {offdiag_error:.4f} (expect → 0)")

    # 3. Distance distribution
    D = fubini_study_distance_matrix(points[:200])  # subsample for speed
    d_vals = D[np.triu_indices(200, k=1)]
    print(f"\n3. FS distance distribution:")
    print(f"   Mean: {d_vals.mean():.4f} (CP² mean ≈ 0.785 = π/4)")
    print(f"   Max:  {d_vals.max():.4f} (max = π/2 ≈ 1.571)")

    # 4. Fiber Laplacian spectrum
    print(f"\n4. Fiber Laplacian eigenvalues (first 8):")
    evals, evecs = fiber_laplacian_eigendecomposition(points, n_neighbors=15, n_modes=8)
    for i, ev in enumerate(evals):
        label = "(constant mode)" if i == 0 else ""
        print(f"   λ_{i} = {ev:.4f} {label}")
    print(f"   Gap λ₁/λ₀ = {evals[1]/max(evals[0], 1e-10):.1f}")

    print("\n" + "=" * 60)
    return points


if __name__ == "__main__":
    validate_cp2_geometry(n_points=2000, seed=42)
