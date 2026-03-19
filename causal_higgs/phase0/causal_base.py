#!/usr/bin/env python3
"""
Causal set d'Alembertian for the spacetime base manifold.

Implements the Sorkin retarded d'Alembertian for a scalar field
on a Poisson-sprinkled causal set in d-dimensional Minkowski spacetime.

The key operator is the Benincasa-Dowker (BD) d'Alembertian:
  (□φ)(x) = (2/ℓ²) Σ_{y ≺ x} C_n(x,y) φ(y)

where the sum is over all points y in the causal past of x,
the coefficients C_n depend on the number of points between x and y
("order interval" |I(y,x)|), and ℓ is the discreteness scale
(related to sprinkling density ρ by ℓ ~ ρ^{-1/d}).

References:
  - Sorkin (2003): "Does locality fail at intermediate length-scales?"
  - Benincasa-Dowker (2010): "The scalar curvature of a causal set"
  - Dowker-Glaser (2013): coefficients for general dimension
"""

import numpy as np
from collections import defaultdict


def poisson_sprinkle_minkowski(rho, dim, box_size=1.0, seed=42):
    """Generate a Poisson sprinkling in d-dimensional Minkowski spacetime.

    The 0-th coordinate is time, coordinates 1..d-1 are spatial.
    Spatial coordinates have periodic boundary conditions.
    Time runs from 0 to box_size.

    Args:
        rho: sprinkling density (expected points per unit volume)
        dim: total spacetime dimension (e.g., 2 for 1+1D, 4 for 3+1D)
        box_size: size of the spacetime region
        seed: random seed

    Returns:
        points: (N, dim) array, sorted by time coordinate
        N: number of points
    """
    rng = np.random.default_rng(seed)
    volume = box_size ** dim
    N = rng.poisson(rho * volume)
    points = rng.uniform(0, box_size, size=(N, dim))

    # Sort by time
    order = np.argsort(points[:, 0])
    points = points[order]
    return points, N


def causal_relation(p, q, periodic_spatial=True, box_size=1.0):
    """Check if p ≺ q (p is in the causal past of q) in Minkowski spacetime.

    p ≺ q iff t_q - t_p > 0 and |x_q - x_p|² ≤ (t_q - t_p)²

    With periodic spatial BCs, spatial distance uses the minimum image.

    Returns: True if p ≺ q
    """
    dt = q[0] - p[0]
    if dt <= 0:
        return False

    dx = q[1:] - p[1:]
    if periodic_spatial:
        dx = np.abs(dx)
        dx = np.minimum(dx, box_size - dx)

    return np.sum(dx ** 2) <= dt ** 2


def build_causal_matrix(points, periodic_spatial=True, box_size=1.0):
    """Build the causal relation matrix C where C[i,j] = 1 iff i ≺ j.

    Points must be sorted by time.

    Returns:
        C: (N, N) boolean array
    """
    N = len(points)
    C = np.zeros((N, N), dtype=bool)

    for i in range(N):
        for j in range(i + 1, N):
            if causal_relation(points[i], points[j], periodic_spatial, box_size):
                C[i, j] = True

    return C


def order_intervals(C):
    """Compute the order interval sizes |I(i,j)| for all causal pairs.

    I(i,j) = {k : i ≺ k ≺ j} (the "Alexandrov set" between i and j).
    |I(i,j)| = number of elements strictly between i and j.

    Returns:
        intervals: (N, N) integer array where intervals[i,j] = |I(i,j)|
    """
    N = C.shape[0]
    intervals = np.zeros((N, N), dtype=int)

    for i in range(N):
        for j in range(i + 1, N):
            if C[i, j]:
                # Count k with i ≺ k ≺ j
                count = 0
                for k in range(i + 1, j):
                    if C[i, k] and C[k, j]:
                        count += 1
                intervals[i, j] = count

    return intervals


def bd_coefficients_2d():
    """Benincasa-Dowker coefficients for d=2 (1+1D).

    (□φ)(x) = (2/ℓ²) [ -2φ(x) + 4 Σ_{n=0}^{∞} (-1)^n C_n Σ_{|I|=n, y≺x} φ(y) ]

    In 2D, the nonlocal coefficients are:
      C(n) = (-1)^n  (i.e., alternating sign, no combinatorial factor needed
             beyond the binomial structure of the retarded sum)

    More precisely, the BD action in 2D uses:
      a_n = (4/√6) · (-1)^n · (n+1)  for the first few terms
    but the standard simplified form sums over layers:
      layer n = {y ≺ x : |I(y,x)| = n}

    We use the Sorkin (2003) form with a finite cutoff:
      (□φ)(x) = (2ρ/d!) [ -2φ(x) + 4 Σ_{y≺x} (-1)^{|I(y,x)|} φ(y) · ε(|I|) ]

    where ε(n) is a cutoff that makes the sum convergent.
    For our purposes we use the "minimal" BD operator with
    cutoff at order N_cut (typically 3-4 layers suffice).
    """
    # Coefficients for the first few order intervals
    # These come from the causal set discretization of □ in 2D
    # From Benincasa-Dowker (2010), Eq. (12):
    #   B_n = (-1)^n for 2D (flat spacetime)
    # The retarded operator is:
    #   (□_R φ)(x) = (4/ℓ²) [ φ(x) + Σ_n a_n Σ_{|I|=n} φ(y) ]
    # where a_n encode the dimension-dependent smearing.
    #
    # For 2D Minkowski: a_0 = -2, a_1 = 1 (and higher terms are zero
    # for the minimal operator).
    return {0: -2, 1: 1}


def bd_coefficients_4d():
    """Benincasa-Dowker coefficients for d=4 (3+1D).

    From Benincasa-Dowker (2010), the 4D scalar d'Alembertian on a
    causal set is:

      (□φ)(x) = (4!·ρ^{2/4}/l_p²) Σ_{y ≺ x} C(n) φ(y)

    where n = |I(y,x)| and:
      C(0) = -2/√6
      C(1) = 8/√6
      C(2) = -8/√6
      C(3) = 16/(3√6)

    and C(n) = 0 for n ≥ 4 in the minimal truncation.

    The overall normalization is (4/√6) ρ^{1/2}.
    """
    s6 = np.sqrt(6)
    return {
        0: -2 / s6,
        1: 8 / s6,
        2: -8 / s6,
        3: 16 / (3 * s6),
    }


def apply_dalembertian(phi, C, intervals, dim, rho, n_cut=4):
    """Apply the discrete d'Alembertian to a scalar field.

    The Benincasa-Dowker retarded d'Alembertian:

      (□φ)(x) = (2ρ/l_d) [ -a_self · φ(x) + Σ_{y≺x} c(|I(y,x)|) · φ(y) ]

    In 2D (Sorkin 2003): (□φ)(x) = 2ρ[-φ(x) + Σ_layers]
    where layers are weighted by order interval size.

    The self-term ensures □(constant) ≈ 0: the sum over past of a
    constant field cancels the self-term in expectation.

    Args:
        phi: (N,) array — field values at each causal set point
        C: (N, N) boolean causal matrix
        intervals: (N, N) integer order interval sizes
        dim: spacetime dimension
        rho: sprinkling density
        n_cut: maximum order interval size to include

    Returns:
        box_phi: (N,) array — (□φ) at each point
    """
    N = len(phi)

    # The BD operator uses alternating signs on layers:
    #   (□φ)(x) = scale · [-φ(x) + Σ_n (-1)^n · L_n(x, φ)]
    # where L_n(x,φ) = Σ_{y: |I(y,x)|=n} φ(y).
    #
    # In 2D: scale = 2/ℓ² with ℓ² ~ 1/ρ → scale = 2ρ
    # In 4D: scale = (4!/Γ(3)) · ρ^{1/2} = 4√6 · ρ^{1/2}
    #
    # IMPORTANT: On a SINGLE Poisson realization, □(const) has
    # O(√ρ) fluctuations. Convergence is in the ensemble mean.

    if dim == 2:
        scale = 2.0 * rho
    elif dim == 4:
        scale = 4.0 * np.sqrt(6.0) * np.sqrt(rho)
    else:
        raise ValueError(f"BD coefficients not implemented for dim={dim}")

    box_phi = np.zeros(N)

    for x in range(N):
        # Self-term
        val = -phi[x]

        # Sum over causal past with alternating signs by layer
        for y in range(x):
            if not C[y, x]:
                continue
            n = intervals[y, x]
            if n < n_cut:
                val += ((-1.0) ** n) * phi[y]

        box_phi[x] = scale * val

    return box_phi


def build_dalembertian_matrix(C, intervals, dim, rho, n_cut=4):
    """Build the full d'Alembertian as an explicit matrix.

    This is the retarded (lower-triangular) operator plus diagonal self-term.

    Returns:
        box_mat: (N, N) array where box_phi = box_mat @ phi
    """
    N = C.shape[0]

    if dim == 2:
        scale = 2.0 * rho
    elif dim == 4:
        scale = 4.0 * np.sqrt(6.0) * np.sqrt(rho)
    else:
        raise ValueError(f"BD coefficients not implemented for dim={dim}")

    box_mat = np.zeros((N, N))

    for x in range(N):
        # Self-term
        box_mat[x, x] = -scale

        # Past contributions with alternating signs by layer
        for y in range(x):
            if not C[y, x]:
                continue
            n = intervals[y, x]
            if n < n_cut:
                box_mat[x, y] = scale * ((-1.0) ** n)

    return box_mat


# ============================================================
# Links (for visualization and graph structure)
# ============================================================

def extract_links(C):
    """Extract links (irreducible causal relations) from the causal matrix.

    (i,j) is a link iff C[i,j]=True and there is no k with C[i,k] and C[k,j].
    Equivalently, |I(i,j)| = 0.
    """
    N = C.shape[0]
    links = []
    for i in range(N):
        for j in range(i + 1, N):
            if C[i, j]:
                # Check if it's a link
                is_link = True
                for k in range(i + 1, j):
                    if C[i, k] and C[k, j]:
                        is_link = False
                        break
                if is_link:
                    links.append((i, j))
    return links


# ============================================================
# Validation
# ============================================================

def validate_dalembertian(dim=2, rho=200, seed=42):
    """Validate the d'Alembertian on a known solution.

    For a plane wave φ(x) = exp(ik·x) in Minkowski space,
    □φ = -k² φ (with signature -+++).

    We check that the discrete □ converges to this.
    """
    print("=" * 60)
    print(f"d'ALEMBERTIAN VALIDATION ({dim}D, ρ={rho})")
    print("=" * 60)

    points, N = poisson_sprinkle_minkowski(rho, dim, seed=seed)
    print(f"  N = {N} points")

    # Build causal structure
    C = build_causal_matrix(points)
    n_causal = np.sum(C)
    print(f"  Causal pairs: {n_causal}")

    intervals = order_intervals(C)

    # Test field: φ = t (linear in time)
    # □(t) = 0 in flat space
    phi_linear = points[:, 0].copy()
    box_linear = apply_dalembertian(phi_linear, C, intervals, dim, rho)

    # Only check interior points (not too close to boundaries)
    interior = (points[:, 0] > 0.2) & (points[:, 0] < 0.8)
    if np.any(interior):
        mean_box = np.mean(np.abs(box_linear[interior]))
        print(f"\n  Test: φ = t")
        print(f"  Mean |□φ| (interior): {mean_box:.4e} (expect → 0)")

    # Test field: φ = t² / 2
    # □(t²/2) = -1 in 1+1D (signature -+)
    # □(t²/2) = -1 in d+1D
    phi_quad = points[:, 0] ** 2 / 2
    box_quad = apply_dalembertian(phi_quad, C, intervals, dim, rho)

    if np.any(interior):
        mean_box_quad = np.mean(box_quad[interior])
        print(f"\n  Test: φ = t²/2")
        print(f"  Mean □φ (interior): {mean_box_quad:.4f} (expect ≈ -1)")

    print("\n" + "=" * 60)
    return points, C, intervals


if __name__ == "__main__":
    validate_dalembertian(dim=2, rho=200)
