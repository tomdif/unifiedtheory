#!/usr/bin/env python3
"""
Coupled d'Alembertian on the product space M^d × CP².

The scalar Higgs field Φ lives on the product manifold. The kinetic
operator is the product Laplacian:

    □_{M×F} = □_M ⊗ 1_F + 1_M ⊗ Δ_F

where □_M is the Sorkin retarded d'Alembertian on the causal set M,
and Δ_F is the Laplace-Beltrami operator on the fiber F = CP².

On the discrete product space:
  - Each point is a pair (x_i, f_j) where x_i ∈ M and f_j ∈ CP²
  - The field Φ is a function on M × F, i.e., a matrix Φ[i, j]
  - □_{M×F} Φ[i, j] = (□_M Φ[·, j])[i] + (Δ_F Φ[i, ·])[j]

The coupling between base and fiber arises from:
  1. The product structure itself (each spacetime point carries a fiber)
  2. The Higgs potential V(Φ) = -a|Φ|² + b|Φ|⁴ which acts pointwise
  3. (Optional) A direct coupling term linking Φ at causally related
     points weighted by their fiber separation

This module implements both the "pure product" operator and the
"causally-weighted fiber coupling" variant.
"""

import numpy as np
from scipy.sparse.linalg import LinearOperator, cg
from scipy import sparse

from .cp2_fiber import sprinkle_cp2, fiber_laplacian, o1_sections
from .causal_base import (
    poisson_sprinkle_minkowski,
    build_causal_matrix,
    order_intervals,
    build_dalembertian_matrix,
)


class ProductSpace:
    """Discrete product space M^d × CP² with the coupled d'Alembertian.

    Attributes:
        base_points: (N_M, dim) array — causal set points
        fiber_points: (N_F, 3) complex array — CP² fiber points
        N_M, N_F: number of base/fiber points
        dim: spacetime dimension

        box_M: (N_M, N_M) base d'Alembertian matrix
        lap_F: (N_F, N_F) fiber Laplacian matrix
        sections: (3, N_F) the O(1) sections (generation wavefunctions)
    """

    def __init__(self, dim=2, rho_M=100, N_F=200, box_size=1.0, seed=42,
                 fiber_neighbors=10):
        """Initialize the product space.

        Args:
            dim: spacetime dimension (2 for 1+1D, 4 for 3+1D)
            rho_M: sprinkling density for the base causal set
            N_F: number of fiber points on CP²
            box_size: spacetime box size
            seed: random seed
            fiber_neighbors: k for fiber Laplacian construction
        """
        self.dim = dim
        self.box_size = box_size
        self.rho_M = rho_M

        # Generate base causal set
        self.base_points, self.N_M = poisson_sprinkle_minkowski(
            rho_M, dim, box_size, seed
        )

        # Generate fiber
        self.fiber_points = sprinkle_cp2(N_F, seed + 1000)
        self.N_F = N_F

        # Build base causal structure
        print(f"Building causal matrix ({self.N_M} points)...")
        self.C = build_causal_matrix(self.base_points,
                                      periodic_spatial=True,
                                      box_size=box_size)
        self.intervals = order_intervals(self.C)

        # Build base d'Alembertian
        print("Building base d'Alembertian...")
        self.box_M = build_dalembertian_matrix(
            self.C, self.intervals, dim, rho_M
        )

        # Build fiber Laplacian
        print(f"Building fiber Laplacian ({N_F} points)...")
        self.lap_F, self.sigma_F = fiber_laplacian(
            self.fiber_points, n_neighbors=fiber_neighbors
        )

        # Get O(1) sections
        self.sections = o1_sections(self.fiber_points)

        # Total number of degrees of freedom
        self.N_total = self.N_M * self.N_F

        print(f"Product space: {self.N_M} × {self.N_F} = {self.N_total} DOF")

    def apply_product_dalembertian(self, Phi):
        """Apply □_{M×F} = □_M ⊗ 1 + 1 ⊗ Δ_F to the field Φ.

        Args:
            Phi: (N_M, N_F) complex array — field on the product space

        Returns:
            result: (N_M, N_F) complex array — □_{M×F} Φ
        """
        # Base part: (□_M ⊗ 1) Φ = □_M applied to each fiber index
        # For each fiber point j: result[:, j] += box_M @ Phi[:, j]
        base_part = self.box_M @ Phi  # (N_M, N_F) — matrix mult broadcasts

        # Fiber part: (1 ⊗ Δ_F) Φ = Δ_F applied to each base point
        # For each base point i: result[i, :] += lap_F @ Phi[i, :]
        fiber_part = (self.lap_F @ Phi.T).T  # (N_M, N_F)

        return base_part + fiber_part

    def apply_product_dalembertian_flat(self, phi_flat):
        """Same as apply_product_dalembertian but with flattened I/O.

        Args:
            phi_flat: (N_M * N_F,) array

        Returns:
            result: (N_M * N_F,) array
        """
        Phi = phi_flat.reshape(self.N_M, self.N_F)
        result = self.apply_product_dalembertian(Phi)
        return result.ravel()

    def product_operator_as_linear_op(self):
        """Return the product d'Alembertian as a scipy LinearOperator.

        Useful for iterative solvers (CG, GMRES).
        """
        N = self.N_total
        return LinearOperator(
            shape=(N, N),
            matvec=self.apply_product_dalembertian_flat,
            dtype=complex,
        )

    def apply_coupled_dalembertian(self, Phi, coupling_strength=0.1):
        """Apply the d'Alembertian with causal-fiber coupling.

        In addition to the pure product operator □_M ⊗ 1 + 1 ⊗ Δ_F,
        add a coupling term that links the Higgs values at causally
        related base points, weighted by the fiber separation:

          C_coupling[i,j,a,b] = g · δ(i ≺ j) · K(d_FS(f_a, f_b))

        where K is a kernel (e.g., Gaussian) on the fiber and g is the
        coupling strength. This term couples the base causal structure
        to the fiber geometry.

        Args:
            Phi: (N_M, N_F) complex array
            coupling_strength: g in the coupling term

        Returns:
            result: (N_M, N_F) complex array
        """
        # Pure product part
        result = self.apply_product_dalembertian(Phi)

        if abs(coupling_strength) < 1e-15:
            return result

        # Coupling: for each causal pair (i ≺ j), propagate fiber info
        # This is the key term that breaks the fiber symmetry via causality
        from .cp2_fiber import fubini_study_distance_matrix
        D_F = fubini_study_distance_matrix(self.fiber_points)
        K_F = np.exp(-D_F ** 2 / (2 * self.sigma_F ** 2))

        for i in range(self.N_M):
            for j in range(i + 1, self.N_M):
                if self.C[i, j]:
                    # Coupling: Φ at point j gets contribution from Φ at point i
                    # through the fiber kernel
                    coupling = coupling_strength * (K_F @ Phi[i, :] - Phi[j, :])
                    result[j, :] += coupling

        return result


def compute_overlap_matrix(Phi, sections, N_F):
    """Compute the overlap (Yukawa) matrix from the Higgs field and sections.

    Y_{ab} = (1/N_F) Σ_j Φ(x_0, f_j) · s_a(f_j)* · s_b(f_j)

    where x_0 is a fixed "observation" point (e.g., the midpoint of the
    causal set) and s_a are the O(1) sections.

    For the full Yukawa matrix, we average over base points in a
    "late time" region to get the vacuum expectation.

    Args:
        Phi: (N_M, N_F) complex array — Higgs field solution
        sections: (3, N_F) complex array — O(1) sections
        N_F: number of fiber points

    Returns:
        Y: (3, 3) complex Yukawa matrix
    """
    N_g = 3
    Y = np.zeros((N_g, N_g), dtype=complex)

    # Average Phi over late-time base points
    N_M = Phi.shape[0]
    late_start = int(0.6 * N_M)  # last 40% of time range
    Phi_avg = np.mean(Phi[late_start:, :], axis=0)  # (N_F,)

    for a in range(N_g):
        for b in range(N_g):
            # Y_{ab} = ⟨Φ · s_a* · s_b⟩_fiber
            integrand = Phi_avg * np.conj(sections[a]) * sections[b]
            Y[a, b] = np.mean(integrand)

    return Y


def yukawa_to_masses_and_ckm(Y_up, Y_down, v=246.0):
    """Extract masses and CKM matrix from Yukawa matrices.

    Mass matrix: M = v · Y
    Diagonalize: M = V_L · diag(m) · V_R†
    CKM: V_CKM = V_u_L† · V_d_L

    Args:
        Y_up: (3, 3) complex Yukawa for up-type quarks
        Y_down: (3, 3) complex Yukawa for down-type quarks
        v: Higgs vev in GeV (default 246 GeV)

    Returns:
        masses_up, masses_down: (3,) arrays of masses (GeV)
        V_ckm: (3, 3) CKM matrix
    """
    M_up = v * Y_up
    M_down = v * Y_down

    # SVD: M = U · diag(σ) · V†
    U_u, s_u, Vh_u = np.linalg.svd(M_up)
    U_d, s_d, Vh_d = np.linalg.svd(M_down)

    # Masses are the singular values (ascending order)
    masses_up = np.sort(s_u)
    masses_down = np.sort(s_d)

    # CKM matrix
    V_ckm = U_u.conj().T @ U_d

    return masses_up, masses_down, V_ckm


# ============================================================
# Validation
# ============================================================

def validate_product_operator(dim=2, rho_M=50, N_F=100, seed=42):
    """Validate the product d'Alembertian.

    Test: constant field Φ = 1 should give □Φ ≈ 0.
    Test: fiber-only mode Φ(x,f) = s_0(f) should give □Φ = λ_0 · s_0.
    """
    print("=" * 60)
    print(f"PRODUCT OPERATOR VALIDATION ({dim}D × CP²)")
    print(f"ρ_M = {rho_M}, N_F = {N_F}")
    print("=" * 60)

    ps = ProductSpace(dim=dim, rho_M=rho_M, N_F=N_F, seed=seed)

    # Test 1: constant field
    Phi_const = np.ones((ps.N_M, ps.N_F), dtype=complex)
    box_const = ps.apply_product_dalembertian(Phi_const)
    print(f"\n  Test 1: Φ = 1 (constant)")
    print(f"  Mean |□Φ|: {np.mean(np.abs(box_const)):.4e} (expect → 0)")

    # Test 2: pure fiber mode
    s0 = ps.sections[0]  # first O(1) section
    Phi_fiber = np.outer(np.ones(ps.N_M), s0)
    box_fiber = ps.apply_product_dalembertian(Phi_fiber)
    # Should be dominated by the fiber Laplacian eigenvalue
    ratio = box_fiber / (Phi_fiber + 1e-30)
    interior = (ps.base_points[:, 0] > 0.2) & (ps.base_points[:, 0] < 0.8)
    if np.any(interior):
        mean_ratio = np.mean(ratio[interior, :].real)
        print(f"\n  Test 2: Φ = s₀(f) (pure fiber mode)")
        print(f"  Mean □Φ/Φ: {mean_ratio:.4f} (expect ≈ fiber eigenvalue)")

    # Overlap matrix for constant Higgs
    Y = compute_overlap_matrix(Phi_const, ps.sections, ps.N_F)
    print(f"\n  Overlap matrix for Φ=1:")
    for i in range(3):
        row = "   "
        for j in range(3):
            row += f" {Y[i, j].real:+.4f}"
        print(row)
    print(f"  (Expect ≈ (1/3)·I₃ by section orthogonality)")

    print("\n" + "=" * 60)
    return ps


if __name__ == "__main__":
    validate_product_operator(dim=2, rho_M=50, N_F=100)
