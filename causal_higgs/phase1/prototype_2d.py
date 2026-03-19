#!/usr/bin/env python3
"""
Phase 1 prototype: 2D causal set × S¹ fiber.

This is the simplest version of the full computation:
  - 1+1D Minkowski spacetime (Poisson causal set)
  - S¹ fiber (circle, Fourier modes)
  - Mexican-hat Higgs potential
  - Overlap integrals → Yukawa analog

Uses the IMEX Crank-Nicolson solver for stability (the d'Alembertian
has eigenvalues ~ ρ, making explicit schemes CFL-limited).

The key question Phase 1 answers:
  Does the causal structure break the fiber symmetry and produce
  a mass hierarchy, even in 2D?

If yes: the mechanism works. Scale to 4D × CP² (Phase 2).
If no: need to understand what additional ingredient is needed.
"""

import sys
import os
import numpy as np
import time

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

from phase0.causal_base import (
    poisson_sprinkle_minkowski,
    build_causal_matrix,
    order_intervals,
    build_dalembertian_matrix,
)
from phase0.solvers import IMEXCrankNicolson, AdaptiveExplicit
from phase1.s1_fiber import sprinkle_s1, s1_laplacian, fourier_sections


class ProductSpace2DS1:
    """2D causal set × S¹ product space."""

    def __init__(self, rho_M=100, N_F=100, seed=42):
        self.rho_M = rho_M

        # Base: 1+1D causal set
        self.base_points, self.N_M = poisson_sprinkle_minkowski(
            rho_M, dim=2, seed=seed)
        self.C = build_causal_matrix(self.base_points)
        self.intervals = order_intervals(self.C)
        self.box_M = build_dalembertian_matrix(self.C, self.intervals, 2, rho_M)

        # Fiber: S¹
        self.thetas = sprinkle_s1(N_F, seed + 1000)
        self.N_F = N_F
        self.lap_F, self.sigma_F = s1_laplacian(self.thetas)
        self.sections = fourier_sections(self.thetas, n_modes=3)

        self.N_total = self.N_M * self.N_F
        print(f"2D × S¹ product: {self.N_M} × {self.N_F} = {self.N_total} DOF")

    def apply_product_dalembertian(self, Phi):
        base_part = self.box_M @ Phi
        fiber_part = (self.lap_F @ Phi.T).T
        return base_part + fiber_part


def run_phase1_prototype(rho_M=100, N_F=100, seed=42, solver='cn'):
    """Run the Phase 1 prototype with stable solvers."""
    print("=" * 70)
    print("  PHASE 1 PROTOTYPE: 2D CAUSAL SET × S¹")
    print(f"  Solver: {'Crank-Nicolson' if solver == 'cn' else 'Adaptive explicit'}")
    print("=" * 70)
    t0 = time.time()

    ps = ProductSpace2DS1(rho_M=rho_M, N_F=N_F, seed=seed)

    a, b = 1.0, 1.0
    v = np.sqrt(a / (2 * b))

    if solver == 'cn':
        s = IMEXCrankNicolson(
            ps.apply_product_dalembertian, ps.N_M, ps.N_F, a=a, b=b)
        Phi, history = s.solve(
            dt=0.005, n_steps=500, tol=1e-6,
            gmres_tol=1e-3, verbose=True, log_interval=50)
    else:
        s = AdaptiveExplicit(
            ps.apply_product_dalembertian, ps.N_M, ps.N_F, a=a, b=b)
        Phi, history = s.solve(
            dt_init=1e-5, n_steps=2000, tol=1e-6,
            verbose=True, log_interval=200)

    # Extract Yukawa analog
    late = int(0.6 * ps.N_M)
    Phi_avg = np.mean(Phi[late:, :], axis=0)

    Y = np.zeros((3, 3), dtype=complex)
    for a_idx in range(3):
        for b_idx in range(3):
            Y[a_idx, b_idx] = np.mean(
                Phi_avg * np.conj(ps.sections[a_idx]) * ps.sections[b_idx]
            )

    _, masses, _ = np.linalg.svd(Y)
    masses = np.sort(np.abs(masses))[::-1]

    print(f"\n  Yukawa analog matrix (real part):")
    for i in range(3):
        row = "   "
        for j in range(3):
            row += f" {Y[i, j].real:+.6f}"
        print(row)

    print(f"\n  Mass eigenvalues: {masses}")
    if masses[0] > 0:
        print(f"  Ratios: m₂/m₁ = {masses[1] / masses[0]:.4f}, "
              f"m₃/m₁ = {masses[2] / masses[0]:.4f}")

    # Check for geometric hierarchy
    r21 = masses[1] / masses[0] if masses[0] > 0 else 0
    r31 = masses[2] / masses[0] if masses[0] > 0 else 0
    if r31 > 0:
        geometric_test = r21 ** 2 / r31
        print(f"  Geometric test (m₂/m₁)²/(m₃/m₁) = {geometric_test:.4f} "
              f"(expect ≈ 1 for m ~ ε^n)")

    elapsed = time.time() - t0
    print(f"\n  Runtime: {elapsed:.1f}s")
    print("=" * 70)

    return Y, masses


if __name__ == "__main__":
    solver = sys.argv[1] if len(sys.argv) > 1 else 'cn'

    for rho in [50, 100, 200]:
        print(f"\n{'#' * 70}")
        print(f"# ρ = {rho}")
        print(f"{'#' * 70}")
        run_phase1_prototype(rho_M=rho, N_F=80, seed=42, solver=solver)
