#!/usr/bin/env python3
"""
Discrete Higgs action and field equation on the product space M^d × CP².

The Higgs action on the product manifold is:

    S[Φ] = Σ_{(x,f)} [ ½ Φ* □_{M×F} Φ + V(Φ) ]

where V(Φ) = -a|Φ|² + b|Φ|⁴ is the Mexican-hat potential.

The Euler-Lagrange equation is:

    □_{M×F} Φ + V'(Φ) = 0
    □_{M×F} Φ - a Φ + 2b |Φ|² Φ = 0

This is a nonlinear equation. We solve it using:
  1. Newton-Krylov method (scipy)
  2. Relaxation (gradient descent on the action)
  3. Imaginary-time evolution (diffusion to the ground state)

The solution Φ(x, f) determines the Higgs vacuum profile.
The overlap integrals of Φ with the O(1) sections yield the Yukawa matrix.
"""

import numpy as np
from scipy.optimize import root
from scipy.sparse.linalg import LinearOperator, gmres

from .product_operator import ProductSpace, compute_overlap_matrix


class HiggsFieldEquation:
    """Solver for the Higgs field equation on M^d × CP².

    □Φ - aΦ + 2b|Φ|²Φ = 0

    with boundary condition Φ → v = √(a/2b) at late times.
    """

    def __init__(self, product_space, a=1.0, b=1.0, coupling=0.0):
        """
        Args:
            product_space: ProductSpace instance
            a: mass² parameter (a > 0 for symmetry breaking)
            b: quartic coupling (b > 0)
            coupling: strength of causal-fiber coupling (0 = pure product)
        """
        self.ps = product_space
        self.a = a
        self.b = b
        self.coupling = coupling
        self.v = np.sqrt(a / (2 * b))  # vacuum expectation value
        self.N_M = product_space.N_M
        self.N_F = product_space.N_F

    def higgs_potential(self, Phi):
        """V(Φ) = -a|Φ|² + b|Φ|⁴"""
        abs2 = np.abs(Phi) ** 2
        return -self.a * abs2 + self.b * abs2 ** 2

    def higgs_potential_derivative(self, Phi):
        """V'(Φ) = dV/dΦ* = -aΦ + 2b|Φ|²Φ"""
        abs2 = np.abs(Phi) ** 2
        return -self.a * Phi + 2 * self.b * abs2 * Phi

    def field_equation_residual(self, Phi):
        """Compute the residual F(Φ) = □Φ + V'(Φ).

        F = 0 is the field equation.

        Args:
            Phi: (N_M, N_F) complex array

        Returns:
            residual: (N_M, N_F) complex array
        """
        if self.coupling > 0:
            box_phi = self.ps.apply_coupled_dalembertian(Phi, self.coupling)
        else:
            box_phi = self.ps.apply_product_dalembertian(Phi)

        return box_phi + self.higgs_potential_derivative(Phi)

    def action(self, Phi):
        """Compute the total action S[Φ].

        S = Σ [ ½ Φ* □Φ + V(Φ) ]
        """
        box_phi = self.ps.apply_product_dalembertian(Phi)
        kinetic = 0.5 * np.sum(np.conj(Phi) * box_phi).real
        potential = np.sum(self.higgs_potential(Phi)).real
        return kinetic + potential

    def solve_relaxation(self, Phi_init=None, n_steps=1000, dt=0.01,
                          verbose=True):
        """Solve by gradient descent (imaginary-time evolution).

        ∂Φ/∂τ = -δS/δΦ* = -(□Φ + V'(Φ))

        This drives Φ toward a local minimum of S.

        Args:
            Phi_init: initial field configuration (default: v + noise)
            n_steps: number of relaxation steps
            dt: step size
            verbose: print progress

        Returns:
            Phi: (N_M, N_F) converged field
            history: list of (step, action, residual_norm) tuples
        """
        if Phi_init is None:
            # Start near the vacuum with small perturbations
            rng = np.random.default_rng(999)
            Phi = self.v * np.ones((self.N_M, self.N_F), dtype=complex)
            Phi += 0.1 * self.v * (rng.standard_normal(Phi.shape)
                                    + 1j * rng.standard_normal(Phi.shape))
        else:
            Phi = Phi_init.copy()

        history = []

        for step in range(n_steps):
            residual = self.field_equation_residual(Phi)
            res_norm = np.sqrt(np.mean(np.abs(residual) ** 2))

            if step % max(1, n_steps // 20) == 0:
                S = self.action(Phi)
                history.append((step, S, res_norm))
                if verbose:
                    mean_phi = np.mean(np.abs(Phi))
                    print(f"  step {step:5d}: S = {S:+.4e}, "
                          f"|res| = {res_norm:.4e}, ⟨|Φ|⟩ = {mean_phi:.4f}")

            # Gradient descent step
            Phi -= dt * residual

            # Check convergence
            if res_norm < 1e-8:
                if verbose:
                    print(f"  Converged at step {step}")
                break

        return Phi, history

    def solve_newton_krylov(self, Phi_init=None, verbose=True):
        """Solve using scipy's Newton-Krylov method.

        This is more sophisticated: it uses GMRES to solve the
        linearized equation at each Newton step.

        Args:
            Phi_init: initial field (default: v + noise)
            verbose: print progress

        Returns:
            Phi: (N_M, N_F) converged field
            info: solver info dict
        """
        if Phi_init is None:
            rng = np.random.default_rng(999)
            Phi_init = self.v * np.ones((self.N_M, self.N_F), dtype=complex)
            Phi_init += 0.05 * self.v * (rng.standard_normal(Phi_init.shape)
                                          + 1j * rng.standard_normal(Phi_init.shape))

        def F_real(phi_real_flat):
            """Wrapper: maps real vector to real residual."""
            n = len(phi_real_flat) // 2
            phi_c = phi_real_flat[:n] + 1j * phi_real_flat[n:]
            Phi = phi_c.reshape(self.N_M, self.N_F)
            res = self.field_equation_residual(Phi)
            res_flat = res.ravel()
            return np.concatenate([res_flat.real, res_flat.imag])

        x0 = np.concatenate([Phi_init.ravel().real, Phi_init.ravel().imag])

        if verbose:
            print("  Running Newton-Krylov solver...")

        try:
            result = root(F_real, x0, method='krylov',
                         options={'maxiter': 100, 'fatol': 1e-6,
                                  'disp': verbose})
            n = len(result.x) // 2
            Phi_sol = (result.x[:n] + 1j * result.x[n:]).reshape(
                self.N_M, self.N_F)

            info = {
                'success': result.success,
                'message': result.message,
                'nit': getattr(result, 'nit', -1),
                'residual': np.max(np.abs(result.fun)),
            }

            if verbose:
                print(f"  Success: {info['success']}")
                print(f"  Max residual: {info['residual']:.4e}")

            return Phi_sol, info

        except Exception as e:
            if verbose:
                print(f"  Newton-Krylov failed: {e}")
                print("  Falling back to relaxation...")
            return self.solve_relaxation(Phi_init)

    def solve_and_extract_yukawa(self, method='relaxation', **kwargs):
        """Solve the field equation and extract the Yukawa matrix.

        This is the main entry point for Phase 0.

        Returns:
            Y: (3, 3) complex Yukawa matrix
            masses: (3,) mass eigenvalues (arbitrary units)
            Phi: (N_M, N_F) field solution
        """
        if method == 'relaxation':
            Phi, history = self.solve_relaxation(**kwargs)
        elif method == 'newton':
            Phi, info = self.solve_newton_krylov(**kwargs)
        else:
            raise ValueError(f"Unknown method: {method}")

        # Extract Yukawa matrix
        Y = compute_overlap_matrix(Phi, self.ps.sections, self.N_F)

        # Get masses from SVD of Y
        _, masses, _ = np.linalg.svd(Y)
        masses = np.sort(masses)[::-1]  # descending

        return Y, masses, Phi


# ============================================================
# Validation
# ============================================================

def validate_higgs_equation(dim=2, rho_M=50, N_F=80, seed=42):
    """End-to-end validation of the Higgs field equation solver."""
    print("=" * 60)
    print(f"HIGGS FIELD EQUATION VALIDATION ({dim}D × CP²)")
    print("=" * 60)

    ps = ProductSpace(dim=dim, rho_M=rho_M, N_F=N_F, seed=seed)
    hfe = HiggsFieldEquation(ps, a=1.0, b=1.0, coupling=0.0)

    print(f"\n  Higgs parameters: a={hfe.a}, b={hfe.b}")
    print(f"  Vacuum: v = √(a/2b) = {hfe.v:.4f}")

    # Test 1: vacuum is a solution
    Phi_vac = hfe.v * np.ones((ps.N_M, ps.N_F), dtype=complex)
    res_vac = hfe.field_equation_residual(Phi_vac)
    print(f"\n  Test 1: Φ = v (uniform vacuum)")
    print(f"  Max |residual|: {np.max(np.abs(res_vac)):.4e}")
    print(f"  (Not exactly 0 because □(const) ≠ 0 on finite causal set)")

    # Test 2: solve with perturbation
    print(f"\n  Test 2: Relaxation from perturbed vacuum")
    Phi_sol, history = hfe.solve_relaxation(n_steps=200, dt=0.005)

    # Extract Yukawa
    Y = compute_overlap_matrix(Phi_sol, ps.sections, ps.N_F)
    _, masses, _ = np.linalg.svd(Y)
    masses = np.sort(masses)[::-1]

    print(f"\n  Yukawa matrix (real part):")
    for i in range(3):
        row = "   "
        for j in range(3):
            row += f" {Y[i, j].real:+.4f}"
        print(row)

    print(f"\n  Mass eigenvalues: {masses}")
    if masses[0] > 0:
        print(f"  Hierarchy ratios: m₂/m₁ = {masses[1] / masses[0]:.4f}, "
              f"m₃/m₁ = {masses[2] / masses[0]:.4f}")

    print("\n" + "=" * 60)
    return hfe, Phi_sol, Y


if __name__ == "__main__":
    validate_higgs_equation(dim=2, rho_M=50, N_F=80)
