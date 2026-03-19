#!/usr/bin/env python3
"""
Stable solvers for the Higgs field equation on M^d × F.

The field equation is:
    □Φ - aΦ + 2b|Φ|²Φ = 0

Split into linear L = □ - aI and nonlinear N(Φ) = 2b|Φ|²Φ:
    LΦ + N(Φ) = 0

Three solver strategies:

1. IMEX Crank-Nicolson: Treat L implicitly, N explicitly.
   Unconditionally stable for the linear part, which is the stiff
   component (the d'Alembertian has eigenvalues ~ ρ).

2. Adaptive explicit: Plain gradient descent with step-size control.
   Simple but limited by CFL condition.

3. Newton-Krylov with preconditioner: Direct steady-state solve.
   Most robust for strong nonlinearities.

4. Pseudo-transient continuation: Newton with increasing effective dt.
"""

import numpy as np
from scipy.sparse.linalg import LinearOperator, gmres, cg


class IMEXCrankNicolson:
    """IMEX Crank-Nicolson solver for the Higgs field equation.

    Treats the linear part (□ - a) implicitly and the quartic
    nonlinearity (2b|Φ|²Φ) explicitly.

    Each step solves:
        (I - dt/2 · L̃) Φ^{n+1} = (I + dt/2 · L̃) Φ^n - dt · Ñ(Φ^n)

    where L̃ = L/σ is the spectrally normalized linear operator
    (σ = spectral radius of □), and Ñ = N/σ.

    Normalization ensures the operator eigenvalues are O(1),
    making the GMRES solve well-conditioned regardless of ρ.
    """

    def __init__(self, apply_box, N_M, N_F, a=1.0, b=1.0, coupling_op=None):
        """
        Args:
            apply_box: callable (N_M, N_F) -> (N_M, N_F), applies □_{M×F}
            N_M, N_F: grid dimensions
            a, b: Higgs potential parameters
            coupling_op: optional callable for coupled d'Alembertian
        """
        self.apply_box = apply_box
        self.N_M = N_M
        self.N_F = N_F
        self.a = a
        self.b = b
        self.v = np.sqrt(a / (2 * b))
        self.coupling_op = coupling_op

        # Estimate spectral radius for normalization
        self.spectral_radius = estimate_operator_spectral_radius(
            apply_box, N_M, N_F)
        if self.spectral_radius < 1.0:
            self.spectral_radius = 1.0

    def _apply_L(self, Phi):
        """Linear operator L = □ - aI, normalized by spectral radius."""
        if self.coupling_op is not None:
            raw = self.coupling_op(Phi) - self.a * Phi
        else:
            raw = self.apply_box(Phi) - self.a * Phi
        return raw / self.spectral_radius

    def _apply_N(self, Phi):
        """Nonlinear term N(Φ) = 2b|Φ|²Φ, normalized."""
        return (2 * self.b * np.abs(Phi) ** 2 * Phi) / self.spectral_radius

    def _residual(self, Phi):
        """Full residual F(Φ) = LΦ + N(Φ) (normalized)."""
        return self._apply_L(Phi) + self._apply_N(Phi)

    def _apply_lhs(self, phi_flat, dt):
        """Apply (I - dt/2 · L) in flattened form for GMRES."""
        Phi = phi_flat.reshape(self.N_M, self.N_F)
        result = Phi - (dt / 2) * self._apply_L(Phi)
        return result.ravel()

    def solve(self, Phi_init=None, dt=0.001, n_steps=1000,
              tol=1e-7, gmres_tol=1e-4, verbose=True, log_interval=50):
        """Run the IMEX Crank-Nicolson iteration.

        Args:
            Phi_init: initial field (default: v + noise)
            dt: time step (CN is unconditionally stable for L)
            n_steps: maximum number of steps
            tol: convergence tolerance on residual norm
            gmres_tol: tolerance for inner GMRES solve
            verbose: print progress
            log_interval: steps between log messages

        Returns:
            Phi: converged field (N_M, N_F)
            history: list of (step, res_norm, mean_phi) tuples
        """
        if Phi_init is None:
            rng = np.random.default_rng(999)
            Phi = self.v * np.ones((self.N_M, self.N_F), dtype=complex)
            Phi += 0.01 * self.v * (
                rng.standard_normal(Phi.shape)
                + 1j * rng.standard_normal(Phi.shape)
            )
        else:
            Phi = Phi_init.astype(complex).copy()

        if verbose:
            print(f"    Spectral radius σ = {self.spectral_radius:.1f}, "
                  f"v = {self.v:.4f}")

        N_total = self.N_M * self.N_F
        history = []

        # Build the LHS operator for GMRES (fixed for given dt)
        lhs_op = LinearOperator(
            shape=(N_total, N_total),
            matvec=lambda x: self._apply_lhs(x, dt),
            dtype=complex,
        )

        prev_res_norm = float('inf')

        for step in range(n_steps):
            # Compute RHS: (I + dt/2 · L) Φ^n - dt · N(Φ^n)
            L_Phi = self._apply_L(Phi)
            N_Phi = self._apply_N(Phi)
            rhs = Phi + (dt / 2) * L_Phi - dt * N_Phi

            # Solve (I - dt/2 · L) Φ^{n+1} = rhs via GMRES
            rhs_flat = rhs.ravel()
            Phi_new_flat, info = gmres(
                lhs_op, rhs_flat, x0=Phi.ravel(),
                rtol=gmres_tol, maxiter=80, restart=30
            )

            Phi_new = Phi_new_flat.reshape(self.N_M, self.N_F)

            # Soft clamp: prevent runaway
            max_allowed = 5.0 * self.v
            mask = np.abs(Phi_new) > max_allowed
            if np.any(mask):
                Phi_new[mask] *= max_allowed / np.abs(Phi_new[mask])

            # Compute residual of the field equation
            res = self._residual(Phi_new)
            res_norm = np.sqrt(np.mean(np.abs(res) ** 2))
            mean_phi = np.mean(np.abs(Phi_new))

            if step % log_interval == 0:
                history.append((step, res_norm, mean_phi))
                if verbose:
                    print(f"    step {step:5d}: |res| = {res_norm:.4e}, "
                          f"⟨|Φ|⟩ = {mean_phi:.4f}")

            prev_res_norm = res_norm
            Phi = Phi_new

            if res_norm < tol:
                if verbose:
                    print(f"    Converged at step {step}, |res| = {res_norm:.4e}")
                history.append((step, res_norm, mean_phi))
                break

        return Phi, history


class AdaptiveExplicit:
    """Adaptive explicit (gradient descent) solver.

    Uses step-size control: reduce dt when residual grows,
    increase when solution is smooth. Simple fallback solver.
    """

    def __init__(self, apply_box, N_M, N_F, a=1.0, b=1.0, coupling_op=None):
        self.apply_box = apply_box
        self.N_M = N_M
        self.N_F = N_F
        self.a = a
        self.b = b
        self.v = np.sqrt(a / (2 * b))
        self.coupling_op = coupling_op

        # Estimate spectral radius for safe initial dt
        self.spectral_radius = estimate_operator_spectral_radius(
            apply_box, N_M, N_F)
        if self.spectral_radius < 1.0:
            self.spectral_radius = 1.0

    def _residual(self, Phi):
        if self.coupling_op is not None:
            box_phi = self.coupling_op(Phi)
        else:
            box_phi = self.apply_box(Phi)
        return box_phi - self.a * Phi + 2 * self.b * np.abs(Phi) ** 2 * Phi

    def solve(self, Phi_init=None, dt_init=None, n_steps=2000,
              tol=1e-7, verbose=True, log_interval=100):
        """Run adaptive explicit iteration.

        Step-size control:
          - If |res| decreased: increase dt by 5%
          - If |res| increased: halve dt and reject the step
          - Initial dt is set to 0.5/spectral_radius if not provided
        """
        if Phi_init is None:
            rng = np.random.default_rng(999)
            Phi = self.v * np.ones((self.N_M, self.N_F), dtype=complex)
            Phi += 0.01 * self.v * (
                rng.standard_normal(Phi.shape)
                + 1j * rng.standard_normal(Phi.shape)
            )
        else:
            Phi = Phi_init.astype(complex).copy()

        # Safe initial dt from spectral radius
        dt = dt_init if dt_init is not None else 0.5 / self.spectral_radius
        dt_max = 2.0 / self.spectral_radius

        if verbose:
            print(f"    Spectral radius σ = {self.spectral_radius:.1f}, "
                  f"dt_init = {dt:.2e}, dt_max = {dt_max:.2e}")
        history = []
        prev_res_norm = float('inf')

        for step in range(n_steps):
            res = self._residual(Phi)
            res_norm = np.sqrt(np.mean(np.abs(res) ** 2))

            # Adaptive step size
            if res_norm > 1.5 * prev_res_norm and step > 0:
                # Growing — reduce dt and reject
                dt *= 0.5
                Phi = Phi_prev.copy()
                res_norm = prev_res_norm
                if dt < 1e-12:
                    if verbose:
                        print(f"    dt underflow at step {step}")
                    break
                continue
            elif res_norm < 0.9 * prev_res_norm:
                # Decreasing — can increase dt
                dt = min(dt * 1.05, dt_max)

            Phi_prev = Phi.copy()
            prev_res_norm = res_norm

            if step % log_interval == 0:
                mean_phi = np.mean(np.abs(Phi))
                history.append((step, res_norm, mean_phi))
                if verbose:
                    print(f"    step {step:5d}: |res| = {res_norm:.4e}, "
                          f"⟨|Φ|⟩ = {mean_phi:.4f}, dt = {dt:.2e}")

            if res_norm < tol:
                if verbose:
                    print(f"    Converged at step {step}")
                break

            # Gradient step with clamping
            Phi -= dt * res

            # Soft clamp: project back if magnitude exceeds 5v
            mask = np.abs(Phi) > 5 * self.v
            if np.any(mask):
                Phi[mask] *= 5 * self.v / np.abs(Phi[mask])

        return Phi, history


class PseudoTransientNewton:
    """Pseudo-transient continuation (ΨTC) solver.

    Starts with a small effective time step (like explicit) and
    increases it as the residual decreases, transitioning smoothly
    to a full Newton iteration at convergence.

    At each step, solve:
        (1/δt · I + J(Φ^n)) δΦ = -F(Φ^n)

    where δt starts small and grows as |F| decreases.
    J is applied matrix-free via finite differences.
    """

    def __init__(self, apply_box, N_M, N_F, a=1.0, b=1.0, coupling_op=None):
        self.apply_box = apply_box
        self.N_M = N_M
        self.N_F = N_F
        self.a = a
        self.b = b
        self.v = np.sqrt(a / (2 * b))
        self.coupling_op = coupling_op

    def _residual(self, Phi):
        if self.coupling_op is not None:
            box_phi = self.coupling_op(Phi)
        else:
            box_phi = self.apply_box(Phi)
        return box_phi - self.a * Phi + 2 * self.b * np.abs(Phi) ** 2 * Phi

    def _jacobian_vec(self, Phi, dPhi, eps=1e-7):
        """Approximate J(Φ)·dΦ by finite difference."""
        norm_dPhi = np.linalg.norm(dPhi.ravel())
        if norm_dPhi < 1e-15:
            return np.zeros_like(dPhi)
        h = eps * max(1.0, np.linalg.norm(Phi.ravel())) / norm_dPhi
        return (self._residual(Phi + h * dPhi) - self._residual(Phi)) / h

    def solve(self, Phi_init=None, dt_init=1e-4, n_steps=200,
              tol=1e-7, verbose=True, log_interval=10):
        """Run pseudo-transient continuation.

        Args:
            dt_init: initial pseudo-time step (small = stable)
            n_steps: max Newton-like iterations
            tol: convergence tolerance
        """
        if Phi_init is None:
            rng = np.random.default_rng(999)
            Phi = self.v * np.ones((self.N_M, self.N_F), dtype=complex)
            Phi += 0.05 * self.v * (
                rng.standard_normal(Phi.shape)
                + 1j * rng.standard_normal(Phi.shape)
            )
        else:
            Phi = Phi_init.astype(complex).copy()

        dt = dt_init
        history = []
        N_total = self.N_M * self.N_F
        res0_norm = None

        for step in range(n_steps):
            F = self._residual(Phi)
            res_norm = np.sqrt(np.mean(np.abs(F) ** 2))

            if res0_norm is None:
                res0_norm = res_norm

            if step % log_interval == 0:
                mean_phi = np.mean(np.abs(Phi))
                history.append((step, res_norm, mean_phi))
                if verbose:
                    print(f"    step {step:4d}: |res| = {res_norm:.4e}, "
                          f"⟨|Φ|⟩ = {mean_phi:.4f}, δt = {dt:.2e}")

            if res_norm < tol:
                if verbose:
                    print(f"    Converged at step {step}")
                break

            # Build LHS operator: (1/dt · I + J(Φ))
            def lhs_matvec(dphi_flat, Phi_ref=Phi, dt_ref=dt):
                dPhi = dphi_flat.reshape(self.N_M, self.N_F)
                return ((1.0 / dt_ref) * dPhi
                        + self._jacobian_vec(Phi_ref, dPhi)).ravel()

            lhs_op = LinearOperator(
                shape=(N_total, N_total),
                matvec=lhs_matvec,
                dtype=complex,
            )

            # Solve for δΦ
            rhs = -F.ravel()
            dPhi_flat, info = gmres(
                lhs_op, rhs, x0=np.zeros(N_total, dtype=complex),
                rtol=1e-3, maxiter=30, restart=15
            )

            if info != 0 and verbose and step % log_interval == 0:
                print(f"      GMRES info={info}")

            dPhi = dPhi_flat.reshape(self.N_M, self.N_F)

            # Line search: ensure residual decreases
            alpha = 1.0
            for _ in range(5):
                Phi_trial = Phi + alpha * dPhi
                F_trial = self._residual(Phi_trial)
                trial_norm = np.sqrt(np.mean(np.abs(F_trial) ** 2))
                if trial_norm < res_norm:
                    break
                alpha *= 0.5
            else:
                alpha = 0.1  # fallback

            Phi = Phi + alpha * dPhi

            # Increase dt as residual decreases (SER rule)
            # dt_{n+1} = dt_n · |F_n| / |F_{n+1}|
            new_res_norm = np.sqrt(np.mean(np.abs(self._residual(Phi)) ** 2))
            if new_res_norm > 0:
                dt = min(dt * res_norm / new_res_norm, 1e6)

        return Phi, history


def estimate_operator_spectral_radius(apply_op, N_M, N_F, n_iter=20):
    """Estimate spectral radius of a linear operator via power iteration.

    Args:
        apply_op: callable (N_M, N_F) -> (N_M, N_F)
        N_M, N_F: dimensions
        n_iter: power iteration steps

    Returns:
        estimated spectral radius
    """
    rng = np.random.default_rng(12345)
    v = rng.standard_normal((N_M, N_F)) + 1j * rng.standard_normal((N_M, N_F))
    v /= np.linalg.norm(v.ravel())

    for _ in range(n_iter):
        Av = apply_op(v)
        sigma = np.linalg.norm(Av.ravel())
        if sigma > 1e-15:
            v = Av / sigma
        else:
            break

    return sigma
