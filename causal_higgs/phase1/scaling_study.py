#!/usr/bin/env python3
"""
Phase 1 systematic scaling study.

Runs the 2D × S¹ prototype across a grid of parameters:
  - N (sprinkling density ρ): 50, 100, 200, 400
  - Coupling strength g: 0.0, 0.01, 0.1, 0.5, 1.0
  - Multiple seeds for ensemble averaging

For each run, records:
  - Mass eigenvalues m₁, m₂, m₃
  - Mass ratios m₂/m₁, m₃/m₁
  - Off-diagonal Yukawa magnitudes (mixing signal)
  - Solver convergence info

Outputs a summary table and saves raw data for plotting.
"""

import sys
import os
import numpy as np
import time
import json

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

from phase0.causal_base import (
    poisson_sprinkle_minkowski,
    build_causal_matrix,
    order_intervals,
    build_dalembertian_matrix,
)
from phase0.solvers import IMEXCrankNicolson, AdaptiveExplicit
from phase1.s1_fiber import sprinkle_s1, s1_laplacian, fourier_sections


class ScalableProductSpace:
    """2D × S¹ product space with precomputed operators and coupling."""

    def __init__(self, rho_M=100, N_F=80, seed=42):
        self.rho_M = rho_M

        # Base
        self.base_points, self.N_M = poisson_sprinkle_minkowski(
            rho_M, dim=2, seed=seed)
        self.C = build_causal_matrix(self.base_points)
        self.intervals = order_intervals(self.C)
        self.box_M = build_dalembertian_matrix(
            self.C, self.intervals, 2, rho_M)

        # Fiber
        self.thetas = sprinkle_s1(N_F, seed + 1000)
        self.N_F = N_F
        self.lap_F, self.sigma_F = s1_laplacian(self.thetas)
        self.sections = fourier_sections(self.thetas, n_modes=3)

        # Fiber distance/kernel for coupling
        from phase1.s1_fiber import s1_distance_matrix
        self.D_F = s1_distance_matrix(self.thetas)
        self.K_F = np.exp(-self.D_F ** 2 / (2 * self.sigma_F ** 2))

        self.N_total = self.N_M * self.N_F

    def apply_box(self, Phi):
        """Pure product d'Alembertian."""
        return self.box_M @ Phi + (self.lap_F @ Phi.T).T

    def make_coupled_op(self, g):
        """Return a callable that applies the coupled d'Alembertian.

        Precomputes causal pairs for efficiency.
        """
        if abs(g) < 1e-15:
            return self.apply_box

        # Precompute causal pair list (much faster than scanning C each time)
        causal_pairs = []
        for i in range(self.N_M):
            for j in range(i + 1, self.N_M):
                if self.C[i, j]:
                    causal_pairs.append((i, j))
        causal_pairs = np.array(causal_pairs, dtype=int) if causal_pairs else np.empty((0, 2), dtype=int)

        K_F = self.K_F

        def coupled(Phi):
            result = self.apply_box(Phi)
            if len(causal_pairs) > 0:
                # Vectorized coupling: for all (i,j) pairs at once
                Phi_i = Phi[causal_pairs[:, 0], :]  # (n_pairs, N_F)
                Phi_j = Phi[causal_pairs[:, 1], :]
                # K_F @ Phi_i.T gives (N_F, n_pairs), transpose -> (n_pairs, N_F)
                transported = (K_F @ Phi_i.T).T
                coupling = g * (transported - Phi_j)
                # Scatter-add coupling to result at indices j
                np.add.at(result, causal_pairs[:, 1], coupling)
            return result

        return coupled

    def extract_yukawa(self, Phi):
        """Extract 3×3 Yukawa matrix from converged field."""
        late = int(0.6 * self.N_M)
        Phi_avg = np.mean(Phi[late:, :], axis=0)
        Y = np.zeros((3, 3), dtype=complex)
        for a in range(3):
            for b in range(3):
                Y[a, b] = np.mean(
                    Phi_avg * np.conj(self.sections[a]) * self.sections[b])
        return Y


def run_single(rho_M, N_F, coupling_g, seed, solver_type='cn',
               a=1.0, b=1.0, verbose=False):
    """Run a single configuration and return results.

    Args:
        rho_M: base sprinkling density
        N_F: fiber point count
        coupling_g: coupling strength
        seed: random seed
        solver_type: 'cn' (Crank-Nicolson), 'adaptive' (adaptive explicit)
        a, b: Higgs potential parameters

    Returns:
        dict with masses, ratios, yukawa, convergence info
    """
    t0 = time.time()

    ps = ScalableProductSpace(rho_M=rho_M, N_F=N_F, seed=seed)

    coupling_op = ps.make_coupled_op(coupling_g) if coupling_g > 0 else None

    if solver_type == 'cn':
        solver = IMEXCrankNicolson(
            ps.apply_box, ps.N_M, ps.N_F, a=a, b=b,
            coupling_op=coupling_op)
        Phi, history = solver.solve(
            dt=0.005, n_steps=500, tol=1e-6,
            gmres_tol=1e-3, verbose=verbose, log_interval=100)
    else:
        solver = AdaptiveExplicit(
            ps.apply_box, ps.N_M, ps.N_F, a=a, b=b,
            coupling_op=coupling_op)
        Phi, history = solver.solve(
            dt_init=1e-5, n_steps=2000, tol=1e-6,
            verbose=verbose, log_interval=200)

    # Extract Yukawa
    Y = ps.extract_yukawa(Phi)
    _, masses, _ = np.linalg.svd(Y)
    masses = np.sort(np.abs(masses))[::-1]

    # Off-diagonal signal
    offdiag = np.mean([abs(Y[i, j]) for i in range(3)
                       for j in range(3) if i != j])
    diag = np.mean([abs(Y[i, i]) for i in range(3)])

    # Final residual
    final_res = history[-1][1] if history else float('nan')

    elapsed = time.time() - t0

    return {
        'rho_M': rho_M,
        'N_F': N_F,
        'N_M': ps.N_M,
        'coupling_g': coupling_g,
        'seed': seed,
        'masses': masses.tolist(),
        'ratio_21': float(masses[1] / masses[0]) if masses[0] > 0 else 0,
        'ratio_31': float(masses[2] / masses[0]) if masses[0] > 0 else 0,
        'offdiag_signal': float(offdiag),
        'diag_mean': float(diag),
        'mixing_ratio': float(offdiag / diag) if diag > 0 else 0,
        'final_residual': float(final_res),
        'elapsed': elapsed,
        'solver': solver_type,
    }


def run_scaling_study(output_file='scaling_results.json'):
    """Run the full scaling study grid."""

    print("=" * 70)
    print("  PHASE 1 SCALING STUDY: 2D × S¹")
    print("=" * 70)

    # Parameter grid — tuned for tractability
    # Coupling is O(n_causal_pairs · N_F) per solver step
    # At ρ=200, n_causal ~ 5000+, so coupling runs are expensive
    densities = [50, 100, 200]
    couplings = [0.0, 0.1, 0.5]
    seeds = [42, 123]
    N_F = 60  # smaller fiber for speed

    all_results = []
    total_runs = len(densities) * len(couplings) * len(seeds)
    run_count = 0

    for rho in densities:
        for g in couplings:
            ensemble_results = []
            for seed in seeds:
                run_count += 1
                print(f"\n  [{run_count}/{total_runs}] "
                      f"ρ={rho}, g={g}, seed={seed}")

                try:
                    result = run_single(
                        rho_M=rho, N_F=N_F, coupling_g=g,
                        seed=seed, solver_type='cn', verbose=False)
                    ensemble_results.append(result)
                    all_results.append(result)

                    print(f"    N_M={result['N_M']}, "
                          f"masses=[{result['masses'][0]:.4f}, "
                          f"{result['masses'][1]:.4f}, "
                          f"{result['masses'][2]:.4f}], "
                          f"m₂/m₁={result['ratio_21']:.4f}, "
                          f"mixing={result['mixing_ratio']:.4f}, "
                          f"{result['elapsed']:.1f}s")

                except Exception as e:
                    print(f"    FAILED: {e}")

            # Ensemble summary
            if ensemble_results:
                r21s = [r['ratio_21'] for r in ensemble_results]
                r31s = [r['ratio_31'] for r in ensemble_results]
                mixings = [r['mixing_ratio'] for r in ensemble_results]
                print(f"\n  ENSEMBLE (ρ={rho}, g={g}): "
                      f"m₂/m₁ = {np.mean(r21s):.4f} ± {np.std(r21s):.4f}, "
                      f"m₃/m₁ = {np.mean(r31s):.4f} ± {np.std(r31s):.4f}, "
                      f"mixing = {np.mean(mixings):.4f} ± {np.std(mixings):.4f}")

    # Summary table
    print("\n" + "=" * 70)
    print("  SCALING STUDY SUMMARY")
    print("=" * 70)
    print(f"\n  {'ρ':>5} {'g':>6} {'N_seeds':>7} "
          f"{'m₂/m₁':>8} {'±':>6} {'m₃/m₁':>8} {'±':>6} "
          f"{'mixing':>8} {'±':>6}")
    print("  " + "-" * 65)

    for rho in densities:
        for g in couplings:
            subset = [r for r in all_results
                      if r['rho_M'] == rho and r['coupling_g'] == g]
            if not subset:
                continue
            r21s = [r['ratio_21'] for r in subset]
            r31s = [r['ratio_31'] for r in subset]
            mixings = [r['mixing_ratio'] for r in subset]
            print(f"  {rho:>5} {g:>6.2f} {len(subset):>7} "
                  f"{np.mean(r21s):>8.4f} {np.std(r21s):>6.4f} "
                  f"{np.mean(r31s):>8.4f} {np.std(r31s):>6.4f} "
                  f"{np.mean(mixings):>8.4f} {np.std(mixings):>6.4f}")

    # Key trends
    print(f"\n  KEY TRENDS:")
    for g in couplings:
        r21_by_rho = {}
        for rho in densities:
            subset = [r for r in all_results
                      if r['rho_M'] == rho and r['coupling_g'] == g]
            if subset:
                r21_by_rho[rho] = np.mean([r['ratio_21'] for r in subset])
        if len(r21_by_rho) >= 2:
            rhos = sorted(r21_by_rho.keys())
            trend = r21_by_rho[rhos[-1]] - r21_by_rho[rhos[0]]
            direction = "↓ INCREASING hierarchy" if trend < 0 else "↑ DECREASING hierarchy"
            print(f"    g={g:.2f}: m₂/m₁ goes from "
                  f"{r21_by_rho[rhos[0]]:.4f} → {r21_by_rho[rhos[-1]]:.4f} "
                  f"as ρ grows ({direction})")

    # Save raw data
    output_path = os.path.join(
        os.path.dirname(os.path.abspath(__file__)), output_file)
    with open(output_path, 'w') as f:
        json.dump(all_results, f, indent=2)
    print(f"\n  Raw data saved to {output_path}")

    print("\n" + "=" * 70)
    return all_results


if __name__ == "__main__":
    run_scaling_study()
