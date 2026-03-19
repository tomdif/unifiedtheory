#!/usr/bin/env python3
"""
Extended scaling study with 6 seeds per configuration for publication-quality
error bars. Outputs JSON for analysis and plotting.
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
from phase0.solvers import IMEXCrankNicolson
from phase1.s1_fiber import sprinkle_s1, s1_laplacian, fourier_sections, s1_distance_matrix


class ScalableProductSpace:
    def __init__(self, rho_M=100, N_F=60, seed=42):
        self.rho_M = rho_M
        self.base_points, self.N_M = poisson_sprinkle_minkowski(
            rho_M, dim=2, seed=seed)
        self.C = build_causal_matrix(self.base_points)
        self.intervals = order_intervals(self.C)
        self.box_M = build_dalembertian_matrix(
            self.C, self.intervals, 2, rho_M)

        self.thetas = sprinkle_s1(N_F, seed + 1000)
        self.N_F = N_F
        self.lap_F, self.sigma_F = s1_laplacian(self.thetas)
        self.sections = fourier_sections(self.thetas, n_modes=3)

        self.D_F = s1_distance_matrix(self.thetas)
        self.K_F = np.exp(-self.D_F ** 2 / (2 * self.sigma_F ** 2))
        self.N_total = self.N_M * self.N_F

    def apply_box(self, Phi):
        return self.box_M @ Phi + (self.lap_F @ Phi.T).T

    def make_coupled_op(self, g):
        if abs(g) < 1e-15:
            return self.apply_box
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
                Phi_i = Phi[causal_pairs[:, 0], :]
                Phi_j = Phi[causal_pairs[:, 1], :]
                transported = (K_F @ Phi_i.T).T
                coupling = g * (transported - Phi_j)
                np.add.at(result, causal_pairs[:, 1], coupling)
            return result
        return coupled

    def extract_yukawa(self, Phi):
        late = int(0.6 * self.N_M)
        Phi_avg = np.mean(Phi[late:, :], axis=0)
        Y = np.zeros((3, 3), dtype=complex)
        for a in range(3):
            for b in range(3):
                Y[a, b] = np.mean(
                    Phi_avg * np.conj(self.sections[a]) * self.sections[b])
        return Y


def run_single(rho_M, N_F, coupling_g, seed, a=1.0, b=1.0):
    t0 = time.time()
    ps = ScalableProductSpace(rho_M=rho_M, N_F=N_F, seed=seed)
    coupling_op = ps.make_coupled_op(coupling_g) if coupling_g > 0 else None

    solver = IMEXCrankNicolson(
        ps.apply_box, ps.N_M, ps.N_F, a=a, b=b, coupling_op=coupling_op)
    Phi, history = solver.solve(
        dt=0.005, n_steps=500, tol=1e-6,
        gmres_tol=1e-3, verbose=False, log_interval=500)

    Y = ps.extract_yukawa(Phi)
    _, masses, _ = np.linalg.svd(Y)
    masses = np.sort(np.abs(masses))[::-1]

    offdiag = np.mean([abs(Y[i, j]) for i in range(3)
                       for j in range(3) if i != j])
    diag = np.mean([abs(Y[i, i]) for i in range(3)])
    final_res = history[-1][1] if history else float('nan')

    r21 = float(masses[1] / masses[0]) if masses[0] > 0 else 0
    r31 = float(masses[2] / masses[0]) if masses[0] > 0 else 0
    geometric = float(r21 ** 2 / r31) if r31 > 0 else 0

    return {
        'rho_M': rho_M, 'N_F': N_F, 'N_M': ps.N_M,
        'coupling_g': coupling_g, 'seed': seed,
        'masses': masses.tolist(),
        'ratio_21': r21, 'ratio_31': r31,
        'geometric_test': geometric,
        'offdiag_signal': float(offdiag),
        'diag_mean': float(diag),
        'mixing_ratio': float(offdiag / diag) if diag > 0 else 0,
        'final_residual': float(final_res),
        'elapsed': time.time() - t0,
    }


def main():
    print("=" * 70)
    print("  EXTENDED SCALING STUDY (6 seeds per configuration)")
    print("=" * 70)

    densities = [50, 100, 200]
    couplings = [0.0, 0.1, 0.5]
    seeds = [42, 123, 456, 789, 1001, 2025]
    N_F = 60

    all_results = []
    total = len(densities) * len(couplings) * len(seeds)
    n = 0

    for rho in densities:
        for g in couplings:
            results_this = []
            for seed in seeds:
                n += 1
                sys.stdout.write(f"\r  [{n}/{total}] ρ={rho}, g={g}, seed={seed}   ")
                sys.stdout.flush()
                try:
                    r = run_single(rho, N_F, g, seed)
                    results_this.append(r)
                    all_results.append(r)
                except Exception as e:
                    print(f"\n    FAILED: {e}")

            if results_this:
                r21 = [r['ratio_21'] for r in results_this]
                r31 = [r['ratio_31'] for r in results_this]
                geo = [r['geometric_test'] for r in results_this]
                mix = [r['mixing_ratio'] for r in results_this]
                print(f"\n  ρ={rho}, g={g}: "
                      f"m₂/m₁ = {np.mean(r21):.4f}±{np.std(r21):.4f}, "
                      f"m₃/m₁ = {np.mean(r31):.4f}±{np.std(r31):.4f}, "
                      f"geo = {np.mean(geo):.3f}±{np.std(geo):.3f}, "
                      f"mix = {np.mean(mix):.4f}±{np.std(mix):.4f}")

    # Summary table
    print("\n" + "=" * 80)
    print(f"  {'ρ':>5} {'g':>5} {'n':>3} "
          f"{'m₂/m₁':>8} {'±':>6} {'m₃/m₁':>8} {'±':>6} "
          f"{'geo':>6} {'±':>5} {'mix':>7} {'±':>6}")
    print("  " + "-" * 72)

    for rho in densities:
        for g in couplings:
            s = [r for r in all_results
                 if r['rho_M'] == rho and abs(r['coupling_g'] - g) < 1e-6]
            if not s:
                continue
            r21 = [r['ratio_21'] for r in s]
            r31 = [r['ratio_31'] for r in s]
            geo = [r['geometric_test'] for r in s]
            mix = [r['mixing_ratio'] for r in s]
            print(f"  {rho:>5} {g:>5.1f} {len(s):>3} "
                  f"{np.mean(r21):>8.4f} {np.std(r21):>6.4f} "
                  f"{np.mean(r31):>8.4f} {np.std(r31):>6.4f} "
                  f"{np.mean(geo):>6.3f} {np.std(geo):>5.3f} "
                  f"{np.mean(mix):>7.4f} {np.std(mix):>6.4f}")

    # Trends
    print(f"\n  TRENDS (m₂/m₁ vs ρ):")
    for g in couplings:
        vals = {}
        for rho in densities:
            s = [r for r in all_results
                 if r['rho_M'] == rho and abs(r['coupling_g'] - g) < 1e-6]
            if s:
                vals[rho] = (np.mean([r['ratio_21'] for r in s]),
                             np.std([r['ratio_21'] for r in s]))
        if len(vals) >= 2:
            rhos = sorted(vals.keys())
            v0, v1 = vals[rhos[0]][0], vals[rhos[-1]][0]
            print(f"    g={g:.1f}: {v0:.4f} → {v1:.4f} "
                  f"({'↓ hierarchy deepens' if v1 < v0 else '↑ hierarchy weakens'})")

    out = os.path.join(os.path.dirname(os.path.abspath(__file__)),
                       'scaling_results_full.json')
    with open(out, 'w') as f:
        json.dump(all_results, f, indent=2)
    print(f"\n  Saved to {out}")
    print("=" * 70)


if __name__ == "__main__":
    main()
