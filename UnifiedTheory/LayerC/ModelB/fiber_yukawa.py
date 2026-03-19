#!/usr/bin/env python3
"""
fiber_yukawa.py — Compute Yukawa couplings from overlap integrals on CP²

THE COMPUTATION:
  The three generations are sections s₀, s₁, s₂ of O(1) on the fiber
  CP² = SU(3)/(SU(2)×U(1)). The Yukawa coupling is:

    Y_ij = ∫_{CP²} s_i*(p) · H(p) · s_j(p) dμ_{FS}(p)

  where H(p) is the Higgs field profile on the fiber and dμ_{FS} is
  the Fubini-Study measure.

  On a Poisson lattice with density ρ, the integral becomes a Monte Carlo
  sum over N randomly sprinkled points on CP².

INGREDIENTS:
  - Sections: s_k([z₀:z₁:z₂]) = z_k / |z|  (coordinate functions)
  - Higgs profile: H(p) = exp(-d²(p, p₀) / (2σ²))
    where d is the Fubini-Study distance to the VEV direction p₀
  - Measure: uniform Fubini-Study sampling on CP²
  - Parameter σ: Higgs localization width (= 1/√ρ at Planck scale)

THE QUESTION:
  Is there a value of σ such that:
  - y₀ ≈ 1/3  (overall Yukawa scale, from m_t ≈ v)
  - ε ≈ 0.22  (hierarchy parameter, from Cabibbo angle)
  If yes, the framework determines ALL 13 mass parameters from one number (σ).
"""

import numpy as np
from dataclasses import dataclass
from typing import Tuple, Dict
import json


# ============================================================
# CP² geometry
# ============================================================

def sample_CP2(n_points: int, rng: np.random.RandomState) -> np.ndarray:
    """Sample n points uniformly on CP² using the Fubini-Study measure.

    Method: generate z ∈ ℂ³ with each component ~ N(0,1) + i·N(0,1),
    then normalize to |z| = 1. The unit sphere S⁵ ⊂ ℂ³ projects to CP²
    with the correct Fubini-Study measure (Haar measure on SU(3) quotient).

    Returns: (n_points, 3) complex array of homogeneous coordinates.
    """
    real = rng.randn(n_points, 3)
    imag = rng.randn(n_points, 3)
    z = real + 1j * imag
    # Normalize to unit sphere S⁵
    norms = np.linalg.norm(z, axis=1, keepdims=True)
    z /= norms
    return z


def fubini_study_distance(z: np.ndarray, w: np.ndarray) -> np.ndarray:
    """Fubini-Study distance between points on CP².

    d([z], [w]) = arccos(|⟨z,w⟩| / (|z|·|w|))

    For normalized z, w (|z|=|w|=1): d = arccos(|⟨z,w⟩|).
    """
    inner = np.abs(np.sum(z * np.conj(w), axis=-1))
    inner = np.clip(inner, 0, 1)  # numerical safety
    return np.arccos(inner)


def sections_O1(z: np.ndarray) -> Tuple[np.ndarray, np.ndarray, np.ndarray]:
    """The three sections of O(1) on CP² evaluated at points z.

    s_k(z) = z_k (the k-th coordinate function, already normalized since |z|=1).

    Returns: (s₀, s₁, s₂) each of shape (n_points,).
    """
    return z[:, 0], z[:, 1], z[:, 2]


# ============================================================
# Higgs field profile on CP²
# ============================================================

def higgs_profile(z: np.ndarray, p0: np.ndarray, sigma: float) -> np.ndarray:
    """Higgs field profile on CP²: Gaussian localized around p₀.

    H(p) = exp(-d²(p, p₀) / (2σ²))

    where d is the Fubini-Study distance and σ is the localization width.

    σ → 0: delta-function at p₀ (rank-1 Yukawa, democratic limit if p₀ symmetric)
    σ → ∞: constant on CP² (diagonal Yukawa, equal masses)

    The physical σ is set by the Planck-scale lattice: σ ~ 1/√ρ^{1/4}.

    Returns: (n_points,) real array of Higgs field values.
    """
    p0_norm = p0 / np.linalg.norm(p0)
    dist = fubini_study_distance(z, p0_norm[np.newaxis, :])
    return np.exp(-dist**2 / (2 * sigma**2))


# ============================================================
# Yukawa matrix computation
# ============================================================

def compute_yukawa_matrix(n_points: int, sigma: float, p0: np.ndarray,
                           seed: int = 42) -> np.ndarray:
    """Compute the 3×3 Yukawa matrix by Monte Carlo integration on CP².

    Y_ij = (1/N) Σ_n s_i*(z_n) · H(z_n) · s_j(z_n)

    This is the Poisson lattice approximation to the fiber overlap integral.

    Returns: 3×3 complex Yukawa matrix.
    """
    rng = np.random.RandomState(seed)
    z = sample_CP2(n_points, rng)

    s0, s1, s2 = sections_O1(z)
    H = higgs_profile(z, p0, sigma)

    # Y_ij = <s_i* · H · s_j>
    sections = np.stack([s0, s1, s2], axis=0)  # (3, n_points)
    Y = np.zeros((3, 3), dtype=complex)
    for i in range(3):
        for j in range(3):
            Y[i, j] = np.mean(np.conj(sections[i]) * H * sections[j])

    return Y


def diagonalize_yukawa(Y: np.ndarray) -> Dict:
    """Diagonalize the Yukawa matrix via SVD.

    Y = U† · D · V where D = diag(y₁, y₂, y₃) with y₁ ≤ y₂ ≤ y₃.

    The CKM matrix is V_u† · V_d (for different up/down-type Y).
    For a single Yukawa matrix, V is the right-singular matrix.

    Returns: masses, CKM angles, and diagnostic quantities.
    """
    U, singular_values, Vh = np.linalg.svd(Y)
    # Sort in ascending order
    idx = np.argsort(singular_values)
    masses = singular_values[idx]

    return {
        'yukawa_eigenvalues': masses.tolist(),
        'y1': float(masses[0]),
        'y2': float(masses[1]),
        'y3': float(masses[2]),
        'ratio_32': float(masses[2] / masses[1]) if masses[1] > 1e-15 else float('inf'),
        'ratio_21': float(masses[1] / masses[0]) if masses[0] > 1e-15 else float('inf'),
        'y0_effective': float(masses[2] / 3),  # compare to y₀ ≈ 1/3
        'trace': float(np.real(np.trace(Y))),
        'det': float(np.abs(np.linalg.det(Y))),
    }


def compute_ckm(Y_up: np.ndarray, Y_down: np.ndarray) -> Dict:
    """Compute the CKM matrix from up-type and down-type Yukawa matrices.

    CKM = V_u† · V_d where V_u, V_d are the right-singular matrices.
    """
    _, _, Vh_u = np.linalg.svd(Y_up)
    _, _, Vh_d = np.linalg.svd(Y_down)
    V_CKM = Vh_u @ np.conj(Vh_d.T)

    # Extract magnitudes
    V_abs = np.abs(V_CKM)

    # Wolfenstein-like parameters
    V_us = V_abs[0, 1]
    V_cb = V_abs[1, 2]
    V_ub = V_abs[0, 2]

    # Jarlskog invariant: J = Im(V_us · V_cb · V*_ub · V*_cs)
    J = np.imag(V_CKM[0, 1] * V_CKM[1, 2] *
                np.conj(V_CKM[0, 2]) * np.conj(V_CKM[1, 1]))

    return {
        'V_CKM_abs': V_abs.tolist(),
        'V_us': float(V_us),
        'V_cb': float(V_cb),
        'V_ub': float(V_ub),
        'Jarlskog': float(J),
        'unitarity_check': float(np.max(np.abs(V_CKM @ np.conj(V_CKM.T) - np.eye(3)))),
    }


# ============================================================
# Main computation: scan over σ
# ============================================================

def scan_sigma(sigma_values: np.ndarray, n_points: int = 100000,
               seed: int = 42) -> Dict:
    """Scan over Higgs profile widths σ to find the best fit.

    For each σ, compute the Yukawa matrix, extract y₀ and ε, and
    compare to the target values y₀ ≈ 1/3 and ε ≈ 0.22.

    The VEV direction is taken as [1:1:1]/√3 (democratic point)
    perturbed slightly toward [0:0:1] (breaking S₃).
    """
    # VEV direction: slightly broken from democratic
    # [1:1:1+δ] where δ controls the breaking
    delta = 0.5  # perturbation from democratic point
    p0 = np.array([1.0, 1.0, 1.0 + delta]) / np.sqrt(2 + (1+delta)**2)

    results = []

    for sigma in sigma_values:
        Y = compute_yukawa_matrix(n_points, sigma, p0, seed)
        diag = diagonalize_yukawa(Y)

        # Extract effective parameters
        y3 = diag['y3']
        y2 = diag['y2']
        y1 = diag['y1']

        # y₀ = y₃/3 (from democratic limit: largest eigenvalue = 3y₀)
        y0 = y3 / 3

        # ε = y₂/y₃ (ratio of second to third generation)
        epsilon = y2 / y3 if y3 > 1e-15 else 0

        # ε² ≈ y₁/y₂ (geometric hierarchy check)
        eps_sq = y1 / y2 if y2 > 1e-15 else 0

        results.append({
            'sigma': float(sigma),
            'y0': float(y0),
            'epsilon': float(epsilon),
            'epsilon_squared_check': float(eps_sq),
            'y1': float(y1),
            'y2': float(y2),
            'y3': float(y3),
            'ratio_32': diag['ratio_32'],
            'ratio_21': diag['ratio_21'],
        })

    return {
        'scan_results': results,
        'n_points': n_points,
        'p0': p0.tolist(),
        'delta': delta,
    }


def run_full_computation(n_points: int = 200000, seed: int = 42) -> Dict:
    """Run the full Yukawa computation.

    1. Scan σ to find the best fit
    2. At the best σ, compute masses and CKM
    3. Compare to experimental values
    """
    print("=" * 70)
    print("  YUKAWA COUPLING COMPUTATION FROM CP² FIBER OVERLAP INTEGRALS")
    print("=" * 70)
    print(f"  Lattice points: {n_points}")
    print(f"  Seed: {seed}")
    print()

    # Step 1: Scan σ
    sigma_values = np.linspace(0.1, 2.0, 40)
    scan = scan_sigma(sigma_values, n_points, seed)

    # Find σ closest to ε ≈ 0.22
    best_idx = min(range(len(scan['scan_results'])),
                   key=lambda i: abs(scan['scan_results'][i]['epsilon'] - 0.22))
    best = scan['scan_results'][best_idx]
    best_sigma = best['sigma']

    print(f"  SCAN RESULTS (VEV perturbation δ = {scan['delta']}):")
    print(f"  {'σ':>6s}  {'y₀':>8s}  {'ε':>8s}  {'ε²check':>8s}  {'y₃/y₂':>8s}  {'y₂/y₁':>8s}")
    print(f"  {'-'*6}  {'-'*8}  {'-'*8}  {'-'*8}  {'-'*8}  {'-'*8}")
    for r in scan['scan_results'][::4]:  # every 4th for brevity
        print(f"  {r['sigma']:6.3f}  {r['y0']:8.4f}  {r['epsilon']:8.4f}  "
              f"{r['epsilon_squared_check']:8.4f}  {r['ratio_32']:8.2f}  {r['ratio_21']:8.2f}")
    print()
    print(f"  BEST FIT: σ = {best_sigma:.3f}")
    print(f"    y₀ = {best['y0']:.4f}  (target: ~0.33)")
    print(f"    ε  = {best['epsilon']:.4f}  (target: ~0.22)")
    print(f"    ε² check = {best['epsilon_squared_check']:.4f}  (target: ~{0.22**2:.4f})")
    print()

    # Step 2: Compute up-type and down-type Yukawas at best σ
    # Up-type: VEV slightly toward z₂ (third generation = top)
    delta_u = 0.5
    p0_u = np.array([1.0, 1.0, 1.0 + delta_u])
    p0_u /= np.linalg.norm(p0_u)
    Y_u = compute_yukawa_matrix(n_points, best_sigma, p0_u, seed)

    # Down-type: VEV slightly different (CKM from misalignment)
    delta_d = 0.45  # slightly different from up-type
    p0_d = np.array([1.0, 1.0 + 0.05, 1.0 + delta_d])
    p0_d /= np.linalg.norm(p0_d)
    Y_d = compute_yukawa_matrix(n_points, best_sigma, p0_d, seed + 1)

    diag_u = diagonalize_yukawa(Y_u)
    diag_d = diagonalize_yukawa(Y_d)
    ckm = compute_ckm(Y_u, Y_d)

    # Step 3: Convert to physical masses (m = y · v, v = 174 GeV)
    v = 174.0  # GeV
    m_u_type = [y * v for y in diag_u['yukawa_eigenvalues']]
    m_d_type = [y * v for y in diag_d['yukawa_eigenvalues']]

    print(f"  MASS PREDICTIONS (v = {v} GeV):")
    print(f"  Up-type:   m₁ = {m_u_type[0]*1000:.2f} MeV,  m₂ = {m_u_type[1]*1000:.1f} MeV,  "
          f"m₃ = {m_u_type[2]:.1f} GeV")
    print(f"  Down-type: m₁ = {m_d_type[0]*1000:.2f} MeV,  m₂ = {m_d_type[1]*1000:.1f} MeV,  "
          f"m₃ = {m_d_type[2]:.1f} GeV")
    print()

    # Experimental values (running masses at M_Z)
    exp_up = [0.00216, 1.27, 173.0]    # GeV
    exp_down = [0.00467, 0.093, 4.18]  # GeV
    exp_ckm = {'V_us': 0.2243, 'V_cb': 0.0422, 'V_ub': 0.00394, 'J': 3.08e-5}

    print(f"  COMPARISON WITH EXPERIMENT:")
    print(f"  {'':>20s}  {'Computed':>10s}  {'Measured':>10s}  {'Ratio':>8s}")
    print(f"  {'-'*20}  {'-'*10}  {'-'*10}  {'-'*8}")

    for name, comp, exp_val in [
        ('m_u (MeV)', m_u_type[0]*1000, exp_up[0]*1000),
        ('m_c (GeV)', m_u_type[1], exp_up[1]),
        ('m_t (GeV)', m_u_type[2], exp_up[2]),
        ('m_d (MeV)', m_d_type[0]*1000, exp_down[0]*1000),
        ('m_s (MeV)', m_d_type[1]*1000, exp_down[1]*1000),
        ('m_b (GeV)', m_d_type[2], exp_down[2]),
    ]:
        ratio = comp / exp_val if exp_val > 0 else 0
        print(f"  {name:>20s}  {comp:>10.3f}  {exp_val:>10.3f}  {ratio:>8.2f}")

    print()
    print(f"  CKM MATRIX:")
    V = np.array(ckm['V_CKM_abs'])
    print(f"  |V_ud| = {V[0,0]:.4f}  |V_us| = {V[0,1]:.4f}  |V_ub| = {V[0,2]:.6f}")
    print(f"  |V_cd| = {V[1,0]:.4f}  |V_cs| = {V[1,1]:.4f}  |V_cb| = {V[1,2]:.4f}")
    print(f"  |V_td| = {V[2,0]:.4f}  |V_ts| = {V[2,1]:.4f}  |V_tb| = {V[2,2]:.4f}")
    print()
    print(f"  CKM COMPARISON:")
    print(f"  {'':>12s}  {'Computed':>10s}  {'Measured':>10s}")
    print(f"  {'|V_us|':>12s}  {ckm['V_us']:>10.4f}  {exp_ckm['V_us']:>10.4f}")
    print(f"  {'|V_cb|':>12s}  {ckm['V_cb']:>10.4f}  {exp_ckm['V_cb']:>10.4f}")
    print(f"  {'|V_ub|':>12s}  {ckm['V_ub']:>10.6f}  {exp_ckm['V_ub']:>10.6f}")
    print(f"  {'Jarlskog':>12s}  {ckm['Jarlskog']:>10.2e}  {exp_ckm['J']:>10.2e}")
    print(f"  Unitarity: max|VV†-1| = {ckm['unitarity_check']:.2e}")

    print()
    print(f"  FREE PARAMETERS USED:")
    print(f"    σ = {best_sigma:.3f}  (Higgs profile width on CP²)")
    print(f"    δ_u = {delta_u}  (up-type VEV perturbation)")
    print(f"    δ_d = {delta_d}  (down-type VEV perturbation)")
    print(f"    Δ_d = 0.05  (down-type VEV misalignment → CKM)")
    print()

    full_result = {
        'best_sigma': best_sigma,
        'scan': scan,
        'up_type': diag_u,
        'down_type': diag_d,
        'ckm': ckm,
        'masses_up_GeV': m_u_type,
        'masses_down_GeV': m_d_type,
        'n_points': n_points,
    }

    return full_result


if __name__ == '__main__':
    result = run_full_computation(n_points=200000, seed=42)

    # Save certificate
    cert_path = 'fiber_yukawa_certificate.json'
    with open(cert_path, 'w') as f:
        json.dump({
            'best_sigma': result['best_sigma'],
            'masses_up_GeV': result['masses_up_GeV'],
            'masses_down_GeV': result['masses_down_GeV'],
            'ckm': result['ckm'],
            'n_points': result['n_points'],
        }, f, indent=2)
    print(f"  Certificate saved to {cert_path}")
