#!/usr/bin/env python3
"""
Yukawa matrix extraction from the Higgs vacuum profile.

Given a Higgs field solution Φ(x, f) on M^d × CP², the Yukawa
coupling matrix is:

    Y_{ab} = ∫_{CP²} Φ_vac(f) · s_a(f)* · s_b(f) dμ_FS(f)

where s_a are the three O(1) sections (generation wavefunctions)
and Φ_vac is the vacuum profile (averaged over spacetime).

For up-type quarks and down-type quarks, the Yukawa matrices can
differ due to hypercharge dependence:
  Y^u_{ab} = ∫ Φ(f) · s_a* · s_b · w_u(f) dμ
  Y^d_{ab} = ∫ Φ(f) · s_a* · s_b · w_d(f) dμ

where w_u, w_d encode the hypercharge weight factors.

The physical masses and CKM matrix follow from:
  M_u = v · Y^u, M_d = v · Y^d
  V_CKM = V_u† · V_d (misalignment of diagonalizations)
"""

import numpy as np


def extract_yukawa_matrix(Phi_vac_fiber, sections):
    """Extract the Yukawa matrix from the fiber profile of the Higgs.

    Args:
        Phi_vac_fiber: (N_F,) complex — Higgs vacuum profile on fiber
        sections: (3, N_F) complex — O(1) sections

    Returns:
        Y: (3, 3) complex Yukawa matrix
    """
    N_g = 3
    Y = np.zeros((N_g, N_g), dtype=complex)
    for a in range(N_g):
        for b in range(N_g):
            Y[a, b] = np.mean(Phi_vac_fiber * np.conj(sections[a]) * sections[b])
    return Y


def extract_with_hypercharge(Phi_vac_fiber, sections, fiber_points, y_ratio):
    """Extract Yukawa with hypercharge-dependent weight.

    The hypercharge introduces a U(1) phase rotation that differs
    between up-type and down-type quarks. This can produce different
    Yukawa matrices for the two sectors even from a single Higgs.

    Args:
        Phi_vac_fiber: (N_F,) Higgs vacuum on fiber
        sections: (3, N_F) O(1) sections
        fiber_points: (N_F, 3) CP² points
        y_ratio: hypercharge ratio parameter

    Returns:
        Y: (3, 3) Yukawa matrix with hypercharge weight
    """
    # Hypercharge weight: phase rotation by y_ratio * arg(z_0)
    # This is a U(1) action on the fiber
    phases = np.exp(1j * y_ratio * np.angle(fiber_points[:, 0]))
    weighted_phi = Phi_vac_fiber * phases

    return extract_yukawa_matrix(weighted_phi, sections)


def masses_and_ckm(Y_up, Y_down, v_higgs=246.0):
    """Compute masses and CKM matrix from Yukawa matrices.

    Args:
        Y_up: (3, 3) up-type Yukawa
        Y_down: (3, 3) down-type Yukawa
        v_higgs: Higgs vev in GeV

    Returns:
        dict with masses_up, masses_down, V_ckm, jarlskog
    """
    M_up = v_higgs * Y_up
    M_down = v_higgs * Y_down

    # SVD: M = U · Σ · V†
    U_u, s_u, Vh_u = np.linalg.svd(M_up)
    U_d, s_d, Vh_d = np.linalg.svd(M_down)

    masses_up = np.sort(np.abs(s_u))
    masses_down = np.sort(np.abs(s_d))

    # CKM = V_uL† · V_dL
    V_ckm = U_u.conj().T @ U_d

    # Jarlskog invariant: J = Im(V_us V_cb V_ub* V_cs*)
    J = np.imag(V_ckm[0, 1] * V_ckm[1, 2]
                * np.conj(V_ckm[0, 2]) * np.conj(V_ckm[1, 1]))

    return {
        'masses_up': masses_up,
        'masses_down': masses_down,
        'V_ckm': V_ckm,
        'V_ckm_abs': np.abs(V_ckm),
        'jarlskog': J,
    }


def analyze_hierarchy(masses, label=""):
    """Analyze the mass hierarchy of a set of masses.

    The democratic limit gives m₁ : m₂ : m₃ ≈ 1 : ε : ε²
    where ε is the S₃-breaking parameter.

    The Wolfenstein parametrization of CKM has |V_{us}| ~ ε.

    Args:
        masses: (3,) sorted descending
        label: string label for printing
    """
    if masses[0] == 0:
        print(f"  {label}: all masses zero")
        return None

    masses = np.sort(np.abs(masses))[::-1]  # descending

    r21 = masses[1] / masses[0] if masses[0] > 0 else 0
    r31 = masses[2] / masses[0] if masses[0] > 0 else 0

    print(f"\n  {label} mass hierarchy:")
    print(f"    m₁ = {masses[0]:.4e}")
    print(f"    m₂ = {masses[1]:.4e}")
    print(f"    m₃ = {masses[2]:.4e}")
    print(f"    m₂/m₁ = {r21:.4f}")
    print(f"    m₃/m₁ = {r31:.4f}")

    # Check if geometric: m₂/m₁ ≈ (m₃/m₁)^{1/2}
    if r31 > 0:
        geometric_test = r21 / np.sqrt(r31) if r31 > 0 else float('inf')
        print(f"    Geometric test (m₂/m₁)/√(m₃/m₁) = {geometric_test:.4f} (expect ≈ 1)")

    # Extract epsilon
    if r21 > 0:
        epsilon = r21
        print(f"    Implied ε ≈ {epsilon:.4f}")
        print(f"    Predicted m₃/m₁ ~ ε² = {epsilon ** 2:.4f} (actual: {r31:.4f})")

    return {'masses': masses, 'r21': r21, 'r31': r31}


def compare_with_experiment():
    """Print experimental values for comparison.

    Quark masses at M_Z (MS-bar, PDG 2024):
      m_u = 1.27 MeV, m_c = 0.619 GeV, m_t = 171.8 GeV
      m_d = 2.67 MeV, m_s = 53.5 MeV, m_b = 2.85 GeV

    CKM (Wolfenstein, PDG 2024):
      |V_ud| = 0.9742, |V_us| = 0.2243, |V_ub| = 0.00382
      |V_cd| = 0.221,  |V_cs| = 0.975,  |V_cb| = 0.0408
      |V_td| = 0.0080, |V_ts| = 0.0388, |V_tb| = 0.9991

    Jarlskog: J = 3.08 × 10⁻⁵
    """
    print("\n" + "=" * 60)
    print("EXPERIMENTAL VALUES (PDG 2024)")
    print("=" * 60)

    # Up-type masses
    m_u = np.array([171.8, 0.619, 0.00127])  # t, c, u in GeV
    print("\n  Up-type quarks:")
    print(f"    m_t = {m_u[0]:.1f} GeV, m_c = {m_u[1]:.3f} GeV, m_u = {m_u[2]:.5f} GeV")
    print(f"    m_c/m_t = {m_u[1] / m_u[0]:.4f}")
    print(f"    m_u/m_t = {m_u[2] / m_u[0]:.6f}")
    print(f"    Geometric? (m_c/m_t)/√(m_u/m_t) = "
          f"{(m_u[1] / m_u[0]) / np.sqrt(m_u[2] / m_u[0]):.4f}")

    # Down-type masses
    m_d = np.array([2.85, 0.0535, 0.00267])  # b, s, d in GeV
    print("\n  Down-type quarks:")
    print(f"    m_b = {m_d[0]:.2f} GeV, m_s = {m_d[1]:.4f} GeV, m_d = {m_d[2]:.5f} GeV")
    print(f"    m_s/m_b = {m_d[1] / m_d[0]:.4f}")
    print(f"    m_d/m_b = {m_d[2] / m_d[0]:.6f}")

    # CKM
    print("\n  CKM matrix |V|:")
    V_exp = np.array([
        [0.9742, 0.2243, 0.00382],
        [0.221, 0.975, 0.0408],
        [0.0080, 0.0388, 0.9991],
    ])
    for i in range(3):
        print(f"    [{V_exp[i, 0]:.4f}  {V_exp[i, 1]:.4f}  {V_exp[i, 2]:.5f}]")

    print(f"\n  Wolfenstein λ = |V_us| = {V_exp[0, 1]:.4f}")
    print(f"  Jarlskog J = 3.08 × 10⁻⁵")

    return m_u, m_d, V_exp


if __name__ == "__main__":
    compare_with_experiment()
