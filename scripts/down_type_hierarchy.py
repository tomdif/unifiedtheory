"""
down_type_hierarchy.py — Derive down-type and lepton mass hierarchies

The up-type ratio ln(m_c/m_t)/ln(m_u/m_t) = ln(5-√7)/ln(5+√7) = 0.421
comes from the J₄ eigenvalues with b₁²=1/25, b₂²=1/50.

For down-type quarks and charged leptons, the off-diagonal couplings
are modified by the hypercharge ratio |Y_f|²/|Y_ref|²:

  Up-type:   |Y(u_R)|² = (4/3)² = 16/9   → b₁² = 1/25,  b₂² = 1/50
  Down-type: |Y(d_R)|² = (2/3)² = 4/9    → b₁² = 1/100, b₂² = 1/200
  Leptons:   |Y(e_R)|² = 1² = 1           → b₁² = 9/400, b₂² = 9/800

The diagonal entries {1/3, 2/5, 1/5} are universal (from Volterra SVs,
independent of hypercharge).
"""

import numpy as np

def jacobi_eigenvalues(diag, b_sq):
    """Compute eigenvalues of tridiagonal Jacobi matrix."""
    n = len(diag)
    J = np.zeros((n, n))
    for i in range(n):
        J[i, i] = diag[i]
    for i in range(n - 1):
        J[i, i+1] = np.sqrt(b_sq[i])
        J[i+1, i] = np.sqrt(b_sq[i])
    return np.sort(np.linalg.eigvalsh(J))[::-1]

def hierarchy_ratio(eigvals):
    """R = ln(λ₁/λ₂)/ln(λ₁/λ₃) = ln(m_mid/m_heavy)/ln(m_light/m_heavy)."""
    if len(eigvals) < 3 or eigvals[0] <= 0 or eigvals[1] <= 0 or eigvals[2] <= 0:
        return 0
    r1 = eigvals[0] / eigvals[1]  # λ₁/λ₂
    r2 = eigvals[0] / eigvals[2]  # λ₁/λ₃
    if r1 <= 1 or r2 <= 1:
        return 0
    return np.log(r1) / np.log(r2)

def main():
    print("=" * 72)
    print("DOWN-TYPE AND LEPTON MASS HIERARCHY PREDICTIONS")
    print("=" * 72)

    # Universal diagonal from Volterra SV ratios
    diag = [1/3, 2/5, 1/5]

    # Hypercharge-squared ratios (normalized to up-type = 1)
    Y2_up   = (4/3)**2  # = 16/9
    Y2_down = (2/3)**2  # = 4/9
    Y2_lept = 1.0**2    # = 1

    # Reference: up-type couplings
    b1_sq_ref = 1/25
    b2_sq_ref = 1/50

    sectors = {
        "Up-type": Y2_up / Y2_up,      # ratio = 1
        "Down-type": Y2_down / Y2_up,    # ratio = 1/4
        "Charged lepton": Y2_lept / Y2_up,  # ratio = 9/16
    }

    # Measured hierarchy ratios
    measured = {
        "Up-type": {
            "m1": 0.00216,   # m_u (GeV)
            "m2": 1.27,      # m_c
            "m3": 173.0,     # m_t
            "label": ("u", "c", "t"),
        },
        "Down-type": {
            "m1": 0.0047,    # m_d
            "m2": 0.093,     # m_s
            "m3": 4.18,      # m_b
            "label": ("d", "s", "b"),
        },
        "Charged lepton": {
            "m1": 0.000511,  # m_e
            "m2": 0.10566,   # m_μ
            "m3": 1.777,     # m_τ
            "label": ("e", "μ", "τ"),
        },
    }

    print(f"\n{'Sector':<20} {'Y²/Y²_ref':>10} {'b₁²':>10} {'b₂²':>10} "
          f"{'R_pred':>8} {'R_meas':>8} {'error':>8}")
    print("─" * 78)

    for name, ratio in sectors.items():
        b1_sq = b1_sq_ref * ratio
        b2_sq = b2_sq_ref * ratio

        eigvals = jacobi_eigenvalues(diag, [b1_sq, b2_sq])
        R_pred = hierarchy_ratio(eigvals)

        # Measured ratio
        m = measured[name]
        R_meas = np.log(m["m2"]/m["m3"]) / np.log(m["m1"]/m["m3"])

        err = abs(R_pred - R_meas) / R_meas * 100

        print(f"{name:<20} {ratio:>10.4f} {b1_sq:>10.5f} {b2_sq:>10.5f} "
              f"{R_pred:>8.4f} {R_meas:>8.4f} {err:>7.1f}%")

    # Also try: constant off-diagonal (no hypercharge modification)
    print(f"\n{'─' * 72}")
    print("ALTERNATIVE: Universal couplings (no hypercharge modification)")
    print(f"{'─' * 72}")

    eigvals_univ = jacobi_eigenvalues(diag, [b1_sq_ref, b2_sq_ref])
    R_univ = hierarchy_ratio(eigvals_univ)

    print(f"\nUniversal prediction R = {R_univ:.4f}")
    for name in measured:
        m = measured[name]
        R_meas = np.log(m["m2"]/m["m3"]) / np.log(m["m1"]/m["m3"])
        err = abs(R_univ - R_meas) / R_meas * 100
        print(f"  {name:<20}: R_meas = {R_meas:.4f}, error = {err:.1f}%")

    # Scan: what Y² ratio gives the best fit for each sector?
    print(f"\n{'─' * 72}")
    print("BEST-FIT Y² RATIOS")
    print(f"{'─' * 72}")

    for name in measured:
        m = measured[name]
        R_target = np.log(m["m2"]/m["m3"]) / np.log(m["m1"]/m["m3"])

        best_ratio = 1.0
        best_err = abs(R_univ - R_target)

        for r in np.linspace(0.01, 4.0, 4000):
            b1 = b1_sq_ref * r
            b2 = b2_sq_ref * r
            eig = jacobi_eigenvalues(diag, [b1, b2])
            R = hierarchy_ratio(eig)
            if abs(R - R_target) < best_err:
                best_err = abs(R - R_target)
                best_ratio = r

        print(f"  {name:<20}: best Y²/Y²_ref = {best_ratio:.4f} "
              f"(R_pred = {R_target:.4f}, error = {best_err:.5f})")

        # Compare with theoretical Y² ratio
        theory_ratio = sectors[name]
        print(f"    theoretical ratio = {theory_ratio:.4f}, "
              f"discrepancy = {abs(best_ratio - theory_ratio)/theory_ratio*100:.1f}%")

    print(f"\n{'=' * 72}")
    print("EIGENVALUE DETAILS")
    print(f"{'=' * 72}")

    for name, ratio in sectors.items():
        b1_sq = b1_sq_ref * ratio
        b2_sq = b2_sq_ref * ratio
        eigvals = jacobi_eigenvalues(diag, [b1_sq, b2_sq])
        print(f"\n{name} (Y²/Y²_ref = {ratio:.4f}):")
        print(f"  Eigenvalues: {eigvals[0]:.6f}, {eigvals[1]:.6f}, {eigvals[2]:.6f}")
        print(f"  Ratios: λ₁/λ₂ = {eigvals[0]/eigvals[1]:.4f}, λ₁/λ₃ = {eigvals[0]/eigvals[2]:.4f}")
        if eigvals[2] > 0:
            s = np.sqrt(7) if name == "Up-type" else 0
            print(f"  ln(λ₁/λ₂) = {np.log(eigvals[0]/eigvals[1]):.4f}, "
                  f"ln(λ₁/λ₃) = {np.log(eigvals[0]/eigvals[2]):.4f}")

if __name__ == "__main__":
    main()
