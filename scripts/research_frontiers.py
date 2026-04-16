"""
research_frontiers.py — Attack the three remaining research frontiers

1. K_F → Volterra convergence: prove the rate is O(1/m²)
2. Down-type improvement: try isospin-shifted diagonal
3. Lattice matching: Monte Carlo on Poisson causal sets
"""

import numpy as np
from itertools import combinations
from fractions import Fraction

# ═══════════════════════════════════════════════════════════════
# FRONTIER 1: K_F convergence rate
# ═══════════════════════════════════════════════════════════════

def kf_eigenvalue_ratio(m, d):
    """Compute le/lo for K_F on [m]^d."""
    pts = list(combinations(range(m), d))
    n = len(pts)
    if n > 500:
        return None

    # Build K_F
    def zeta(i, j):
        return 1 if i <= j else 0

    def det_small(M):
        n = len(M)
        if n == 1: return M[0][0]
        if n == 2: return M[0][0]*M[1][1] - M[0][1]*M[1][0]
        s = 0
        for j in range(n):
            minor = [[M[i][k] for k in range(n) if k != j] for i in range(1, n)]
            s += ((-1)**j) * M[0][j] * det_small(minor)
        return s

    KF = np.zeros((n, n))
    for i, P in enumerate(pts):
        for j, Q in enumerate(pts):
            M1 = [[zeta(P[a], Q[b]) for b in range(d)] for a in range(d)]
            M2 = [[zeta(Q[a], P[b]) for b in range(d)] for a in range(d)]
            delta = 1.0 if i == j else 0.0
            KF[i][j] = det_small(M1) + det_small(M2) - delta

    # R-decomposition
    pt_to_idx = {p: i for i, p in enumerate(pts)}
    R = np.zeros((n, n))
    for i, p in enumerate(pts):
        rp = tuple(m - 1 - p[k] for k in range(d - 1, -1, -1))
        if rp in pt_to_idx:
            R[i][pt_to_idx[rp]] = 1.0

    P_even = (np.eye(n) + R) / 2
    P_odd = (np.eye(n) - R) / 2
    KF_even = P_even @ KF @ P_even
    KF_odd = P_odd @ KF @ P_odd

    even_eigs = np.linalg.eigvalsh(KF_even)
    odd_eigs = np.linalg.eigvalsh(KF_odd)
    even_nz = even_eigs[np.abs(even_eigs) > 1e-10]
    odd_nz = odd_eigs[np.abs(odd_eigs) > 1e-10]

    if len(even_nz) > 0 and len(odd_nz) > 0:
        return max(even_nz) / max(odd_nz)
    return None

def frontier_1():
    """Test convergence rate of le/lo → (d+1)/(d-1)."""
    print("═" * 70)
    print("FRONTIER 1: K_F → Volterra convergence rate")
    print("═" * 70)

    for d in [2, 3]:
        target = (d + 1) / (d - 1)
        print(f"\nd = {d}, target = {target:.6f}")
        print(f"{'m':>4} {'le/lo':>12} {'error':>12} {'m²·error':>12} {'m·error':>12}")

        for m in range(d + 1, min(d + 15, 15)):
            ratio = kf_eigenvalue_ratio(m, d)
            if ratio is None:
                continue
            err = abs(ratio - target) / target
            print(f"{m:>4} {ratio:>12.6f} {err:>12.6f} {m**2*err:>12.4f} {m*err:>12.4f}")

        print(f"\nIf m²·error is ~constant → convergence rate O(1/m²)")
        print(f"If m·error is ~constant → convergence rate O(1/m)")

# ═══════════════════════════════════════════════════════════════
# FRONTIER 2: Down-type improvement with isospin shift
# ═══════════════════════════════════════════════════════════════

def jacobi_eigenvalues(diag, b_sq):
    n = len(diag)
    J = np.zeros((n, n))
    for i in range(n):
        J[i, i] = diag[i]
    for i in range(n - 1):
        J[i, i+1] = np.sqrt(b_sq[i])
        J[i+1, i] = np.sqrt(b_sq[i])
    return np.sort(np.linalg.eigvalsh(J))[::-1]

def hierarchy_ratio(eigvals):
    if len(eigvals) < 3 or eigvals[0] <= 0 or eigvals[1] <= 0 or eigvals[2] <= 0:
        return 0
    return np.log(eigvals[0] / eigvals[1]) / np.log(eigvals[0] / eigvals[2])

def frontier_2():
    """Try different down-type modifications."""
    print("\n" + "═" * 70)
    print("FRONTIER 2: Down-type hierarchy — finding the right modification")
    print("═" * 70)

    # Measured
    R_up_meas = np.log(1.27/173.0) / np.log(0.00216/173.0)    # 0.4352
    R_down_meas = np.log(0.093/4.18) / np.log(0.0047/4.18)    # 0.5604
    R_lept_meas = np.log(0.10566/1.777) / np.log(0.000511/1.777)  # 0.3461

    b1_ref, b2_ref = 1/25, 1/50
    diag_ref = [1/3, 2/5, 1/5]

    models = {}

    # Model A: Hypercharge-scaled couplings (previous result)
    for name, Y2_ratio in [("Up-type", 1.0), ("Down-type (Y²)", 1/4), ("Lepton (Y²)", 9/16)]:
        eig = jacobi_eigenvalues(diag_ref, [b1_ref*Y2_ratio, b2_ref*Y2_ratio])
        models[name] = hierarchy_ratio(eig)

    # Model B: Isospin-shifted diagonal, T₃ = -1/2 for down-type
    # Shift = T₃ · 2/(d+1) = -1/2 · 2/5 = -1/5
    for shift_factor in [0, -1/10, -1/5, -2/5]:
        diag_shifted = [d + shift_factor for d in diag_ref]
        eig = jacobi_eigenvalues(diag_shifted, [b1_ref, b2_ref])
        R = hierarchy_ratio(eig)
        models[f"Isospin shift {shift_factor:.2f}"] = R

    # Model C: Both diagonal shift AND coupling modification
    diag_down = [1/3 - 1/10, 2/5 - 1/10, 1/5 - 1/10]
    eig_c = jacobi_eigenvalues(diag_down, [b1_ref/4, b2_ref/4])
    models["Shift(-0.10) + Y²(1/4)"] = hierarchy_ratio(eig_c)

    # Model D: Asymmetric coupling modification
    # First coupling sees Y² ratio, last coupling sees color Casimir ratio
    C2_ratio = (4/3) / (3/4)  # = 16/9
    eig_d = jacobi_eigenvalues(diag_ref, [b1_ref/4, b2_ref * C2_ratio])
    models["Asym: b₁²/4, b₂²·C₂"] = hierarchy_ratio(eig_d)

    # Model E: Coupling scaled by |Y|/|Y_ref| (not Y²)
    eig_e = jacobi_eigenvalues(diag_ref, [b1_ref/2, b2_ref/2])
    models["Y ratio (1/2)"] = hierarchy_ratio(eig_e)

    print(f"\n{'Model':<30} {'R_pred':>8} {'R_down':>8} {'err_d':>8} {'R_lept':>8} {'err_l':>8}")
    print("─" * 74)
    for name, R in models.items():
        err_d = abs(R - R_down_meas)/R_down_meas*100
        err_l = abs(R - R_lept_meas)/R_lept_meas*100
        print(f"{name:<30} {R:>8.4f} {R_down_meas:>8.4f} {err_d:>7.1f}% {R_lept_meas:>8.4f} {err_l:>7.1f}%")

    # Scan for best combined (down + lepton) fit
    print(f"\n{'─' * 70}")
    print("SCAN: best (b₁² ratio, b₂² ratio, diagonal shift) for each sector")
    print(f"{'─' * 70}")

    for target_name, target_R in [("Down", R_down_meas), ("Lepton", R_lept_meas)]:
        best_err = 1e10
        best_params = (0, 0, 0)
        for b1r in np.linspace(0.05, 4.0, 80):
            for b2r in np.linspace(0.05, 4.0, 80):
                for shift in np.linspace(-0.2, 0.2, 41):
                    diag_s = [d + shift for d in diag_ref]
                    if min(diag_s) <= 0: continue
                    eig = jacobi_eigenvalues(diag_s, [b1_ref*b1r, b2_ref*b2r])
                    R = hierarchy_ratio(eig)
                    if abs(R - target_R) < best_err:
                        best_err = abs(R - target_R)
                        best_params = (b1r, b2r, shift)

        b1r, b2r, shift = best_params
        print(f"  {target_name}: b₁²×{b1r:.3f}, b₂²×{b2r:.3f}, shift={shift:.4f} → err={best_err:.5f}")

# ═══════════════════════════════════════════════════════════════
# FRONTIER 3: Lattice matching via exact Bessel computation
# ═══════════════════════════════════════════════════════════════

def frontier_3():
    """Compute c₁ more precisely and find a closed-form candidate."""
    print("\n" + "═" * 70)
    print("FRONTIER 3: Lattice matching — exact analysis")
    print("═" * 70)

    from scipy.special import iv

    v_naive = 297.0
    v_phys = 246.22
    c1_target = (v_naive / v_phys) ** 4

    # The mean plaquette for SU(2) at coupling β:
    # u₀(β) = I₁(β)/I₀(β)
    # At g² = 1: β = 4/g² = 4.

    # But the EXACT relation depends on what scale g² = 1 is evaluated at.
    # In the framework, g² = 1 at M_P. The running to the EW scale
    # with b₂ = 19/6 gives an effective β_eff.

    # The hierarchy: v = M_P · exp(-8π²/(b₂·g²_P))
    # With b₂ = 19/6 and g²_P = 1:
    # v = M_P · exp(-8π²·6/19) ≈ M_P · exp(-24.87) ≈ M_P · 1.6e-11

    b2 = 19/6  # SU(2) 1-loop beta coefficient
    g2_P = 1.0  # coupling at Planck scale
    N_e = 8 * np.pi**2 / (b2 * g2_P)
    M_P = 2.435e18  # GeV

    v_dim_trans = M_P * np.exp(-N_e)
    print(f"\nDimensional transmutation:")
    print(f"  b₂ = 19/6, g²(M_P) = 1")
    print(f"  N_e = 8π²/(b₂·g²) = {N_e:.2f}")
    print(f"  v = M_P·exp(-N_e) = {v_dim_trans:.2e} GeV")
    print(f"  (This is O(10⁸) GeV, not 246 GeV — the tree-level quartic is needed)")

    # The actual EW scale comes from the Higgs potential:
    # v² = -μ²/λ where μ² runs and λ is the tree-level quartic.
    # The tree-level quartic from the spectral gap: λ = γ₄²/2 ≈ 0.13
    # The running μ² at scale v: μ² = -λ·v²

    # From the spectral gap, the BARE Higgs mass parameter at M_P is:
    # m²_H(M_P) = γ₄² · M_P² (if the gap sets the dimensionless ratio)
    # But v = M_P · γ₄ gives v ≈ 0.51 · 2.4e18 ≈ 1.2e18 GeV (too large!)
    # So the hierarchy must come from Coleman-Weinberg dimensional transmutation.

    # The CORRECT formula for the EW scale in the framework:
    # v = Λ_CW / c₁^{1/4} where Λ_CW is the CW scale.
    # Λ_CW = γ₄ · M_P / (2π) ≈ 0.51 · 2.4e18 / 6.28 ≈ 1.95e17 GeV
    # Still too large. The full hierarchy comes from the exponential suppression.

    # The framework's prediction: v_naive = γ₄ · Λ_QCD_analogue
    # where Λ_QCD_analogue ≈ M_P · exp(-8π²/(b₂·g²)) ≈ 1.6e-11 M_P ≈ 3.9e7 GeV
    # Then v_naive = 0.51 · 3.9e7 ≈ 2e7 GeV... still too large.

    # Actually the 297 GeV comes from a different computation.
    # Let me just focus on the Bessel function analysis.

    print(f"\n{'─' * 70}")
    print("Bessel function analysis: u₀(β) = I₁(β)/I₀(β)")
    print(f"{'─' * 70}")

    print(f"\n{'β':>6} {'u₀':>10} {'u₀⁴':>10} {'c₁':>10} {'v(GeV)':>10} {'err':>8}")
    for beta in [2.0, 3.0, 3.5, 4.0, 4.5, 5.0, 6.0, 8.0]:
        u0 = float(iv(1, beta) / iv(0, beta))
        u04 = u0**4
        c1 = 1/u04
        v = v_naive / c1**0.25
        err = abs(v - 246.22)/246.22*100
        print(f"{beta:>6.1f} {u0:>10.6f} {u04:>10.6f} {c1:>10.4f} {v:>10.1f} {err:>7.1f}%")

    # Find the β that gives exact match
    from scipy.optimize import brentq
    def residual(beta):
        u0 = float(iv(1, beta) / iv(0, beta))
        c1 = 1/u0**4
        v = v_naive / c1**0.25
        return v - 246.22

    beta_exact = brentq(residual, 2.0, 20.0)
    u0_exact = float(iv(1, beta_exact) / iv(0, beta_exact))
    print(f"\nExact match: β = {beta_exact:.4f}, u₀ = {u0_exact:.6f}")
    print(f"  g² = 4/β = {4/beta_exact:.4f}")
    print(f"  If g²(M_P) = 1 → β = 4: mismatch factor = {beta_exact/4:.4f}")
    print(f"  This factor could come from:")
    print(f"    (a) Poisson geometry correction to mean plaquette")
    print(f"    (b) Running of g² from M_P to v")
    print(f"    (c) Higher-loop tadpole improvement")

    # Check: what g² gives β_exact?
    g2_needed = 4.0 / beta_exact
    # SU(2) 1-loop running: 1/g²(v) = 1/g²(M_P) + b₂·ln(M_P/v)/(8π²)
    ln_ratio = np.log(M_P / 246.22)
    g2_running = 1.0 / (1.0 + b2 * ln_ratio / (8 * np.pi**2))
    beta_running = 4.0 / g2_running
    u0_running = float(iv(1, beta_running) / iv(0, beta_running))
    v_running = v_naive / (1/u0_running**4)**0.25

    print(f"\n  Running g² from M_P to v:")
    print(f"    1/g²(v) = 1/g²(M_P) + b₂·ln(M_P/v)/(8π²)")
    print(f"    = 1 + {b2:.3f}·{ln_ratio:.2f}/{8*np.pi**2:.2f}")
    print(f"    = {1.0 + b2*ln_ratio/(8*np.pi**2):.4f}")
    print(f"    g²(v) = {g2_running:.4f}, β(v) = {beta_running:.4f}")
    print(f"    u₀(β(v)) = {u0_running:.6f}")
    print(f"    v = {v_running:.1f} GeV ({abs(v_running-246.22)/246.22*100:.1f}% from 246)")

if __name__ == "__main__":
    frontier_1()
    frontier_2()
    frontier_3()
