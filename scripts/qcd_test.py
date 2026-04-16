#!/usr/bin/env python3
"""
qcd_test.py — The honest test: does the Jacobi matrix give hadron mass ratios?

The sharpest test: m_π/m_ρ ≈ 0.174.

But first, the CORRECT test: ratios between NON-Goldstone hadrons,
since the pion is anomalously light (pseudo-Goldstone of chiral symmetry).

Pure QCD mass ratios (no chiral symmetry involved):
  m_ρ / m_proton   = 775 / 938   = 0.826
  m_Δ / m_proton   = 1232 / 938  = 1.313
  m_Ω / m_proton   = 1672 / 938  = 1.783
  m_N* / m_proton  = 1440 / 938  = 1.535
  m_ρ / m_Δ        = 775 / 1232  = 0.629

The pion ratio:
  m_π / m_ρ        = 135 / 775   = 0.174

APPROACH:
  1. Define J_QCD with coupling strength α (free parameter)
  2. Scan α to find which value gives the best hadron mass ratios
  3. If NO α works, the framework doesn't extend to QCD
  4. If a SPECIFIC α works for multiple ratios simultaneously, that's evidence
"""

import numpy as np

def jacobi_eigenvalues(diag, b_sq):
    n = len(diag)
    J = np.zeros((n, n))
    for i in range(n):
        J[i, i] = diag[i]
    for i in range(n - 1):
        J[i, i+1] = np.sqrt(b_sq[i])
        J[i+1, i] = np.sqrt(b_sq[i])
    return np.sort(np.linalg.eigvalsh(J))[::-1]

# EW reference values
b1_ew = 1/25
b2_ew = 1/50
diag = [1/3, 2/5, 1/5]

# Measured hadron masses (MeV)
hadrons = {
    'π':    135,    # pseudoscalar (Goldstone!)
    'ρ':    775,    # vector
    'ω':    783,    # vector (isospin singlet)
    'p':    938,    # baryon
    'Δ':    1232,   # baryon (spin 3/2)
    'Σ':    1193,   # strange baryon
    'Ξ':    1318,   # double-strange baryon
    'Ω':    1672,   # triple-strange baryon
    'N*':   1440,   # excited nucleon
    'f₀':   500,    # scalar (broad)
}

print("=" * 75)
print("THE QCD TEST: DOES THE JACOBI MATRIX GIVE HADRON MASS RATIOS?")
print("=" * 75)

# ═══════════════════════════════════════════════════════════════
# TEST 1: 3×3 Jacobi with scaled couplings
# ═══════════════════════════════════════════════════════════════
print("\n" + "─" * 75)
print("TEST 1: 3×3 Jacobi matrix, scan coupling strength α")
print("Diagonal: {1/3, 2/5, 1/5} (universal)")
print("Off-diagonal: b₁² = α/25, b₂² = α/50")
print("─" * 75)

# The EW sector uses α = 1 and eigenvalue ratios give
# the Higgs/top/charm hierarchy. The QCD sector might use
# α = C₂(SU3)/C₂(SU2) = 16/9 ≈ 1.78.

print(f"\n{'α':>6} {'λ₁':>8} {'λ₂':>8} {'λ₃':>8} {'λ₁/λ₂':>8} {'λ₂/λ₃':>8} {'λ₁/λ₃':>8}")
print("─" * 55)

results = []
for alpha_100 in range(0, 1000, 5):
    alpha = alpha_100 / 100
    if alpha == 0:
        continue
    b1 = alpha * b1_ew
    b2 = alpha * b2_ew
    eig = jacobi_eigenvalues(diag, [b1, b2])
    if eig[-1] <= 0:
        continue
    r12 = eig[0] / eig[1]
    r23 = eig[1] / eig[2]
    r13 = eig[0] / eig[2]
    results.append((alpha, eig, r12, r23, r13))

# Print selected values
for alpha, eig, r12, r23, r13 in results[::20]:
    print(f"{alpha:>6.2f} {eig[0]:>8.4f} {eig[1]:>8.4f} {eig[2]:>8.4f} {r12:>8.4f} {r23:>8.4f} {r13:>8.4f}")

# ═══════════════════════════════════════════════════════════════
# TEST 2: Find α that matches specific hadron ratios
# ═══════════════════════════════════════════════════════════════
print("\n" + "─" * 75)
print("TEST 2: Which α gives observed hadron mass ratios?")
print("─" * 75)

targets = {
    'λ₁/λ₂ = m_Δ/m_p = 1.313': 1.313,
    'λ₁/λ₂ = m_p/m_ρ = 1.210': 938/775,
    'λ₁/λ₃ = m_Ω/m_ρ = 2.157': 1672/775,
    'λ₂/λ₃ = m_ρ/m_π = 5.741': 775/135,  # Goldstone!
}

for name, target in targets.items():
    best_alpha = None
    best_err = 1e10
    for alpha, eig, r12, r23, r13 in results:
        for ratio_name, ratio_val in [('λ₁/λ₂', r12), ('λ₂/λ₃', r23), ('λ₁/λ₃', r13)]:
            if ratio_name in name:
                err = abs(ratio_val - target) / target
                if err < best_err:
                    best_err = err
                    best_alpha = alpha
                    best_ratio = ratio_val

    if best_alpha is not None:
        print(f"\n  {name}")
        print(f"  Best α = {best_alpha:.2f}, ratio = {best_ratio:.4f} ({best_err*100:.1f}% error)")

# ═══════════════════════════════════════════════════════════════
# TEST 3: The REAL test — does ONE α fit MULTIPLE ratios?
# ═══════════════════════════════════════════════════════════════
print("\n" + "─" * 75)
print("TEST 3: Can ONE α fit multiple hadron ratios simultaneously?")
print("─" * 75)

# If the framework works for QCD, there should be a SINGLE α where:
# λ₁/λ₂ matches one ratio AND λ₂/λ₃ matches another.
# If no such α exists, the 3×3 Jacobi doesn't capture QCD.

# Non-Goldstone ratios to fit simultaneously:
# The three eigenvalues should map to three hadron masses.
# Hypothesis A: λ₁ → Δ(1232), λ₂ → p(938), λ₃ → ρ(775)
# Then λ₁/λ₂ = 1.313 and λ₂/λ₃ = 1.210

# Hypothesis B: λ₁ → Ω(1672), λ₂ → Δ(1232), λ₃ → p(938)
# Then λ₁/λ₂ = 1.357 and λ₂/λ₃ = 1.313

# Hypothesis C: λ₁ → p(938), λ₂ → ρ(775), λ₃ → π(135)
# Then λ₁/λ₂ = 1.210 and λ₂/λ₃ = 5.741

hypotheses = {
    'A: Δ, p, ρ': (1232/938, 938/775),
    'B: Ω, Δ, p': (1672/1232, 1232/938),
    'C: p, ρ, π': (938/775, 775/135),
    'D: N*, Δ, p': (1440/1232, 1232/938),
    'E: Δ, Σ, p': (1232/1193, 1193/938),
}

for hyp_name, (target12, target23) in hypotheses.items():
    best_alpha = None
    best_err = 1e10
    for alpha, eig, r12, r23, r13 in results:
        err = np.sqrt(((r12 - target12)/target12)**2 + ((r23 - target23)/target23)**2)
        if err < best_err:
            best_err = err
            best_alpha = alpha
            best_r12 = r12
            best_r23 = r23

    print(f"\n  Hypothesis {hyp_name}:")
    print(f"    Target: λ₁/λ₂ = {target12:.4f}, λ₂/λ₃ = {target23:.4f}")
    print(f"    Best α = {best_alpha:.2f}: λ₁/λ₂ = {best_r12:.4f}, λ₂/λ₃ = {best_r23:.4f}")
    print(f"    Combined error: {best_err*100:.1f}%")

    # Check: is the α physically motivated?
    alpha_Casimir = (4/3) / (3/4)  # C₂(SU3)/C₂(SU2) = 16/9
    print(f"    (Casimir ratio α = {alpha_Casimir:.3f}: {'MATCH' if abs(best_alpha - alpha_Casimir)/alpha_Casimir < 0.3 else 'no match'})")

# ═══════════════════════════════════════════════════════════════
# TEST 4: Larger matrices (4×4, 5×5) for more hadrons
# ═══════════════════════════════════════════════════════════════
print("\n" + "─" * 75)
print("TEST 4: Can larger Jacobi matrices (d > 4) capture more hadrons?")
print("─" * 75)

for d in [5, 6, 7]:
    n = d - 1
    # Build J_d with α-scaled couplings
    # Diagonal: {1/3, 2/5, ..., 2/5, 1/5}
    diag_d = [1/3] + [2/5]*(n-2) + [1/5]
    lam_star = (d-1)/(d+1)
    C_int = 3/(10*(d-2))
    D1 = lam_star - 1/3
    b1_sq_d = C_int * D1
    x_int = lam_star - 2/5 - C_int if d >= 4 else 0
    C_last = lam_star - 1/5
    b_sq_d = [b1_sq_d]
    for k in range(1, n-2):
        b_sq_d.append(C_int * x_int)
    if n >= 2:
        b_sq_d.append(C_last * x_int if d >= 4 else b1_sq_d)

    eig = jacobi_eigenvalues(diag_d, b_sq_d)
    ratios = [eig[i]/eig[i+1] for i in range(len(eig)-1) if eig[i+1] > 0]

    print(f"\n  d = {d}: {n}×{n} matrix, λ* = {lam_star:.4f}")
    print(f"    Eigenvalues: {[f'{e:.4f}' for e in eig]}")
    print(f"    Consecutive ratios: {[f'{r:.4f}' for r in ratios]}")

    # Compare with hadron mass ratios
    # Sorted hadron masses: π(135), ρ(775), p(938), Δ(1232), N*(1440), Ω(1672)
    mass_seq = sorted([135, 500, 775, 938, 1232, 1440, 1672])[:n]
    mass_ratios = [mass_seq[i+1]/mass_seq[i] for i in range(len(mass_seq)-1)]
    print(f"    Hadron masses: {mass_seq}")
    print(f"    Hadron ratios: {[f'{r:.4f}' for r in mass_ratios]}")

# ═══════════════════════════════════════════════════════════════
# VERDICT
# ═══════════════════════════════════════════════════════════════
print("\n" + "═" * 75)
print("VERDICT")
print("═" * 75)
print("""
The 3×3 Jacobi matrix with universal diagonal {1/3, 2/5, 1/5}
gives eigenvalue RATIOS that are bounded: λ₁/λ₂ ranges from 1 (α→∞)
to ∞ (α→0), and λ₂/λ₃ similarly. So for ANY pair of target ratios,
there EXISTS some α that approximately matches.

This means the test is NOT whether you CAN fit hadron ratios (you
always can with a free parameter α). The test is:

  1. Does the SAME α that fits one pair also fit others?
  2. Is that α the Casimir ratio C₂(SU3)/C₂(SU2) = 16/9?
  3. Does a SINGLE Jacobi matrix give the full hadron spectrum?

If the answer to all three is yes, the framework extends to QCD.
If the answer to any is no, it doesn't — and that's an honest
boundary of the framework.
""")

if __name__ == "__main__":
    main = lambda: None
    # Run all the code above
    exec(open(__file__).read().replace("if __name__", "if False"))
