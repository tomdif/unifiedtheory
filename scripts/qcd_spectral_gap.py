#!/usr/bin/env python3
"""
qcd_spectral_gap.py — Can the chamber kernel compute hadron masses?

The electroweak spectral gap γ₄ = ln(5/3) gives the Higgs mass.
The QCD analog should give the proton mass.

The QCD chamber kernel acts on the CONFINING vacuum, not the EW vacuum.
Key differences:
  - The gauge group is SU(3) (not SU(2))
  - The relevant scale is Λ_QCD ≈ 0.3 GeV (not v = 246 GeV)
  - The fiber is the SU(3) flux tube (not CP²)

APPROACH: The QCD spectral gap γ_QCD determines m_proton/Λ_QCD
via the same transfer matrix correspondence that gives m_H/v.

The SU(3) Jacobi matrix uses different Volterra SVs because the
color group has a different Casimir structure.
"""

import numpy as np

def main():
    print("=" * 70)
    print("QCD SPECTRAL GAP: CAN WE PREDICT HADRON MASSES?")
    print("=" * 70)

    # ── EW sector (validated) ──
    gamma_ew = np.log(5/3)  # ≈ 0.511
    v = 246.22  # GeV
    m_H = gamma_ew * v  # ≈ 125.7 GeV

    # ── QCD sector (to predict) ──
    Lambda_QCD = 0.332  # GeV (MS-bar, 3 flavors)
    m_proton = 0.938  # GeV (measured)
    m_pion = 0.135  # GeV
    m_rho = 0.775  # GeV

    # The QCD spectral gap:
    # m_proton = γ_QCD · Λ_QCD · f(N_c)
    # where f(N_c) is a color factor.
    gamma_QCD_needed = m_proton / Lambda_QCD  # ≈ 2.83

    print(f"\nElectroweak sector (validated):")
    print(f"  γ_EW = ln(5/3) = {gamma_ew:.4f}")
    print(f"  m_H = γ_EW · v = {gamma_ew:.4f} · {v} = {m_H:.1f} GeV")

    print(f"\nQCD sector (to predict):")
    print(f"  Λ_QCD = {Lambda_QCD} GeV")
    print(f"  m_proton/Λ_QCD = {m_proton/Lambda_QCD:.4f}")
    print(f"  m_pion/Λ_QCD = {m_pion/Lambda_QCD:.4f}")
    print(f"  m_rho/Λ_QCD = {m_rho/Lambda_QCD:.4f}")

    # ── Hypothesis: the QCD gap uses d_eff = N_c + 1 = 4 ──
    # Same formula: γ = ln((d_eff+1)/(d_eff-1))
    # For d_eff = 4: γ = ln(5/3) ≈ 0.511 (same as EW!)
    # Then m_proton = γ · Λ_QCD = 0.511 · 0.332 = 0.170 GeV. TOO SMALL.

    # ── Hypothesis: the QCD gap uses the COLOR Casimir ──
    # γ_QCD = C₂(SU3) · γ₄ = (4/3) · ln(5/3) ≈ 0.681
    # m_proton = γ_QCD · Λ_QCD = 0.681 · 0.332 = 0.226 GeV. Still too small.

    # ── Hypothesis: multiple spectral gaps contribute (N_c = 3 quarks) ──
    # The proton has 3 valence quarks, each contributing a spectral gap.
    # m_proton ≈ N_c · γ₄ · Λ_QCD = 3 · 0.511 · 0.332 = 0.509 GeV. Closer!

    # ── Hypothesis: the proton mass is the EXPONENTIAL of the gap ──
    # m_proton = Λ_QCD · exp(γ₄ · N_c) = 0.332 · exp(0.511 · 3) = 0.332 · 4.63 = 1.54 GeV. Too large!
    # m_proton = Λ_QCD · exp(γ₄ · C₂(SU3)) = 0.332 · exp(0.511 · 4/3) = 0.332 · 1.976 = 0.656 GeV. Getting close!

    # ── Hypothesis: use the Bessel matching at β = N_c ──
    from scipy.special import iv
    u0 = float(iv(1, 3) / iv(0, 3))  # I₁(3)/I₀(3) ≈ 0.810
    # m_proton = Λ_QCD / u0 / γ₄? Or m_proton = Λ_QCD · (1/u0)^{N_c}?

    print(f"\n{'─' * 70}")
    print(f"CANDIDATE FORMULAS")
    print(f"{'─' * 70}")

    candidates = [
        ("γ₄ · Λ_QCD", gamma_ew * Lambda_QCD),
        ("N_c · γ₄ · Λ_QCD", 3 * gamma_ew * Lambda_QCD),
        ("C₂ · γ₄ · Λ_QCD", (4/3) * gamma_ew * Lambda_QCD),
        ("Λ_QCD · exp(γ₄ · C₂)", Lambda_QCD * np.exp(gamma_ew * 4/3)),
        ("Λ_QCD · exp(γ₄ · √N_c)", Lambda_QCD * np.exp(gamma_ew * np.sqrt(3))),
        ("Λ_QCD / (u₀ · γ₄)", Lambda_QCD / (u0 * gamma_ew)),
        ("Λ_QCD · N_c / u₀", Lambda_QCD * 3 / u0),
        ("Λ_QCD · π / u₀", Lambda_QCD * np.pi / u0),
        ("Λ_QCD · (1/u₀)^{C₂}", Lambda_QCD * (1/u0)**(4/3)),
        ("Λ_QCD · exp(π·γ₄)", Lambda_QCD * np.exp(np.pi * gamma_ew)),
        ("Λ_QCD · exp(L·γ₄/N_c)", Lambda_QCD * np.exp(np.pi**2/np.sqrt(3) * gamma_ew / 3)),
        ("4π · Λ_QCD / (3γ₄)", 4*np.pi*Lambda_QCD / (3*gamma_ew)),
    ]

    print(f"\n  {'Formula':<30} {'Predicted':>10} {'m_p':>10} {'Error':>8}")
    print(f"  {'─'*60}")
    for name, val in candidates:
        err = abs(val - m_proton) / m_proton * 100
        mark = "✓" if err < 10 else "○" if err < 30 else ""
        print(f"  {name:<30} {val:>10.4f} {m_proton:>10.4f} {err:>7.1f}% {mark}")

    # The best candidates:
    best = [(name, val, abs(val-m_proton)/m_proton*100) for name, val in candidates]
    best.sort(key=lambda x: x[2])
    print(f"\n  BEST FIT: {best[0][0]} = {best[0][1]:.4f} GeV ({best[0][2]:.1f}%)")

    # Check pion and rho with the same formula
    print(f"\n{'─' * 70}")
    print(f"EXTENDING TO OTHER HADRONS")
    print(f"{'─' * 70}")

    # Pion: pseudo-Goldstone boson, m_π² ∝ m_q · Λ_QCD
    # In the framework: m_π/m_proton = √(m_u · m_d) / Λ_QCD^{something}
    # This is the GMOR relation, which is standard QCD, not new.

    # Rho: vector meson, m_ρ ≈ √(2) · Λ_QCD / γ_ρ
    # The rho mass should come from a DIFFERENT spectral gap (the vector channel).

    # The key question: is there a SINGLE formula that gives all hadron masses
    # from the chamber kernel? Or are different hadrons different channels?

    print(f"\n  The hadron spectrum requires MULTIPLE spectral gaps")
    print(f"  (one per channel: scalar, vector, tensor, ...).")
    print(f"  The chamber kernel gives the GROUND STATE gap (lightest hadron")
    print(f"  in each channel). Different J^PC quantum numbers give different")
    print(f"  Jacobi matrices.")
    print(f"\n  This is analogous to how J₄ gives the Higgs (scalar channel)")
    print(f"  and the mass hierarchy (fermion channels). In QCD, the channels")
    print(f"  would be: pseudoscalar (pion), vector (rho), baryon (proton).")

if __name__ == "__main__":
    main()
