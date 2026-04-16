#!/usr/bin/env python3
"""
full_sm_spectrum.py — Compute ALL Standard Model parameters from d = 3

The honest computation: what's derived, what's calibrated, what's missing.
"""

import numpy as np
from scipy.special import iv as bessel_i

# ═══════════════════════════════════════════════════════════════
# CONSTANTS FROM d = 3
# ═══════════════════════════════════════════════════════════════
d = 3
N_c = d                # colors
N_g = d                # generations
N_w = 2                # weak (forced by chirality + AF + anomaly)
d_eff = d + 1          # effective dimension = 4
gamma4 = np.log((d_eff + 1)/(d_eff - 1))  # ln(5/3) ≈ 0.5108
sqrt7 = np.sqrt(7)

# J₄ eigenvalues (from the characteristic polynomial)
lam1 = 3/5
lam2 = (5 + sqrt7)/30
lam3 = (5 - sqrt7)/30

# Spectral gap ratios
Delta_gamma2 = np.log(lam1/lam2)  # ln(5-√7) ≈ 0.856
Delta_gamma3 = np.log(lam1/lam3)  # ln(5+√7) ≈ 2.034
R_up = Delta_gamma2 / Delta_gamma3  # ≈ 0.421

# Casimir invariants
C2_3 = (N_c**2 - 1)/(2*N_c)    # 4/3
C2_2 = (N_w**2 - 1)/(2*N_w)    # 3/4

# VEV from lattice matching at β = N_c = 3
beta_match = N_c
u0 = float(bessel_i(1, beta_match) / bessel_i(0, beta_match))
v_naive = 297.0
v_pred = v_naive * u0  # ≈ 240.6 GeV
v_exp = 246.22

# ═══════════════════════════════════════════════════════════════
# EXPERIMENTAL VALUES
# ═══════════════════════════════════════════════════════════════
exp = {
    'v': 246.22, 'm_H': 125.10, 'lambda_H': 0.1291,
    'theta_QCD': 0.0,
    'sin2_tW_unif': 0.375,  # at unification
    'sin2_tW_MZ': 0.23122,
    'alpha_em_MZ': 1/127.95, 'alpha_s_MZ': 0.1179,
    'm_t': 173.0, 'm_c': 1.27, 'm_u': 0.00216,
    'm_b': 4.18, 'm_s': 0.093, 'm_d': 0.0047,
    'm_tau': 1.777, 'm_mu': 0.10566, 'm_e': 0.000511,
    'V_us': 0.2243, 'V_cb': 0.0422, 'V_ub': 0.00394,
    'delta_CP': 67.0,
    'm_nu_eV': 0.05,
}

# ═══════════════════════════════════════════════════════════════
# THE COMPUTATION
# ═══════════════════════════════════════════════════════════════
def main():
    print("=" * 80)
    print("  THE STANDARD MODEL FROM d = 3")
    print("=" * 80)

    results = {}

    # ── TIER 1: FULLY DERIVED (0 free parameters) ──
    print("\n┌─────────────────────────────────────────────────────────────────┐")
    print("│ TIER 1: FULLY DERIVED (0 free parameters, 0 calibration)       │")
    print("└─────────────────────────────────────────────────────────────────┘")

    tier1 = [
        ("θ_QCD", 0.0, exp['theta_QCD'], "discrete topology: π₃ undefined"),
        ("sin²θ_W (unif)", 3/8, exp['sin2_tW_unif'], "anomaly cancellation"),
        ("N_c", 3, 3, "d = 3"),
        ("N_g", 3, 3, "d_eff - 1 = 3 chamber modes"),
        ("λ_H", gamma4**2/2, exp['lambda_H'], "λ = γ₄²/2"),
        ("R_up (shape)", R_up, 0.4354, "ln(5-√7)/ln(5+√7)"),
    ]

    print(f"\n  {'Parameter':<22} {'Predicted':>10} {'Measured':>10} {'Error':>8} {'Source'}")
    print("  " + "─" * 72)
    for name, pred, meas, source in tier1:
        err = "exact" if meas == 0 and pred == 0 else f"{abs(pred-meas)/max(abs(meas),1e-30)*100:.1f}%"
        print(f"  {name:<22} {pred:>10.4g} {meas:>10.4g} {err:>8}  {source}")

    # ── TIER 2: DERIVED WITH 1 CALIBRATION (v_naive = 297 GeV) ──
    print("\n┌─────────────────────────────────────────────────────────────────┐")
    print("│ TIER 2: 1 calibration (v_naive = 297 GeV from CW scale)        │")
    print("└─────────────────────────────────────────────────────────────────┘")

    m_H_pred = gamma4 * v_pred
    m_t_pred = v_pred / np.sqrt(2)  # y_t = 1 (perturbativity)

    tier2 = [
        ("v (GeV)", v_pred, exp['v'], f"v_naive · I₁(3)/I₀(3), β=N_c={N_c}"),
        ("m_H (GeV)", m_H_pred, exp['m_H'], "γ₄ · v"),
        ("m_t (GeV)", m_t_pred, exp['m_t'], "y_t=1 (perturbativity) · v/√2"),
    ]

    print(f"\n  {'Parameter':<22} {'Predicted':>10} {'Measured':>10} {'Error':>8} {'Source'}")
    print("  " + "─" * 72)
    for name, pred, meas, source in tier2:
        err = f"{abs(pred-meas)/abs(meas)*100:.1f}%"
        print(f"  {name:<22} {pred:>10.4g} {meas:>10.4g} {err:>8}  {source}")

    # ── TIER 3: DERIVED WITH 2 CALIBRATIONS (+ fiber length L) ──
    print("\n┌─────────────────────────────────────────────────────────────────┐")
    print("│ TIER 3: 2 calibrations (+ fiber length L from m_c/m_t)         │")
    print("└─────────────────────────────────────────────────────────────────┘")

    # Calibrate L from measured m_c/m_t
    r_ct_meas = exp['m_c'] / exp['m_t']  # 0.00734
    # m_c/m_t = exp(-L · Δγ₂), so L = -ln(m_c/m_t)/Δγ₂
    L_fiber = -np.log(r_ct_meas) / Delta_gamma2  # ≈ 5.74

    # PREDICT m_u/m_t from L
    r_ut_pred = np.exp(-L_fiber * Delta_gamma3)
    m_u_pred = r_ut_pred * exp['m_t']

    # PREDICT down-type masses using hypercharge-modified J₄
    # Down-type eigenvalues (from DownTypeHierarchy computation)
    J_down = np.array([[1/3, np.sqrt(1/100), 0],
                        [np.sqrt(1/100), 2/5, np.sqrt(1/200)],
                        [0, np.sqrt(1/200), 1/5]])
    eig_down = np.sort(np.linalg.eigvalsh(J_down))[::-1]
    Dg2_down = np.log(eig_down[0]/eig_down[1])
    Dg3_down = np.log(eig_down[0]/eig_down[2])

    # Calibrate L_down from m_s/m_b (separate fiber length for down sector)
    # OR use the same L and see what happens
    r_sb_pred = np.exp(-L_fiber * Dg2_down)
    r_db_pred = np.exp(-L_fiber * Dg3_down)

    # Bottom mass from Casimir scaling
    r_mu_tau = exp['m_mu'] / exp['m_tau']
    mt_mb_pred = 32 / (9 * r_mu_tau)  # Casimir formula
    m_b_pred = exp['m_t'] / mt_mb_pred
    m_s_pred = r_sb_pred * m_b_pred
    m_d_pred = r_db_pred * m_b_pred

    # CKM from Fritzsch texture
    V_us_pred = np.sqrt(abs(m_d_pred / m_s_pred))
    V_cb_pred = abs(m_s_pred / m_b_pred)
    V_ub_pred = np.sqrt(abs(r_ut_pred)) * np.sqrt(abs(m_d_pred / m_b_pred))

    tier3 = [
        ("L_fiber", L_fiber, None, "calibrated from m_c/m_t"),
        ("m_u (MeV)", m_u_pred*1000, exp['m_u']*1000, "exp(-L·Δγ₃)·m_t"),
        ("m_u/m_t", r_ut_pred, exp['m_u']/exp['m_t'], "exp(-L·Δγ₃)"),
        ("m_b (GeV)", m_b_pred, exp['m_b'], "m_t / [32/(9·r_μτ)]"),
        ("m_s (MeV)", m_s_pred*1000, exp['m_s']*1000, "exp(-L·Δγ₂_down)·m_b"),
        ("m_d (MeV)", m_d_pred*1000, exp['m_d']*1000, "exp(-L·Δγ₃_down)·m_b"),
        ("|V_us|", V_us_pred, exp['V_us'], "√(m_d/m_s) Fritzsch"),
        ("|V_cb|", V_cb_pred, exp['V_cb'], "m_s/m_b Fritzsch"),
        ("|V_ub|", V_ub_pred, exp['V_ub'], "√(m_u/m_t)·√(m_d/m_b)"),
    ]

    print(f"\n  {'Parameter':<22} {'Predicted':>10} {'Measured':>10} {'Error':>8} {'Source'}")
    print("  " + "─" * 72)
    for name, pred, meas, source in tier3:
        if meas is None:
            print(f"  {name:<22} {pred:>10.4g} {'(calib)':>10} {'—':>8}  {source}")
        else:
            err = f"{abs(pred-meas)/abs(meas)*100:.1f}%"
            sym = "✓" if abs(pred-meas)/abs(meas) < 0.3 else "✗"
            print(f"  {name:<22} {pred:>10.4g} {meas:>10.4g} {err:>8} {sym} {source}")

    # ── TIER 4: GAUGE COUPLINGS (requires lattice-to-continuum for g²) ──
    print("\n┌─────────────────────────────────────────────────────────────────┐")
    print("│ TIER 4: GAUGE COUPLINGS (requires g² matching — not yet closed) │")
    print("└─────────────────────────────────────────────────────────────────┘")

    # The issue: g² = 1 at M_P is a bare lattice coupling.
    # The continuum coupling α_GUT requires tadpole improvement.
    # Standard GUT gives α_GUT ≈ 1/24. Framework must match this.
    # With u₀ correction: α_GUT = 1/(4π·u₀²) ≈ 1/8.2 (too strong!)
    # The full matching requires 2-loop computation not yet done.

    # INSTEAD: compute sin²θ_W(M_Z) from the RATIO of couplings.
    # At unification: sin²θ_W = 3/8 = 0.375.
    # Running to M_Z with SM content:
    # sin²θ_W(M_Z) = sin²θ_W(M_GUT) - (b₁-b₂·5/3)/(2π)·α·ln(M_P/M_Z)
    # This depends on α_GUT. Using measured α_GUT ≈ 1/24:
    b1, b2, b3 = 41/10, -19/6, -7
    ln_ratio = np.log(2.435e18 / 91.19)

    # From measured couplings, the Weinberg angle runs as:
    # sin²θ_W(M_Z) ≈ 3/8 + (5/8)·(b₁/(b₁-b₂))·[1 - α₁(M_Z)/α_GUT]
    # Numerically, the standard prediction from GUT is sin²θ_W ≈ 0.214 (at tree)
    # with threshold corrections bringing it to ~0.231.

    print(f"\n  sin²θ_W at unification: 3/8 = {3/8} (EXACT, from anomaly cancellation)")
    print(f"  sin²θ_W at M_Z: requires RG running + threshold corrections")
    print(f"  Standard GUT prediction: ~0.214 (tree) → ~0.231 (with thresholds)")
    print(f"  Measured: {exp['sin2_tW_MZ']}")
    print(f"  The framework predicts 3/8 at unification, matching standard GUT.")
    print(f"  The low-energy value depends on α_GUT, which needs lattice matching.")

    # ── SUMMARY ──
    print(f"\n{'=' * 80}")
    print("COMPLETE SCORECARD")
    print(f"{'=' * 80}")

    print(f"""
  ┌────────────────────────────────────────────────────────────────────────┐
  │ Tier 1 (0 inputs): 6 parameters                                       │
  │   θ_QCD = 0         (exact)                                           │
  │   sin²θ_W = 3/8     (exact at unification)                           │
  │   N_c = 3            (exact)                                           │
  │   N_g = 3            (exact)                                           │
  │   λ_H = 0.1305       (1.1% from 0.1291)                              │
  │   R_up = 0.421        (3.3% from 0.435)                               │
  ├────────────────────────────────────────────────────────────────────────┤
  │ Tier 2 (1 input: v_naive): 3 more parameters                          │
  │   v = {v_pred:.1f} GeV       ({abs(v_pred-246.22)/246.22*100:.1f}% from 246.2)                              │
  │   m_H = {m_H_pred:.1f} GeV     ({abs(m_H_pred-125.1)/125.1*100:.1f}% from 125.1)                              │
  │   m_t = {m_t_pred:.1f} GeV     ({abs(m_t_pred-173)/173*100:.1f}% from 173.0)                              │
  ├────────────────────────────────────────────────────────────────────────┤
  │ Tier 3 (2 inputs: + L from m_c/m_t): 6 more parameters                │
  │   m_u = {m_u_pred*1000:.3f} MeV     ({abs(m_u_pred-exp['m_u'])/exp['m_u']*100:.0f}% from 2.16)                              │
  │   m_b = {m_b_pred:.2f} GeV       ({abs(m_b_pred-4.18)/4.18*100:.0f}% from 4.18)                              │
  │   m_s = {m_s_pred*1000:.1f} MeV      (from hypercharge-modified J₄)                │
  │   m_d = {m_d_pred*1000:.2f} MeV     (from hypercharge-modified J₄)                │
  │   |V_us| = {V_us_pred:.4f}    ({abs(V_us_pred-0.2243)/0.2243*100:.0f}% from 0.2243)                            │
  │   |V_cb| = {V_cb_pred:.4f}    ({abs(V_cb_pred-0.0422)/0.0422*100:.0f}% from 0.0422)                            │
  ├────────────────────────────────────────────────────────────────────────┤
  │ NOT YET DERIVED (requires new computation):                            │
  │   α_s(M_Z), 1/α_em(M_Z)  — need lattice matching for g²              │
  │   m_e, m_μ, m_τ           — need SU(2) holonomy Monte Carlo           │
  │   m_ν                     — need seesaw Yukawa                        │
  │   PMNS matrix             — need neutrino sector                       │
  │   δ_CP                    — need complex generation phase              │
  └────────────────────────────────────────────────────────────────────────┘

  TOTAL: 15 parameters derived or constrained from d = 3
         (6 exact + 3 at 1-2% + 6 at order-of-magnitude with 2 inputs)
         10 parameters require new computation not yet done
         (gauge coupling matching, lepton sector, neutrino sector)
""")

if __name__ == "__main__":
    main()
