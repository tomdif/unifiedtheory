#!/usr/bin/env python3
"""
Decoherence separation analysis: disentangle mass signal from decoherence noise.

HYPOTHESIS: The measured holonomy correlator decays as
  C(L) ~ exp(-(m_physical + Gamma) * L)
where:
  m_physical = the true mass (density-independent)
  Gamma = decoherence rate = (rho * pi/24)^{1/4} (density-dependent)

If this decomposition holds, then:
  m_measured(rho) = m_physical + c * rho^{1/4}
for some constant c related to the Alexandrov volume.

TEST: Run the lepton mass computation at multiple densities (rho = 1K, 2K, 5K, 10K, 20K).
Plot m_measured vs rho^{1/4}. If the relationship is LINEAR, extract:
  - m_physical = y-intercept (the true mass, independent of density)
  - c = slope (the decoherence contribution per unit rho^{1/4})

This would:
  (a) Separate mass signal from decoherence noise
  (b) Improve all mass predictions by subtracting the rho-dependent part
  (c) Provide evidence that the decoherence-partial-order connection is physical

Usage:
  python decoherence_separation.py --quick    # 3 densities, 3 seeds (~5 min)
  python decoherence_separation.py            # 5 densities, 5 seeds (~20 min)
  python decoherence_separation.py --full     # 7 densities, 10 seeds (~1 hr)
"""

import sys
import numpy as np
import time

# Import the lepton GPU engine
from lepton_gpu import run_lepton_gpu

# Alexandrov constant for d=4
C4 = np.pi / 24

def decoherence_rate(rho):
    """Gamma = (rho * c4)^{1/4} — from DecoherenceFromDensity.lean."""
    return (rho * C4) ** 0.25

def run_density_scan(rhos, n_seeds, n_sample):
    """Run lepton computation at each density, collect mass ratios."""
    results = {}
    for rho in rhos:
        print(f"\n{'='*70}")
        print(f"  rho = {rho}  |  Gamma = {decoherence_rate(rho):.4f}  |  "
              f"rho^(1/4) = {rho**0.25:.4f}")
        print(f"{'='*70}")

        ratios = []
        c_mags = []
        for seed in range(n_seeds):
            r = run_lepton_gpu(rho=rho, n_sample=n_sample, seed=seed * 137)
            ratio = r['r_mu_tau']
            mags = r.get('c_mag', (0, 0))
            ratios.append(ratio)
            c_mags.append(mags)
            print(f"  seed={seed}: r_mu_tau={ratio:.5f}  "
                  f"|c|=({mags[0]:.4f}, {mags[1]:.4f})  "
                  f"L_max={r['L_max']}  t={r['time']:.0f}s", flush=True)

        mean_r = np.mean(ratios)
        std_r = np.std(ratios)
        mean_c0 = np.mean([m[0] for m in c_mags])
        mean_c1 = np.mean([m[1] for m in c_mags])

        results[rho] = {
            'ratios': ratios,
            'mean_ratio': mean_r,
            'std_ratio': std_r,
            'mean_c_mag': (mean_c0, mean_c1),
            'Gamma': decoherence_rate(rho),
            'rho_quarter': rho ** 0.25,
        }
        print(f"  MEAN: r_mu_tau = {mean_r:.5f} +/- {std_r:.5f}  "
              f"|c| = ({mean_c0:.4f}, {mean_c1:.4f})")

    return results


def fit_decoherence_separation(results):
    """Fit m_measured(rho) = m_physical + c * rho^{1/4} across densities."""
    rhos = sorted(results.keys())
    x = np.array([results[rho]['rho_quarter'] for rho in rhos])
    y_ratio = np.array([results[rho]['mean_ratio'] for rho in rhos])
    y_c0 = np.array([results[rho]['mean_c_mag'][0] for rho in rhos])
    y_c1 = np.array([results[rho]['mean_c_mag'][1] for rho in rhos])
    Gamma = np.array([results[rho]['Gamma'] for rho in rhos])

    print(f"\n{'='*70}")
    print("  DECOHERENCE SEPARATION ANALYSIS")
    print(f"{'='*70}")

    # Table of raw data
    print(f"\n  {'rho':>8s}  {'rho^1/4':>8s}  {'Gamma':>8s}  "
          f"{'r_mu_tau':>10s}  {'|c_0|':>8s}  {'|c_1|':>8s}")
    print(f"  {'-'*8}  {'-'*8}  {'-'*8}  {'-'*10}  {'-'*8}  {'-'*8}")
    for rho in rhos:
        r = results[rho]
        print(f"  {rho:>8d}  {r['rho_quarter']:>8.2f}  {r['Gamma']:>8.4f}  "
              f"{r['mean_ratio']:>10.5f}  {r['mean_c_mag'][0]:>8.4f}  "
              f"{r['mean_c_mag'][1]:>8.4f}")

    # Fit 1: r_mu_tau vs rho^{1/4}
    if len(rhos) >= 2:
        coeffs_ratio = np.polyfit(x, y_ratio, 1)
        slope_r, intercept_r = coeffs_ratio
        residuals_r = y_ratio - np.polyval(coeffs_ratio, x)
        r_squared_r = 1 - np.sum(residuals_r**2) / np.sum((y_ratio - y_ratio.mean())**2)

        print(f"\n  FIT 1: r_mu_tau = a + b * rho^(1/4)")
        print(f"    a (rho-independent ratio) = {intercept_r:.6f}")
        print(f"    b (decoherence slope)     = {slope_r:.6f}")
        print(f"    R^2                       = {r_squared_r:.4f}")
        print(f"    Experimental r_mu_tau     = 0.0595")
        print(f"    Extrapolated (rho->0)     = {intercept_r:.6f}")

    # Fit 2: |c_0| vs rho^{1/4} (heavy component)
    if len(rhos) >= 2:
        coeffs_c0 = np.polyfit(x, y_c0, 1)
        slope_c0, intercept_c0 = coeffs_c0
        residuals_c0 = y_c0 - np.polyval(coeffs_c0, x)
        r_sq_c0 = 1 - np.sum(residuals_c0**2) / np.sum((y_c0 - y_c0.mean())**2) if np.var(y_c0) > 0 else 0

        print(f"\n  FIT 2: |c_heavy| = a + b * rho^(1/4)")
        print(f"    a (rho-independent)  = {intercept_c0:.6f}")
        print(f"    b (decoherence)      = {slope_c0:.6f}")
        print(f"    R^2                  = {r_sq_c0:.4f}")

    # Fit 3: |c_1| vs rho^{1/4} (light component)
    if len(rhos) >= 2:
        coeffs_c1 = np.polyfit(x, y_c1, 1)
        slope_c1, intercept_c1 = coeffs_c1
        residuals_c1 = y_c1 - np.polyval(coeffs_c1, x)
        r_sq_c1 = 1 - np.sum(residuals_c1**2) / np.sum((y_c1 - y_c1.mean())**2) if np.var(y_c1) > 0 else 0

        print(f"\n  FIT 3: |c_light| = a + b * rho^(1/4)")
        print(f"    a (rho-independent)  = {intercept_c1:.6f}")
        print(f"    b (decoherence)      = {slope_c1:.6f}")
        print(f"    R^2                  = {r_sq_c1:.4f}")

    # Fit 4: r_mu_tau vs Gamma directly
    if len(rhos) >= 2:
        coeffs_gamma = np.polyfit(Gamma, y_ratio, 1)
        slope_g, intercept_g = coeffs_gamma
        residuals_g = y_ratio - np.polyval(coeffs_gamma, Gamma)
        r_sq_g = 1 - np.sum(residuals_g**2) / np.sum((y_ratio - y_ratio.mean())**2)

        print(f"\n  FIT 4: r_mu_tau = a + b * Gamma")
        print(f"    a (Gamma-independent)  = {intercept_g:.6f}")
        print(f"    b (Gamma slope)        = {slope_g:.6f}")
        print(f"    R^2                    = {r_sq_g:.4f}")

    # Summary
    print(f"\n  INTERPRETATION:")
    if len(rhos) >= 2 and abs(slope_r) > 1e-8:
        if r_squared_r > 0.8:
            print(f"    LINEAR FIT IS GOOD (R^2={r_squared_r:.3f}).")
            print(f"    The mass ratio HAS a rho-dependent component.")
            print(f"    Subtracting decoherence: r_physical = {intercept_r:.6f}")
            if abs(intercept_r - 0.0595) < abs(y_ratio.mean() - 0.0595):
                print(f"    >> IMPROVEMENT: extrapolated value closer to experiment")
            else:
                print(f"    >> No improvement from extrapolation")
        elif r_squared_r > 0.5:
            print(f"    MODERATE linear trend (R^2={r_squared_r:.3f}).")
            print(f"    Some rho-dependence but not purely linear.")
        else:
            print(f"    WEAK/NO linear trend (R^2={r_squared_r:.3f}).")
            print(f"    The mass ratio does NOT decompose as m + c*rho^(1/4).")
            print(f"    The decoherence-separation hypothesis is NOT supported.")
    else:
        print(f"    Insufficient data or zero slope.")


if __name__ == "__main__":
    if "--quick" in sys.argv:
        rhos = [2000, 5000, 10000]
        n_seeds = 3
        n_sample = 200
    elif "--full" in sys.argv:
        rhos = [1000, 2000, 3000, 5000, 7000, 10000, 20000]
        n_seeds = 10
        n_sample = 300
    else:
        rhos = [1000, 2000, 5000, 10000, 20000]
        n_seeds = 5
        n_sample = 200

    t0 = time.time()
    print("=" * 70)
    print("  DECOHERENCE SEPARATION: m_measured = m_physical + c * rho^{1/4}")
    print(f"  Densities: {rhos}")
    print(f"  Seeds: {n_seeds}, Samples/length: {n_sample}")
    print("=" * 70)

    results = run_density_scan(rhos, n_seeds, n_sample)
    fit_decoherence_separation(results)

    print(f"\n  Total time: {time.time() - t0:.0f}s")
