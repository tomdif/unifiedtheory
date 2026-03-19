#!/usr/bin/env python3
"""
Analyze scaling study results and generate publication-quality tables.

Reads scaling_results_full.json and produces:
  1. Summary table (LaTeX-formatted)
  2. Trend analysis
  3. Statistical tests for geometric hierarchy
"""

import json
import os
import sys
import numpy as np

def load_results(filename='scaling_results_full.json'):
    path = os.path.join(os.path.dirname(os.path.abspath(__file__)), filename)
    if not os.path.exists(path):
        path = os.path.join(os.path.dirname(os.path.abspath(__file__)),
                            'scaling_results.json')
    with open(path) as f:
        return json.load(f)


def ensemble_stats(results, rho, g):
    """Get ensemble statistics for a (ρ, g) pair."""
    sub = [r for r in results
           if r['rho_M'] == rho and abs(r['coupling_g'] - g) < 1e-6]
    if not sub:
        return None

    r21 = np.array([r['ratio_21'] for r in sub])
    r31 = np.array([r['ratio_31'] for r in sub])
    geo = np.array([r['geometric_test'] for r in sub])
    mix = np.array([r['mixing_ratio'] for r in sub])

    return {
        'n': len(sub),
        'r21_mean': np.mean(r21), 'r21_std': np.std(r21),
        'r21_sem': np.std(r21) / np.sqrt(len(r21)),
        'r31_mean': np.mean(r31), 'r31_std': np.std(r31),
        'r31_sem': np.std(r31) / np.sqrt(len(r31)),
        'geo_mean': np.mean(geo), 'geo_std': np.std(geo),
        'mix_mean': np.mean(mix), 'mix_std': np.std(mix),
    }


def latex_table(results, densities, couplings):
    """Generate LaTeX table for the paper."""
    lines = []
    lines.append(r"\begin{table}[h]")
    lines.append(r"\centering")
    lines.append(r"\caption{Mass hierarchy ratios from the 2D $\times$ S$^1$ "
                 r"prototype. Ensemble averages over $N_\mathrm{seeds}$ Poisson "
                 r"sprinklings. The geometric test column checks "
                 r"$(m_2/m_1)^2 / (m_3/m_1)$; values near 1 confirm the "
                 r"$m \sim \varepsilon^n$ pattern.}")
    lines.append(r"\label{tab:scaling}")
    lines.append(r"\begin{tabular}{cccccc}")
    lines.append(r"\toprule")
    lines.append(r"$\rho$ & $g$ & $N_\mathrm{seeds}$ & "
                 r"$m_2/m_1$ & $m_3/m_1$ & Geometric test \\")
    lines.append(r"\midrule")

    for rho in densities:
        for g in couplings:
            s = ensemble_stats(results, rho, g)
            if s is None:
                continue
            lines.append(
                f"  {rho} & {g:.1f} & {s['n']} & "
                f"${s['r21_mean']:.3f} \\pm {s['r21_std']:.3f}$ & "
                f"${s['r31_mean']:.3f} \\pm {s['r31_std']:.3f}$ & "
                f"${s['geo_mean']:.3f} \\pm {s['geo_std']:.3f}$ \\\\"
            )

    lines.append(r"\bottomrule")
    lines.append(r"\end{tabular}")
    lines.append(r"\end{table}")
    return "\n".join(lines)


def trend_analysis(results, densities, couplings):
    """Analyze how hierarchy changes with density for each coupling."""
    print("\n  TREND ANALYSIS")
    print("  " + "=" * 60)

    for g in couplings:
        print(f"\n  Coupling g = {g:.1f}:")
        rho_vals = []
        r21_vals = []
        r31_vals = []

        for rho in densities:
            s = ensemble_stats(results, rho, g)
            if s:
                rho_vals.append(rho)
                r21_vals.append(s['r21_mean'])
                r31_vals.append(s['r31_mean'])
                print(f"    ρ={rho:>4}: m₂/m₁ = {s['r21_mean']:.4f} ± {s['r21_sem']:.4f}, "
                      f"m₃/m₁ = {s['r31_mean']:.4f} ± {s['r31_sem']:.4f}")

        if len(rho_vals) >= 2:
            # Linear fit in log space
            log_rho = np.log(rho_vals)
            slope_21, _ = np.polyfit(log_rho, r21_vals, 1)
            slope_31, _ = np.polyfit(log_rho, r31_vals, 1)
            print(f"    Slope d(m₂/m₁)/d(ln ρ) = {slope_21:.4f}")
            print(f"    Slope d(m₃/m₁)/d(ln ρ) = {slope_31:.4f}")
            if slope_21 < 0:
                print(f"    → Hierarchy DEEPENS with density (good!)")
            else:
                print(f"    → Hierarchy weakens with density")

            # Extrapolate: at what ρ would m₂/m₁ reach 0.1 (rough target)?
            if slope_21 < 0:
                target = 0.1
                current = r21_vals[-1]
                rho_current = rho_vals[-1]
                # m₂/m₁(ρ) ≈ current + slope * ln(ρ/ρ_current)
                # target = current + slope * ln(ρ_target/ρ_current)
                # ln(ρ_target/ρ_current) = (target - current) / slope
                log_ratio = (target - current) / slope_21
                rho_target = rho_current * np.exp(log_ratio)
                print(f"    Extrapolation: m₂/m₁ ≈ {target} at ρ ≈ {rho_target:.0f}")


def geometric_hierarchy_test(results):
    """Statistical test for the geometric hierarchy relation."""
    print("\n  GEOMETRIC HIERARCHY TEST")
    print("  " + "=" * 60)
    print("  Testing: (m₂/m₁)² / (m₃/m₁) = 1 (geometric hierarchy)")

    all_geo = [r['geometric_test'] for r in results
               if r['geometric_test'] > 0 and np.isfinite(r['geometric_test'])]

    if all_geo:
        mean_geo = np.mean(all_geo)
        std_geo = np.std(all_geo)
        sem_geo = std_geo / np.sqrt(len(all_geo))
        t_stat = (mean_geo - 1.0) / sem_geo if sem_geo > 0 else float('inf')

        print(f"  N = {len(all_geo)} measurements")
        print(f"  Mean = {mean_geo:.4f} ± {sem_geo:.4f}")
        print(f"  t-statistic (vs H₀: mean=1): {t_stat:.2f}")
        print(f"  {'CONSISTENT with geometric hierarchy (|t| < 2)' if abs(t_stat) < 2 else 'DEVIATES from geometric hierarchy'}")


def coupling_effect_test(results, densities):
    """Compare g=0 vs g=0.5 to quantify coupling effect."""
    print("\n  COUPLING EFFECT")
    print("  " + "=" * 60)

    for rho in densities:
        s0 = ensemble_stats(results, rho, 0.0)
        s5 = ensemble_stats(results, rho, 0.5)
        if s0 and s5:
            delta_r21 = s5['r21_mean'] - s0['r21_mean']
            delta_r31 = s5['r31_mean'] - s0['r31_mean']
            print(f"  ρ={rho}: Δ(m₂/m₁) = {delta_r21:+.4f}, "
                  f"Δ(m₃/m₁) = {delta_r31:+.4f} "
                  f"({'deepens' if delta_r31 < 0 else 'weakens'})")


def main():
    results = load_results()
    print(f"Loaded {len(results)} results")

    densities = sorted(set(r['rho_M'] for r in results))
    couplings = sorted(set(r['coupling_g'] for r in results))

    print("\n  SUMMARY TABLE")
    print("  " + "=" * 60)
    print(f"  {'ρ':>5} {'g':>5} {'n':>3} "
          f"{'m₂/m₁':>12} {'m₃/m₁':>12} {'geo':>10} {'mix':>10}")
    print("  " + "-" * 58)

    for rho in densities:
        for g in couplings:
            s = ensemble_stats(results, rho, g)
            if s:
                print(f"  {rho:>5} {g:>5.1f} {s['n']:>3} "
                      f"{s['r21_mean']:>6.4f}±{s['r21_std']:.4f} "
                      f"{s['r31_mean']:>6.4f}±{s['r31_std']:.4f} "
                      f"{s['geo_mean']:>5.3f}±{s['geo_std']:.3f} "
                      f"{s['mix_mean']:>5.4f}±{s['mix_std']:.4f}")

    trend_analysis(results, densities, couplings)
    geometric_hierarchy_test(results)
    coupling_effect_test(results, densities)

    # LaTeX table
    latex = latex_table(results, densities, couplings)
    latex_path = os.path.join(os.path.dirname(os.path.abspath(__file__)),
                              '..', 'docs', 'scaling_table.tex')
    with open(latex_path, 'w') as f:
        f.write(latex)
    print(f"\n  LaTeX table saved to {latex_path}")

    # Experimental comparison
    print("\n  EXPERIMENTAL COMPARISON")
    print("  " + "=" * 60)
    print("  Up-type quarks: m_c/m_t = 0.0036, m_u/m_t = 7.4e-6")
    print("  Down-type quarks: m_s/m_b = 0.019, m_d/m_b = 9.4e-4")
    print("  CKM: |V_us| = 0.224, |V_cb| = 0.041, |V_ub| = 0.004")
    print()
    best = ensemble_stats(results, max(densities), 0.5)
    if best:
        print(f"  Best simulation (ρ={max(densities)}, g=0.5):")
        print(f"    m₂/m₁ = {best['r21_mean']:.3f} (need ~0.004 for quarks)")
        print(f"    m₃/m₁ = {best['r31_mean']:.3f} (need ~7e-6 for quarks)")
        print(f"    mixing = {best['mix_mean']:.3f} (need ~0.2 for CKM)")
        gap_21 = np.log10(best['r21_mean'] / 0.004) if best['r21_mean'] > 0 else 0
        print(f"    Gap to experiment: {gap_21:.1f} orders of magnitude")
        print(f"    (Expected to close with 4D base + RG flow)")


if __name__ == "__main__":
    main()
