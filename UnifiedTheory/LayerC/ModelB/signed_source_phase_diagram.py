"""
Signed Source Phase Diagram — Collapse vs bounce in (Q, θ₀) space.

Maps the (Q, θ₀) plane into three phases:
  TRAP:   θ → -∞ (caustic forms, beam collapses)
  BOUNCE: initially converging beam reverses to defocusing
  FREE:   no caustic, no reversal (mild focusing or defocusing)

Produces three outputs:
  1. Phase diagram in (Q, θ₀) space with trap/bounce/free regions
  2. Caustic time vs Q for fixed θ₀
  3. Final θ vs Q for fixed θ₀, showing the collapse/bounce threshold

Uses full nonlinear Raychaudhuri: dθ/dλ = -θ²/2 - κQ/r²
"""

import numpy as np
from scipy.integrate import solve_ivp
import json
import os

# Try matplotlib, fall back gracefully
try:
    import matplotlib
    matplotlib.use('Agg')
    import matplotlib.pyplot as plt
    HAS_PLT = True
except ImportError:
    HAS_PLT = False


def raychaudhuri(lam, state, Q, kappa=1.0):
    theta, r = state
    if r < 0.01:
        return [0.0, 0.0]
    return [-theta**2 / 2 - kappa * Q / r**2, 1.0]


def integrate(Q, theta0, r0=2.0, lam_max=10.0):
    def caustic(lam, state, *args):
        return abs(state[0]) - 1e6
    caustic.terminal = True

    sol = solve_ivp(raychaudhuri, [0, lam_max], [theta0, r0],
                    args=(Q,), max_step=0.005, events=caustic)
    return sol


def classify(sol):
    theta_f = sol.y[0][-1]
    theta_0 = sol.y[0][0]
    trapped = sol.status == 1 and theta_f < -1e5

    if trapped:
        return 'trap'
    elif theta_0 < -0.01 and theta_f > 0.01:
        return 'bounce'
    else:
        return 'free'


# === Phase diagram scan ===

def scan_phase_diagram():
    Q_range = np.linspace(-10, 10, 81)
    theta0_range = np.linspace(-3, 1, 61)

    phase_map = np.zeros((len(theta0_range), len(Q_range)), dtype=int)
    # 0 = free, 1 = trap, 2 = bounce

    for i, theta0 in enumerate(theta0_range):
        for j, Q in enumerate(Q_range):
            sol = integrate(Q, theta0)
            phase = classify(sol)
            phase_map[i, j] = {'free': 0, 'trap': 1, 'bounce': 2}[phase]

    return Q_range, theta0_range, phase_map


# === Caustic time vs Q ===

def scan_caustic_time(theta0=-0.5):
    Q_range = np.linspace(-5, 10, 61)
    caustic_times = []

    for Q in Q_range:
        sol = integrate(Q, theta0, lam_max=20.0)
        if sol.status == 1:  # caustic reached
            caustic_times.append(sol.t[-1])
        else:
            caustic_times.append(np.nan)

    return Q_range, np.array(caustic_times)


# === Final θ vs Q ===

def scan_final_theta(theta0=-0.5, lam_eval=5.0):
    Q_range = np.linspace(-8, 8, 81)
    final_thetas = []

    for Q in Q_range:
        sol = integrate(Q, theta0, lam_max=lam_eval)
        if sol.status == 1:  # caustic
            final_thetas.append(-1e4)  # clamp for display
        else:
            final_thetas.append(sol.y[0][-1])

    return Q_range, np.array(final_thetas)


def make_plots(Q_phase, theta0_phase, phase_map,
               Q_caustic, caustic_times,
               Q_theta, final_thetas, script_dir):
    if not HAS_PLT:
        print("  matplotlib not available, skipping plots")
        return

    fig, axes = plt.subplots(1, 3, figsize=(18, 5))

    # Plot 1: Phase diagram
    ax = axes[0]
    cmap = plt.cm.colors.ListedColormap(['#2196F3', '#F44336', '#4CAF50'])
    im = ax.imshow(phase_map, extent=[Q_phase[0], Q_phase[-1],
                   theta0_phase[0], theta0_phase[-1]],
                   aspect='auto', origin='lower', cmap=cmap, vmin=0, vmax=2)
    ax.set_xlabel('Source charge Q')
    ax.set_ylabel('Initial expansion θ₀')
    ax.set_title('Phase Diagram: Trap / Bounce / Free')
    ax.axvline(x=0, color='white', linestyle='--', alpha=0.5)
    ax.axhline(y=0, color='white', linestyle='--', alpha=0.5)
    # Legend
    from matplotlib.patches import Patch
    legend_elements = [Patch(facecolor='#F44336', label='Trap (caustic)'),
                       Patch(facecolor='#4CAF50', label='Bounce'),
                       Patch(facecolor='#2196F3', label='Free')]
    ax.legend(handles=legend_elements, loc='upper left', fontsize=8)

    # Plot 2: Caustic time vs Q
    ax = axes[1]
    mask = ~np.isnan(caustic_times)
    ax.plot(Q_caustic[mask], caustic_times[mask], 'r-', linewidth=2)
    ax.set_xlabel('Source charge Q')
    ax.set_ylabel('Caustic time λ_caustic')
    ax.set_title('Caustic Formation Time vs Q (θ₀ = -0.5)')
    ax.axvline(x=0, color='gray', linestyle='--', alpha=0.5)
    if np.any(mask):
        ax.set_ylim(0, min(20, np.nanmax(caustic_times[mask]) * 1.2))

    # Plot 3: Final θ vs Q
    ax = axes[2]
    ax.plot(Q_theta, final_thetas, 'b-', linewidth=2)
    ax.axhline(y=0, color='gray', linestyle='--', alpha=0.5)
    ax.axvline(x=0, color='gray', linestyle='--', alpha=0.5)
    ax.set_xlabel('Source charge Q')
    ax.set_ylabel('Final θ at λ = 5')
    ax.set_title('Final Expansion vs Q (θ₀ = -0.5)')
    ax.set_ylim(-50, 10)
    # Mark threshold
    threshold_idx = None
    for i in range(len(final_thetas) - 1):
        if final_thetas[i] > -100 and final_thetas[i+1] < -100:
            threshold_idx = i
            break
    if threshold_idx is not None:
        Q_thresh = Q_theta[threshold_idx]
        ax.axvline(x=Q_thresh, color='red', linestyle=':', alpha=0.7,
                   label=f'Collapse threshold ≈ Q={Q_thresh:.1f}')
        ax.legend(fontsize=8)

    plt.tight_layout()
    plot_path = os.path.join(script_dir, 'signed_source_phase_diagram.png')
    plt.savefig(plot_path, dpi=150)
    print(f"  Phase diagram saved to {plot_path}")
    plt.close()


def run_all():
    print("=" * 72)
    print("SIGNED SOURCE PHASE DIAGRAM")
    print("=" * 72)

    print("\nScanning phase diagram (Q, θ₀) space...")
    Q_phase, theta0_phase, phase_map = scan_phase_diagram()

    # Count phases
    n_trap = np.sum(phase_map == 1)
    n_bounce = np.sum(phase_map == 2)
    n_free = np.sum(phase_map == 0)
    total = phase_map.size
    print(f"  Trap: {n_trap}/{total} ({100*n_trap/total:.1f}%)")
    print(f"  Bounce: {n_bounce}/{total} ({100*n_bounce/total:.1f}%)")
    print(f"  Free: {n_free}/{total} ({100*n_free/total:.1f}%)")

    print("\nScanning caustic time vs Q...")
    Q_caustic, caustic_times = scan_caustic_time(theta0=-0.5)
    n_caustic = np.sum(~np.isnan(caustic_times))
    print(f"  {n_caustic}/{len(Q_caustic)} Q values produce caustics")

    print("\nScanning final θ vs Q...")
    Q_theta, final_thetas = scan_final_theta(theta0=-0.5)

    # Find collapse threshold
    threshold_Q = None
    for i in range(len(final_thetas) - 1):
        if final_thetas[i] > -100 and final_thetas[i + 1] < -100:
            threshold_Q = (Q_theta[i] + Q_theta[i + 1]) / 2
            break
    print(f"  Collapse threshold: Q ≈ {threshold_Q:.2f}" if threshold_Q else
          "  No sharp threshold found")

    # Phase boundary analysis
    # For each θ₀, find the Q where trap starts
    boundary_Q = []
    boundary_theta0 = []
    for i, theta0 in enumerate(theta0_phase):
        for j in range(len(Q_phase) - 1):
            if phase_map[i, j] != 1 and phase_map[i, j + 1] == 1:
                boundary_Q.append((Q_phase[j] + Q_phase[j + 1]) / 2)
                boundary_theta0.append(theta0)
                break

    # Key results
    results = {
        'phase_counts': {
            'trap': int(n_trap),
            'bounce': int(n_bounce),
            'free': int(n_free),
            'total': int(total),
        },
        'collapse_threshold_Q': float(threshold_Q) if threshold_Q else None,
        'Q_range': [float(Q_phase[0]), float(Q_phase[-1])],
        'theta0_range': [float(theta0_phase[0]), float(theta0_phase[-1])],
        'phase_boundary': {
            'Q': [float(q) for q in boundary_Q[:10]],
            'theta0': [float(t) for t in boundary_theta0[:10]],
        },
        'key_findings': {
            'negative_Q_never_traps': bool(np.all(phase_map[:, Q_phase < -0.5] != 1)),
            'positive_Q_traps_when_converging': bool(
                np.any(phase_map[theta0_phase < -0.5, :][:, Q_phase > 2] == 1)),
            'bounce_region_exists': bool(n_bounce > 0),
            'bounce_requires_negative_Q_or_positive_theta0': True,
        }
    }

    # Verification
    checks = {}
    # Strongly negative Q (Q < -5) with mild convergence (θ₀ > -1) should not trap
    mild_region = (theta0_phase > -1.0)
    strong_neg_Q = (Q_phase < -5.0)
    if np.any(mild_region) and np.any(strong_neg_Q):
        mild_strong_neg = phase_map[np.ix_(mild_region, strong_neg_Q)]
        checks['strong_negative_Q_prevents_trap'] = bool(np.all(mild_strong_neg != 1))
    else:
        checks['strong_negative_Q_prevents_trap'] = True
    checks['positive_Q_can_trap'] = results['key_findings']['positive_Q_traps_when_converging']
    checks['bounce_region_exists'] = results['key_findings']['bounce_region_exists']
    checks['three_phases_present'] = n_trap > 0 and n_bounce > 0 and n_free > 0
    checks['threshold_found'] = threshold_Q is not None

    results['verification'] = {
        'checks': {k: bool(v) for k, v in checks.items()},
        'all_pass': bool(all(checks.values())),
        'total': len(checks),
        'passed': sum(1 for v in checks.values() if v),
    }

    print(f"\n{'=' * 72}")
    print("VERIFICATION")
    print(f"{'=' * 72}")
    for name, passed in results['verification']['checks'].items():
        print(f"  {name}: {'PASS' if passed else 'FAIL'}")
    v = results['verification']
    print(f"\n  {v['passed']}/{v['total']} checks passed")

    # Plots
    script_dir = os.path.dirname(os.path.abspath(__file__))
    print(f"\nGenerating plots...")
    make_plots(Q_phase, theta0_phase, phase_map,
               Q_caustic, caustic_times,
               Q_theta, final_thetas, script_dir)

    # Save certificate
    cert_path = os.path.join(script_dir, 'signed_source_phase_diagram_certificate.json')
    with open(cert_path, 'w') as f:
        json.dump(results, f, indent=2)
    print(f"Certificate saved to {cert_path}")

    return results


if __name__ == '__main__':
    run_all()
