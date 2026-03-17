"""
Signed Source Strong Field — Trapping, collapse, and bounce behavior.

Extends the weak-field benchmark to the nonlinear regime:

  1. Trapping vs anti-trapping: does θ → -∞ (caustic) or θ → +∞ (dispersal)?
  2. Collapse vs anti-collapse: does r → 0 focusing occur or not?
  3. Mixed-sign critical threshold: Q_pos + Q_neg near zero shows bounce
  4. Nonlinear amplification: the -θ²/2 term amplifies focusing asymmetrically

Uses the full Raychaudhuri equation (not linearized):
  dθ/dλ = -θ²/2 - κQ/r²

The -θ²/2 nonlinear term means:
  - Focusing (θ < 0) self-amplifies: converging beams converge faster
  - Defocusing (θ > 0) self-decelerates: diverging beams slow down
  - This asymmetry means positive Q is "stronger" than negative Q nonlinearly
"""

import numpy as np
from scipy.integrate import solve_ivp
import json
import os


def raychaudhuri_full(lam, state, Q, kappa=1.0):
    """Full nonlinear Raychaudhuri: dθ/dλ = -θ²/2 - κQ/r²"""
    theta, r = state
    if r < 0.01:
        return [0.0, 0.0]
    dtheta = -theta**2 / 2 - kappa * Q / r**2
    return [dtheta, 1.0]


def integrate_full(Q, theta0=0.0, r0=1.0, lam_max=10.0, kappa=1.0):
    """Integrate with event detection for caustics (|θ| → large)."""
    def caustic_event(lam, state, Q, kappa):
        return abs(state[0]) - 1e6  # detect |θ| > 10^6
    caustic_event.terminal = True

    sol = solve_ivp(
        raychaudhuri_full, [0, lam_max], [theta0, r0],
        args=(Q, kappa), max_step=0.01, events=caustic_event
    )
    return sol


def classify_outcome(sol):
    """Classify the integration outcome."""
    theta_final = sol.y[0][-1]
    lam_final = sol.t[-1]
    terminated_early = sol.status == 1  # event triggered

    if terminated_early and theta_final < -1e5:
        return 'trapped', theta_final, lam_final
    elif terminated_early and theta_final > 1e5:
        return 'dispersed', theta_final, lam_final
    elif theta_final < -10:
        return 'strongly_focused', theta_final, lam_final
    elif theta_final > 10:
        return 'strongly_defocused', theta_final, lam_final
    elif abs(theta_final) < 0.1:
        return 'neutral', theta_final, lam_final
    elif theta_final < 0:
        return 'mildly_focused', theta_final, lam_final
    else:
        return 'mildly_defocused', theta_final, lam_final


def run_strong_field():
    results = {}

    # === Test 1: Trapping (large positive Q) ===
    Q_trap = 10.0
    sol_trap = integrate_full(Q_trap, r0=2.0, lam_max=5.0)
    outcome_trap, theta_trap, lam_trap = classify_outcome(sol_trap)
    results['trapping'] = {
        'Q': Q_trap,
        'outcome': outcome_trap,
        'theta_final': float(theta_trap),
        'lambda_at_end': float(lam_trap),
        'terminated_early': sol_trap.status == 1,
        'description': 'Large Q > 0: nonlinear self-amplification causes caustic'
    }

    # === Test 2: Anti-trapping (large negative Q) ===
    Q_anti = -10.0
    sol_anti = integrate_full(Q_anti, r0=2.0, lam_max=5.0)
    outcome_anti, theta_anti, lam_anti = classify_outcome(sol_anti)
    results['anti_trapping'] = {
        'Q': Q_anti,
        'outcome': outcome_anti,
        'theta_final': float(theta_anti),
        'lambda_at_end': float(lam_anti),
        'terminated_early': sol_anti.status == 1,
        'description': 'Large Q < 0: defocusing resists caustic formation'
    }

    # === Test 3: Critical threshold (Q near zero) ===
    # Sweep Q from positive to negative and find where trapping stops
    Q_sweep = np.linspace(5.0, -5.0, 21)
    threshold_results = []
    for Q in Q_sweep:
        sol = integrate_full(Q, r0=2.0, lam_max=5.0)
        outcome, theta, lam = classify_outcome(sol)
        threshold_results.append({
            'Q': float(Q),
            'outcome': outcome,
            'theta_final': float(theta),
            'trapped': outcome == 'trapped'
        })

    # Find critical Q where trapping stops
    trapped_Qs = [r['Q'] for r in threshold_results if r['trapped']]
    untrapped_Qs = [r['Q'] for r in threshold_results if not r['trapped']]
    Q_crit_upper = min(trapped_Qs) if trapped_Qs else None
    Q_crit_lower = max(untrapped_Qs) if untrapped_Qs else None

    results['critical_threshold'] = {
        'sweep': threshold_results,
        'Q_crit_upper_bound': float(Q_crit_upper) if Q_crit_upper is not None else None,
        'Q_crit_lower_bound': float(Q_crit_lower) if Q_crit_lower is not None else None,
        'description': 'Sweep Q: find where caustic formation stops'
    }

    # === Test 4: Bounce behavior (mixed sign, near cancellation) ===
    # Start with mild focusing (θ₀ = -0.5), compare positive vs negative Q
    # Negative Q should resist collapse; positive Q should accelerate it
    Q_bounce = -5.0
    sol_bounce = integrate_full(Q_bounce, theta0=-0.5, r0=3.0, lam_max=10.0)
    outcome_bounce, theta_bounce, lam_bounce = classify_outcome(sol_bounce)

    Q_collapse = 5.0
    sol_collapse = integrate_full(Q_collapse, theta0=-0.5, r0=3.0, lam_max=10.0)
    outcome_collapse, theta_collapse, lam_collapse = classify_outcome(sol_collapse)

    results['bounce_vs_collapse'] = {
        'negative_Q': {
            'Q': Q_bounce,
            'theta0': -0.5,
            'outcome': outcome_bounce,
            'theta_final': float(theta_bounce),
            'description': 'Initially converging + negative source: bounce/resist collapse'
        },
        'positive_Q': {
            'Q': Q_collapse,
            'theta0': -0.5,
            'outcome': outcome_collapse,
            'theta_final': float(theta_collapse),
            'description': 'Initially converging + positive source: accelerate collapse'
        }
    }

    # === Test 5: Nonlinear asymmetry ===
    # |θ(Q)| vs |θ(-Q)| at the same affine parameter
    Q_asym = 3.0
    sol_pos = integrate_full(Q_asym, r0=3.0, lam_max=3.0)
    sol_neg = integrate_full(-Q_asym, r0=3.0, lam_max=3.0)
    theta_pos = sol_pos.y[0][-1]
    theta_neg = sol_neg.y[0][-1]

    results['nonlinear_asymmetry'] = {
        'Q': Q_asym,
        'theta_positive_Q': float(theta_pos),
        'theta_negative_Q': float(theta_neg),
        'ratio': float(abs(theta_pos) / abs(theta_neg)) if abs(theta_neg) > 1e-10 else float('inf'),
        'positive_stronger': abs(theta_pos) > abs(theta_neg),
        'description': 'Nonlinear -θ²/2 amplifies focusing more than defocusing'
    }

    # === Verification ===
    checks = {}

    # Trapping: positive Q causes caustic
    checks['positive_Q_traps'] = results['trapping']['outcome'] == 'trapped'

    # Anti-trapping: negative Q avoids caustic
    checks['negative_Q_avoids_trap'] = results['anti_trapping']['outcome'] != 'trapped'

    # Bounce: negative Q resists collapse of initially converging beam
    checks['negative_Q_resists_collapse'] = (
        results['bounce_vs_collapse']['negative_Q']['outcome'] != 'trapped'
    )

    # Collapse: positive Q accelerates collapse
    checks['positive_Q_accelerates_collapse'] = (
        results['bounce_vs_collapse']['positive_Q']['outcome'] == 'trapped'
    )

    # Nonlinear asymmetry: focusing is stronger than defocusing
    checks['focusing_stronger_than_defocusing'] = (
        results['nonlinear_asymmetry']['positive_stronger']
    )

    # Critical threshold exists: some Q values trap, some don't
    checks['critical_threshold_exists'] = (
        Q_crit_upper is not None and Q_crit_lower is not None
    )

    results['verification'] = {
        'checks': {k: bool(v) for k, v in checks.items()},
        'all_pass': bool(all(checks.values())),
        'total': len(checks),
        'passed': sum(1 for v in checks.values() if v)
    }

    return results


def print_results(results):
    print("=" * 72)
    print("SIGNED SOURCE STRONG FIELD BENCHMARK")
    print("=" * 72)

    # Trapping
    t = results['trapping']
    print(f"\n1. TRAPPING (Q = {t['Q']})")
    print(f"   Outcome: {t['outcome']}")
    print(f"   θ_final: {t['theta_final']:.2e}")
    print(f"   Early termination: {t['terminated_early']}")

    # Anti-trapping
    a = results['anti_trapping']
    print(f"\n2. ANTI-TRAPPING (Q = {a['Q']})")
    print(f"   Outcome: {a['outcome']}")
    print(f"   θ_final: {a['theta_final']:.4f}")
    print(f"   Early termination: {a['terminated_early']}")

    # Critical threshold
    c = results['critical_threshold']
    print(f"\n3. CRITICAL THRESHOLD")
    print(f"   Trapping stops between Q = {c['Q_crit_lower_bound']} and Q = {c['Q_crit_upper_bound']}")

    # Bounce vs collapse
    b = results['bounce_vs_collapse']
    print(f"\n4. BOUNCE vs COLLAPSE (θ₀ = -2.0)")
    print(f"   Q = {b['negative_Q']['Q']}: {b['negative_Q']['outcome']} "
          f"(θ = {b['negative_Q']['theta_final']:.4f})")
    print(f"   Q = {b['positive_Q']['Q']}: {b['positive_Q']['outcome']} "
          f"(θ = {b['positive_Q']['theta_final']:.2e})")

    # Nonlinear asymmetry
    n = results['nonlinear_asymmetry']
    print(f"\n5. NONLINEAR ASYMMETRY (|Q| = {n['Q']})")
    print(f"   θ(+Q) = {n['theta_positive_Q']:.4f}")
    print(f"   θ(-Q) = {n['theta_negative_Q']:.4f}")
    print(f"   |θ(+Q)| / |θ(-Q)| = {n['ratio']:.2f}")
    print(f"   Focusing stronger: {n['positive_stronger']}")

    # Verification
    print(f"\n{'=' * 72}")
    print("VERIFICATION")
    print(f"{'=' * 72}")
    v = results['verification']
    for name, passed in v['checks'].items():
        status = "PASS" if passed else "FAIL"
        print(f"  {name}: {status}")
    print(f"\n  {v['passed']}/{v['total']} checks passed")


if __name__ == '__main__':
    results = run_strong_field()
    print_results(results)

    script_dir = os.path.dirname(os.path.abspath(__file__))
    cert_path = os.path.join(script_dir, 'signed_source_strong_field_certificate.json')
    with open(cert_path, 'w') as f:
        json.dump(results, f, indent=2, default=str)
    print(f"\nCertificate saved to {cert_path}")
