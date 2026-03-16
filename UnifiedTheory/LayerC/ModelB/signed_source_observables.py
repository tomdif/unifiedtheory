"""
Signed Source Observables — Full weak-field benchmark for signed charges.

For Q > 0, Q = 0, Q < 0, computes three weak-field observables:

  1. Focusing (Raychaudhuri): dθ/dλ = -θ²/2 - κQ/r²
  2. Deflection: Δφ = 4Q/b (gravitational lensing angle)
  3. Shapiro delay: Δt = 4Q·ln(r_ref/b) (excess travel time)

All three should flip sign coherently when Q flips sign:
  Q > 0: focusing, inward bending, time delay
  Q = 0: neutral on all three
  Q < 0: defocusing, outward bending, time advance

No hardcoded answers. Each observable is computed from its defining
formula with Q as a signed parameter.
"""

import numpy as np
from scipy.integrate import solve_ivp
import json
import os


# === Observable 1: Focusing (Raychaudhuri) ===

def raychaudhuri(lam, state, Q, kappa=1.0):
    """dθ/dλ = -θ²/2 - κQ/r²"""
    theta, r = state
    if r < 0.01:
        return [0.0, 0.0]
    dtheta = -theta**2 / 2 - kappa * Q / r**2
    return [dtheta, 1.0]


def compute_focusing(Q, r0=1.0, lam_max=3.0):
    """Integrate Raychaudhuri and return final Δθ."""
    sol = solve_ivp(raychaudhuri, [0, lam_max], [0.0, r0],
                    args=(Q,), max_step=0.01)
    delta_theta = sol.y[0][-1] - sol.y[0][0]
    return delta_theta


# === Observable 2: Deflection ===

def compute_deflection(Q, b):
    """Weak-field gravitational deflection angle.

    Δφ = 4Q/b (linearized GR formula).
    Q > 0: positive = inward bending (attractive lensing)
    Q < 0: negative = outward bending (repulsive lensing)
    Q = 0: zero deflection
    """
    if b <= 0:
        return 0.0
    return 4.0 * Q / b


# === Observable 3: Shapiro delay ===

def compute_shapiro(Q, b, r_ref=10.0):
    """Weak-field Shapiro time delay/advance.

    Δt = 4Q · ln(r_ref / b)
    Q > 0: positive = time delay (signal arrives late)
    Q < 0: negative = time advance (signal arrives early)
    Q = 0: zero delay
    """
    if b <= 0 or r_ref <= 0:
        return 0.0
    return 4.0 * Q * np.log(r_ref / b)


# === Run the benchmark ===

def run_benchmark():
    """Compute all three observables for Q > 0, Q = 0, Q < 0."""

    Q_values = [
        ('positive', 2.0),
        ('neutral', 0.0),
        ('negative', -2.0),
    ]
    b = 5.0       # impact parameter
    r_ref = 50.0  # reference distance for Shapiro

    results = {}

    for name, Q in Q_values:
        # Compute all three observables
        focusing = compute_focusing(Q)
        deflection = compute_deflection(Q, b)
        shapiro = compute_shapiro(Q, b, r_ref)

        # Classify signs
        def sign_label(x):
            if abs(x) < 1e-12:
                return 'zero'
            return 'positive' if x > 0 else 'negative'

        results[name] = {
            'Q': Q,
            'focusing': {
                'value': float(focusing),
                'sign': sign_label(focusing),
            },
            'deflection': {
                'value': float(deflection),
                'sign': sign_label(deflection),
                'impact_parameter': b,
            },
            'shapiro': {
                'value': float(shapiro),
                'sign': sign_label(shapiro),
                'impact_parameter': b,
                'reference_distance': r_ref,
            },
        }

    # === Verification ===
    checks = {}

    # Positive source: all three should be sign-consistent
    pos = results['positive']
    checks['positive_focuses'] = pos['focusing']['sign'] == 'negative'  # θ decreases
    checks['positive_deflects_inward'] = pos['deflection']['sign'] == 'positive'
    checks['positive_delays'] = pos['shapiro']['sign'] == 'positive'

    # Neutral: all three should be zero
    neu = results['neutral']
    checks['neutral_no_focusing'] = neu['focusing']['sign'] == 'zero'
    checks['neutral_no_deflection'] = neu['deflection']['sign'] == 'zero'
    checks['neutral_no_delay'] = neu['shapiro']['sign'] == 'zero'

    # Negative source: all three should flip sign
    neg = results['negative']
    checks['negative_defocuses'] = neg['focusing']['sign'] == 'positive'  # θ increases
    checks['negative_deflects_outward'] = neg['deflection']['sign'] == 'negative'
    checks['negative_advances'] = neg['shapiro']['sign'] == 'negative'

    # Magnitude symmetry: |observable(Q)| ≈ |observable(-Q)|
    checks['deflection_magnitude_symmetric'] = (
        abs(abs(pos['deflection']['value']) - abs(neg['deflection']['value'])) < 1e-10
    )
    checks['shapiro_magnitude_symmetric'] = (
        abs(abs(pos['shapiro']['value']) - abs(neg['shapiro']['value'])) < 1e-10
    )

    all_pass = all(checks.values())
    results['verification'] = {
        'checks': {k: bool(v) for k, v in checks.items()},
        'all_pass': bool(all_pass),
        'total': len(checks),
        'passed': sum(1 for v in checks.values() if v),
    }

    return results


def print_table(results):
    """Print the summary table."""
    print("=" * 72)
    print("SIGNED SOURCE OBSERVABLES — WEAK-FIELD BENCHMARK")
    print("=" * 72)
    print()
    print(f"{'Case':<12} {'Q':>6} {'Focusing':>12} {'Deflection':>12} {'Shapiro':>12}")
    print("-" * 72)

    for name in ['positive', 'neutral', 'negative']:
        r = results[name]
        Q = r['Q']
        foc = r['focusing']['sign']
        defl = r['deflection']['sign']
        shap = r['shapiro']['sign']

        # Physical labels
        foc_label = {'negative': 'converge', 'positive': 'diverge', 'zero': 'none'}[foc]
        defl_label = {'positive': 'inward', 'negative': 'outward', 'zero': 'none'}[defl]
        shap_label = {'positive': 'delay', 'negative': 'advance', 'zero': 'none'}[shap]

        print(f"{name:<12} {Q:>6.1f} {foc_label:>12} {defl_label:>12} {shap_label:>12}")

    print()
    print("Expected pattern:")
    print("  Q > 0:  converge / inward / delay     (attractive gravity)")
    print("  Q = 0:  none / none / none             (neutral)")
    print("  Q < 0:  diverge / outward / advance    (repulsive gravity)")

    print()
    print("-" * 72)
    print("VERIFICATION")
    print("-" * 72)
    v = results['verification']
    for name, passed in v['checks'].items():
        status = "PASS" if passed else "FAIL"
        print(f"  {name}: {status}")
    print(f"\n  {v['passed']}/{v['total']} checks passed")


if __name__ == '__main__':
    results = run_benchmark()
    print_table(results)

    # Save certificate
    script_dir = os.path.dirname(os.path.abspath(__file__))
    cert_path = os.path.join(script_dir, 'signed_source_observables_certificate.json')
    with open(cert_path, 'w') as f:
        json.dump(results, f, indent=2)
    print(f"\nCertificate saved to {cert_path}")
