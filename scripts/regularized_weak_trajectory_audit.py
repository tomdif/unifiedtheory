#!/usr/bin/env python3
"""Finite Gaussian transcription checks for the weak-limit estimates.

These calculations check formulas and bounds, not infinite-dimensional
compactness or convergence. Those claims are checked by Lean.
"""
import hashlib
import json
from pathlib import Path

import numpy as np
import scipy
from scipy import integrate, linalg

from regularized_hamiltonian_audit import clock_integral, gaussian_momentum


NEW_MODULES = [
    'KFCausalHilbertWeakSubsequence', 'KFCausalWeakLimitTransport',
    'KFCausalWeakLimitFromTests', 'KFCausalRationalCauchyExtension',
    'KFCausalPairingCauchyTransfer', 'KFCausalRegularizedFormSeparable',
    'KFCausalRegularizedFormWindowBound', 'KFCausalRegularizedCountableLimit',
    'KFCausalRegularizedWeakPairing', 'KFCausalRegularizedWeakTrajectory',
    'KFCausalWeakIntegralLimit', 'KFCausalRegularizedWeakIntegralEquation',
    'KFCausalWeakContinuity',
]


def main():
    cases = []
    window = .3
    times = np.linspace(-window, window, 13)
    step = 1e-5
    for epsilon in [.01, .1, 1.]:
        for dimension in [3, 5]:
            frequencies = np.arange(dimension)*.5-(dimension-1)*.25
            mass = np.array([[clock_integral(epsilon, 1, float(q-p))
                              for q in frequencies] for p in frequencies])
            clock = .5*np.array([[clock_integral(epsilon, 2, float(q-p))
                                 for q in frequencies] for p in frequencies])
            lower = linalg.cholesky(mass, lower=True)
            inv_lower = linalg.solve_triangular(lower, np.eye(dimension), lower=True)
            identity = np.eye(dimension, dtype=complex)
            initial = np.cos(np.arange(dimension)+.2)+1j*np.sin(np.arange(dimension)+.7)
            initial /= linalg.norm(initial)
            test = np.sin(np.arange(dimension)+.4)+1j*np.cos(np.arange(dimension)+.9)
            test /= linalg.norm(test)
            for hbar in [.2, .7]:
                for coupling in [0., .3, 1.]:
                    momentum = coupling*gaussian_momentum(frequencies, hbar)

                    def physical(t):
                        return inv_lower@(clock+np.exp(2*t)*momentum)@inv_lower.conj().T

                    h0 = physical(0.)
                    gram = identity+h0
                    form_initial = float(np.vdot(initial, h0@initial).real)
                    energy_bound = np.exp(2*window)*form_initial
                    radius_squared = linalg.norm(initial)**2+np.exp(2*window)*energy_bound
                    test_form_norm = np.sqrt(np.vdot(test, gram@test).real)
                    pairing_bound = abs(1/hbar)*np.sqrt(radius_squared)*(1+np.exp(2*window))*test_form_norm
                    for cutoff in [.5, 2., 8., 32.]:
                        def operators(t):
                            h = physical(t)
                            r = linalg.solve(h+cutoff*identity, identity, assume_a='pos')
                            y = cutoff*identity-cutoff**2*r
                            return h, r, y

                        def solve(end):
                            result = integrate.solve_ivp(
                                lambda t, psi: (-1j/hbar)*(operators(t)[2]@psi),
                                (0., end), initial, method='DOP853', dense_output=True,
                                rtol=2e-11, atol=2e-12)
                            assert result.success, result.message
                            return result

                        forward, backward = solve(window), solve(-window)

                        def state(t):
                            return (forward if t >= 0 else backward).sol(t)

                        def pairing(t):
                            return np.vdot(state(t), test)

                        def slope(t):
                            h, r, _ = operators(t)
                            chi = cutoff*(r@state(t))
                            return (1j/hbar)*np.vdot(chi, h@test)

                        form_excess = defect_excess = slope_excess = lipschitz_excess = 0.
                        contraction_excess = 0.
                        samples = []
                        for t in times:
                            t = float(t)
                            _, r, _ = operators(t)
                            psi = state(t)
                            chi = cutoff*(r@psi)
                            form_norm_squared = float(np.vdot(chi, gram@chi).real)
                            defect_squared = float(linalg.norm(psi-chi)**2)
                            form_excess = max(form_excess, form_norm_squared-radius_squared)
                            defect_excess = max(defect_excess, defect_squared-energy_bound/cutoff)
                            contraction_excess = max(contraction_excess, linalg.norm(chi)-linalg.norm(initial))
                            slope_excess = max(slope_excess, abs(slope(t))-pairing_bound)
                            samples.append(dict(time=t, form_norm_squared=form_norm_squared,
                                smoothing_defect_squared=defect_squared, weak_slope_norm=float(abs(slope(t)))))
                        for x, y in zip(times[:-1], times[1:]):
                            lipschitz_excess = max(lipschitz_excess,
                                abs(pairing(y)-pairing(x))-pairing_bound*abs(y-x))
                        derivative_error = max(
                            abs((pairing(t+step)-pairing(t-step))/(2*step)-slope(t))/max(1., abs(slope(t)))
                            for t in [-.15, .15])
                        integral = integrate.quad_vec(slope, -window, window, epsabs=2e-10, epsrel=2e-10)[0]
                        difference = pairing(window)-pairing(-window)
                        integral_error = abs(integral-difference)/max(1., abs(difference))
                        assert max(form_excess, defect_excess, contraction_excess, slope_excess,
                                   lipschitz_excess, integral_error) < 1e-8
                        assert derivative_error < 1e-5
                        cases.append(dict(epsilon=epsilon, dimension=dimension, hbar=hbar,
                            coupling=coupling, cutoff=cutoff, window=window,
                            window_energy=float(energy_bound), reference_form_radius_squared=float(radius_squared),
                            pairing_lipschitz_bound=float(pairing_bound), form_norm_bound_excess=float(form_excess),
                            smoothing_bound_excess=float(defect_excess), contraction_excess=float(contraction_excess),
                            slope_bound_excess=float(slope_excess), lipschitz_bound_excess=float(lipschitz_excess),
                            weak_derivative_relative_error=float(derivative_error),
                            weak_integral_relative_error=float(integral_error), samples=samples))
    root = Path(__file__).resolve().parents[1]
    previous = json.loads((root/'data/regularized_yosida_energy_audit.json').read_text())
    sources = list(previous['source_sha256'])+['scripts/regularized_weak_trajectory_audit.py']
    sources += ['UnifiedTheory/Audit/'+name+'.lean' for name in NEW_MODULES]
    hashes = {p: hashlib.sha256((root/p).read_bytes()).hexdigest() for p in sources}
    assert all(hashes[p] == value for p, value in previous['source_sha256'].items())
    report = dict(cases=cases, source_sha256=hashes, derivative_difference_step=step,
        integrator='DOP853', relative_tolerance=2e-11, absolute_tolerance=2e-12,
        numpy_version=np.__version__, scipy_version=scipy.__version__,
        lean_toolchain=(root/'lean-toolchain').read_text().strip(),
        scope=('Finite Gaussian transcription checks for physical smoothing contraction, the fixed '
               'reference-form norm bound, uniform weak derivative and Lipschitz bounds, and the '
               'scalar integrated Schrodinger equation. Lean independently constructs a common '
               'subsequence at all real times, proves weak form and physical convergence, and passes '
               'the scalar equation through this sequence by dominated convergence. The limit has '
               'the initial datum, is weakly continuous, and has norm at most its initial norm. '
               'Norm conservation, uniqueness, strong convergence and a unitary unbounded propagator '
               'are not established here. Full six-mode infinite dynamics, regulator removal, '
               'physical identification and the TOE remain open.'))
    target = root/'data/regularized_weak_trajectory_audit.json'
    target.write_text(json.dumps(report, indent=2)+'\n')
    print(target, ':', len(cases), 'trajectories,', len(cases)*len(times), 'sampled times,', len(hashes), 'hashes.')
    for key in ['form_norm_bound_excess', 'smoothing_bound_excess', 'contraction_excess',
                'slope_bound_excess', 'lipschitz_bound_excess', 'weak_derivative_relative_error',
                'weak_integral_relative_error']:
        print('Maximum', key, ':', max(row[key] for row in cases))


if __name__ == '__main__':
    main()
