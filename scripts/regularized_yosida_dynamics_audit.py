#!/usr/bin/env python3
"""Independent finite Gaussian checks of bounded Yosida time evolution.

The arbitrary-Hilbert-space evolution theorem is checked by Lean.
These ODE computations check transcription, time ordering and reversibility;
they do not prove convergence as the Yosida cutoff tends to infinity.
"""
import hashlib
import json
from pathlib import Path

import numpy as np
import scipy
from scipy import integrate, linalg

from regularized_hamiltonian_audit import clock_integral, gaussian_momentum


def main():
    cases = []
    step = 1e-5
    start, middle, end = -.3, 0., .3
    for epsilon in [.01, .1, 1.]:
        for dimension in [3, 5]:
            frequencies = np.arange(dimension)*.5-(dimension-1)*.25
            mass = np.array([[clock_integral(epsilon, 1, float(q-p))
                              for q in frequencies] for p in frequencies])
            clock = .5*np.array([[clock_integral(epsilon, 2, float(q-p))
                                 for q in frequencies] for p in frequencies])
            lower = linalg.cholesky(mass, lower=True)
            inverse_lower = linalg.solve_triangular(lower, np.eye(dimension), lower=True)
            identity = np.eye(dimension, dtype=complex)
            for hbar in [.2, .7]:
                for coupling in [0., .3, 1.]:
                    momentum = coupling*gaussian_momentum(frequencies, hbar)
                    for cutoff in [.5, 2., 8.]:
                        def generator(t):
                            hamiltonian = inverse_lower@(clock+np.exp(2*t)*momentum)@inverse_lower.conj().T
                            resolvent = linalg.solve(hamiltonian+cutoff*identity, identity, assume_a='pos')
                            yosida = cutoff*identity-cutoff*cutoff*resolvent
                            return (-1j/hbar)*yosida

                        def solve(s, t):
                            result = integrate.solve_ivp(
                                lambda r, u: (generator(r)@u.reshape(dimension, dimension)).reshape(-1),
                                (s, t), identity.reshape(-1), method='DOP853', dense_output=True,
                                rtol=2e-11, atol=2e-12)
                            assert result.success, result.message
                            return result

                        full = solve(start, end)
                        before, after, reverse = solve(start, middle), solve(middle, end), solve(end, start)
                        u = full.y[:, -1].reshape(dimension, dimension)
                        u1 = before.y[:, -1].reshape(dimension, dimension)
                        u2 = after.y[:, -1].reshape(dimension, dimension)
                        back = reverse.y[:, -1].reshape(dimension, dimension)
                        composition_error = linalg.norm(u2@u1-u)
                        reverse_error = linalg.norm(back-u.conj().T)
                        inverse_error = max(linalg.norm(back@u-identity), linalg.norm(u@back-identity))
                        unitary_error = max(linalg.norm(u.conj().T@u-identity), linalg.norm(u@u.conj().T-identity))
                        at_middle = full.sol(middle).reshape(dimension, dimension)
                        derivative = (full.sol(middle+step)-full.sol(middle-step)).reshape(dimension, dimension)/(2*step)
                        expected = generator(middle)@at_middle
                        derivative_error = linalg.norm(derivative-expected)/max(1., linalg.norm(expected))
                        norm_error = max(abs(linalg.svdvals(u)-1.))
                        assert max(composition_error, reverse_error, inverse_error, unitary_error, norm_error) < 1e-8
                        assert derivative_error < 5e-6
                        cases.append(dict(epsilon=epsilon, dimension=dimension, hbar=hbar,
                            coupling=coupling, cutoff=cutoff, start=start, end=end,
                            composition_error=float(composition_error), reverse_error=float(reverse_error),
                            inverse_error=float(inverse_error), unitary_error=float(unitary_error),
                            derivative_relative_error=float(derivative_error), norm_error=float(norm_error),
                            rhs_evaluations=int(sum(sol.nfev for sol in [full, before, after, reverse]))))
    root = Path(__file__).resolve().parents[1]
    previous = json.loads((root/'data/regularized_resolvent_audit.json').read_text())
    sources = list(previous['source_sha256'])+['scripts/regularized_yosida_dynamics_audit.py']
    sources += ['UnifiedTheory/Audit/'+name+'.lean' for name in [
        'KFCausalHilbertIntervalPropagator', 'KFCausalHilbertGlobalFlow',
        'KFCausalHilbertEvolution', 'KFCausalHilbertStateEvolution',
        'KFCausalHilbertEvolutionStability', 'KFCausalRegularizedYosidaDynamics']]
    hashes = {p: hashlib.sha256((root/p).read_bytes()).hexdigest() for p in sources}
    assert all(hashes[p] == digest for p, digest in previous['source_sha256'].items())
    report = dict(cases=cases, source_sha256=hashes, derivative_difference_step=step,
        integrator='DOP853', relative_tolerance=2e-11, absolute_tolerance=2e-12,
        numpy_version=np.__version__, scipy_version=scipy.__version__,
        lean_toolchain=(root/'lean-toolchain').read_text().strip(),
        scope=('Lean constructs all-time, two-parameter unitary evolution for continuous '
               'bounded skew-adjoint operators on any complete complex Hilbert space, '
               'including composition, backward evolution, joint continuity and unique '
               'state solutions. The concrete regularized homogeneous Yosida Hamiltonians '
               'supply the generator; for nonzero hbar the states solve the bounded '
               'Schrodinger equation. A generic stability estimate bounds evolution '
               'differences by a supplied bound on the generator residual along the '
               'second trajectory; decay of that residual is not proved. These finite '
               'Gaussian computations check transcription only. Convergence as cutoff '
               'tends to infinity, the unbounded propagator, the full six-mode infinite '
               'model, regulator removal, physical identification and TOE remain open.'))
    target = root/'data/regularized_yosida_dynamics_audit.json'
    target.write_text(json.dumps(report, indent=2)+'\n')
    print(target, ':', len(cases), 'cases,', len(hashes), 'hashes.')
    for key in ['composition_error', 'reverse_error', 'inverse_error', 'unitary_error',
                'derivative_relative_error', 'norm_error']:
        print('Maximum', key, ':', max(row[key] for row in cases))


if __name__ == '__main__':
    main()
