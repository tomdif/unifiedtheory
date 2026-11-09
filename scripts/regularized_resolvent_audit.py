#!/usr/bin/env python3
"""Finite Gaussian transcription checks for shifted resolvents and Yosida operators.

Lean separately proves the infinite-Hilbert-space fixed-time strong limits.
These matrices do not establish convergence of time evolution or a TOE.
"""
import hashlib
import json
from pathlib import Path

import numpy as np
import scipy
from scipy import linalg

from regularized_form_time_audit import roots
from regularized_hamiltonian_audit import clock_integral, gaussian_momentum


def main():
    cases = []
    step = 1e-4
    shifts = [.25, 1., 4., 16., 64., 256.]
    for epsilon in [.01, .1, 1.]:
        for dimension in [3, 5]:
            frequencies = np.arange(dimension)*.5-(dimension-1)*.25
            mass = np.array([[clock_integral(epsilon, 1, float(q-p))
                              for q in frequencies] for p in frequencies])
            clock = .5*np.array([[clock_integral(epsilon, 2, float(q-p))
                                 for q in frequencies] for p in frequencies])
            lower = linalg.cholesky(mass, lower=True)
            inverse_lower = linalg.solve_triangular(lower, np.eye(dimension), lower=True)
            identity = np.eye(dimension)
            state = np.cos(np.arange(dimension)+.2)+1j*np.sin(np.arange(dimension)+.7)
            state /= linalg.norm(state)
            for hbar in [.2, .7]:
                for coupling in [0., .3, 1.]:
                    momentum = coupling*gaussian_momentum(frequencies, hbar)

                    def energy(t):
                        return clock+np.exp(2*t)*momentum

                    _, inverse_reference = roots(mass+energy(0.))
                    embedding = lower.conj().T@inverse_reference

                    def form_shift(a, t):
                        return inverse_reference@(a*mass+energy(t))@inverse_reference

                    def physical_resolvent(a, t):
                        return embedding@linalg.solve(form_shift(a, t), embedding.conj().T,
                                                       assume_a='pos')

                    for t in [-1., -.5, 0., .5, 1.]:
                        hamiltonian = inverse_lower@energy(t)@inverse_lower.conj().T
                        derivative = inverse_reference@(2*np.exp(2*t)*momentum)@inverse_reference
                        previous_state_error = np.inf
                        for a in shifts:
                            form = form_shift(a, t)
                            inverse = linalg.solve(form, identity, assume_a='pos')
                            resolvent = physical_resolvent(a, t)
                            direct = linalg.solve(hamiltonian+a*identity, identity, assume_a='pos')
                            derivative_resolvent = -embedding@inverse@derivative@inverse@embedding.conj().T
                            finite_difference = (physical_resolvent(a, t+step)-physical_resolvent(a, t-step))/(2*step)
                            derivative_error = linalg.norm(finite_difference-derivative_resolvent)/max(1., linalg.norm(derivative_resolvent))
                            inverse_defect = linalg.norm(form@inverse-identity)
                            direct_defect = linalg.norm(resolvent-direct)
                            equation_defect = max(linalg.norm((hamiltonian+a*identity)@resolvent-identity),
                                                  linalg.norm(resolvent@(hamiltonian+a*identity)-identity))
                            resolvent_eigenvalues = linalg.eigvalsh(resolvent)
                            yosida = a*identity-a*a*resolvent
                            yosida_eigenvalues = linalg.eigvalsh(yosida)
                            domain_defect = linalg.norm(yosida-a*resolvent@hamiltonian)/max(1., linalg.norm(hamiltonian))
                            state_error = linalg.norm(a*resolvent@state-state)
                            error_bound = linalg.norm(hamiltonian@state)/a
                            assert max(inverse_defect, direct_defect, equation_defect, domain_defect) < 1e-8
                            assert derivative_error < 1e-7
                            assert resolvent_eigenvalues[0] > 0
                            assert resolvent_eigenvalues[-1] <= 1/a+1e-9
                            assert yosida_eigenvalues[0] >= -1e-8
                            assert yosida_eigenvalues[-1] <= a+1e-8
                            assert state_error <= error_bound+1e-9
                            assert state_error <= previous_state_error+1e-9
                            previous_state_error = state_error
                            cases.append(dict(epsilon=epsilon, dimension=dimension, hbar=hbar,
                                coupling=coupling, time=t, shift=a, inverse_defect=float(inverse_defect),
                                direct_resolvent_defect=float(direct_defect), equation_defect=float(equation_defect),
                                derivative_relative_error=float(derivative_error), domain_identity_defect=float(domain_defect),
                                resolvent_norm=float(resolvent_eigenvalues[-1]),
                                min_yosida_eigenvalue=float(yosida_eigenvalues[0]),
                                max_yosida_eigenvalue=float(yosida_eigenvalues[-1]),
                                normalized_resolvent_state_error=float(state_error), state_error_bound=float(error_bound)))
    root = Path(__file__).resolve().parents[1]
    previous = json.loads((root/'data/regularized_form_time_audit.json').read_text())
    sources = list(previous['source_sha256'])+['scripts/regularized_resolvent_audit.py']
    sources += ['UnifiedTheory/Audit/'+name+'.lean' for name in [
        'KFCausalCoerciveInverse', 'KFCausalShiftedForm', 'KFCausalInverseCurve',
        'KFCausalRegularizedShiftedResolvent', 'KFCausalPositiveResolventBounds',
        'KFCausalYosidaApproximation', 'KFCausalRegularizedYosida']]
    hashes = {p: hashlib.sha256((root/p).read_bytes()).hexdigest() for p in sources}
    assert all(hashes[p] == digest for p, digest in previous['source_sha256'].items())
    report = dict(cases=cases, source_sha256=hashes, derivative_difference_step=step,
        numpy_version=np.__version__, scipy_version=scipy.__version__,
        lean_toolchain=(root/'lean-toolchain').read_text().strip(),
        scope=('Lean constructs the positive shifted resolvents of the actual homogeneous '
               'Hamiltonian, proves both inverse equations, positivity, self-adjointness, '
               'the 1/a norm bound, and strong convergence of normalized resolvents to identity. '
               'Its positive bounded Yosida operators are norm-continuous in time and converge '
               'strongly on the fixed-time Hamiltonian domain. The form-space inverse is '
               'continuously differentiable. These finite matrices check transcription only. '
               'Convergence of evolving states, an unbounded time-dependent unitary propagator, '
               'the full six-mode limit, regulator removal, physical identification and TOE remain open.'))
    target = root/'data/regularized_resolvent_audit.json'
    target.write_text(json.dumps(report, indent=2)+'\n')
    print(target, ':', len(cases), 'cases,', len(hashes), 'hashes.')
    for key in ['inverse_defect', 'direct_resolvent_defect', 'equation_defect',
                'derivative_relative_error', 'domain_identity_defect']:
        print('Maximum', key, ':', max(row[key] for row in cases))


if __name__ == '__main__':
    main()
