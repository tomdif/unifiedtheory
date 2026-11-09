#!/usr/bin/env python3
"""Finite transcription checks for the constructed homogeneous evolution.

Independent matrix and vector ODE solves test the signs, complex linearity,
composition, inverse, physical norm, and weak form equation. These checks
do not prove dense extension or infinite-dimensional evolution; Lean does.
"""
import hashlib
import json
from pathlib import Path

import numpy as np
import scipy
from scipy import integrate, linalg

from regularized_hamiltonian_audit import clock_integral, gaussian_momentum

NEW_MODULES = [
    'KFCausalWeakFormSolution', 'KFCausalRegularizedWeakSolution',
    'KFCausalRegularizedFormLinearity', 'KFCausalDenseUnitaryExtension',
    'KFCausalRegularizedHomogeneousEvolution', 'KFCausalStrongUnitaryContinuity',
    'KFCausalRegularizedHomogeneousContinuity',
]


def main():
    cases = []
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
            for hbar in [.4, .9]:
                for coupling in [0., .3]:
                    momentum = coupling*gaussian_momentum(frequencies, hbar)

                    def physical(t):
                        return inv_lower@(clock+np.exp(2*t)*momentum)@inv_lower.conj().T

                    values, basis = linalg.eigh(identity+physical(0.))
                    square = (basis*np.sqrt(values))@basis.conj().T
                    embedding = (basis/np.sqrt(values))@basis.conj().T
                    start, middle, end = (-.1, .03, .14) if hbar == .4 else (.1, -.04, -.12)

                    def solve(a, b, initial):
                        shape = initial.shape
                        solution = integrate.solve_ivp(
                            lambda z, v: ((-1j/hbar)*(physical(z)@v.reshape(shape))).reshape(-1),
                            (a, b), initial.reshape(-1), method='DOP853', dense_output=True,
                            rtol=2e-11, atol=2e-12)
                        assert solution.success, solution.message
                        return solution, solution.y[:, -1].reshape(shape)

                    trajectory, direct = solve(start, end, identity)
                    _, first = solve(start, middle, identity)
                    _, second = solve(middle, end, identity)
                    _, backward = solve(end, start, identity)
                    u = np.cos(np.arange(dimension)+.2)+1j*np.sin(np.arange(dimension)+.6)
                    v = np.sin(np.arange(dimension)+.4)+1j*np.cos(np.arange(dimension)+.8)
                    u /= linalg.norm(u)
                    v /= linalg.norm(v)
                    coefficient = .37+.81j
                    _, vector_u = solve(start, end, u)
                    _, vector_sum = solve(start, end, coefficient*u+v)
                    form_map = square@direct@embedding
                    form_initial = square@u
                    form_test = square@v

                    def weak_integrand(z):
                        state = trajectory.sol(z).reshape(dimension, dimension)@u
                        form = embedding.conj().T@physical(z)@embedding
                        return np.vdot(square@state, form@form_test)

                    weak_integral = integrate.quad_vec(weak_integrand, start, end,
                        epsabs=2e-9, epsrel=2e-9)[0]
                    weak_target = -1j*hbar*(np.vdot(direct@u, embedding@form_test)-
                                           np.vdot(u, embedding@form_test))
                    row = dict(epsilon=epsilon, dimension=dimension, hbar=hbar, coupling=coupling,
                        start=start, middle=middle, end=end,
                        unitarity_error=float(linalg.norm(direct.conj().T@direct-identity)),
                        composition_error=float(linalg.norm(second@first-direct)),
                        inverse_error=float(linalg.norm(backward@direct-identity)),
                        adjoint_error=float(linalg.norm(backward-direct.conj().T)),
                        independent_vector_error=float(linalg.norm(vector_u-direct@u)),
                        complex_linearity_error=float(linalg.norm(vector_sum-(coefficient*vector_u+direct@v))),
                        embedding_error=float(linalg.norm(embedding@form_map-direct@embedding)),
                        physical_norm_error=float(abs(linalg.norm(embedding@form_map@form_initial)-linalg.norm(u))),
                        weak_integral_error=float(abs(weak_integral-weak_target)))
                    for key, value in row.items():
                        if key.endswith('_error'):
                            assert value < 3e-8, (key, value, epsilon, dimension, hbar, coupling)
                    cases.append(row)

    root = Path(__file__).resolve().parents[1]
    previous = json.loads((root/'data/regularized_mass_energy_audit.json').read_text())
    sources = list(previous['source_sha256'])+['scripts/regularized_homogeneous_evolution_audit.py']
    sources += ['UnifiedTheory/Audit/'+name+'.lean' for name in NEW_MODULES]
    hashes = {p: hashlib.sha256((root/p).read_bytes()).hexdigest() for p in sources}
    assert all(hashes[p] == h for p, h in previous['source_sha256'].items())
    report = dict(cases=cases, source_sha256=hashes,
        integrator='DOP853', relative_tolerance=2e-11, absolute_tolerance=2e-12,
        numpy_version=np.__version__, scipy_version=scipy.__version__,
        lean_toolchain=(root/'lean-toolchain').read_text().strip(),
        scope=('Finite Gaussian transcription of the fixed-regulator homogeneous Schrodinger '
               'evolution. Lean separately proves closure of weak solutions under complex '
               'linear combinations, uniqueness in the stated weak-solution class, dense '
               'extension to all physical L2 data, unitarity, composition, backward evolution, '
               'joint strong continuity, and the integrated equation for form-domain data. '
               'Full cutoff-family convergence, classical differentiation on the operator '
               'domain, the full six-mode infinite model, regulator removal, continuum limits, '
               'physical identification and the TOE are not established by this audit.'))
    target = root/'data/regularized_homogeneous_evolution_audit.json'
    target.write_text(json.dumps(report, indent=2)+'\n')
    print(target, ':', len(cases), 'evolution cases,', len(hashes), 'source hashes.')
    for key in cases[0]:
        if key.endswith('_error'):
            print('Maximum', key, ':', max(row[key] for row in cases))


if __name__ == '__main__':
    main()
