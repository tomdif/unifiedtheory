#!/usr/bin/env python3
"""Finite Gaussian checks of mass regularization and energy conservation.

The finite computations check the algebra, signs, and uniform bounds.
Lean proves conservation for the constructed infinite-dimensional weak
trajectory, uniqueness among constructed trajectories, and a reversible
flow on the form domain; the computations do not prove those limit theorems.
"""
import hashlib
import json
from pathlib import Path

import numpy as np
import scipy
from scipy import integrate, linalg

from regularized_hamiltonian_audit import clock_integral, gaussian_momentum

NEW_MODULES = [
    'KFCausalMassGram', 'KFCausalLocalWeakContinuity',
    'KFCausalWeakQuadraticDerivative', 'KFCausalRegularizedWeakFormContinuity',
    'KFCausalMassRegularization', 'KFCausalRegularizedEnergyLimit',
    'KFCausalMassEnergyIdentities', 'KFCausalRegularizedMassEnergy',
    'KFCausalWeakNormStrongLimit', 'KFCausalRegularizedWeakNormConservation',
    'KFCausalWeakMassConservation', 'KFCausalRegularizedWeakUniqueness',
    'KFCausalRegularizedFormFlow',
]


def main():
    cases = []
    window = .3
    times = np.linspace(-window, window, 13)
    deltas = [.5, .1, .02, .004, .0008]
    step = 1e-6
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
            for hbar in [.2, .7]:
                for coupling in [0., .3, 1.]:
                    momentum = coupling*gaussian_momentum(frequencies, hbar)

                    def physical(t):
                        return inv_lower@(clock+np.exp(2*t)*momentum)@inv_lower.conj().T

                    form_gram = identity+physical(0.)
                    eig, basis = linalg.eigh(form_gram)
                    square = (basis*np.sqrt(eig))@basis.conj().T
                    embedding = (basis/eig**.5)@basis.conj().T
                    gram = embedding.conj().T@embedding
                    inverses = [linalg.solve(gram+delta*identity, identity, assume_a='pos') for delta in deltas]
                    form_initial = float(np.vdot(initial, physical(0.)@initial).real)
                    radius = np.sqrt(1+np.exp(4*window)*form_initial)
                    slope_bound = abs(1/hbar)*radius*(1+np.exp(2*window))
                    derivative_bound = 2*slope_bound*radius

                    def solve(end):
                        result = integrate.solve_ivp(lambda t, psi: (-1j/hbar)*(physical(t)@psi),
                            (0., end), initial, method='DOP853', dense_output=True,
                            rtol=2e-11, atol=2e-12)
                        assert result.success, result.message
                        return result

                    forward, backward = solve(window), solve(-window)

                    def state(t):
                        return (forward if t >= 0 else backward).sol(t)

                    def quantities(t):
                        psi = state(t)
                        u = square@psi
                        g = gram@u
                        form = embedding.conj().T@physical(t)@embedding
                        d = (-1j/hbar)*(form@u)
                        return psi, u, g, d

                    def energies(t):
                        _, _, g, _ = quantities(t)
                        return np.array([np.vdot(g, p@g).real for p in inverses])

                    def derivatives(t):
                        _, _, g, d = quantities(t)
                        return np.array([2*np.vdot(d, p@g).real for p in inverses])

                    integral = integrate.quad_vec(derivatives, -window, window, epsabs=2e-9, epsrel=2e-9)[0]
                    integral_errors = np.abs(integral-(energies(window)-energies(-window)))
                    derivative_errors = np.zeros(len(deltas))
                    for t in [-.15, .15]:
                        exact = derivatives(t)
                        finite = (energies(t+step)-energies(t-step))/(2*step)
                        derivative_errors = np.maximum(derivative_errors,
                            np.abs(finite-exact)/np.maximum(1., np.abs(exact)))
                    rows = [dict(delta=delta, samples=[], identity_error=0., derivative_bound_excess=0.,
                        damping_contraction_excess=0., physical_norm_error=0., form_bound_excess=0.,
                        weak_energy_derivative_relative_error=float(derivative_errors[i]),
                        integrated_derivative_error=float(integral_errors[i])) for i, delta in enumerate(deltas)]
                    for t in times:
                        psi, u, g, d = quantities(float(t))
                        energy_values = energies(t)
                        derivative_values = derivatives(t)
                        damping_norms = []
                        for i, (delta, p, row) in enumerate(zip(deltas, inverses, rows)):
                            damp = delta*(p@u)
                            damping_norms.append(linalg.norm(damp))
                            residual = abs(derivative_values[i]+2*np.vdot(d, damp).real)
                            row['identity_error'] = max(row['identity_error'], float(residual))
                            row['derivative_bound_excess'] = max(row['derivative_bound_excess'],
                                float(abs(derivative_values[i])-derivative_bound))
                            row['damping_contraction_excess'] = max(row['damping_contraction_excess'],
                                float(linalg.norm(damp)-linalg.norm(u)))
                            row['physical_norm_error'] = max(row['physical_norm_error'], float(abs(linalg.norm(psi)-1)))
                            row['form_bound_excess'] = max(row['form_bound_excess'], float(linalg.norm(u)-radius))
                            row['samples'].append(dict(time=float(t), regularized_energy=float(energy_values[i]),
                                energy_derivative=float(derivative_values[i]), damping_norm=float(linalg.norm(damp)),
                                physical_norm_squared=float(linalg.norm(psi)**2)))
                        assert all(damping_norms[i+1] <= damping_norms[i]+1e-9 for i in range(len(deltas)-1))
                        assert all(energy_values[i] <= energy_values[i+1]+1e-9 for i in range(len(deltas)-1))
                    for row in rows:
                        for key in ['identity_error', 'derivative_bound_excess', 'damping_contraction_excess',
                                    'physical_norm_error', 'form_bound_excess', 'integrated_derivative_error']:
                            assert row[key] < 2e-8, (key, row[key], epsilon, dimension, hbar, coupling)
                        assert row['weak_energy_derivative_relative_error'] < 1e-4, row
                        cases.append(dict(epsilon=epsilon, dimension=dimension, hbar=hbar, coupling=coupling,
                            window=window, reference_form_radius=float(radius), mass_slope_bound=float(slope_bound),
                            uniform_energy_derivative_bound=float(derivative_bound), **row))
    root = Path(__file__).resolve().parents[1]
    previous = json.loads((root/'data/regularized_weak_trajectory_audit.json').read_text())
    sources = list(previous['source_sha256'])+['scripts/regularized_mass_energy_audit.py']
    sources += ['UnifiedTheory/Audit/'+name+'.lean' for name in NEW_MODULES]
    hashes = {p: hashlib.sha256((root/p).read_bytes()).hexdigest() for p in sources}
    assert all(hashes[p] == value for p, value in previous['source_sha256'].items())
    report = dict(cases=cases, source_sha256=hashes, derivative_difference_step=step,
        integrator='DOP853', relative_tolerance=2e-11, absolute_tolerance=2e-12,
        numpy_version=np.__version__, scipy_version=scipy.__version__,
        lean_toolchain=(root/'lean-toolchain').read_text().strip(),
        scope=('Finite Gaussian checks of the reference mass G=J*J, positive mass regularization '
               'P_delta=(G+delta I)^(-1), its exact energy derivative and cancellation identity, '
               'damping contraction and local derivative bound. Lean independently proves '
               'conservation of the physical norm, strong continuity of the constructed weak '
               'solution and strong convergence along its cutoff subsequence. It also proves '
               'uniqueness among constructed trajectories, physical distance conservation, '
               'composition and backward evolution on the form domain. Complex linearity, '
               'extension to all physical L2 data, convergence of the full cutoff family, '
               'a unitary unbounded propagator, full '
               'six-mode infinite dynamics, regulator removal, physical identification and TOE '
               'remain open.'))
    target = root/'data/regularized_mass_energy_audit.json'
    target.write_text(json.dumps(report, indent=2)+'\n')
    print(target, ':', len(cases), 'regularized energies,', len(cases)*len(times), 'sampled times,', len(hashes), 'hashes.')
    for key in ['identity_error', 'derivative_bound_excess', 'damping_contraction_excess',
                'physical_norm_error', 'form_bound_excess', 'weak_energy_derivative_relative_error',
                'integrated_derivative_error']:
        print('Maximum', key, ':', max(row[key] for row in cases))


if __name__ == '__main__':
    main()
