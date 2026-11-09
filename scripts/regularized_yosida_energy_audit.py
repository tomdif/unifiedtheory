#!/usr/bin/env python3
"""Finite Gaussian checks of the proved cutoff-uniform bounded-energy estimate.

E_a is the Yosida energy, not the unbounded form energy of the evolving
state. These computations do not prove existence of the unbounded limit.
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
    times = np.linspace(-.3, .3, 13)
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
                        return (inv_lower@(clock+np.exp(2*t)*momentum)@inv_lower.conj().T,
                                inv_lower@(2*np.exp(2*t)*momentum)@inv_lower.conj().T)

                    for cutoff in [.5, 2., 8., 32.]:
                        def operators(t):
                            h, dh = physical(t)
                            r = linalg.solve(h+cutoff*identity, identity, assume_a='pos')
                            y = cutoff*identity-cutoff**2*r
                            dy = cutoff**2*r@dh@r
                            return h, r, y, dy

                        def solve(end):
                            result = integrate.solve_ivp(
                                lambda t, state: (-1j/hbar)*(operators(t)[2]@state),
                                (0., end), initial, method='DOP853', dense_output=True,
                                rtol=2e-11, atol=2e-12)
                            assert result.success, result.message
                            return result

                        forward, backward = solve(.3), solve(-.3)

                        def state(t):
                            return (forward if t >= 0 else backward).sol(t)

                        def energy(t):
                            psi = state(t)
                            return float(np.vdot(psi, operators(t)[2]@psi).real)

                        form_initial = float(np.vdot(initial, physical(0.)[0]@initial).real)
                        energy_initial = energy(0.)
                        assert energy_initial <= form_initial+1e-8
                        identity_error = square_error = order_defect = bound_excess = weak_defect = 0.
                        energies = []
                        for t in times:
                            t = float(t)
                            h, r, y, dy = operators(t)
                            psi = state(t)
                            e = float(np.vdot(psi, y@psi).real)
                            de = float(np.vdot(psi, dy@psi).real)
                            v = r@psi
                            residual = psi-cutoff*v
                            weak_defect = max(weak_defect, linalg.norm(h@(cutoff*v)-y@psi)/max(1., linalg.norm(y@psi)))
                            split = cutoff*linalg.norm(residual)**2+cutoff**2*np.vdot(v, h@v).real
                            identity_error = max(identity_error, abs(e-split)/max(1., abs(e)))
                            q = float(np.vdot(psi, h@psi).real)
                            completed = e+np.vdot(residual, h@residual).real+cutoff*linalg.norm(residual)**2
                            square_error = max(square_error, abs(q-completed)/max(1., abs(q)))
                            order_defect = max(order_defect, -float(linalg.eigvalsh(dy)[0]),
                                               -float(linalg.eigvalsh(2*y-dy)[0]))
                            assert -1e-8 <= de <= 2*e+1e-8
                            uniform_bound = np.exp(2*abs(t))*form_initial
                            smoothed_form_energy = float(cutoff**2*np.vdot(v, h@v).real)
                            smoothed_defect_squared = float(linalg.norm(residual)**2)
                            assert e <= uniform_bound+1e-8
                            assert smoothed_form_energy <= uniform_bound+1e-8
                            assert smoothed_defect_squared <= uniform_bound/cutoff+1e-8
                            upper = np.exp(2*max(t, 0))*energy_initial
                            bound_excess = max(bound_excess, e-upper)
                            assert e <= upper+1e-8
                            energies.append(dict(time=t, energy=e, derivative=de,
                                smoothed_form_energy=smoothed_form_energy,
                                smoothed_defect_squared=smoothed_defect_squared,
                                smoothed_defect_bound=float(uniform_bound/cutoff),
                                initial_energy_bound=float(upper),
                                uniform_form_bound=float(np.exp(2*abs(t))*form_initial)))
                        assert all(energies[i]['energy'] <= energies[i+1]['energy']+1e-8
                                   for i in range(len(energies)-1))
                        derivative_error = 0.
                        for t in [-.15, .15]:
                            finite = (energy(t+step)-energy(t-step))/(2*step)
                            psi = state(t)
                            exact = float(np.vdot(psi, operators(t)[3]@psi).real)
                            derivative_error = max(derivative_error, abs(finite-exact)/max(1., abs(exact)))
                        assert max(identity_error, square_error, order_defect, bound_excess, weak_defect) < 1e-8
                        assert derivative_error < 1e-5
                        cases.append(dict(epsilon=epsilon, dimension=dimension, hbar=hbar,
                            coupling=coupling, cutoff=cutoff, initial_form_energy=form_initial,
                            initial_yosida_energy=energy_initial, energy_identity_error=float(identity_error),
                            completed_square_error=float(square_error), derivative_order_defect=float(order_defect),
                            energy_bound_excess=float(bound_excess), weak_pairing_defect=float(weak_defect),
                            energy_derivative_relative_error=float(derivative_error), samples=energies))
    root = Path(__file__).resolve().parents[1]
    previous = json.loads((root/'data/regularized_yosida_dynamics_audit.json').read_text())
    sources = list(previous['source_sha256'])+['scripts/regularized_yosida_energy_audit.py']
    sources += ['UnifiedTheory/Audit/'+name+'.lean' for name in [
        'KFCausalSandwichCalculus', 'KFCausalFormEnergyIdentities',
        'KFCausalSchrodingerEnergyEstimate', 'KFCausalRegularizedYosidaDerivative',
        'KFCausalRegularizedYosidaEnergy', 'KFCausalRegularizedSmoothedTrajectory']]
    hashes = {p: hashlib.sha256((root/p).read_bytes()).hexdigest() for p in sources}
    assert all(hashes[p] == digest for p, digest in previous['source_sha256'].items())
    report = dict(cases=cases, source_sha256=hashes, derivative_difference_step=step,
        integrator='DOP853', relative_tolerance=2e-11, absolute_tolerance=2e-12,
        numpy_version=np.__version__, scipy_version=scipy.__version__,
        lean_toolchain=(root/'lean-toolchain').read_text().strip(),
        scope=('Lean differentiates the actual physical resolvent and Yosida Hamiltonian '
               'in operator norm and proves the exact derivative quadratic pairing. '
               'The completed-square identity bounds initial Yosida energy by the closed '
               'form energy. Along the constructed bounded evolution, its energy derivative '
               'lies between zero and twice its energy. This gives an all-time energy bound '
               'independent of the Yosida cutoff for initial data in the common form domain. '
               'The bounded energy E_a is controlled. The smoothed state a R_a psi_a lies in '
               'the original form domain with a uniform form-energy bound, has squared '
               'distance at most that bound divided by a from psi_a, and satisfies the '
               'exact weak pairing with the derivative of psi_a. This does not prove form '
               'domain invariance of each unsmoothed trajectory. These computations check transcription '
               'only. Convergence of the evolutions, an unbounded propagator, the full six-mode '
               'infinite model, regulator removal, physical identification and TOE remain open.'))
    target = root/'data/regularized_yosida_energy_audit.json'
    target.write_text(json.dumps(report, indent=2)+'\n')
    print(target, ':', len(cases), 'trajectories,', len(cases)*len(times), 'samples,', len(hashes), 'hashes.')
    for key in ['energy_identity_error', 'completed_square_error', 'derivative_order_defect',
                'energy_bound_excess', 'weak_pairing_defect', 'energy_derivative_relative_error']:
        print('Maximum', key, ':', max(row[key] for row in cases))


if __name__ == '__main__':
    main()
