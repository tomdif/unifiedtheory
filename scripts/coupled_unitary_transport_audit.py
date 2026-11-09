#!/usr/bin/env python3
"""Coordinate/Jacobian and Gaussian transcription checks for coupled transport.

Lean constructs the actual L2 unitary maps from a dense compact test space.
These finite-dimensional coordinate checks do not prove that construction,
an unbounded generator domain, or full Hamiltonian evolution.
"""
import hashlib
import json
from pathlib import Path

import numpy as np
import scipy
from scipy import integrate, linalg

from coupled_longitudinal_domain_audit import (
    chart, chart_inverse, phase, coupled, straightening, transverse_matrix,
    transverse_velocity, relative_error,
)

NEW_MODULES = [
    'KFCausalConfigurationTestSpace', 'KFCausalCoupledCoordinateHomeomorph',
    'KFCausalWeightedConfigurationTests', 'KFCausalCoupledTestPullback',
    'KFCausalCoupledUnitaryCoordinates', 'KFCausalConfigurationTranslation',
    'KFCausalCoupledUnitaryTransport', 'KFCausalCoupledTransportDerivative',
]


def amplitude(epsilon, s):
    return np.sqrt(np.exp(s)+epsilon)*np.exp(-phase(epsilon, s))


def jacobian(function, x, step=1e-5):
    basis = np.eye(len(x))
    return np.column_stack([(function(x+step*d)-function(x-step*d))/(2*step) for d in basis])


def configuration_cases():
    rows = []
    v = np.array([.4, -.2, .6, -.3, .1, .5])

    def packet(x):
        return np.exp(-x@x/2+1j*v@x)

    for epsilon in [.1, .4, 1., 2.]:
        for s in [-.5, .1, .6]:
            state = np.r_[s, [.3, -.2, .4, .1, -.7]]
            coord_jac = jacobian(lambda z: straightening(epsilon, z), state)
            for t in [-.12, .08, .17]:
                u = -.07
                evolved = coupled(epsilon, t, state)
                ratio = amplitude(epsilon, s)/amplitude(epsilon, evolved[0])
                flow_jac = jacobian(lambda z: coupled(epsilon, t, z), state)

                def action(time, x):
                    y = coupled(epsilon, time, x)
                    return amplitude(epsilon, x[0])/amplitude(epsilon, y[0])*packet(y)

                composed = ratio*action(u, evolved)
                back = ratio*action(-t, evolved)
                step = 1e-5
                numerical = (action(step, state)-action(-step, state))/(2*step)
                velocity = np.r_[1/(np.exp(s)+epsilon),
                    np.exp(-s)*transverse_velocity(state[1:])]
                rate = np.exp(-s)-np.exp(s)/(2*(np.exp(s)+epsilon)**2)
                target = (rate+(-state+1j*v)@velocity)*packet(state)
                row = dict(epsilon=epsilon, s=s, t=t,
                    coordinate_jacobian_error=relative_error(linalg.det(coord_jac), amplitude(epsilon, s)**2),
                    flow_half_density_error=relative_error(linalg.det(flow_jac), ratio**2),
                    composition_error=float(abs(composed-action(t+u, state))),
                    inverse_error=float(abs(back-packet(state))),
                    infinitesimal_expression_error=float(abs(numerical-target)),
                    half_density_term_magnitude=float(abs(rate*packet(state))))
                for key, value in row.items():
                    if key.endswith('_error'):
                        assert value < 2e-8, (key, row)
                assert row['half_density_term_magnitude'] > 1e-4, row
                rows.append(row)
    return rows


def gaussian_transcription_cases():
    rows = []
    lower, upper = .3, 2.
    transverse_frequency = np.array([.3, -.2, .4, .1, -.5])
    for epsilon in [.1, .4, 1., 2.]:
        for frequency in [0., .7]:
            def clock_cross(q):
                if not lower < q < upper:
                    return 0j
                bump = np.sin(np.pi*(q-lower)/(upper-lower))**2
                return bump**2*np.exp(1j*frequency*q)

            transverse_cross = np.exp(-transverse_frequency@transverse_frequency/4)
            expected = integrate.quad_vec(lambda q: clock_cross(q)*transverse_cross,
                lower, upper, epsabs=2e-12, epsrel=2e-12)[0]

            def transformed(s):
                matrix = transverse_matrix(-phase(epsilon, s))
                quadratic = matrix.T@matrix
                linear = matrix.T@transverse_frequency
                # Direct Gaussian integration of the transformed x profile.
                inner = np.exp(-linear@linalg.solve(quadratic, linear)/4)/np.sqrt(linalg.det(quadratic))
                return amplitude(epsilon, s)**2*clock_cross(chart(epsilon, s))*inner

            actual = integrate.quad_vec(transformed, chart_inverse(epsilon, lower),
                chart_inverse(epsilon, upper), epsabs=2e-12, epsrel=2e-12)[0]
            row = dict(epsilon=epsilon, clock_frequency=frequency,
                q_support=[lower, upper], inner_product_error=float(abs(actual-expected)))
            assert row['inner_product_error'] < 2e-10, row
            rows.append(row)
    return rows


def main():
    configurations = configuration_cases()
    gaussians = gaussian_transcription_cases()
    root = Path(__file__).resolve().parents[1]
    previous = json.loads((root/'data/damped_gaussian_momentum_audit.json').read_text())
    sources = list(previous['source_sha256'])+['scripts/coupled_unitary_transport_audit.py']
    sources += ['UnifiedTheory/Audit/'+name+'.lean' for name in NEW_MODULES]
    hashes = {p: hashlib.sha256((root/p).read_bytes()).hexdigest() for p in sources}
    assert all(hashes[p] == h for p, h in previous['source_sha256'].items())
    report = dict(configuration_cases=configurations, gaussian_transcription_cases=gaussians,
        source_sha256=hashes, numpy_version=np.__version__, scipy_version=scipy.__version__,
        lean_toolchain=(root/'lean-toolchain').read_text().strip(),
        scope=('Lean constructs a dense compact continuous test space, the actual weighted '
            'coordinate equivalence and its unitary extension on six-coordinate L2, '
            'clock translation, and conjugated coupled longitudinal transport with '
            'unitary group laws and strong continuity. Its test representative and '
            'pointwise derivative include the half-density correction. Numerical '
            'Jacobian and Gaussian checks concern explicit function formulas and '
            'do not establish the L2 extension. The pointwise derivative is not yet '
            'an L2 strong-generator/domain theorem. A self-adjoint longitudinal '
            'generator, all full Hamiltonian form terms on a dense common domain, '
            'charge averaging, finite-to-infinite identification, controlled limits, '
            'physical identification and the TOE remain open. Longitudinal transport '
            'is not the physical Hamiltonian time evolution.'))
    target = root/'data/coupled_unitary_transport_audit.json'
    target.write_text(json.dumps(report, indent=2)+'\n')
    print(target, ':', len(configurations), 'configuration cases,', len(gaussians),
        'Gaussian transcription cases,', len(hashes), 'source hashes.')
    for key in configurations[0]:
        if key.endswith('_error'):
            print('Maximum', key, ':', max(row[key] for row in configurations))
    print('Maximum Gaussian inner-product error:', max(row['inner_product_error'] for row in gaussians))


if __name__ == '__main__':
    main()
