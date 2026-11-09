#!/usr/bin/env python3
"""Independent finite Gaussian checks of common-form transport and regularity.

The infinite-domain assertions are Lean theorems. These Galerkin matrices
check the energy weights, reference-space coordinates and time derivative;
no convergence or infinite-dimensional propagator is claimed here.
"""
import hashlib
import json
from pathlib import Path

import numpy as np
import scipy
from scipy import linalg

from regularized_hamiltonian_audit import clock_integral, gaussian_momentum


def roots(matrix):
    values, vectors = linalg.eigh(matrix)
    assert values[0] > 0
    return ((vectors*np.sqrt(values))@vectors.conj().T,
            (vectors/np.sqrt(values))@vectors.conj().T)


def main():
    regularity = []
    transports = []
    times = [-1., -.5, 0., .5, 1.]
    step = 1e-4
    for epsilon in [.01, .1, 1.]:
        for dimension in [3, 5]:
            frequencies = np.arange(dimension)*.5-(dimension-1)*.25
            mass = np.array([[clock_integral(epsilon,1,float(q-p))
                              for q in frequencies] for p in frequencies])
            clock = .5*np.array([[clock_integral(epsilon,2,float(q-p))
                                 for q in frequencies] for p in frequencies])
            lower = linalg.cholesky(mass,lower=True)
            for hbar in [.2,.7]:
                for coupling in [0.,.3,1.]:
                    momentum = coupling*gaussian_momentum(frequencies,hbar)
                    def energy(t):
                        return clock + np.exp(2*t)*momentum
                    _, reference_inverse = roots(mass+energy(0))
                    def bounded_form(t):
                        return reference_inverse@energy(t)@reference_inverse
                    at_time = {}
                    for t in times:
                        sqrt, inverse_sqrt = roots(mass+energy(t))
                        embedding = lower.conj().T@inverse_sqrt
                        at_time[t] = sqrt,inverse_sqrt,embedding
                        form = bounded_form(t)
                        derivative = 2*np.exp(2*t)*reference_inverse@momentum@reference_inverse
                        finite_difference = (bounded_form(t+step)-bounded_form(t-step))/(2*step)
                        relative_error = linalg.norm(finite_difference-derivative)/max(1.,linalg.norm(derivative))
                        assert relative_error < 1e-7
                        assert linalg.norm(form,2) <= 1+np.exp(2*t)+1e-9
                        assert linalg.norm(derivative,2) <= 2*np.exp(2*t)+1e-9
                        assert linalg.eigvalsh(derivative)[0] >= -1e-9
                        assert linalg.eigvalsh(2*form-derivative)[0] >= -1e-9
                        regularity.append(dict(epsilon=epsilon,dimension=dimension,hbar=hbar,
                            coupling=coupling,time=t,form_operator_norm=float(linalg.norm(form,2)),
                            derivative_operator_norm=float(linalg.norm(derivative,2)),
                            derivative_relative_error=float(relative_error)))
                    for i,s in enumerate(times):
                        for t in times[i+1:]:
                            gs, ins, js = at_time[s]
                            gt, int_, jt = at_time[t]
                            transport = gt@ins
                            reverse = gs@int_
                            inverse_defect = linalg.norm(reverse@transport-np.eye(dimension))
                            input_defect = linalg.norm(jt@transport-js)
                            singular = linalg.svdvals(transport)
                            assert max(inverse_defect,input_defect) < 1e-8
                            assert singular[-1] >= 1-1e-9
                            assert singular[0] <= np.exp(t-s)+1e-9
                            assert linalg.eigvalsh(energy(t)-energy(s))[0] >= -1e-8
                            assert linalg.eigvalsh(np.exp(2*(t-s))*energy(s)-energy(t))[0] >= -1e-8
                            transports.append(dict(epsilon=epsilon,dimension=dimension,hbar=hbar,
                                coupling=coupling,start=s,end=t,inverse_defect=float(inverse_defect),
                                input_defect=float(input_defect),min_singular_value=float(singular[-1]),
                                max_singular_value=float(singular[0])))
    root = Path(__file__).resolve().parents[1]
    previous = json.loads((root/'data/regularized_hamiltonian_audit.json').read_text())
    sources = list(previous['source_sha256'])+['scripts/regularized_form_time_audit.py']
    sources += ['UnifiedTheory/Audit/'+name+'.lean' for name in [
        'KFCausalGraphTransport','KFCausalRegularizedFormTransport',
        'KFCausalRegularizedFormTimeControl','KFCausalBoundedFormCurve',
        'KFCausalRegularizedFormRegularity','KFCausalRegularizedHamiltonianFormBridge']]
    hashes = {p:hashlib.sha256((root/p).read_bytes()).hexdigest() for p in sources}
    assert all(hashes[p]==digest for p,digest in previous['source_sha256'].items())
    report = dict(regularity_cases=regularity,transport_cases=transports,source_sha256=hashes,
        derivative_difference_step=step,numpy_version=np.__version__,scipy_version=scipy.__version__,
        lean_toolchain=(root/'lean-toolchain').read_text().strip(),
        scope=('Lean proves common homogeneous closed-form domains, exact form transport, '
               'energy and graph-norm comparisons, a positive form-norm lower bound, '
               'continuous differentiability in bounded-operator norm, and the exact '
               'reference-form characterization of the constructed Hamiltonian domain. '
               'These finite matrices check transcription only. Time-dependent infinite '
               'evolution, the full six-mode limit, regulator removal, physical identification '
               'and TOE remain unproved.'))
    target = root/'data/regularized_form_time_audit.json'
    target.write_text(json.dumps(report,indent=2)+'\n')
    print(target,':',len(regularity),'regularity cases,',len(transports),'transport cases,',len(hashes),'hashes.')
    print('Maximum derivative relative error:',max(row['derivative_relative_error'] for row in regularity))
    print('Maximum inverse defect:',max(row['inverse_defect'] for row in transports))
    print('Maximum input embedding defect:',max(row['input_defect'] for row in transports))


if __name__ == '__main__':
    main()
