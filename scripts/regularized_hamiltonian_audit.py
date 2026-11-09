#!/usr/bin/env python3
"""Independent Gaussian Galerkin transcription of the homogeneous form.

Lean constructs the infinite-dimensional fixed-time Hamiltonian. These
finite matrices check the clock, Fourier weight and resolvent conventions;
they do not prove Galerkin convergence or time-dependent evolution.
"""
from functools import lru_cache
import hashlib
import json
from pathlib import Path

import numpy as np
import scipy
from scipy import integrate, linalg, special


@lru_cache(maxsize=None)
def clock_integral(epsilon, power, frequency):
    def amplitude(q):
        clock = epsilon * special.wrightomega(q / epsilon - np.log(epsilon))
        return clock**power * np.exp(-2 * np.pi * q*q)
    real, re_error = integrate.quad(
        lambda q: amplitude(q)*np.cos(2*np.pi*frequency*q),
        -np.inf, np.inf, epsabs=2e-12, epsrel=2e-12, limit=250)
    imag, im_error = integrate.quad(
        lambda q: amplitude(q)*np.sin(2*np.pi*frequency*q),
        -np.inf, np.inf, epsabs=2e-12, epsrel=2e-12, limit=250)
    assert max(re_error, im_error) < 1e-10
    return real + 1j*imag


def gaussian_momentum(frequencies, hbar):
    p, q = np.meshgrid(frequencies, frequencies, indexing='ij')
    return np.exp(np.pi*(p+q+hbar)**2/2 - np.pi*(p*p+q*q))/np.sqrt(2)


def main():
    rows = []
    fourier_checks = []
    for hbar in [.2, .7]:
        for p, q in [(-1, .5), (0, 0), (.5, 1)]:
            numerical, error = integrate.quad(
                lambda k: np.exp(2*np.pi*hbar*k - np.pi*((k-p)**2+(k-q)**2)),
                -np.inf, np.inf, epsabs=2e-12, epsrel=2e-12)
            exact = np.exp(np.pi*(p+q+hbar)**2/2 - np.pi*(p*p+q*q))/np.sqrt(2)
            assert abs(numerical-exact) < 1e-10
            fourier_checks.append(dict(hbar=hbar,p=p,q=q,error=abs(numerical-exact),
                                       quadrature_estimated_error=error))
    for epsilon in [.01, .1, 1.]:
        for dimension in [3, 5]:
            frequencies = np.arange(dimension)*.5 - (dimension-1)*.25
            mass = np.array([[clock_integral(epsilon,1,float(q-p))
                              for q in frequencies] for p in frequencies])
            clock_energy = .5*np.array([[clock_integral(epsilon,2,float(q-p))
                                        for q in frequencies] for p in frequencies])
            lower = linalg.cholesky(mass,lower=True)
            lower_inverse = linalg.solve_triangular(lower,np.eye(dimension),lower=True)
            for hbar in [.2, .7]:
                momentum = gaussian_momentum(frequencies,hbar)
                for coupling in [0., .3, 1.]:
                    for time in [-1., 0., 1.]:
                        stiffness = clock_energy + coupling*np.exp(2*time)*momentum
                        form_gram = mass + stiffness
                        values, vectors = linalg.eigh(form_gram)
                        inverse_sqrt = (vectors / np.sqrt(values)) @ vectors.conj().T
                        # J maps energy-orthonormal to physical-orthonormal coordinates.
                        embedding = lower.conj().T @ inverse_sqrt
                        resolvent = embedding @ embedding.conj().T
                        # Independent direct transformation of the energy form.
                        hamiltonian = lower_inverse @ stiffness @ lower_inverse.conj().T
                        ident = np.eye(dimension)
                        defect = linalg.norm((ident+hamiltonian)@resolvent-ident)
                        direct_resolvent = linalg.solve(ident+hamiltonian,ident,assume_a='her')
                        agreement = linalg.norm(resolvent-direct_resolvent)
                        hermitian_defect = linalg.norm(hamiltonian-hamiltonian.conj().T)
                        h_eigen = linalg.eigvalsh(hamiltonian)
                        r_eigen = linalg.eigvalsh(resolvent)
                        assert max(defect,agreement,hermitian_defect) < 2e-8
                        assert h_eigen[0] >= -1e-10
                        assert r_eigen[0] > 0 and r_eigen[-1] <= 1+1e-10
                        # Check a complex-vector variational pairing, including conjugations.
                        force = np.arange(1,dimension+1) + 1j*np.arange(dimension)
                        test = np.exp(1j*frequencies)
                        lifted = embedding.conj().T@force
                        variational_defect = abs(np.vdot(lifted,test)-np.vdot(force,embedding@test))
                        assert variational_defect < 1e-10
                        rows.append(dict(epsilon=epsilon,dimension=dimension,hbar=hbar,
                            coupling=coupling,time=time,min_hamiltonian_eigenvalue=float(h_eigen[0]),
                            min_resolvent_eigenvalue=float(r_eigen[0]),
                            max_resolvent_eigenvalue=float(r_eigen[-1]),
                            inverse_identity_defect=float(defect),resolvent_agreement=float(agreement),
                            hermitian_defect=float(hermitian_defect),
                            variational_pairing_defect=float(variational_defect)))
    root = Path(__file__).resolve().parents[1]
    previous = json.loads((root/'data/regularized_closed_form_audit.json').read_text())
    sources = list(previous['source_sha256']) + ['scripts/regularized_hamiltonian_audit.py']
    sources += ['UnifiedTheory/Audit/'+name+'.lean' for name in [
        'KFCausalFormResolvent','KFCausalResolventHamiltonian',
        'KFCausalFormHamiltonian','KFCausalRegularizedHamiltonian']]
    hashes = {path:hashlib.sha256((root/path).read_bytes()).hexdigest() for path in sources}
    assert all(hashes[path]==digest for path,digest in previous['source_sha256'].items())
    report = dict(galerkin_cases=rows,fourier_weight_checks=fourier_checks,source_sha256=hashes,
        numpy_version=np.__version__,scipy_version=scipy.__version__,
        lean_toolchain=(root/'lean-toolchain').read_text().strip(),
        scope=('Lean constructs a positive self-adjoint fixed-time homogeneous Hamiltonian '
               'at epsilon>0 and nonnegative coupling, identifies its actual domain by the '
               'form variational equation and represents the specified closed energy form. '
               'The finite Gaussian Galerkin matrices here check transcription only. '
               'Nonautonomous evolution, full six-mode infinite dynamics, controlled '
               'capacity and regulator limits, physical identification and TOE remain unproved.'))
    target = root/'data/regularized_hamiltonian_audit.json'
    target.write_text(json.dumps(report,indent=2)+'\n')
    print(target,':',len(rows),'Galerkin cases,',len(fourier_checks),'Fourier checks,',len(hashes),'hashes.')
    print('Maximum inverse identity defect:',max(row['inverse_identity_defect'] for row in rows))
    print('Maximum independent resolvent disagreement:',max(row['resolvent_agreement'] for row in rows))


if __name__ == '__main__':
    main()
