#!/usr/bin/env python3
"""Quadrature of the actual adjoint pairings for finite Gaussian sums.

Closability and graph completeness are Lean conclusions. These quadratures
check the Fourier sign, weighting and coordinate transcription. They do
not establish a capacity, regulator, Hamiltonian or physical limit.
"""
import hashlib
import json
from pathlib import Path

import mpmath as mp


def main():
    rows = []
    with mp.workdps(50):
        coefficients = [mp.mpc(1),mp.mpc('.3','.2'),mp.mpc('-.2','.4')]
        frequencies = [mp.mpf(0),mp.mpf('.5'),mp.mpf(-1)]
        def gaussian(q):
            return mp.exp(-mp.pi*q*q)
        def dressed(q):
            return sum(a*mp.exp(2j*mp.pi*p*q)*gaussian(q) for a,p in zip(coefficients,frequencies))
        def transformed(k):
            return sum(a*gaussian(k-p) for a,p in zip(coefficients,frequencies))
        for epsilon in ['0.01','0.1','1']:
            e = mp.mpf(epsilon)
            def c(q):
                return e*mp.lambertw(mp.exp(q/e)/e).real
            def psi(q):
                return mp.sqrt(c(q))*dressed(q)
            for hbar in ['0.2','0.7']:
                h = mp.mpf(hbar)
                for momentum in ['-1','0','0.5']:
                    p = mp.mpf(momentum)
                    def phase(q):
                        return mp.exp(2j*mp.pi*p*q)
                    def output_test(k):
                        return phase(k)*mp.exp(-mp.pi*h*k)*gaussian(k)
                    def momentum_output(k):
                        return mp.exp(mp.pi*h*k)*transformed(k)
                    def input_test(q):
                        return gaussian(q-p)/mp.sqrt(c(q))
                    left = mp.quad(lambda k:output_test(k)*momentum_output(k),[-mp.inf,0,mp.inf])
                    right = mp.quad(lambda q:input_test(q)*psi(q),[-mp.inf,0,mp.inf])
                    error = abs(left-right)
                    assert error<mp.mpf('1e-40'),(epsilon,hbar,momentum,error)
                    clock_left = mp.quad(lambda q:phase(q)*gaussian(q)/mp.sqrt(c(q))*
                        (mp.sqrt(c(q))*psi(q)),[-mp.inf,0,mp.inf])
                    clock_right = mp.quad(lambda q:phase(q)*gaussian(q)*psi(q),[-mp.inf,0,mp.inf])
                    clock_error = abs(clock_left-clock_right)
                    assert clock_error<mp.mpf('1e-40')
                    rows.append(dict(epsilon=epsilon,hbar=hbar,test_momentum=momentum,
                        momentum_pairing_real=mp.nstr(left.real,30),momentum_pairing_imag=mp.nstr(left.imag,30),
                        momentum_pairing_error=mp.nstr(error,8),clock_pairing_error=mp.nstr(clock_error,8)))
    root = Path(__file__).resolve().parents[1]
    previous = json.loads((root/'data/regularized_spin_dynamics_audit.json').read_text())
    sources = list(previous['source_sha256'])+['scripts/regularized_closed_form_audit.py']
    sources += ['UnifiedTheory/Audit/'+name+'.lean' for name in [
        'KFCausalRegularizedAdjointTests','KFCausalSeparatedGraphClosure',
        'KFCausalRegularizedMomentumClosure','KFCausalRegularizedClockFactor','KFCausalRegularizedClosedForm',
        'KFCausalRegularizedFormEmbedding']]
    hashes = {p:hashlib.sha256((root/p).read_bytes()).hexdigest() for p in sources}
    assert all(hashes[p]==h for p,h in previous['source_sha256'].items())
    report = dict(pairing_cases=rows,source_sha256=hashes,precision_decimal_digits=50,mpmath_version=mp.__version__,
        lean_toolchain=(root/'lean-toolchain').read_text().strip(),
        scope=('Explicit homogeneous adjoint tests, operator closability, a closed densely defined '
               'joint energy factor, a complete energy graph and its injective dense contraction '
               'into L2 are proved in Lean. The associated '
               'self-adjoint Hamiltonian, time evolution, full six-mode infinite domain, capacity '
               'and regulator limits, physical identification and TOE remain unproved.'))
    target = root/'data/regularized_closed_form_audit.json'
    target.write_text(json.dumps(report,indent=2)+'\n')
    print(target,':',len(rows),'momentum and clock pairing cases,',len(hashes),'source hashes.')
    print('Maximum momentum pairing error:',max(float(r['momentum_pairing_error']) for r in rows))
    print('Maximum clock pairing error:',max(float(r['clock_pairing_error']) for r in rows))


if __name__ == '__main__':
    main()
