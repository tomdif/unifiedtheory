#!/usr/bin/env python3
"""Full clock-integrated projected response matrices on displaced packets.

All complex cross terms are retained, including different positive clock
widths and real clock frequencies. These are floating-point tests of a
finite subspace, not a sign certificate or a state-uniform bound.
Run: OPENBLAS_NUM_THREADS=1 python3 scripts/projected_integrated_response_probe.py --output PATH
"""
import argparse
import hashlib
import json
from pathlib import Path
import time

import numpy as np
from numpy.polynomial.legendre import leggauss
from scipy.linalg import eigh
import matter_energy_gram_probe as old
import projected_kernel_matrix_probe as transverse
import zero_charge_response_probe as diagonal


def hermitian(matrix):
    if not np.isfinite(matrix).all():
        raise ArithmeticError('Nonfinite matrix; no result accepted.')
    error = np.linalg.norm(matrix-matrix.conj().T)/max(1., np.linalg.norm(matrix))
    if error > 2e-10:
        raise ArithmeticError(f'Non-Hermitian matrix: {error}')
    return (matrix+matrix.conj().T)/2


class Integrated:
    def __init__(self, packets, h=.3, eps=1., nt=24, nd=96):
        # Each row is [positive transverse displacement A, lambda,
        #              positive clock Gaussian width a, clock frequency p].
        self.packets = np.asarray(packets, float)
        if self.packets.ndim != 2 or self.packets.shape[1] != 4 or not len(self.packets):
            raise ValueError('Expected a nonempty list of [A,lambda,a,p].')
        if not np.isfinite(self.packets).all() or np.any(self.packets[:, [0, 2]] <= 0):
            raise ValueError('Require finite parameters and positive A,a.')
        seeds, self.indices = np.unique(self.packets[:, :2], axis=0, return_inverse=True)
        self.kernels = transverse.Kernels(seeds, h=h, eps=eps, nt=nt, nd=nd)
        self.h, self.eps = h, eps
        self.a, self.p = self.packets[:, 2:].T
        self.N, self.Kin = self.expand(self.kernels.N), self.expand(self.kernels.Kin)

    def expand(self, matrix):
        return matrix[np.ix_(self.indices, self.indices)]

    def clock_pair(self, s, shifted):
        C = np.exp(s)+self.eps
        chart = np.exp(s)+self.eps*s
        z = old.inverse_shift(s, self.eps, self.h) if shifted else s
        argument = chart-.5j*self.h if shifted else chart
        # Frequency phase is exp(i*p*z), NOT exp(i*p*argument).
        log_amplitude = -self.a*argument**2+1j*self.p*z
        prefactor = C*np.exp(-2*s) if shifted else C*C*np.exp(-2*s)
        return prefactor*np.exp(log_amplitude.conj()[:, None]+log_amplitude[None, :])

    def densities(self, s):
        T, Tp, coefficient, C = self.kernels.at(s)
        T, Tp = self.expand(T), self.expand(Tp)
        zg, zi = self.clock_pair(s, True), self.clock_pair(s, False)
        chart = np.exp(s)+self.eps*s
        z = old.inverse_shift(s, self.eps, self.h)
        Cz = np.exp(z)+self.eps
        slope = (1j*self.p-1)/Cz-2*self.a*(chart-.5j*self.h)+np.exp(z)/(2*Cz*Cz)
        slope0 = (1j*self.p-1)/C-2*self.a*chart+np.exp(s)/(2*C*C)
        static = zi*(C*self.N+self.Kin/C)/2
        ordered = zg*(coefficient*T-Tp/C)
        remainder = zi*(-np.exp(s)*self.N/C+np.exp(s)*self.Kin/C**3)/2
        return dict(energy=zg*T+static, ordered=ordered, remainder=remainder,
                    norm=zi*self.N,
                    ordered_direct=zg*T*(slope.conj()[:, None]+slope[None, :]),
                    remainder_direct=static*(slope0.conj()[:, None]+slope0[None, :]),
                    ordered_boundary=zg*T/C, remainder_boundary=static/C)

    def integrate(self, left=-10., right=4., panels=28, order=10):
        if not np.isfinite([left, right]).all() or left >= right:
            raise ValueError('Invalid clock interval.')
        if any(isinstance(n, bool) or not isinstance(n, int) for n in [panels, order]) or panels < 1 or order < 4:
            raise ValueError('Invalid composite quadrature counts.')
        nodes, weights = leggauss(order)
        edges = np.linspace(left, right, panels+1)
        names = ['energy', 'ordered', 'remainder', 'norm', 'ordered_direct', 'remainder_direct']
        forms = {name: np.zeros_like(self.N) for name in names}
        for lo, hi in zip(edges, edges[1:]):
            for s, ds in zip(lo+(nodes+1)*(hi-lo)/2, weights*(hi-lo)/2):
                values = self.densities(s)
                for name in names:
                    forms[name] += ds*values[name]
        forms = {name: hermitian(matrix) for name, matrix in forms.items()}
        endpoint = [self.densities(s) for s in [left, right]]
        errors, boundary_sizes = {}, {}
        for name in ['ordered', 'remainder']:
            boundary = endpoint[1][name+'_boundary']-endpoint[0][name+'_boundary']
            denominator = max(1., np.linalg.norm(forms[name]), np.linalg.norm(forms[name+'_direct']))
            errors[name] = float(np.linalg.norm(forms[name+'_direct']-forms[name]-boundary)/denominator)
            boundary_sizes[name] = float(np.linalg.norm(boundary)/max(1., np.linalg.norm(forms['energy'])))
        if max(errors.values()) > 2e-8:
            raise ArithmeticError(f'Unresolved integration-by-parts identity: {errors}')
        forms['response'] = forms['ordered']+forms['remainder']
        return forms, dict(integration_by_parts_errors=errors, boundary_over_energy=boundary_sizes,
                           projected_gram_oracle_error=float(self.kernels.oracle_error))


def spectrum(forms):
    E = forms['energy']
    W, condition = old.whitening(E)
    if condition['whitening_residual'] > 2e-8:
        raise ArithmeticError('Unresolved energy whitening.')
    result = dict(conditioning=condition)
    for name in ['ordered', 'response', 'remainder', 'norm']:
        M = forms[name]
        H = hermitian(W.conj().T@M@W)
        values, vectors = eigh(H)
        witness = W@vectors[:, 0]
        residual = np.linalg.norm(M@witness-values[0]*(E@witness))/max(
            1., np.linalg.norm(M@witness), abs(values[0])*np.linalg.norm(E@witness))
        if residual > 2e-8:
            raise ArithmeticError('Unresolved generalized eigenpair.')
        result[name] = dict(minimum=float(values[0]), maximum=float(values[-1]),
                            diagonal_minimum=float(np.min(np.diag(M).real/np.diag(E).real)),
                            witness_real=witness.real.tolist(), witness_imag=witness.imag.tolist(),
                            residual=float(residual))
    return result


def absolute_angle_reference(packets, h=.3, nt=32, ns=200):
    """Separate absolute-angle grid and recursive Gaussian moments.

    Shares the source and inverse-chart helpers, but not Kernels.at(),
    its explicit quartic polynomial, or the reduced/static IBP formulas.
    """
    theta = 2*np.pi*np.arange(nt)/nt
    data = [transverse.single.sources(A, lam, h, theta) for A, lam, _, _ in packets]
    widths = data[0][0]
    b = np.concatenate([v[1] for v in data])
    amp = np.exp(np.concatenate([v[2] for v in data]))
    a = np.repeat([v[2] for v in packets], nt)
    p = np.repeat([v[3] for v in packets], nt)
    Z0, _, _, moment0 = old.gaussian_gram(b, amp, widths, np.eye(5))
    base = np.exp(2.5*np.log(np.pi)-.5*np.linalg.slogdet(np.diag(2*widths))[1])
    kin = np.zeros_like(Z0)
    for d in np.array([[1, 1, 0, 0, 0], [0, 0, 1, 1, 1], [1, -1, 0, 0, 0], [0, 0, 1, -1, 0]]):
        row, constant = -2*widths*d, b@d
        kin += h*h*(constant.conj()[:, None]*constant[None, :]+
                    (constant.conj()[:, None]+constant[None, :])*moment0(row)+moment0(row, row))
    nodes, weights = leggauss(ns)
    nodes, weights = -10+(nodes+1)*7, weights*7
    F = np.array([0., 0., 1., 1., 1.])
    out = {name: np.zeros((len(packets), len(packets)), complex) for name in ['energy', 'response', 'norm']}
    for s, ds in zip(nodes, weights):
        C, chart = np.exp(s)+1, np.exp(s)+s
        z = old.inverse_shift(s, 1., h)
        Cz, r = np.exp(z)+1, np.exp((z-s)/2)
        L = np.eye(5, dtype=complex)*r
        L[4, 4], L[4, 2:4] = 1, 2*(r-1)
        Z, _, _, moment = old.gaussian_gram(b, amp, widths, L)
        unshift = C*np.exp(-s-a*chart**2+1j*p*s)
        shift = np.sqrt(C)*np.exp(-s-a*(chart-.5j*h)**2+1j*p*z)
        static = unshift.conj()[:, None]*unshift[None, :]*Z0*(C+kin/C)/2
        growing = shift.conj()[:, None]*shift[None, :]*Z*(1+moment(F, F)/2+moment(F, F, F, F)/4)
        slope0 = (1j*p-1)/C-2*a*chart+np.exp(s)/(2*C*C)
        slope = (1j*p-1)/Cz-2*a*(chart-.5j*h)+np.exp(z)/(2*Cz*Cz)
        values = dict(energy=static+growing,
                      response=static*(slope0.conj()[:, None]+slope0[None, :])+
                      growing*(slope.conj()[:, None]+slope[None, :]),
                      norm=unshift.conj()[:, None]*unshift[None, :]*Z0)
        for name, value in values.items():
            out[name] += ds*value.reshape(len(packets), nt, len(packets), nt).mean(axis=(1, 3))/base
    return out


def validation():
    packets = [[1., .4, 1., 0.], [1.2, .7, 1., 0.], [1.5, .9, 1., 0.]]
    forms, checks = Integrated(packets).integrate()
    errors = []
    for i, (A, lam, a, _) in enumerate(packets):
        ref = diagonal.projected(A=A, lam=lam, a=a, h=.3, ns=200, nt=32, nd=128)
        errors.append({key: float(abs(forms[name][i, i]-ref[key])/max(1., abs(ref[key])))
                       for name, key in [('energy', 'E'), ('response', 'R')]})
    assert max(max(e.values()) for e in errors) < 2e-8
    # Reversing h conjugates the p=0 matrices and preserves their spectra.
    conjugate, _ = Integrated(packets, h=-.3).integrate()
    sign_errors = {name: float(np.linalg.norm(conjugate[name]-value.conj())/max(1., np.linalg.norm(value)))
                   for name, value in forms.items()}
    assert max(sign_errors.values()) < 2e-9
    # A duplicate packet is a true unresolved mode, not a license to truncate.
    duplicate, _ = Integrated([packets[0], packets[0]]).integrate()
    try:
        spectrum(duplicate)
    except ValueError as exc:
        rejection = str(exc)
        assert 'insufficiently conditioned' in rejection
    else:
        raise AssertionError('Duplicate packets were not rejected.')
    mixed = [[1., .4, .5, -2.], [1.2, .7, 1., 0.], [1.5, .9, 2., 2.]]
    k = Integrated(mixed)
    actual, _ = k.integrate()
    reference = absolute_angle_reference(mixed)
    reference_errors = {name: float(np.linalg.norm(value-actual[name])/max(1., np.linalg.norm(value)))
                        for name, value in reference.items()}
    assert max(reference_errors.values()) < 2e-8
    finite, boundary_check = k.integrate(left=-1., right=.2, panels=6, order=14)
    omitted = float(np.linalg.norm(finite['ordered_direct']-finite['ordered'])/np.linalg.norm(finite['energy']))
    assert omitted > .01
    return dict(diagonal_checks=errors, positive_h_checks=checks,
                conjugation_errors=sign_errors, duplicate_rejection=rejection,
                mixed_absolute_angle_matrix_errors=reference_errors,
                finite_interval_check=dict(left=-1., right=.2, checks=boundary_check,
                                           error_if_boundary_omitted=omitted),
                transverse_independent_check=transverse.independent_check())


def run_case(case, settings):
    runs, first, witness = [], None, None
    for setting in case.get('settings', settings):
        start = time.monotonic()
        k = Integrated(case['packets'], h=case.get('h', .3), eps=case.get('eps', 1.),
                       nt=setting['nt'], nd=setting['nd'])
        forms, checks = k.integrate(**{p: setting[p] for p in ['left', 'right', 'panels', 'order']})
        extrema = spectrum(forms)
        # Check the already-proved static bound in the complete finite subspace.
        assert max(abs(extrema['remainder'][p]) for p in ['minimum', 'maximum']) <= 1/(4*k.eps)+2e-8
        if first is None:
            first = forms
            w = extrema['response']
            witness = np.array(w['witness_real'])+1j*np.array(w['witness_imag'])
        changes = {name: float(np.linalg.norm(M-first[name])/max(1., np.linalg.norm(M))) for name, M in forms.items()}
        quotient = float(np.vdot(witness, forms['response']@witness).real/np.vdot(witness, forms['energy']@witness).real)
        assert max(changes.values()) < 2e-8
        if runs:
            assert abs(quotient-runs[0]['spectrum']['response']['minimum']) < 2e-8
            assert abs(extrema['response']['minimum']-runs[0]['spectrum']['response']['minimum']) < 2e-8
        record = dict(quadrature=setting, checks=checks, spectrum=extrema, matrix_changes=changes,
                      original_witness_quotient=quotient,
                      matrices={name: transverse.matrix_record(M) for name, M in forms.items()},
                      seconds=time.monotonic()-start)
        runs.append(record)
        print(json.dumps(dict(case=case['name'], quadrature=setting,
                              response=extrema['response']['minimum'], ordered=extrema['ordered']['minimum'],
                              diagonal=extrema['response']['diagonal_minimum'],
                              condition=extrema['conditioning']['normalized_energy_condition'])), flush=True)
    return dict(**case, runs=runs)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    np.seterr(over='raise', invalid='raise', divide='raise')
    checks = validation()
    print('Diagonal, conjugation, transverse derivative and unresolved-mode checks passed.', flush=True)
    settings = [dict(nt=24, nd=96, left=-10., right=4., panels=28, order=10),
                dict(nt=40, nd=160, left=-12., right=4.5, panels=33, order=14)]
    cases = [dict(name='transverse_superposition', packets=[[1., .4, 1., 0.], [1.2, .7, 1., 0.], [1.5, .9, 1., 0.]]),
             dict(name='clock_frequency_superposition', packets=[[1.5, .9, 1., p] for p in [-4., -2., 0., 2., 4.]]),
             dict(name='mixed_width_frequency_superposition', packets=[[1., .4, .5, -2.], [1.2, .7, 1., 0.], [1.5, .9, 2., 2.]])]
    adverse_settings = [dict(nt=64, nd=512, left=-10., right=4., panels=56, order=24),
                        dict(nt=96, nd=768, left=-12., right=4.5, panels=66, order=28)]
    cases += [dict(name='negative_clock_span_33', h=.05,
                   packets=[[10., 4., 1., float(4*j)] for j in range(-16, 17)], settings=adverse_settings),
              dict(name='negative_transverse_clock_span_9', h=.05,
                   packets=[[10., lam, 1., p] for lam in [3., 4., 5.] for p in [-4., 0., 4.]],
                   settings=adverse_settings)]
    results = [run_case(case, settings) for case in cases]
    root = Path(__file__).resolve().parents[1]
    sources = ['scripts/projected_integrated_response_probe.py', 'scripts/projected_kernel_matrix_probe.py',
               'scripts/zero_charge_response_probe.py', 'scripts/matter_energy_gram_probe.py',
               'scripts/displaced_signed_response_probe.py',
               'UnifiedTheory/Audit/KFCausalClockResponseTransport.lean',
               'UnifiedTheory/Audit/KFCausalShiftedGaussianPhysicalProfile.lean',
               'UnifiedTheory/Audit/KFCausalProjectedClockResponse.lean',
               'data/projected_hamiltonian_response_audit.json']
    report = dict(kind='Exploratory full clock-integrated projected complex response matrices',
                  physical_time=0., couplings=dict(mass2=1., quartic=1., vacuum=1.),
                  default_parameters=dict(h=.3, eps=1.), packet_columns=['A', 'lambda', 'clock_width', 'clock_frequency'],
                  checks=checks, cases=results,
                  normalization='All matrices divide out the common transverse unprojected norm. Individual positive packet normalizers are omitted consistently by a diagonal basis rescaling, preserving the finite span and generalized spectra. Witness entries refer to this rescaled basis, not unit-normalized packet coefficients.',
                  formulas='clockPair_shift(i,j)=C*exp(-2s)*conj(exp(-a_i*(chart-i*h/2)^2+i*p_i*z))*exp(-a_j*(chart-i*h/2)^2+i*p_j*z), where exp(z)+eps*z=chart-i*h/2. Unshifted clockPair uses C^2*exp(-2s), chart real and z=s. Energy=shiftPair*T+unshiftPair*(C*N+Kin/C)/2; ordered=shiftPair*(coefficient*T-Tprime/C); remainder=unshiftPair*(-exp(s)*N/C+exp(s)*Kin/C^3)/2. Frequencies multiply z, not chart.',
                  source_sha256={p: hashlib.sha256((root/p).read_bytes()).hexdigest() for p in sources},
                  limitations=['Floating quadrature, moments and spectra; no certified clock tails, error enclosure or sign.',
                               'Finite endpoint terms are retained when checking direct/reduced integration by parts; small sampled endpoint terms are not tail certificates.',
                               'Numerical transcription is not formalized in Lean; checks share source and inverse-chart helpers.',
                               'All modes are retained; unresolved energy Gram modes are rejected.',
                               'Finite negative quotients do not refute a uniform finite lower bound.',
                               'No evolution derivative, controlled regulator limit, necessary model revision, or physical TOE is established.'])
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(report, indent=2, allow_nan=False)+'\n')
    print(args.output, flush=True)


if __name__ == '__main__':
    main()
