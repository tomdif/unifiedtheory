#!/usr/bin/env python3
"""Test the actual signed response on independent-neutral packet spans.

Keeps all eight energy factors and the positive terms in the full response.
Retests the prior field-moment witnesses on this different quadratic form.
Floating integration is not a certified sign or a uniform energy estimate.
"""
import argparse
import hashlib
import json
from pathlib import Path
import time
import numpy as np
from numpy.polynomial.legendre import leggauss
import independent_neutral_moment_probe as family
import projected_integrated_response_probe as baseline
import projected_kernel_matrix_probe as transverse
import matter_energy_gram_probe as old


class Response(family.Moments):
    # Integrated.integrate dispatches through this method, not moment densities.
    densities = baseline.Integrated.densities


def reference(packets, h=.3, nt=48, ns=240):
    """Absolute-angle Gaussian/Wick integral of the direct momentum pairing.

    Does not use Kernels.at, its derivatives, or the reduced-response formula.
    Shares inverse-clock/Gaussian helpers and the admitted source convention.
    """
    theta = 2*np.pi*np.arange(nt)/nt
    widths = np.array([1., 1., 1., 1., 1/32])/(2*abs(h))
    rows, amps = [], []
    for A, B, P, _, _ in packets:
        b = np.zeros((nt, 5), complex)
        b[:, 2] = widths[2]*A*np.cos(theta)+1j*A*np.sin(theta)/(2*h)
        b[:, 3] = widths[3]*A*np.cos(theta)-1j*A*np.sin(theta)/(2*h)
        b[:, 4] = 2*widths[4]*B+1j*P/h
        rows.append(b)
        amps.append(np.exp(-widths[2]*A*A*np.cos(theta)**2/2-widths[4]*B*B))
    b, amp = np.concatenate(rows), np.concatenate(amps)
    a, p = [np.repeat([v[col] for v in packets], nt) for col in [3, 4]]
    Z0, _, _, moment0 = old.gaussian_gram(b, amp, widths, np.eye(5))
    base = np.exp(2.5*np.log(np.pi)-.5*np.linalg.slogdet(np.diag(2*widths))[1])
    kin = np.zeros_like(Z0)
    for d in np.array([[1, 1, 0, 0, 0], [0, 0, 1, 1, 1],
                       [1, -1, 0, 0, 0], [0, 0, 1, -1, 0]]):
        row, constant = -2*widths*d, b@d
        kin += h*h*(constant.conj()[:, None]*constant[None, :]+
                    (constant.conj()[:, None]+constant[None, :])*moment0(row)+moment0(row, row))
    nodes, weights = leggauss(ns)
    nodes, weights = -10+(nodes+1)*7, weights*7
    F = np.array([0., 0., 1., 1., 1.])
    out = {name: np.zeros((len(packets), len(packets)), complex)
           for name in ['energy', 'response', 'norm']}
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


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    np.seterr(over='raise', invalid='raise', divide='raise')
    root = Path(__file__).resolve().parents[1]
    prior_path = root/'data/independent_neutral_moment_probe.json'
    prior = json.loads(prior_path.read_text())
    assert all(sha(root/p) == h for p, h in prior['source_sha256'].items())
    mixed = prior['cases'][2]['packets']
    independent = []
    for h in [.3, -.3]:
        forms, checks = Response(mixed, h=h, nt=40, nd=160).integrate()
        ref = reference(mixed, h)
        errors = {name: float(np.linalg.norm(forms[name]-M)/max(1., np.linalg.norm(M)))
                  for name, M in ref.items()}
        assert max(errors.values()) < 2e-8, errors
        independent.append(dict(h=h, packets=mixed, errors=errors, checks=checks,
                                reference_absolute_angles=48, reference_clock_nodes=240))
    finite, boundary = Response(mixed).integrate(left=-1., right=.2, panels=6, order=14)
    omitted = float(np.linalg.norm(finite['ordered_direct']-finite['ordered'])/
                    np.linalg.norm(finite['energy']))
    assert omitted > .01
    print('Independent direct-pairing references and finite-interval boundary check passed.', flush=True)
    settings = [dict(nt=32, nd=128, left=-10., right=4., panels=28, order=10),
                dict(nt=48, nd=192, left=-12., right=4.5, panels=44, order=12)]
    cases = [dict(name=c['name'], packets=c['packets'], h=c['h'], eps=c['eps'],
                  prior_moment_case=c['name'], settings=settings) for c in prior['cases'][:2]]
    cases.append(dict(name='independent_neutral_adverse_9', h=.05, eps=1.,
                      packets=[[10., B, P, 1., 0.] for B in [7., 8., 9.] for P in [-.3, -.4, -.5]],
                      settings=[dict(nt=64, nd=512, left=-10., right=4., panels=28, order=12),
                                dict(nt=96, nd=768, left=-12., right=4.5, panels=44, order=14)]))
    reports = []
    for case in cases:
        first, response_witness, prior_witnesses, runs = None, None, {}, []
        if 'prior_moment_case' in case:
            previous = next(c for c in prior['cases'] if c['name'] == case['prior_moment_case'])
            assert previous['packets'] == case['packets']
            prior_witnesses = {p: np.array(v['witness_real'])+1j*np.array(v['witness_imag'])
                               for p, v in previous['runs'][-1]['spectra'].items()}
        for setting in case['settings']:
            start = time.monotonic()
            k = Response(case['packets'], h=case['h'], eps=case['eps'], nt=setting['nt'], nd=setting['nd'])
            forms, checks = k.integrate(**{p: setting[p] for p in ['left', 'right', 'panels', 'order']})
            spectrum = baseline.spectrum(forms)
            assert max(abs(spectrum['remainder'][p]) for p in ['minimum', 'maximum']) <= 1/(4*k.eps)+2e-8
            W, _ = old.whitening(forms['energy'])
            changes = {} if first is None else {
                name: float(np.linalg.norm(W.conj().T@(M-first[name])@W, 2)/
                            max(1., np.linalg.norm(W.conj().T@M@W, 2))) for name, M in forms.items()}
            assert not changes or max(changes.values()) < 2e-8, changes
            if first is None:
                first = forms
                w = spectrum['response']
                response_witness = np.array(w['witness_real'])+1j*np.array(w['witness_imag'])
            quotient = old.value(forms['response'], response_witness)/old.value(forms['energy'], response_witness)
            prior_values = {p: dict(response_over_energy=old.value(forms['response'], w)/old.value(forms['energy'], w),
                                    ordered_over_energy=old.value(forms['ordered'], w)/old.value(forms['energy'], w))
                            for p, w in prior_witnesses.items()}
            runs.append(dict(quadrature=setting, checks=checks, spectrum=spectrum,
                             energy_scaled_matrix_changes=changes, original_witness_quotient=quotient,
                             prior_moment_witness_responses=prior_values,
                             matrices={name: transverse.matrix_record(M) for name, M in forms.items()},
                             seconds=time.monotonic()-start))
            print(json.dumps(dict(case=case['name'], response=spectrum['response']['minimum'],
                                  ordered=spectrum['ordered']['minimum'],
                                  prior_moment_witness_responses=prior_values)), flush=True)
        reports.append({**case, 'runs': runs})
    paths = ['scripts/independent_neutral_response_probe.py', 'scripts/independent_neutral_moment_probe.py',
             'scripts/projected_initial_moment_probe.py', 'scripts/projected_integrated_response_probe.py',
             'scripts/projected_kernel_matrix_probe.py', 'scripts/projected_matter_cost_probe.py',
             'scripts/matter_energy_gram_probe.py', 'scripts/displaced_signed_response_probe.py',
             'UnifiedTheory/Audit/KFCausalIndependentNeutralTestFamily.lean',
             'UnifiedTheory/Audit/KFCausalStructuredProjectedHamiltonian.lean',
             'UnifiedTheory/Audit/KFCausalProjectedClockResponse.lean']
    report = dict(kind='Actual full response on independent-neutral packet spans', cases=reports,
                  checks=dict(independent_direct_references=independent,
                              finite_interval_boundary=dict(left=-1., right=.2, checks=boundary,
                                                            error_if_omitted=omitted)),
                  prior_moment_report=dict(path=str(prior_path.relative_to(root)), sha256=sha(prior_path)),
                  source_sha256={p: sha(root/p) for p in paths}, physical_time=0.,
                  energy_couplings=dict(mass2=1., quartic=1., vacuum=1.),
                  limitations=['Floating integration, no certified tails, error enclosure or formal sign.',
                               'All complex modes retained; unresolved Gram modes rejected without truncation.',
                               'References share inverse-clock and Gaussian-integration helpers.',
                               'Positive finite-span results and stable negative finite minima do not prove a uniform lower bound.',
                               'Failure of a sufficient field-moment comparison is distinguished from failure of the actual response bound.',
                               'No new Lean theorem, response identity along the existing propagator, model revision or physical TOE is established.'])
    args.output.write_text(json.dumps(report, indent=2, allow_nan=False)+'\n')
    print(args.output, flush=True)


if __name__ == '__main__':
    main()
