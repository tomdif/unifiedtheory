#!/usr/bin/env python3
"""Test ordinary initial field moments against actual final projected moments.

The p=0 comparison has a separate Lean proof. For p=1,2 these complete
finite-space tests examine the tempting coefficient-one extension. Floating
quadrature is not a certified counterexample or a uniform comparison.
"""
import argparse
import hashlib
import json
from pathlib import Path
import time

import numpy as np
from numpy.polynomial.legendre import leggauss
from scipy.linalg import eigh
import projected_integrated_response_probe as baseline
import projected_kernel_matrix_probe as transverse
import projected_matter_cost_probe as costs
import matter_energy_gram_probe as old


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


class Moments(baseline.Integrated):
    def __init__(self, *args, **kwargs):
        super().__init__(*args, **kwargs)
        self.initial = self.transverse_moments(np.eye(5))

    def transverse_moments(self, L):
        k = self.kernels
        H = 2*(L.T@k.W@L).real
        if np.linalg.eigvalsh(H)[0] <= 0:
            raise ArithmeticError('Nonpositive Gaussian precision.')
        V = .5*np.linalg.inv(H)
        B, D = k.b@L, k.c@L
        matrices = [np.zeros((k.n, k.n), complex) for _ in range(3)]
        for i in range(k.n):
            for j in range(k.n):
                lin = B[i].conj()+D[j]
                mu = lin@V
                Z = np.exp(2.5*np.log(np.pi)-.5*np.linalg.slogdet(H)[1]
                           +.5*np.sum(lin*mu, axis=-1)+k.la[i]+k.lc[j]-k.logbase)
                for M, P in zip(matrices, [1, costs.m2(mu, V, costs.F, costs.F),
                                          costs.m4(mu, V, costs.F, costs.F)]):
                    M[i, j] = k.aw@(Z*P)
        return [self.expand(baseline.hermitian(M)) for M in matrices]

    def densities(self, s):
        delta = old.inverse_shift(s, self.eps, self.h)-s
        r = np.exp(delta/2)
        L = np.eye(5, dtype=complex)*r
        L[4, 4], L[4, 2:4] = 1, 2*(r-1)
        final = self.transverse_moments(L)
        pair1 = self.clock_pair(s, True)
        pair0 = np.exp(-2*delta.real)*pair1
        out = {f'initial{p}': pair0*M for p, M in enumerate(self.initial)}
        out.update({f'final{p}': pair1*M for p, M in enumerate(final)})
        C = np.exp(s)+self.eps
        out['energy'] = out['final0']+.5*out['final1']+.25*out['final2']+\
            self.clock_pair(s, False)*(C*self.N+self.Kin/C)/2
        return out

    def integrate_moments(self, setting):
        nodes, weights = leggauss(setting['order'])
        edges = np.linspace(setting['left'], setting['right'], setting['panels']+1)
        forms = {name: np.zeros_like(self.N) for name in
                 ['initial0', 'initial1', 'initial2', 'final0', 'final1', 'final2', 'energy']}
        for lo, hi in zip(edges, edges[1:]):
            for s, ds in zip(lo+(nodes+1)*(hi-lo)/2, weights*(hi-lo)/2):
                for name, value in self.densities(s).items():
                    forms[name] += ds*value
        return {name: baseline.hermitian(M) for name, M in forms.items()}


def reference_density(packets, s, h, nt=64):
    """Separate absolute-angle torus and recursive Gaussian moments."""
    theta = 2*np.pi*np.arange(nt)/nt
    data = [transverse.single.sources(A, lam, h, theta) for A, lam, _, _ in packets]
    widths = data[0][0]
    b = np.concatenate([d[1] for d in data])
    amp = np.exp(np.concatenate([d[2] for d in data]))
    a, p = [np.repeat([v[col] for v in packets], nt) for col in [2, 3]]
    z = old.inverse_shift(s, 1., h)
    delta, C, chart = z-s, np.exp(s)+1, np.exp(s)+s
    r = np.exp(delta/2)
    L = np.eye(5, dtype=complex)*r
    L[4, 4], L[4, 2:4] = 1, 2*(r-1)
    A = np.sqrt(C)*np.exp(-s-a*(chart-.5j*h)**2+1j*p*z)
    base = np.exp(2.5*np.log(np.pi)-.5*np.linalg.slogdet(np.diag(2*widths))[1])
    out = {}
    for name, T, amplitude in [('initial', np.eye(5), np.exp(-delta)*A), ('final', L, A)]:
        Z, _, _, moment = old.gaussian_gram(b, amp, widths, T)
        pair = amplitude.conj()[:, None]*amplitude[None, :]
        for power in range(3):
            P = 1 if power == 0 else moment(*([costs.F]*(2*power)))
            M = pair*Z*P
            out[name+str(power)] = M.reshape(len(packets), nt, len(packets), nt).mean(axis=(1, 3))/base
    return out


def spectra(forms):
    out = {}
    for p in range(3):
        I, F = forms[f'initial{p}'], forms[f'final{p}']
        W, condition = old.whitening(F)
        assert condition['whitening_residual'] < 2e-8
        ev, vec = eigh(baseline.hermitian(W.conj().T@I@W))
        w = W@vec[:, -1]
        residual = np.linalg.norm(I@w-ev[-1]*F@w)/max(1., np.linalg.norm(I@w), abs(ev[-1])*np.linalg.norm(F@w))
        assert residual < 2e-8 and ev[0] >= -2e-8
        if p == 0:
            assert ev[-1] <= 1+2e-8
        out[str(p)] = dict(minimum=float(ev[0]), maximum=float(ev[-1]), conditioning=condition,
                          witness_real=w.real.tolist(), witness_imag=w.imag.tolist(), residual=float(residual))
    return out


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', required=True, type=Path)
    args = parser.parse_args()
    np.seterr(over='raise', invalid='raise', divide='raise')
    root = Path(__file__).resolve().parents[1]
    packets = [[A, 0., 1., 0.] for A in [.3, .7, 1.2, 1.8]]
    mixed = [[.3, 0., .5, -2.], [.7, 0., .8, -.5], [1.2, 0., 1.3, .7], [1.8, 0., 2., 2.]]
    checks = []
    for h in [.05, -.05, .3]:
        k = Moments(mixed, h=h, nt=40, nd=160)
        for s in [-2., -.5, .5]:
            actual, ref = k.densities(s), reference_density(mixed, s, h)
            errors = {name: float(np.linalg.norm(actual[name]-M)/max(1., np.linalg.norm(M))) for name, M in ref.items()}
            assert max(errors.values()) < 2e-9, errors
            checks.append(dict(h=h, s=s, packets=mixed, errors=errors))
    print('Nine independent density comparisons passed.', flush=True)
    settings = [dict(nt=32, nd=128, left=-10., right=4., panels=28, order=10),
                dict(nt=48, nd=192, left=-12., right=4.5, panels=44, order=12)]
    cases = []
    for name, h, states in [('four_displacements', .05, packets),
                            ('negative_h', -.05, packets), ('mixed_clock', .3, mixed)]:
        runs, first, first_witnesses = [], None, None
        for setting in settings:
            start = time.monotonic()
            k = Moments(states, h=h, nt=setting['nt'], nd=setting['nd'])
            forms = k.integrate_moments(setting)
            spec = spectra(forms)
            W, energy_condition = old.whitening(forms['energy'])
            changes = {} if first is None else {key: float(np.linalg.norm(W.conj().T@(M-first[key])@W, 2)/
                        max(1., np.linalg.norm(W.conj().T@M@W, 2))) for key, M in forms.items()}
            assert not changes or max(changes.values()) < 2e-7, changes
            if first is None:
                first = forms
                first_witnesses = {p: np.array(v['witness_real'])+1j*np.array(v['witness_imag']) for p, v in spec.items()}
            witness_ratios = {p: old.value(forms['initial'+p], w)/old.value(forms['final'+p], w)
                              for p, w in first_witnesses.items()}
            runs.append(dict(quadrature=setting, spectra=spec, energy_condition=energy_condition,
                             refinement_energy_scaled_changes=changes, first_witness_ratios=witness_ratios,
                             gram_oracle_error=float(k.kernels.oracle_error),
                             matrices={key: transverse.matrix_record(M) for key, M in forms.items()},
                             seconds=time.monotonic()-start))
            print(json.dumps(dict(case=name, maxima={p: v['maximum'] for p, v in spec.items()})), flush=True)
        cases.append(dict(name=name, h=h, eps=1., packets=states, runs=runs))
    sources = ['scripts/projected_initial_moment_probe.py', 'scripts/projected_integrated_response_probe.py',
               'scripts/projected_kernel_matrix_probe.py', 'scripts/projected_matter_cost_probe.py',
               'scripts/matter_energy_gram_probe.py', 'scripts/displaced_signed_response_probe.py',
               'UnifiedTheory/Audit/KFCausalProjectedInitialFieldBound.lean',
               'UnifiedTheory/Audit/KFCausalProjectedInitialVacuumBound.lean',
               'UnifiedTheory/Audit/KFCausalImaginaryShearInterpolation.lean']
    report = dict(kind='Ordinary initial versus final projected field moments', checks=checks, cases=cases,
                  physical_time=0., energy_couplings=dict(mass2=1., quartic=1., vacuum=1.),
                  source_sha256={p: sha(root/p) for p in sources},
                  formulas='initial_p=integral |Phi^p G0|^2; final_p=integral |Phi^p G1|^2, p=0,1,2. G0 retains exp(-Delta)*A. These are ordinary initial field moments, not the transported H_p from the secant bound.',
                  limitations=['Floating quadrature, no certified tail or error enclosure and no formal counterexample.',
                               'Independent density reference shares displaced sources and inverse-clock helper.',
                               'All complex modes retained; unresolved Gram modes rejected without rank truncation.',
                               'Ratios above one challenge only the coefficient-one field extension; they do not refute a larger uniform bound or the physical model.',
                               'The p=0 comparison has a separate Lean proof; the numerical implementation is not Lean-verified.',
                               'No field-energy bound, physical evolution, limit or TOE is established.'])
    args.output.write_text(json.dumps(report, indent=2, allow_nan=False)+'\n')
    print(args.output, flush=True)


if __name__ == '__main__':
    main()
