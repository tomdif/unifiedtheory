#!/usr/bin/env python3
"""Compare actual projected secant costs with full finite-subspace energy.

Independent charge angles and all complex coefficients are retained.
These floating matrices test sufficient estimates, not uniform bounds.
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
import matter_energy_gram_probe as old


F = np.array([0., 0., 1., 1., 1.])
Q = np.array([0., 0., 1., 1., 0.])
COST_NAMES = ['A0', 'A1', 'B0', 'B1', 'E0', 'E1', 'H0', 'H1']


def m2(mu, V, a, b):
    return (mu@a)*(mu@b)+a@V@b


def m4(mu, V, a, b):
    """Gaussian E[(a.x)^2 (b.x)^2], with bilinear complex covariance."""
    ma, mb = mu@a, mu@b
    aa, bb, ab = a@V@a, b@V@b, a@V@b
    return ma*ma*mb*mb+aa*mb*mb+bb*ma*ma+4*ab*ma*mb+aa*bb+2*ab*ab


def unpack(record):
    return np.array(record['real'])+1j*np.array(record['imag'])


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


class Costs(baseline.Integrated):
    def __init__(self, *args, **kwargs):
        super().__init__(*args, **kwargs)
        k = self.kernels
        self.V0 = np.diag(1/(4*k.widths))
        self.initial = {}
        for i in range(k.n):
            for j in range(k.n):
                lin = k.b[i].conj()+k.c[j]
                mu = lin@self.V0
                self.initial[i, j] = (mu, np.exp(.5*np.sum(lin*mu, axis=-1)+k.la[i]+k.lc[j]))

    def densities(self, s):
        k, h, eps = self.kernels, self.h, self.eps
        z = old.inverse_shift(s, eps, h)
        delta = z-s
        C, Cz = np.exp(s)+eps, np.exp(z)+eps
        chart = np.exp(s)+eps*s
        r = np.exp(delta/2)
        L = np.eye(5, dtype=complex)*r
        L[4, 4], L[4, 2:4] = 1, 2*(r-1)
        H = 2*(L.T@k.W@L).real
        if np.linalg.eigvalsh(H)[0] <= 0:
            raise ArithmeticError('Nonpositive Gaussian precision.')
        V = .5*np.linalg.inv(H)
        B, D = k.b@L, k.c@L
        P = (3*np.exp(-delta/2)-2)*Q.astype(complex)
        P[4] = 1
        parts = {name: np.zeros((k.n, k.n), complex) for name in ['vacuum', 'field', 'quartic', 'A0', 'A1', 'H0', 'H1']}
        for i in range(k.n):
            for j in range(k.n):
                lin = B[i].conj()+D[j]
                mu = lin@V
                Z = np.exp(2.5*np.log(np.pi)-.5*np.linalg.slogdet(H)[1]+.5*np.sum(lin*mu, axis=-1)
                           +k.la[i]+k.lc[j]-k.logbase)
                mu0, Z0 = self.initial[i, j]
                parts['vacuum'][i, j] = k.aw@Z
                parts['field'][i, j] = k.aw@(Z*m2(mu, V, F, F))
                parts['quartic'][i, j] = k.aw@(Z*m4(mu, V, F, F))
                parts['A0'][i, j] = k.aw@(Z0*m2(mu0, self.V0, P.conj(), P))
                parts['A1'][i, j] = k.aw@(Z0*m4(mu0, self.V0, P.conj(), P))
                parts['H0'][i, j] = k.aw@(Z*2.25*m2(mu, V, Q, Q))
                parts['H1'][i, j] = k.aw@(Z*9*m4(mu, V, F, Q))
        parts = {name: self.expand(v) for name, v in parts.items()}
        pair1, pairf = self.clock_pair(s, True), self.clock_pair(s, False)
        # timeAmplitude at path zero is exp(-delta)*A, not A.
        pair0 = np.exp(-2*delta.real)*pair1
        defect = eps/C
        physical = eps/Cz
        rho = (eps*physical.imag/(2*h))/(1j*delta/h).real
        if not -2e-12 <= rho <= eps/4+2e-12:
            raise ArithmeticError('Clock secant ratio outside proved range.')
        out = {name: pair0*parts[name] for name in ['A0', 'A1']}
        out.update({name: defect**5*(1-defect)*pair1*parts[name] for name in ['H0', 'H1']})
        out.update(B0=rho*out['A0'], B1=rho*out['A1'],
                   E0=rho*pair1*parts['field'], E1=rho*pair1*parts['quartic'])
        growing = pair1*(parts['vacuum']+.5*parts['field']+.25*parts['quartic'])
        static = pairf*(C*self.N+self.Kin/C)/2
        slope = (1j*self.p-1)/Cz-2*self.a*(chart-.5j*h)+np.exp(z)/(2*Cz*Cz)
        slope0 = (1j*self.p-1)/C-2*self.a*chart+np.exp(s)/(2*C*C)
        out.update(energy=growing+static, norm=pairf*self.N,
                   response=growing*(slope.conj()[:, None]+slope[None, :])+
                            static*(slope0.conj()[:, None]+slope0[None, :]))
        return out

    def integrate_costs(self, setting):
        nodes, weights = leggauss(setting['order'])
        edges = np.linspace(setting['left'], setting['right'], setting['panels']+1)
        forms = {name: np.zeros_like(self.N) for name in COST_NAMES+['energy', 'norm', 'response']}
        for left, right in zip(edges, edges[1:]):
            for s, ds in zip(left+(nodes+1)*(right-left)/2, weights*(right-left)/2):
                for name, value in self.densities(s).items():
                    forms[name] += ds*value
        forms = {name: baseline.hermitian(M) for name, M in forms.items()}
        beta = 800*np.exp(4*np.pi/3)*self.h**4/self.eps**5
        slope = beta*(.5*forms['H0']+.25*forms['H1'])
        forms['coarse_loss'] = (.5*forms['A0']+.25*forms['A1'])/(2*self.eps)+slope
        forms['sharp_loss'] = 2/self.eps**2*(.5*(forms['B0']-forms['E0'])+.25*(forms['B1']-forms['E1']))+slope
        forms['bound_gap'] = forms['response']+forms['sharp_loss']+forms['norm']/2
        forms['coarse_gap'] = forms['response']+forms['coarse_loss']+forms['norm']/2
        return forms


def reference_density(packets, s, h=.3, nt=64):
    """Absolute-angle torus and recursive Wick contractions, sharing sources/chart."""
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
    Z0, _, _, m0 = old.gaussian_gram(b, amp, widths, np.eye(5))
    Z1, _, _, m1 = old.gaussian_gram(b, amp, widths, L)
    A = np.sqrt(C)*np.exp(-s-a*(chart-.5j*h)**2+1j*p*z)
    pair1 = A.conj()[:, None]*A[None, :]
    pair0 = np.exp(-delta)*A
    pair0 = pair0.conj()[:, None]*pair0[None, :]
    P = (3*np.exp(-delta/2)-2)*Q.astype(complex)
    P[4] = 1
    defect, physical = 1/C, 1/(np.exp(z)+1)
    rho = physical.imag/(2*h)/(1j*delta/h).real
    values = dict(A0=pair0*Z0*m0(P.conj(), P), A1=pair0*Z0*m0(P.conj(), P.conj(), P, P),
                  H0=defect**5*(1-defect)*pair1*Z1*2.25*m1(Q, Q),
                  H1=defect**5*(1-defect)*pair1*Z1*9*m1(F, F, Q, Q),
                  E0=rho*pair1*Z1*m1(F, F), E1=rho*pair1*Z1*m1(F, F, F, F))
    values.update(B0=rho*values['A0'], B1=rho*values['A1'])
    base = np.exp(2.5*np.log(np.pi)-.5*np.linalg.slogdet(np.diag(2*widths))[1])
    return {name: M.reshape(len(packets), nt, len(packets), nt).mean(axis=(1, 3))/base for name, M in values.items()}


def independent_checks():
    packets = [[1., .4, .5, -2.], [1.2, .7, 1., 0.], [1.5, .9, 2., 2.]]
    checks = []
    for h in [.3, -.3]:
        k = Costs(packets, h=h, nt=40, nd=160)
        for s in [-1.3, -.2, .6]:
            actual, ref = k.densities(s), reference_density(packets, s, h=h)
            errors = {name: float(np.linalg.norm(actual[name]-M)/max(1., np.linalg.norm(M))) for name, M in ref.items()}
            assert max(errors.values()) < 2e-9, errors
            checks.append(dict(h=h, s=s, errors=errors))
    return checks


def compressed_spectrum(forms):
    W, conditioning = old.whitening(forms['energy'])
    assert conditioning['whitening_residual'] < 2e-8
    out = {}
    for name, M in forms.items():
        H = baseline.hermitian(W.conj().T@M@W)
        ev, vec = eigh(H)
        w = W@vec[:, -1]
        residual = np.linalg.norm(M@w-ev[-1]*forms['energy']@w)/max(1., np.linalg.norm(M@w), abs(ev[-1])*np.linalg.norm(forms['energy']@w))
        assert residual < 2e-8
        out[name] = dict(minimum=float(ev[0]), maximum=float(ev[-1]),
                         max_witness_real=w.real.tolist(), max_witness_imag=w.imag.tolist(), residual=float(residual))
        if name in COST_NAMES+['bound_gap', 'coarse_gap']:
            assert ev[0] >= -2e-8*(1+np.max(abs(ev))), (name, ev[0])
    return out, conditioning, W


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', required=True, type=Path)
    args = parser.parse_args()
    np.seterr(over='raise', invalid='raise', divide='raise')
    root = Path(__file__).resolve().parents[1]
    prior_path = root/'data/projected_integrated_response_probe.json'
    prior = json.loads(prior_path.read_text())
    assert all(sha(root/p)==v for p, v in prior['source_sha256'].items())
    checks = independent_checks()
    print('Six independent absolute-angle/recursive-moment comparisons passed.', flush=True)
    results = []
    for case in prior['cases']:
        runs, first = [], None
        for old_run in case['runs']:
            start = time.monotonic()
            setting = old_run['quadrature']
            k = Costs(case['packets'], h=case.get('h', .3), nt=setting['nt'], nd=setting['nd'])
            forms = k.integrate_costs(setting)
            spec, condition, W = compressed_spectrum(forms)
            errors = {}
            for name in ['energy', 'norm', 'response']:
                reference = unpack(old_run['matrices'][name])
                errors[name] = float(np.linalg.norm(W.conj().T@(forms[name]-reference)@W, 2))
                assert errors[name] < 2e-8, errors
            changes = {} if first is None else {name: float(np.linalg.norm(W.conj().T@(M-first[name])@W, 2)/
                max(1., np.linalg.norm(W.conj().T@M@W, 2))) for name, M in forms.items()}
            assert not changes or max(changes.values()) < 2e-6, changes
            if first is None:
                first = forms
            runs.append(dict(quadrature=setting, baseline_energy_scaled_errors=errors, refinement_scaled_changes=changes,
                             conditioning=condition, spectra=spec,
                             matrices={name: transverse.matrix_record(M) for name, M in forms.items()}, seconds=time.monotonic()-start))
            print(json.dumps(dict(case=case['name'], nt=setting['nt'],
                response_min=spec['response']['minimum'], coarse_loss_max=spec['coarse_loss']['maximum'],
                sharp_loss_max=spec['sharp_loss']['maximum'], bound_gap_min=spec['bound_gap']['minimum'])), flush=True)
        results.append(dict(name=case['name'], packets=case['packets'], h=case.get('h', .3), eps=1., runs=runs))
    sources = list(prior['source_sha256'])+['scripts/projected_matter_cost_probe.py',
        'UnifiedTheory/Audit/KFCausalTransportedFieldPolynomial.lean',
        'UnifiedTheory/Audit/KFCausalProjectedTransportedInitialFormula.lean',
        'UnifiedTheory/Audit/KFCausalProjectedMatterCostDensity.lean',
        'UnifiedTheory/Audit/KFCausalImaginaryShearInterpolation.lean',
        'UnifiedTheory/Audit/KFCausalProjectedHamiltonianNormLower.lean']
    report = dict(kind='Exploratory actual projected matter cost matrices', physical_time=0.,
        couplings=dict(mass2=1., quartic=1., vacuum=1.), checks=checks, cases=results,
        baseline_report=dict(path=str(prior_path.relative_to(root)), sha256=sha(prior_path)),
        source_sha256={p: sha(root/p) for p in sources}, normalization=prior['normalization'],
        formulas='H_i=P_delta^(i+1)*G0, P_delta=q4+(3*exp(-delta/2)-2)*(q2+q3); G0 uses exp(-delta)*A(s). A_i=norm(H_i)^2, B_i=norm(M H_i)^2, E_i=norm(M U_i)^2, H0/H1 here denote slope moments. coarse_loss=(A0/2+A1/4)/(2epsilon)+beta*(H0/2+H1/4); sharp_loss=2/epsilon^2*((B0-E0)/2+(B1-E1)/4)+beta*(H0/2+H1/4). The Lean full lower bounds subtract these losses and norm(P0f)^2/2.',
        limitations=['Floating quadrature and spectra, no certified tails, sign or uniform bound.',
          'Numerical implementation is not formally verified; references share source/inverse-chart helpers.',
          'Costs concern the actual projected means, not diagonal charge averages; all finite complex modes retained.',
          'Finite loss maxima do not establish uniform energy control. Large sufficient costs do not refute the model.',
          'No dynamics, regulator limit, physical identification or TOE is established.'])
    args.output.write_text(json.dumps(report, indent=2, allow_nan=False)+'\n')
    print(args.output, flush=True)


if __name__ == '__main__':
    main()
