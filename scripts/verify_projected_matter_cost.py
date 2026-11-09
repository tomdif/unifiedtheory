#!/usr/bin/env python3
"""Independently check recorded projected-cost matrices and proof provenance.

This verifies finite matrix evidence; it does not certify quadrature errors.
"""
import hashlib
import json
from pathlib import Path
import numpy as np
from scipy.linalg import eigh


def sha(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()


def unpack(r):
    return np.array(r['real'])+1j*np.array(r['imag'])


def main():
    root = Path(__file__).resolve().parents[1]
    path = root/'data/projected_matter_cost_probe.json'
    report = json.loads(path.read_text())
    assert report['physical_time']==0. and report['couplings']==dict(mass2=1., quartic=1., vacuum=1.)
    assert all(sha(root/p)==h for p, h in report['source_sha256'].items())
    base_info = report['baseline_report']
    assert sha(root/base_info['path'])==base_info['sha256']
    base = json.loads((root/base_info['path']).read_text())
    assert all(sha(root/p)==h for p, h in base['source_sha256'].items())
    assert len(report['checks'])==6
    assert max(max(c['errors'].values()) for c in report['checks'])<2e-9
    assert len(report['cases'])==len(base['cases'])==5
    checks = []
    for case, base_case in zip(report['cases'], base['cases']):
        assert case['name']==base_case['name'] and case['packets']==base_case['packets']
        assert case['eps']==1. and case['h']==base_case.get('h', .3)
        assert len(case['runs'])==len(base_case['runs'])==2
        previous = None
        for run, old_run in zip(case['runs'], base_case['runs']):
            assert run['quadrature']==old_run['quadrature']
            forms = {n: unpack(r) for n, r in run['matrices'].items()}
            n = len(case['packets'])
            assert all(M.shape==(n,n) and np.isfinite(M).all() for M in forms.values())
            for name, M in forms.items():
                assert np.linalg.norm(M-M.conj().T)<2e-10*max(1., np.linalg.norm(M)), name
            E = forms['energy']
            D = np.sqrt(E.diagonal().real)
            assert np.all(D>0)
            ev = np.linalg.eigvalsh(E/D[:,None]/D[None,:])
            assert ev[0]>1e-10*ev[-1]
            # Cholesky whitening differs from the eigendecomposition used by the probe.
            L = np.linalg.cholesky(E)
            W = np.linalg.solve(L.conj().T, np.eye(n))
            assert np.linalg.norm(W.conj().T@E@W-np.eye(n),2)<2e-8
            eps, h = case['eps'], case['h']
            beta = 800*np.exp(4*np.pi/3)*h**4/eps**5
            slope = beta*(forms['H0']/2+forms['H1']/4)
            expected = dict(coarse_loss=(forms['A0']/2+forms['A1']/4)/(2*eps)+slope,
                sharp_loss=2/eps**2*((forms['B0']-forms['E0'])/2+(forms['B1']-forms['E1'])/4)+slope)
            expected['bound_gap']=forms['response']+expected['sharp_loss']+forms['norm']/2
            expected['coarse_gap']=forms['response']+expected['coarse_loss']+forms['norm']/2
            for name, M in expected.items():
                assert np.linalg.norm(W.conj().T@(M-forms[name])@W,2)<2e-8
            errors = {}
            for name in ['energy','norm','response']:
                errors[name]=float(np.linalg.norm(W.conj().T@(forms[name]-unpack(old_run['matrices'][name]))@W,2))
                assert errors[name]<2e-8
                assert abs(errors[name]-run['baseline_energy_scaled_errors'][name])<2e-8
            for name, M in forms.items():
                values = eigh(M,E,eigvals_only=True)
                saved = run['spectra'][name]
                scale = max(1.,np.max(abs(values)))
                assert abs(values[0]-saved['minimum'])<2e-8*scale
                assert abs(values[-1]-saved['maximum'])<2e-8*scale
                w=np.array(saved['max_witness_real'])+1j*np.array(saved['max_witness_imag'])
                assert abs(np.vdot(w,E@w).real-1)<2e-8
                assert abs(np.vdot(w,M@w).real-saved['maximum'])<2e-8*scale
                if name in ['A0','A1','B0','B1','E0','E1','H0','H1','bound_gap','coarse_gap']:
                    assert values[0]>=-2e-8*scale
            changes = {}
            if previous is not None:
                for name,M in forms.items():
                    changes[name]=float(np.linalg.norm(W.conj().T@(M-previous[name])@W,2)/
                        max(1.,np.linalg.norm(W.conj().T@M@W,2)))
                    assert changes[name]<2e-6
                    assert abs(changes[name]-run['refinement_scaled_changes'][name])<2e-8
            else:
                assert not run['refinement_scaled_changes']
            previous=forms
            checks.append(dict(case=case['name'], quadrature=run['quadrature'], full_dimension=n,
                rank_truncated=False, baseline_energy_scaled_errors=errors,
                refinement_scaled_changes=changes,
                response_minimum=run['spectra']['response']['minimum'],
                coarse_loss_maximum=run['spectra']['coarse_loss']['maximum'],
                sharp_loss_maximum=run['spectra']['sharp_loss']['maximum']))
    target=root/'data/projected_matter_cost_validation.json'
    target.write_text(json.dumps(dict(probe_report_sha256=sha(path),verifier_sha256=sha(Path(__file__)),
        checks=checks,limitations='Finite floating matrices, spectra and refinement checks only; no certified integration or uniform estimate.'),indent=2)+'\n')
    print('Independent matrix verification passed: ten runs, five complete finite spaces; no rank truncation.')
    print(target)


if __name__=='__main__':
    main()
