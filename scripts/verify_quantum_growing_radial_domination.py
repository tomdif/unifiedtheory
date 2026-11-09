#!/usr/bin/env python3
"""Independently verify the growing-radial-domination audit and preserved evidence."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess

EXPECTED = {'KFCausalClockFloorRadialYosidaSymbol': 11, 'KFCausalBoundedDirectionalLeibniz': 3, 'KFCausalClockFloorRadialYosidaDerivative': 5, 'KFCausalClockFloorRadialYosidaKinetics': 9, 'KFCausalClockFloorRadialYosidaStrip': 11, 'KFCausalClockFloorRadialYosidaOrderedTransport': 14, 'KFCausalClockFloorRadialYosidaEnergy': 7, 'KFCausalClockFloorRadialYosidaForm': 3, 'KFCausalClockFloorRadialYosidaReference': 4, 'KFCausalClockFloorRadialYosidaGrowing': 5, 'KFCausalClockFloorRadialYosidaOutputAccretivity': 5, 'KFCausalClockFloorGrowingRadialFormIdentity': 4, 'KFCausalClockFloorGrowingRadialMultiplierForm': 5, 'KFCausalClockFloorRadialYosidaPairing': 2, 'KFCausalClockFloorRadialYosidaDomain': 4, 'KFCausalClockFloorGrowingRadialDomination': 5, 'KFCausalChargedCoolingBoundaryScore': 7, 'KFCausalChargedCoolingMarginalScore': 4, 'KFCausalAngularMassDeterminant': 10}
EXTRA_ANALYTIC = {'analytic_common_complex_mass_abel_angular_closure': {'path': 'data/quantum_common_complex_mass_abel_angular_closure_20261022.txt', 'sha256': '99d4587524c668b6c9d22589c89f21c2800e6995e300f23cb990d8f8f57f4585', 'status': 'Independently reviewed analytic proof candidate, not a Lean response theorem. Actual Abel-circle constraints, a compact-angle ODE barrier, Gaussian mixing and Hardy modes combine with the proved same-packet score to bound the mass-channel geometric response by536*fraction for one common arbitrary complex neutral source and P=1, under the original strict Gaussian margins. The quartic channel, general sources/polynomials and full formal attachment remain open.'}}
SCOPE = 'The actual growing Hamiltonian G now controls the separate maximal radial kinetic operator Kr on its entire operator domain: DomG is contained in DomKr and norm(Kr x)<=norm(G x). The conclusion uses epsilon>0, h!=0 and abs(h)<=pi*epsilon/3, arbitrary original mass/quartic/vacuum parameters, the original weighted joint graph closure and its actual charge-averaged growing completion. No radial domain, common operator core, separate-factor maximal-domain equality, desired bound, or zero-charge condition is assumed. Kr is the self-adjoint real multiplier [momentumScale^2*(u0^2+u1^2)+v0^2+v1^2]/[2*(exp(s)+epsilon)] in the actual charge coordinates. The exact one-half kinetic normalization and weighted moment integrability are derived on every actual growing-output graph pair. Polarization gives the two growing kinetic-row pairing. The actual bounded multipliers M_N=N*Kr/(N+Kr) preserve the original reference form: a strong maximal momentum Leibniz theorem supplies the static defect, a holomorphic half-clock-strip multiplier transports all natural Q, PhiQ and Phi^2Q graphs, and a bounded affine map preserves the literal weighted simultaneous graph closure, including zero couplings. Charge covariance transports the reference action to the averaged form. The static correction vanishes under the growing selector. A bounded-map closure argument then gives an actual action on every vector of the completed growing form. The shifted potential multiplier is bounded and has nonnegative real part. Testing G with the actual M_N form vector yields norm(M_N x)^2<=Re inner(Gx,M_N x), hence norm(M_N x)<=norm(Gx). Fatou derives the missing square moment and gives the full Kr domain and norm bound. Separately, the exact coherent cooling boundary remainder is positive: C-K/a=(a^2+b^2)/(4a^2)*(C+B/T), using existing positive kernels and the inverse-width Schur product. A literal Gaussian boundary integral and exact radial derivative attach this to the original finite coherent charged marginal f. Its actual derivatives obey (scoreRate/2+1/a)*f-(scoreRate/2)*v*f_v<=-f_a, with the same amplitudes and positive widths, alpha>0 and abs(b)<a. This is a proved marginal score inequality, not a Lean proof of the remaining linked mass discriminant or an unrestricted response bound. A separate independently reviewed analytic artifact gives a mass-only closure candidate for common arbitrary complex neutral source and P=1, using actual Abel-circle constraints, an angular ODE barrier, Gaussian mixing, Hardy modes and a2450/9*fraction Young loss below488*fraction. Ten further Lean theorems certify the polynomial quartic positivity, threshold comparison, exact Riccati transport identity and positive boundary derivative at any positive determinant zero. They do not yet attach the actual angular ODE or prove the global moment barrier. The additional analytic steps and full mass response attachment are not Lean-certified; the quartic channel is not covered. Joint H/G operator control and graph approximation, the uniform G_N*(1+H(s))^(-1) estimate, stronger evolved domains, the ordered-static common-coordinate representative and the mixed estimate remain open. The original full-form range restriction in the previous static/growing domain identity has not been removed. General mixed/differing neutral sources and general neutral polynomials remain outside the proved response bounds. General curved gravity, interacting Standard Model dynamics in the same model, microscopic law/phase selection, controlled physical limits and empirical identification remain unproved. Earlier phase/harmonic identification requires revision. A physical TOE is not proved. This checkpoint adds 118 theorems in 19 modules, preserves 3287 parent source/script hashes and adds 21 for 3308 total; the root extends from 8901 to 8920 lines. All 10 parent analytic artifacts and 23 numerical files remain unchanged, with one new reviewed analytic artifact for11 total. Standard axioms only.'
PARENT = 'data/quantum_static_growing_domains_audit.json'
PARENT_SHA = '6a272cefe108b2f0cb8c2bd1a4889dbb7fcac058d4e313d02eb76cd1f7fc0642'
REPORT = 'data/quantum_growing_radial_domination_audit.json'
SCRIPTS = ['scripts/quantum_growing_radial_domination_audit.py',
           'scripts/verify_quantum_growing_radial_domination.py']
ALLOWED = {'propext','Classical.choice','Quot.sound'}
BAD = r': error|: warning|sorryAx|PANIC'


def sha(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()


def declarations(name, source):
    prefix='UnifiedTheory.Audit.'+name+'.'
    names={prefix+n for n in re.findall(r'^theorem (\S+)',source,re.M)}
    printed={prefix+n for n in re.findall(r'^#print axioms (\S+)',source,re.M)}
    assert names==printed and len(names)==EXPECTED[name]
    # Remove Lean comments before checking executable escape hatches.
    body=re.sub(r'/\-.*?\-/', '', source, flags=re.S)
    assert not re.search(r'\b(sorry|admit|axiom|unsafe)\b',body)
    return names


def dependencies(log):
    parsed=re.findall(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]",log)
    audits={n:sorted(x.strip() for x in xs.split(',') if x.strip()) for n,xs in parsed}
    assert len(parsed)==len(audits)
    assert all(set(xs)<=ALLOWED for xs in audits.values())
    assert not re.search(BAD,log)
    return audits

def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--overlay',required=True,type=Path)
    args=parser.parse_args()
    root=Path(__file__).resolve().parents[1]; overlay=args.overlay.resolve()
    report=json.loads((root/REPORT).read_text()); parent=json.loads((root/PARENT).read_text())
    assert report['previous_report']==dict(path=PARENT,sha256=PARENT_SHA) and sha(root/PARENT)==PARENT_SHA
    old=parent['source_sha256']; hashes=report['source_sha256']
    assert len(old)==3287 and len(hashes)==3287+len(EXPECTED)+2
    assert all(hashes[p]==h for p,h in old.items())
    assert all(sha(root/p)==h for p,h in hashes.items())
    additions={'UnifiedTheory/Audit/'+n+'.lean' for n in EXPECTED}|set(SCRIPTS)
    assert set(hashes)-set(old)==additions
    assert [Path(x['source']).stem for x in report['modules']]==list(EXPECTED)
    logs=overlay/'quantum-growing-radial-domination-audit'
    for item in report['modules']:
        name=Path(item['source']).stem; source=(root/item['source']).read_text()
        output=overlay/'UnifiedTheory/Audit'/(name+'.olean')
        assert item['command']==['lean','-j1','-o',str(output),item['source']]
        log=logs/(name+'.log')
        assert item['exit_code']==0 and item['log_sha256']==sha(log)
        audits=dependencies(log.read_text())
        assert set(audits)==declarations(name,source) and audits==item['audited_declarations']
        assert output.is_file() and not output.is_symlink()
        assert not (root/'.lake/build/lib/lean/UnifiedTheory/Audit'/(name+'.olean')).exists()
    assert report['new_lean_theorem_count']==sum(EXPECTED.values())
    text=(root/'UnifiedTheory.lean').read_text()
    suffix=''.join('import UnifiedTheory.Audit.'+n+'\n' for n in EXPECTED)
    assert text.endswith(suffix) and len(text.splitlines())==8901+len(EXPECTED)
    assert hashlib.sha256(text[:-len(suffix)].encode()).hexdigest()==parent['root_check']['source_sha256']
    assert report['root_check']==dict(command=['lean','-j1','UnifiedTheory.lean'],exit_code=0,empty_log=True,
        source_sha256=sha(root/'UnifiedTheory.lean'),log_sha256=sha(logs/'root-import.log'),appended_imports=list(EXPECTED))
    assert not (logs/'root-import.log').read_text().strip()
    old_analytic={k:v for k,v in parent.items() if k.startswith('analytic_')}
    new_analytic={k:v for k,v in report.items() if k.startswith('analytic_')}
    assert len(old_analytic)==10 and new_analytic==dict(**old_analytic,**EXTRA_ANALYTIC)
    assert all(sha(root/v['path'])==v['sha256'] for v in new_analytic.values())
    assert report['numerical_evidence']==parent['numerical_evidence']
    numerical=[v for v in report['numerical_evidence'].values() if isinstance(v,dict) and 'path' in v]
    assert len(numerical)==23 and all(sha(root/v['path'])==v['sha256'] for v in numerical)
    assert report['scope']==SCOPE and report['lean_toolchain']==(root/'lean-toolchain').read_text().strip()
    print('Verified '+str(sum(EXPECTED.values()))+' Lean theorems, '+str(len(hashes))+' source/script hashes,')
    print('exact root extension, all23 numerical files and all analytic artifacts; standard axioms only.')


if __name__=='__main__':
    main()
