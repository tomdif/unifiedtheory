#!/usr/bin/env python3
"""Check the actual growing radial domination and coherent marginal score and preserved evidence."""
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
    parser.add_argument('--baseline-overlay',required=True,type=Path)
    args=parser.parse_args()
    root=Path(__file__).resolve().parents[1]
    overlay=args.overlay.resolve(); baseline=args.baseline_overlay.resolve()
    assert overlay.is_dir() and baseline.is_dir() and overlay!=baseline
    env=os.environ.copy()
    env['LEAN_PATH']=str(overlay)+os.pathsep+str(baseline)+os.pathsep+env['LEAN_PATH']
    logs=overlay/'quantum-growing-radial-domination-audit'
    logs.mkdir(exist_ok=False)
    assert sha(root/PARENT)==PARENT_SHA
    parent=json.loads((root/PARENT).read_text())
    hashes=dict(parent['source_sha256'])
    assert len(hashes)==3287 and all(sha(root/p)==h for p,h in hashes.items())
    additions=['UnifiedTheory/Audit/'+n+'.lean' for n in EXPECTED]+SCRIPTS
    assert not set(additions)&set(hashes)
    hashes.update({p:sha(root/p) for p in additions})
    analytic={k:v for k,v in parent.items() if k.startswith('analytic_')}
    assert len(analytic)==10 and not set(analytic)&set(EXTRA_ANALYTIC)
    analytic.update(EXTRA_ANALYTIC)
    assert all(sha(root/v['path'])==v['sha256'] for v in analytic.values())
    evidence=parent['numerical_evidence']
    numerical=[v for v in evidence.values() if isinstance(v,dict) and 'path' in v]
    assert len(numerical)==23 and all(sha(root/v['path'])==v['sha256'] for v in numerical)
    text=(root/'UnifiedTheory.lean').read_text()
    suffix=''.join('import UnifiedTheory.Audit.'+n+'\n' for n in EXPECTED)
    assert text.endswith(suffix)
    assert hashlib.sha256(text[:-len(suffix)].encode()).hexdigest()==parent['root_check']['source_sha256']
    assert len(text.splitlines())==8901+len(EXPECTED)
    root_hash=sha(root/'UnifiedTheory.lean')
    checks=[]; done=set()
    for name in EXPECTED:
        source='UnifiedTheory/Audit/'+name+'.lean'
        body=(root/source).read_text()
        needed=set(re.findall(r'^import UnifiedTheory\.Audit\.(\S+)',body,re.M))&set(EXPECTED)
        assert needed<=done,(name,needed-done)
        output=overlay/'UnifiedTheory/Audit'/(name+'.olean')
        assert not output.exists() and not output.is_symlink()
        output.parent.mkdir(parents=True,exist_ok=True)
        command=['lean','-j1','-o',str(output),source]
        result=subprocess.run(command,cwd=root,env=env,text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
        log=logs/(name+'.log'); log.write_text(result.stdout)
        assert result.returncode==0,str(log)
        audits=dependencies(result.stdout)
        assert set(audits)==declarations(name,body)
        assert output.is_file() and not output.is_symlink()
        checks.append(dict(source=source,command=command,exit_code=0,log_sha256=sha(log),audited_declarations=audits))
        done.add(name)
        print(name+': clean; '+str(len(audits))+' theorem dependency lists',flush=True)
    result=subprocess.run(['lean','-j1','UnifiedTheory.lean'],cwd=root,env=env,text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
    log=logs/'root-import.log'; log.write_text(result.stdout)
    assert result.returncode==0 and not result.stdout.strip(),str(log)
    assert sha(root/'UnifiedTheory.lean')==root_hash and sha(root/PARENT)==PARENT_SHA
    assert all(sha(root/p)==h for p,h in hashes.items())
    assert all(sha(root/v['path'])==v['sha256'] for v in [*analytic.values(),*numerical])
    assert all(not (root/'.lake/build/lib/lean/UnifiedTheory/Audit'/(n+'.olean')).exists() for n in EXPECTED)
    report=dict(**analytic,modules=checks,new_lean_theorem_count=sum(EXPECTED.values()),
        source_sha256=hashes,numerical_evidence=evidence,previous_report=dict(path=PARENT,sha256=PARENT_SHA),
        root_check=dict(command=['lean','-j1','UnifiedTheory.lean'],exit_code=0,empty_log=True,
            source_sha256=root_hash,log_sha256=sha(log),appended_imports=list(EXPECTED)),
        lean_toolchain=(root/'lean-toolchain').read_text().strip(),scope=SCOPE)
    target=root/REPORT
    assert not target.exists()
    target.write_text(json.dumps(report,indent=2)+'\n')
    print('Root passed; '+str(sum(EXPECTED.values()))+' theorem audits; '+str(len(hashes))+' source/script hashes.',flush=True)
    print(target,flush=True)


if __name__=='__main__':
    main()
