#!/usr/bin/env python3
"""Check the literal four-coordinate operator and response successors and preserved evidence."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess

EXPECTED = {'KFCausalConformal4DSpatialIsometry': 11, 'KFCausalConformal4DEndpointVolume': 7, 'KFCausalConformal4DSpatialRadialMeasure': 11, 'KFCausalConformal4DSpatialRadialMeasureProduct': 8, 'KFCausalConformal4DFullCoordinateOperator': 6, 'KFCausalCommonRealGaussianFieldKernel': 3, 'KFCausalCommonRealGaussianFieldFamily': 8, 'KFCausalCommonRealGaussianOriginalField': 4, 'KFCausalCommonRealGaussianImaginaryDerivative': 7, 'KFCausalCommonRealGaussianClockSplit': 7, 'KFCausalCommonRealGaussianResponse': 6, 'KFCausalCommonRealGaussianTransport': 2}
EXTRA_ANALYTIC = {}
SCOPE = 'Eighty new Lean theorems close two actual attachments for the existing selected model. The literal four-coordinate outer integral uses the metric density and a past defined by actual C1 future-timelike curves in the positive temporal slab -2<=time<=0. Actual spatial isometries transport curves, chronological diamonds and Lebesgue measure. A constructed reflection reduces every endpoint to its radial representative, and inner volume integrability is derived for every endpoint. The Euclidean Haar radial formula gives exactly 4*pi with sharp ball indicators; actual compact-profile L1 justifies outer Fubini. The slab cutoff discards only a proved zero tail of the original compact field. Thus fullOuter=4*pi*chronologicalOuter and the actual four-coordinate operator tends to Box_g(phi)(0)-R(0)*phi(0)/2=8-6c for each fixed |c|<=1/54 and Omega=1+c*time^2. This is one conformal family and one original compact field on a positive patch. Negative c is not asserted to define a globally nondegenerate Lorentzian metric; general metrics, fields and variational Einstein dynamics remain open. The original common-real-source P=1 joint energy now has a derived imaginary derivative via finite sourced kernels and local strict margins. Actual finite-increment monotonicity yields b*E_b>=-2E for both signs of b and zero. An exact arbitrary-field-slope kernel is attached to the full coherent Joint density with all original width factors; L1 precedes Fubini and every cross term is retained. Its actual derivative in the original coefficient orientation satisfies 0<=L*E_L<=4E. The exact actual clock split E_dot=-4hE-q*(bE_b+3chiE_L), together with derived q,h,chi,L bounds, proves original totalResponse<=536*fraction*totalEnergy. The pi/4 normalization is identified on both sides. This theorem assumes alpha>0,beta>0,32beta<=alpha,epsilon>0,|y|<=pi*epsilon/3 and every charged width>=1, with arbitrary finite complex amplitudes held fixed, one common real neutral source and P=1. A further exact attachment gives original transportResponse<=536*fraction*positiveSlice using the actual groundWidth/neutralWidth, y=-h/2 and transported coefficients frozen at evaluation time. It requires epsilon>0,h!=0,|h|<=2pi*epsilon/3 and widths>=1; no separate coefficient derivative or integrated response estimate is asserted. The inherited analytic 536 note remains unchanged historical evidence; the new restricted endpoint is now Lean verified. Arbitrary unequal or complex neutral sources and neutral polynomials remain open, and superposition across distinct sources is not covered merely by linearity. A common H/G operator core, forward stronger-domain propagation, microscopic law and phase selection, interacting Standard Model dynamics in the same model, controlled physical regulator limits and empirical identification remain open. The earlier phase/harmonic identification still requires revision. A physical TOE is not proved. This checkpoint adds 80 theorems in 12 modules, preserves 3193 parent source/script hashes and adds 14 for 3207 total; root extends 8829 to 8841 lines. All 10 analytic artifacts and 23 numerical files are unchanged. Standard axioms only.'
PARENT = 'data/quantum_conformal_chronological_volume_audit.json'
PARENT_SHA = 'e34cb1d4a56ef529d9172dcecb0f05c9f5a2374bc6ca56c32103097f25d2caf2'
REPORT = 'data/quantum_conformal_full_operator_response_audit.json'
SCRIPTS = ['scripts/quantum_conformal_full_operator_response_audit.py',
           'scripts/verify_quantum_conformal_full_operator_response.py']
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
    logs=overlay/'quantum-conformal-full-operator-response-audit'
    logs.mkdir(exist_ok=False)
    assert sha(root/PARENT)==PARENT_SHA
    parent=json.loads((root/PARENT).read_text())
    hashes=dict(parent['source_sha256'])
    assert len(hashes)==3193 and all(sha(root/p)==h for p,h in hashes.items())
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
    assert len(text.splitlines())==8829+len(EXPECTED)
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
