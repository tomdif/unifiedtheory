#!/usr/bin/env python3
"""Check the actual potential clock resolvents and physical metric completion and preserved evidence."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess

EXPECTED = {'KFCausalClockFloorPotentialClockAccretivity': 5, 'KFCausalClockFloorPotentialClockResolvent': 8, 'KFCausalIndependentRadialWeightedContraction': 3, 'KFCausalPhysicalClockMetricCoefficients': 4, 'KFCausalPhysicalClockMetricCompletion': 8}
EXTRA_ANALYTIC = {}
SCOPE = 'The original ordered-potential closure is invariant under the bounded inverse-clock defect. Actual reference-source transport passes through its literal closed graph. On all DomP, Re(inner(Px,Dx))>=0. Positive resolvents (a+P)^(-1) are constructed from the actual form, have the derived inverse-half-clock weighted bound, and adjoint duality proves preservation of Dom(C^(1/2)) with norm(C^(1/2)*(a+P)^(-1)f)<=a^(-1)*norm(C^(1/2)f). This holds for epsilon>0,h!=0,abs(h)<=2*pi*epsilon/3, arbitrary original real couplings and a>0. It establishes only the clock component of static-form preservation; no transverse kinetic preservation or DomS subset DomP is inferred. The actual finite coherent transverse packet integration-by-parts identity is contracted with every entry of an arbitrary constant complex bilinear metric, retaining all25 mixed derivatives and all coherent interference. Weighted Laplacian, gradient and weight terms have derived five-dimensional L1 before integration and finite-sum exchange. The physical clock metric is exactly its column coefficient expansion on the canonical complex Euclidean basis, and the double sum equals its actual Hilbert inner pairing. For the original physical metric with norm(delta)<=1/20, the field vector has squared norm3 and norm(Bx)<=4/(3*C)*norm(x). For nonnegative m,g,kappa and W(phi)=kappa+m*phi^2/2+g*phi^4/4, (Wprime)^2<=2*W*Wsecond. A division-free square completion proves weighted Laplacian density >=-4/C*Wsecond*abs(f)^2, including W=0 and vanishing couplings. The shifted clock term has positive real part. With the physical h^2/2 prefactor, the full pointwise density is at least -2*h^2/C*Wsecond*abs(f)^2. For kappa>0 only, Wsecond<=(12+(m+3*g)/kappa)*W, yielding the uniform-in-clock loss 2*h^2/epsilon*(12+(m+3*g)/kappa)*W*abs(f)^2. Actual finite-family integral attachment and its all-domain extension remain separate. Previous original quartic response, exact residual domain and radial domination results remain unchanged. Full potential-domain control, full H/G domination, simultaneous operator graph core, uniform G_N*(1+H(s))^(-1), stronger evolved domains and unrestricted physical response remain open. General curved gravity, interacting Standard Model dynamics in the same model, microscopic law/phase selection, controlled physical limits and empirical identification remain open. Earlier phase/harmonic identification requires revision. A physical TOE is not proved. This checkpoint adds28 theorems in5 modules, preserves3396 parent source/script hashes and adds7 for3403 total; the exact root extends from8994 to8999 lines. All12 parent analytic artifacts and23 numerical files remain unchanged. Standard axioms only.'
PARENT = 'data/quantum_physical_response_residual_audit.json'
PARENT_SHA = '1c3e2b80a419b76246033f699c76910724a9496c960f5cbdd3b28ab7695f26e7'
REPORT = 'data/quantum_potential_clock_metric_audit.json'
SCRIPTS = ['scripts/quantum_potential_clock_metric_audit.py',
           'scripts/verify_quantum_potential_clock_metric.py']
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
    logs=overlay/'quantum-potential-clock-metric-audit'
    logs.mkdir(exist_ok=False)
    assert sha(root/PARENT)==PARENT_SHA
    parent=json.loads((root/PARENT).read_text())
    hashes=dict(parent['source_sha256'])
    assert len(hashes)==3396 and all(sha(root/p)==h for p,h in hashes.items())
    additions=['UnifiedTheory/Audit/'+n+'.lean' for n in EXPECTED]+SCRIPTS
    assert not set(additions)&set(hashes)
    hashes.update({p:sha(root/p) for p in additions})
    analytic={k:v for k,v in parent.items() if k.startswith('analytic_')}
    assert len(analytic)==12 and not set(analytic)&set(EXTRA_ANALYTIC)
    analytic.update(EXTRA_ANALYTIC)
    assert all(sha(root/v['path'])==v['sha256'] for v in analytic.values())
    evidence=parent['numerical_evidence']
    numerical=[v for v in evidence.values() if isinstance(v,dict) and 'path' in v]
    assert len(numerical)==23 and all(sha(root/v['path'])==v['sha256'] for v in numerical)
    text=(root/'UnifiedTheory.lean').read_text()
    suffix=''.join('import UnifiedTheory.Audit.'+n+'\n' for n in EXPECTED)
    assert text.endswith(suffix)
    assert hashlib.sha256(text[:-len(suffix)].encode()).hexdigest()==parent['root_check']['source_sha256']
    assert len(text.splitlines())==8994+len(EXPECTED)
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
