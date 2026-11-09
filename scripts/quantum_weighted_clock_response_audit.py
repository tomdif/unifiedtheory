#!/usr/bin/env python3
"""Check the weighted actual clock response and physical channel attachment and preserved evidence."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess

EXPECTED = {'KFCausalGaussianWeightedSourcePlaneKernel': 3, 'KFCausalGaussianWeightedSourceKernelDerivative': 6, 'KFCausalWeightedReciprocalNeutralCross': 6, 'KFCausalWeightedReciprocalNeutralPhysicalPair': 8, 'KFCausalWeightedReciprocalNeutralWholeClock': 6, 'KFCausalCommonRealGaussianWeightedKernel': 15, 'KFCausalCommonRealGaussianWeightedImaginaryDerivative': 7, 'KFCausalCommonRealGaussianWeightedClockSplit': 3, 'KFCausalCommonRealGaussianWeightedResponse': 3, 'KFCausalWeightedReciprocalNeutralPotentialTransport': 8}
EXTRA_ANALYTIC = {}
SCOPE = 'Sixty-five new Lean theorems extend the finite original clock-response analysis to W(x)=vacuum+mass2*x^2/2+quartic*x^4/4 with all nonnegative couplings, including zeros. Exact nine-monomial Gaussian integration gives the weighted Wick kernel; its prefactor, mean and variance derivatives are derived. Finite double sums retain charged interference and original width factors. The literal original Joint integral is attached to this kernel after integrability and justified Fubini. Actual local imaginary differentiation and proved finite increments give b*E_b>=-2E for all signs, with negative b handled by conjugated coefficients and zero by positivity; actual field derivatives satisfy 0<=L*E_L<=4E. The original clock split and derived geometry yield the same bound E_clock<=536*fraction*E for arbitrary finite charged widths at least one, fixed complex amplitudes, common real neutral source and P=1; parameters alpha>0,beta>0,32*beta<=alpha,epsilon>0,abs(y)<=pi*epsilon/3. Separately, weighted actual per-channel kernels, C1/envelopes and their clock-normalized derivative bounds are proved for arbitrary real couplings, complex neutral sources and polynomials. Actual Hilbert output and momentum pairings are identified with these channel clock integrals, with L1 established first. The weighted finite-matrix full-clock integration-by-parts identity includes varying Gaussian clock amplitudes and has an integrable boundary. Exact weighted physical potential energy and response are attached to positive-slice and reduced-clock integrals for genuine packet parameters a_i>0,w_i>=1,h!=0,epsilon>0,abs(h)<=2*pi*epsilon/3. The remaining physical normalization bridge between this actual Cross kernel and the weighted Wick family (pi/4 and wi*wj factors) is not asserted here; consequently this checkpoint alone does not prove the weighted integrated potential or full Hamiltonian response bound. No desired weighted response or derivative is added as a premise. Arbitrary differing/complex neutral-source and polynomial response estimates remain open. The parent actual common G/clockHalf core remains intact, while static kinetic control, common full H/G core, the uniform G_N*(1+H(s))^(-1) estimate and stronger evolved domains remain open, as do general gravity, same-model Standard Model dynamics, microscopic law/phase selection, physical regulator limits and empirical identification. The earlier phase/harmonic identification still requires revision; a physical TOE is not proved. This checkpoint adds 65 theorems in 10 modules, preserves 3228 parent source/script hashes and adds 12 for 3240 total; root extends 8854 to 8864 lines. All 10 analytic artifacts and 23 numerical files remain unchanged. Standard axioms only.'
PARENT = 'data/quantum_growing_clock_core_audit.json'
PARENT_SHA = 'e1774f51b6ed50be2e8c4d445b8bd36ae90dff5ae523e0818e921c13ff196904'
REPORT = 'data/quantum_weighted_clock_response_audit.json'
SCRIPTS = ['scripts/quantum_weighted_clock_response_audit.py',
           'scripts/verify_quantum_weighted_clock_response.py']
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
    logs=overlay/'quantum-weighted-clock-response-audit'
    logs.mkdir(exist_ok=False)
    assert sha(root/PARENT)==PARENT_SHA
    parent=json.loads((root/PARENT).read_text())
    hashes=dict(parent['source_sha256'])
    assert len(hashes)==3228 and all(sha(root/p)==h for p,h in hashes.items())
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
    assert len(text.splitlines())==8854+len(EXPECTED)
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
