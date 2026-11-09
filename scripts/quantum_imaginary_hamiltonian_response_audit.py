#!/usr/bin/env python3
"""Check the common imaginary-source Hamiltonian response and initial dynamics and preserved evidence."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess

EXPECTED = {'KFCausalGaussianWeightedGeneralClockSplit': 3, 'KFCausalChargedCoshGaussianMomentSeries': 7, 'KFCausalCommonImaginaryGaussianJointDensity': 5, 'KFCausalCommonImaginaryGaussianEnergy': 9, 'KFCausalCommonImaginaryGaussianWeightedKernel': 15, 'KFCausalCommonImaginaryGaussianWeightedImaginaryDerivative': 7, 'KFCausalCommonImaginaryGaussianWeightedResponse': 3, 'KFCausalCommonImaginaryGaussianWeightedTransport': 3, 'KFCausalCommonImaginaryGaussianPotentialResponse': 2, 'KFCausalCommonImaginaryGaussianHamiltonianResponse': 2, 'KFCausalCommonImaginaryGaussianInitialResponse': 2}
EXTRA_ANALYTIC = {}
SCOPE = 'Fifty-eight new Lean theorems extend the actual weighted full Hamiltonian response bound to one common purely imaginary neutral source B=D*i, with arbitrary real D and P_i=1. Arbitrary fixed complex source pairs now have an exact clock decomposition retaining the full sourceV and sourceX terms. For the common imaginary-source sector, actual coherent charged packets with a linear Gaussian tilt are absolutely integrable under the original strict quadratic margin for every D. Reflection gives a positive cosh-weighted double moment series, retaining all finite-family interference; actual finite increments then prove b*E_b>=-2*E. Differentiability is obtained locally from the exact finite sourced Gaussian kernel, not by differentiating the infinite series. The actual field derivative obeys 0<=L*E_L<=4*E for all nonnegative mass2, quartic and vacuum couplings, including zero. Together with the exact general clock split this gives the original Joint geometric derivative <=536*fraction*energy. The exact pi/4 original-coordinate normalization, proved full-clock integration by parts including amplitude motion, and actual L1/Hilbert identifications yield potentialResponse>=-(136/epsilon)*potentialEnergy. Adding the original clock/kinetic contribution gives fullResponse>=-(136/epsilon)*fullEnergy for the original eight-factor Hamiltonian with exp(2*t) multiplier. The class allows every finite coherent family of charged widths wi>=1, ai>0, complex amplitudes and real clock frequencies, with common D*i and P_i=1. The form bound uses epsilon>0,h!=0,abs(h)<=2*pi*epsilon/3. The actual strong Hamiltonian pairing uses its constructed domain and abs(h)<=pi*epsilon/3; no H applied to B psi is asserted. Initial derivatives of the actual bounded central-difference momentum expectations along the nonautonomous evolution have a punctured-regulator limit obeying this bound, and an eventual bound with arbitrary positive tolerance. This is only an initial-time result; no unbounded-expectation differentiation, limit interchange, trajectory-wide bound or evolved-state-class preservation is asserted. No desired response, domain or integrability conclusion is added as a premise. Arbitrary common mixed complex sources, differing neutral sources, general neutral polynomials, the common full H/G operator core, static kinetic/growing mixed estimates, uniform G_N*(1+H(s))^(-1) bound and stronger evolved domains remain open. General curved gravity, same-model interacting Standard Model dynamics, microscopic law/phase selection, physical regulator limits and empirical identification remain open. The earlier phase/harmonic identification requires revision; a physical TOE is not proved. This checkpoint adds 58 theorems in 11 modules, preserves 3247 parent source/script hashes and adds 13 for 3260 total; the root extends 8869 to 8880 lines. All 10 analytic artifacts and 23 numerical files remain unchanged. Standard axioms only.'
PARENT = 'data/quantum_weighted_hamiltonian_response_audit.json'
PARENT_SHA = '6a2e5bdf11cad2bfbe35e57fdad4943ea031e98d94f975212e5d47ece0dc7d31'
REPORT = 'data/quantum_imaginary_hamiltonian_response_audit.json'
SCRIPTS = ['scripts/quantum_imaginary_hamiltonian_response_audit.py',
           'scripts/verify_quantum_imaginary_hamiltonian_response.py']
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
    logs=overlay/'quantum-imaginary-hamiltonian-response-audit'
    logs.mkdir(exist_ok=False)
    assert sha(root/PARENT)==PARENT_SHA
    parent=json.loads((root/PARENT).read_text())
    hashes=dict(parent['source_sha256'])
    assert len(hashes)==3247 and all(sha(root/p)==h for p,h in hashes.items())
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
    assert len(text.splitlines())==8869+len(EXPECTED)
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
