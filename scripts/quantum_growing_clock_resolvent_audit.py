#!/usr/bin/env python3
"""Check the actual growing resolvent clock-domain successor and preserved evidence."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess

EXPECTED = {'KFCausalClockFloorGrowingClockResolvent': 10}
EXTRA_ANALYTIC = {}
SCOPE = 'Ten new Lean theorems prove actual clock-half-domain regularity for every positive shifted resolvent of the original growing Hamiltonian G. The bounded inverse-half operator L=C^(-1/2) has a derived polarized pairing epsilon*<Lf,Lg>=<f,Dg> with D=epsilon/C, and its self-adjointness and dense range are proved from the existing actual inverse and clock-half graphs. The parent inverse-clock accretivity on every Dom G, together with the actual resolvent equation, gives ||L*(a+G)^(-1)f||<=a^(-1)||L*f|| for every a>0 and physical Hilbert vector f. LinearMap.extendOfNorm constructs the bounded operator T_a on the dense range of L with T_a*L=L*R_a and ||T_a||<=a^(-1), where R_a is the actual growing resolvent. Self-adjointness of L and R_a gives the exact dual identity R_a*L=L*T_a^*. The original clock-half inverse graph then constructs the explicit graph witness (R_a f,T_a^* C^(1/2)f). Thus R_a preserves the full actual Dom(C^(1/2)) and ||C^(1/2)R_a f||<=a^(-1)||C^(1/2)f||. No domain invariance, range factorization, common-core condition or resolvent estimate is supplied as a new premise. The theorem uses epsilon>0,h!=0,|h|<=2pi*epsilon/3 and the existing original growing operator with its couplings retained; no finite-packet, neutral-source, polynomial or zero-charge restriction is required. It is a clock-half-domain statement for G resolvents, not full C-domain preservation or static kinetic-domain preservation, nor a common H/G core, a bound on G_N(1+H(s))^(-1), or stronger domains along the nonautonomous evolution. The parent unit-coupling restricted full Hamiltonian bound and actual initial regularized dynamics remain intact. Weighted clock/Hilbert response attachment, unrestricted source/polynomial response, static kinetic mixed estimates, general curved metrics/testfields and Einstein dynamics, microscopic law/phase selection, same-model interacting Standard Model QFT, physical regulator limits and empirical identification remain open. The earlier phase/harmonic identification still requires revision; a physical TOE is not proved. This checkpoint adds 10 theorems in 1 module, preserves 3221 parent source/script hashes and adds 3 for 3224 total; root extends 8851 to 8852 lines. All 10 analytic artifacts and 23 numerical files remain unchanged. Standard axioms only.'
PARENT = 'data/quantum_hamiltonian_response_dynamics_audit.json'
PARENT_SHA = '8cfc2a393fc7f026ad8ea3e806a813c588eca396c2ff18a01245d130cd122bcd'
REPORT = 'data/quantum_growing_clock_resolvent_audit.json'
SCRIPTS = ['scripts/quantum_growing_clock_resolvent_audit.py',
           'scripts/verify_quantum_growing_clock_resolvent.py']
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
    logs=overlay/'quantum-growing-clock-resolvent-audit'
    logs.mkdir(exist_ok=False)
    assert sha(root/PARENT)==PARENT_SHA
    parent=json.loads((root/PARENT).read_text())
    hashes=dict(parent['source_sha256'])
    assert len(hashes)==3221 and all(sha(root/p)==h for p,h in hashes.items())
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
    assert len(text.splitlines())==8851+len(EXPECTED)
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
