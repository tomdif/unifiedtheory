#!/usr/bin/env python3
"""Independently verify the growing-clock-resolvent audit and preserved evidence."""
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
    args=parser.parse_args()
    root=Path(__file__).resolve().parents[1]; overlay=args.overlay.resolve()
    report=json.loads((root/REPORT).read_text()); parent=json.loads((root/PARENT).read_text())
    assert report['previous_report']==dict(path=PARENT,sha256=PARENT_SHA) and sha(root/PARENT)==PARENT_SHA
    old=parent['source_sha256']; hashes=report['source_sha256']
    assert len(old)==3221 and len(hashes)==3221+len(EXPECTED)+2
    assert all(hashes[p]==h for p,h in old.items())
    assert all(sha(root/p)==h for p,h in hashes.items())
    additions={'UnifiedTheory/Audit/'+n+'.lean' for n in EXPECTED}|set(SCRIPTS)
    assert set(hashes)-set(old)==additions
    assert [Path(x['source']).stem for x in report['modules']]==list(EXPECTED)
    logs=overlay/'quantum-growing-clock-resolvent-audit'
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
    assert text.endswith(suffix) and len(text.splitlines())==8851+len(EXPECTED)
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
