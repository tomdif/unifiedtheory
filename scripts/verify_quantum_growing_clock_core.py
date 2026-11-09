#!/usr/bin/env python3
"""Independently verify the growing-clock-core audit and preserved evidence."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess

EXPECTED = {'KFCausalClockFloorGrowingClockApproximation': 9, 'KFCausalClockFloorGrowingClockCore': 3}
EXTRA_ANALYTIC = {}
SCOPE = 'Twelve new Lean theorems construct a common core for the actual growing operator G and actual half-clock multiplication C^(1/2), where C=exp(s)+epsilon. For a_n=n+1, the scaled actual resolvents a_n*(a_n+G)^(-1) converge strongly to the identity. The weighted bounded extensions S_n=a_n*T_(a_n) are contractions and converge strongly on the dense range of C^(-1/2), hence on the full Hilbert space. A norm-square estimate uses contractivity to prove strong convergence of S_n adjoints as well; it does not infer adjoint strong convergence from general strong convergence. The exact original half-clock graph supplies (a_n*R_(a_n)f,S_n^*z) in its graph whenever (f,z) is in that graph, and every first component lies in actual Dom(G). These pairs converge to (f,z). Thus the half-clock graph restricted to Dom(G) is graph dense. Conversely, actual positive G resolvents preserve Dom(C^(1/2)); applying the source graph-closure theorem to this proved dense source domain makes the G graph restricted to Dom(C^(1/2)) graph dense. Their common domain is dense in the physical Hilbert space. The parameters are epsilon>0,h!=0,abs(h)<=2*pi*epsilon/3, with the original growing couplings retained and no finite-packet, polynomial, neutral-source or zero-charge restriction. No common core, domain preservation or approximation convergence is added as a premise. This is a common G/C^(1/2) core, not a common full H/G operator core. Static kinetic-domain preservation and mixed kinetic/growing estimates, the uniform bound on G_N*(1+H(s))^(-1), stronger evolved domains, weighted physical response attachment, unrestricted source/polynomial response, general gravity, same-model Standard Model dynamics, microscopic law/phase selection, physical regulator limits and empirical identification remain open. The earlier phase/harmonic identification still requires revision; a physical TOE is not proved. This checkpoint adds 12 theorems in 2 modules, preserves 3224 parent source/script hashes and adds 4 for 3228 total; root extends 8852 to 8854 lines. All 10 analytic artifacts and 23 numerical files remain unchanged. Standard axioms only.'
PARENT = 'data/quantum_growing_clock_resolvent_audit.json'
PARENT_SHA = 'ea2491f1309cd0238f3ff55ed009b8a865fa5e23a6293b76c6f9b3dc7550157b'
REPORT = 'data/quantum_growing_clock_core_audit.json'
SCRIPTS = ['scripts/quantum_growing_clock_core_audit.py',
           'scripts/verify_quantum_growing_clock_core.py']
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
    assert len(old)==3224 and len(hashes)==3224+len(EXPECTED)+2
    assert all(hashes[p]==h for p,h in old.items())
    assert all(sha(root/p)==h for p,h in hashes.items())
    additions={'UnifiedTheory/Audit/'+n+'.lean' for n in EXPECTED}|set(SCRIPTS)
    assert set(hashes)-set(old)==additions
    assert [Path(x['source']).stem for x in report['modules']]==list(EXPECTED)
    logs=overlay/'quantum-growing-clock-core-audit'
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
    assert text.endswith(suffix) and len(text.splitlines())==8852+len(EXPECTED)
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
