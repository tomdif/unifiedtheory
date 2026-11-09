#!/usr/bin/env python3
"""Independently verify the static-hamiltonian-closure audit and preserved evidence."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess

EXPECTED = {'KFCausalClockFloorStaticOperator': 6, 'KFCausalClockFloorStaticOperatorGaussianWeight': 4, 'KFCausalClockFloorStaticOperatorSourceCore': 1, 'KFCausalClockFloorStaticRootSource': 5, 'KFCausalClockFloorStaticOutputClosure': 10, 'KFCausalClockFloorStaticHamiltonian': 6}
EXTRA_ANALYTIC = {}
SCOPE = 'Thirty-two new Lean theorems close the original static-output domain and identify its representing Hamiltonian with the maximal static sigma multiplier. The maximal sigma operator T is self-adjoint, has the exact weighted L2 domain and graph, and is exactly S squared including both composition domains, where S is the previously proved maximal square-root multiplier. The root pairing is proved from actual L2 multiplier identities. Every polynomial transverse Gaussian moment and the full clock-weighted Gaussian L2 condition are derived; the positive clock floor bounds inverse clock multiplication. These give full sigma-weighted Gaussian integrability, and the graph of T restricted to inputs in the actual full interacting averaged-form domain is proved dense in the maximal T graph. No operator-domain or density conclusion is assumed. Separately, actual averaged sources embed densely into the complete S graph with the exact original static-output norm. The original three-row static output extends continuously to that root graph, preserves its norm and inner product, and its graph is proved equal to the closure of the literal original static-output graph. This closed original-output operator has exactly Dom(S). The Hamiltonian represented by its closed graph form equals T by the actual variational pairing and self-adjoint maximality; exact Hamiltonian domain and graph are exported. The physical parameters remain epsilon>0,h!=0,abs(h)<=2*pi*epsilon/3, original interaction parameters and time, with an auxiliary Gaussian width a>0 for the core construction. This identifies the separate static Hamiltonian; it does not prove the full interacting form is the intersection of separate maximal static and growing forms, a common full H/G operator core, simultaneous graph approximation, the interacting mixed estimate, uniform G_N*(1+H(s))^(-1) control, or stronger evolved domains. Restricted real and purely imaginary common-source response results are preserved; arbitrary mixed complex or differing neutral sources and general neutral polynomials remain open. General curved gravity, same-model Standard Model interactions, microscopic law/phase selection, controlled physical limits and empirical identification remain unproved. The earlier phase/harmonic identification requires revision. A physical TOE is not proved. This checkpoint adds 32 theorems in 6 modules, preserves 3269 parent source/script hashes and adds 8 for 3277 total; root extends 8887 to 8893 lines. All 10 analytic artifacts and 23 numerical files remain unchanged. Standard axioms only.'
PARENT = 'data/quantum_static_form_core_audit.json'
PARENT_SHA = '10f8859c32e71406f777ff702e7edf524a68f0fb1c478680601e59f27c47788e'
REPORT = 'data/quantum_static_hamiltonian_closure_audit.json'
SCRIPTS = ['scripts/quantum_static_hamiltonian_closure_audit.py',
           'scripts/verify_quantum_static_hamiltonian_closure.py']
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
    assert len(old)==3269 and len(hashes)==3269+len(EXPECTED)+2
    assert all(hashes[p]==h for p,h in old.items())
    assert all(sha(root/p)==h for p,h in hashes.items())
    additions={'UnifiedTheory/Audit/'+n+'.lean' for n in EXPECTED}|set(SCRIPTS)
    assert set(hashes)-set(old)==additions
    assert [Path(x['source']).stem for x in report['modules']]==list(EXPECTED)
    logs=overlay/'quantum-static-hamiltonian-closure-audit'
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
    assert text.endswith(suffix) and len(text.splitlines())==8887+len(EXPECTED)
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
