#!/usr/bin/env python3
"""Independently verify the full-H radial-domain audit and preserved evidence."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess

EXPECTED = {'KFCausalClockFloorRadialYosidaHamiltonianPairing': 4, 'KFCausalClockFloorHamiltonianRadialDomination': 3}
EXTRA_ANALYTIC = {}
SCOPE = 'For the original full averaged Hamiltonian H(t), epsilon>0,h!=0,abs(h)<=pi*epsilon/3 and arbitrary real m,g,kappa,t, every x in DomH(t) belongs to the maximal radial kinetic domain DomKr. The actual completed form and circle sections justify testing against the bounded radial cutoff M_N. The static rows have uniform loss h^2/epsilon^2, while the growing rows retain the radial square. Thus exp(2t)*norm(M_N*x)^2<=Re(inner(H(t)x,M_N*x))+(h^2/epsilon^2)*norm(x)^2 for every positive N and every original operator-domain vector. Cauchy-Schwarz and the actual radial multiplier Fatou theorem give norm(Kr*x)<=exp(-2t)*norm(H(t)x)+(abs(h)/epsilon)*exp(-t)*norm(x). No positive-vacuum condition, DomG premise, common operator core or assumed mixed estimate is used. This closes the full-H radial cutoff and radial operator-domain gap. It does not control the full growing operator G, which also contains the ordered potential P. DomH subset DomG, full H/G domination, a simultaneous operator graph core, uniform G_N*(1+H(s))^(-1), stronger evolved domains and unrestricted physical response remain open. The literal static-plus-potential residual decomposition is not part of this checkpoint. Previous scoped form reconstruction, actual charged Hardy/score bounds and mixed-pairing results remain unchanged. Physical clock-response assembly and full five-dimensional mixed coercivity remain open. General curved gravity, interacting Standard Model dynamics in the same model, microscopic law/phase selection, controlled physical limits and empirical identification remain open; earlier phase/harmonic identification requires revision. A physical TOE is not proved. This checkpoint adds7 theorems in2 modules, preserves3375 parent source/script hashes and adds4 for3379 total; the exact root extends from8977 to8979 lines. All12 parent analytic artifacts and23 numerical files remain unchanged. Standard axioms only.'
PARENT = 'data/quantum_charged_hardy_pairing_audit.json'
PARENT_SHA = 'b1034b0a91f4bc6bae17ffc83171c4c2e8de7c4b5b456eace969e4f5d3c79208'
REPORT = 'data/quantum_full_h_radial_domain_audit.json'
SCRIPTS = ['scripts/quantum_full_h_radial_domain_audit.py',
           'scripts/verify_quantum_full_h_radial_domain.py']
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
    assert len(old)==3375 and len(hashes)==3375+len(EXPECTED)+2
    assert all(hashes[p]==h for p,h in old.items())
    assert all(sha(root/p)==h for p,h in hashes.items())
    additions={'UnifiedTheory/Audit/'+n+'.lean' for n in EXPECTED}|set(SCRIPTS)
    assert set(hashes)-set(old)==additions
    assert [Path(x['source']).stem for x in report['modules']]==list(EXPECTED)
    logs=overlay/'quantum-full-h-radial-domain-audit'
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
    assert text.endswith(suffix) and len(text.splitlines())==8977+len(EXPECTED)
    assert hashlib.sha256(text[:-len(suffix)].encode()).hexdigest()==parent['root_check']['source_sha256']
    assert report['root_check']==dict(command=['lean','-j1','UnifiedTheory.lean'],exit_code=0,empty_log=True,
        source_sha256=sha(root/'UnifiedTheory.lean'),log_sha256=sha(logs/'root-import.log'),appended_imports=list(EXPECTED))
    assert not (logs/'root-import.log').read_text().strip()
    old_analytic={k:v for k,v in parent.items() if k.startswith('analytic_')}
    new_analytic={k:v for k,v in report.items() if k.startswith('analytic_')}
    assert len(old_analytic)==12 and new_analytic==dict(**old_analytic,**EXTRA_ANALYTIC)
    assert all(sha(root/v['path'])==v['sha256'] for v in new_analytic.values())
    assert report['numerical_evidence']==parent['numerical_evidence']
    numerical=[v for v in report['numerical_evidence'].values() if isinstance(v,dict) and 'path' in v]
    assert len(numerical)==23 and all(sha(root/v['path'])==v['sha256'] for v in numerical)
    assert report['scope']==SCOPE and report['lean_toolchain']==(root/'lean-toolchain').read_text().strip()
    print('Verified '+str(sum(EXPECTED.values()))+' Lean theorems, '+str(len(hashes))+' source/script hashes,')
    print('exact root extension, all23 numerical files and all analytic artifacts; standard axioms only.')


if __name__=='__main__':
    main()
