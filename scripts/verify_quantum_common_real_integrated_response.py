#!/usr/bin/env python3
"""Independently verify the common-real-integrated-response audit and preserved evidence."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess

EXPECTED = {'KFCausalCommonRealGaussianPotentialResponse': 3}
EXTRA_ANALYTIC = {}
SCOPE = 'Three new Lean theorems attach the already verified common-real-source P=1 transport bound to the original integrated ordered-potential response. The exact fraction/clock ratio is exp(s)/(epsilon+exp(s))^2 and is at most 1/(4epsilon), derived from a square inequality for every epsilon>0. The retained 536*fraction transport estimate therefore contributes 134/epsilon after clock division; the existing actual coefficient lower bound contributes 2/epsilon. The actual reducedResponse is at least -(136/epsilon)*positiveSlice. Existing positiveSlice and reducedResponse integrability suppliers are applied with all physical hypotheses before integration. The exact full-clock integration-by-parts identity and original potentialEnergy integral give potentialResponse>=-(136/epsilon)*potentialEnergy for the actual Hilbert-space ordered-output/momentum pairings. Clock amplitudes genuinely vary; their contribution and boundary control are accounted for by the previously derived weak-to-reduced integration-by-parts identity. No desired response bound, boundary vanishing, or integrability is inserted as a new premise. The theorem allows arbitrary finite complex amplitudes, real frequencies, charged widths>=1 and positive clock Gaussian widths, with one common real neutral source and every neutral polynomial P=1. It requires epsilon>0,h!=0 and |h|<=2pi*epsilon/3. This is a uniform bound on this restricted class, not the unrestricted unequal/complex-source or neutral-polynomial response theorem. A full-Hamiltonian attachment, unequal potential couplings, common H/G core and forward stronger domains remain separate. The parent literal four-coordinate conformal operator and pointwise transport results remain intact. General curved metrics/testfields and Einstein dynamics, microscopic law/phase selection, same-model interacting Standard Model QFT, physical regulator limits and empirical identification remain open. The earlier phase/harmonic identification still requires revision; a physical TOE is not proved. This checkpoint adds 3 theorems in 1 module, preserving 3207 parent source/script hashes and adding 3 for 3210 total; root extends 8841 to 8842 lines. All 10 analytic artifacts and 23 numerical files remain unchanged. Standard axioms only.'
PARENT = 'data/quantum_conformal_full_operator_response_audit.json'
PARENT_SHA = 'efa0840b0556bdfa88710da613fd9032719b8f22e054116750a3af6e0b7fcd7e'
REPORT = 'data/quantum_common_real_integrated_response_audit.json'
SCRIPTS = ['scripts/quantum_common_real_integrated_response_audit.py',
           'scripts/verify_quantum_common_real_integrated_response.py']
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
    assert len(old)==3207 and len(hashes)==3207+len(EXPECTED)+2
    assert all(hashes[p]==h for p,h in old.items())
    assert all(sha(root/p)==h for p,h in hashes.items())
    additions={'UnifiedTheory/Audit/'+n+'.lean' for n in EXPECTED}|set(SCRIPTS)
    assert set(hashes)-set(old)==additions
    assert [Path(x['source']).stem for x in report['modules']]==list(EXPECTED)
    logs=overlay/'quantum-common-real-integrated-response-audit'
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
    assert text.endswith(suffix) and len(text.splitlines())==8841+len(EXPECTED)
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
