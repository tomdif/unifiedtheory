#!/usr/bin/env python3
"""Independently verify the weighted-hamiltonian-response audit and preserved evidence."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess

EXPECTED = {'KFCausalWeightedReciprocalNeutralKernel': 8, 'KFCausalCommonRealGaussianWeightedTransport': 6, 'KFCausalCommonRealGaussianWeightedPotentialResponse': 2, 'KFCausalCommonRealGaussianWeightedHamiltonianResponse': 2, 'KFCausalCommonRealGaussianWeightedInitialResponse': 2}
EXTRA_ANALYTIC = {}
SCOPE = 'Twenty new Lean theorems complete the weighted physical response attachment and prove the original full Hamiltonian response bound for every nonnegative mass2, quartic and vacuum coupling, including zero. The exact original-coordinate Gaussian reconstruction, spectator integrals and Jacobian give actual Cross kernel=(pi/4)*wi*wj*weighted Wick pairKernel. Actual physical finite clock pairing and geometric transport are identified with pi/4 times the weighted kernel and derivative, retaining all coherent interference and the original clock amplitudes. The geometric derivative freezes labels; the parent full-clock integration-by-parts identity separately retains their motion. For a common real neutral source and P_i=1, the original transported slice obeys transportResponse<=536*fraction*positiveSlice and is nonnegative. The proved original clock coefficient and fraction/clock bound then give reducedResponse>=-(136/epsilon)*positiveSlice. Previously proved actual L1/Hilbert/clock identities attach this to potentialResponse>=-(136/epsilon)*potentialEnergy, without assuming any response inequality. Adding the derived clock/kinetic contribution with its genuine clock-momentum composition domain yields fullResponse>=-(136/epsilon)*fullEnergy for the original eight-factor Hamiltonian with its exp(2*t) multiplier, all nonnegative couplings and all finite coherent charged widths wi>=1, ai>0, complex amplitudes and real clock frequencies, one common real B and P_i=1. The form statement uses epsilon>0,h!=0,abs(h)<=2*pi*epsilon/3. The actual strong statement uses the constructed Hamiltonian domain and Re<H psi,psi>,(-2/h)Im<H psi,B psi> on abs(h)<=pi*epsilon/3; it does not require H applied to B psi. The original bounded central-difference momentum expectations along the nonautonomous evolution have actual initial derivatives whose punctured-regulator limit obeys this same bound, and an eventual lower bound with any positive tolerance. This is an initial-time result; no unbounded-expectation derivative, time/regulator interchange, trajectory-wide response estimate or preservation of the special state class is asserted. No desired response, domain or integrability is introduced as a new premise. Unrestricted differing/complex neutral sources and arbitrary neutral polynomials, the common full H/G operator core, static kinetic/growing mixed estimates, uniform G_N*(1+H(s))^(-1) bound and stronger evolved domains remain open, as do general curved gravity, same-model interacting Standard Model dynamics, microscopic law/phase selection, physical regulator limits and empirical identification. The earlier phase/harmonic identification still requires revision; a physical TOE is not proved. This checkpoint adds 20 theorems in 5 modules, preserves 3240 parent source/script hashes and adds 7 for 3247 total; root extends 8864 to 8869 lines. All 10 analytic artifacts and 23 numerical files remain unchanged. Standard axioms only.'
PARENT = 'data/quantum_weighted_clock_response_audit.json'
PARENT_SHA = 'f1259d7a6fadf1ecc6b1dbe5957e9a14df84f70e6606c09ff3a79a81ad791ebd'
REPORT = 'data/quantum_weighted_hamiltonian_response_audit.json'
SCRIPTS = ['scripts/quantum_weighted_hamiltonian_response_audit.py',
           'scripts/verify_quantum_weighted_hamiltonian_response.py']
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
    assert len(old)==3240 and len(hashes)==3240+len(EXPECTED)+2
    assert all(hashes[p]==h for p,h in old.items())
    assert all(sha(root/p)==h for p,h in hashes.items())
    additions={'UnifiedTheory/Audit/'+n+'.lean' for n in EXPECTED}|set(SCRIPTS)
    assert set(hashes)-set(old)==additions
    assert [Path(x['source']).stem for x in report['modules']]==list(EXPECTED)
    logs=overlay/'quantum-weighted-hamiltonian-response-audit'
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
    assert text.endswith(suffix) and len(text.splitlines())==8864+len(EXPECTED)
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
