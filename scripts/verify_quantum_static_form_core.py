#!/usr/bin/env python3
"""Independently verify the static-form-core audit and preserved evidence."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess

EXPECTED = {'KFCausalClockFloorSymmetricOrbitDomain': 4, 'KFCausalClockFloorDualGaussian': 8, 'KFCausalClockFloorStaticFormIdentity': 5, 'KFCausalChargeDualDisplacement': 8, 'KFCausalClockFloorStaticMultiplierForm': 8, 'KFCausalClockFloorDualModulatedDomain': 4, 'KFCausalClockFloorStaticFormCore': 2}
EXTRA_ANALYTIC = {}
SCOPE = 'Thirty-nine new Lean theorems identify the exact ambient static energy and prove an actual static form core. Maximal Fourier momentum transport gives the reverse weighted symmetric graph implication and exact charge-orbit domain equivalence; finite complementary moments construct continuous actual outputs around the entire charge orbit. Neutral momentum and its cancelling charge-average cross terms are retained. Every completed averaged form vector has an integrable clock moment and two integrable complementary moments, and its actual static output norm squared is exactly half their sum. In the original dualPhysical unitary chart the static symbol is (C+Q/C)/2, C=exp(s)+epsilon, Q=momentumScale(h)^2*(x2^2+x3^2+x4^2)+x0^2+x1^2. The maximal square-root multiplier is self-adjoint; every actual averaged form vector belongs to its domain and has exactly the same static energy norm. The exact dual transform of the original trial state is a continuous, L2, everywhere nonzero anisotropic five-dimensional Fourier Gaussian times the untouched clock factor, with all normalization constants retained. An explicit clock-preserving physical displacement and clock phase give every full six-coordinate dual modulation, as an identity on the entire Hilbert space. Actual displaced averaged-form witnesses, with normalization removed exactly, show that every such modulated Gaussian belongs to the full interacting energy domain. Its root-weighted L2 integrability is derived from an actual zero-coupling form witness because the weight and static symbol are coupling-independent. The proved generic modulated multiplier graph core and continuous unitary transport then show that the closure of the maximal static square-root graph restricted to sources in the actual full interacting energy domain equals the full maximal static square-root graph. The core uses epsilon>0,h!=0,abs(h)<=2*pi*epsilon/3 and an arbitrary auxiliary Gaussian clock width a>0; the original interaction couplings and time are retained. This is density in the static form norm only. It does not identify the full interacting form with the intersection of separate maximal static and growing forms, prove a core for the squared static operator, or establish a common full Hamiltonian/growing operator core. The interacting static/growing mixed estimate, uniform G_N*(1+H(s))^(-1) bound, simultaneous graph approximation and stronger evolved domains remain open. The parent restricted real and purely imaginary common-source response bounds are preserved; arbitrary mixed complex or differing neutral sources and general neutral polynomials remain open. General curved gravity, same-model interacting Standard Model dynamics, microscopic law/phase selection, physical regulator limits and empirical identification remain open; the earlier phase/harmonic identification requires revision and a physical TOE is not proved. No desired integrability, density or domain conclusion is introduced as a new premise. This checkpoint adds 39 theorems in 7 modules, preserves 3260 parent source/script hashes and adds 9 for 3269 total; root extends 8880 to 8887 lines. All 10 analytic artifacts and 23 numerical files remain unchanged. Standard axioms only.'
PARENT = 'data/quantum_imaginary_hamiltonian_response_audit.json'
PARENT_SHA = 'f854545ab016e8e093c938c1a6103e9d87ff8abde6f0324e76fc557313ea4a08'
REPORT = 'data/quantum_static_form_core_audit.json'
SCRIPTS = ['scripts/quantum_static_form_core_audit.py',
           'scripts/verify_quantum_static_form_core.py']
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
    assert len(old)==3260 and len(hashes)==3260+len(EXPECTED)+2
    assert all(hashes[p]==h for p,h in old.items())
    assert all(sha(root/p)==h for p,h in hashes.items())
    additions={'UnifiedTheory/Audit/'+n+'.lean' for n in EXPECTED}|set(SCRIPTS)
    assert set(hashes)-set(old)==additions
    assert [Path(x['source']).stem for x in report['modules']]==list(EXPECTED)
    logs=overlay/'quantum-static-form-core-audit'
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
    assert text.endswith(suffix) and len(text.splitlines())==8880+len(EXPECTED)
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
