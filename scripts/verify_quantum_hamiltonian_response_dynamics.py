#!/usr/bin/env python3
"""Independently verify the Hamiltonian-response-dynamics audit and preserved evidence."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess

EXPECTED = {'KFCausalReciprocalNeutralConstantClockComposition': 4, 'KFCausalReciprocalNeutralKineticResponse': 7, 'KFCausalReciprocalNeutralConstantResponse': 3, 'KFCausalCommonRealGaussianHamiltonianResponse': 2, 'KFCausalCommonRealGaussianInitialResponse': 7, 'KFCausalCommonRealGaussianWeightedEnergy': 11, 'KFCausalCommonRealGaussianWeightedJointEnergy': 5, 'KFCausalClockFloorGrowingClockAccretivity': 6, 'KFCausalFiniteGrowingClockCoercivity': 3}
EXTRA_ANALYTIC = {}
SCOPE = 'Forty-eight new Lean theorems close the full restricted Hamiltonian response attachment and derive actual initial dynamical and clock-growing consequences. The clock-half output of each original sourced reciprocal packet with constant neutral polynomial has a constructed pureMomentum graph, transported from the actual sourced Gaussian composition. Finite sums retain arbitrary complex sources and all cross terms. Actual kinetic responses are nonnegative on the full finite neutral-polynomial family; the clock response on the constant-polynomial family is bounded below by -1/(4epsilon) times its clock energy. Exact full energy/response decompositions retain every factor and the exp(2t) potential multiplier. Combining the previously proved integrated potential bound gives fullResponse>=-(136/epsilon)*fullEnergy at unit mass2/quartic/vacuum couplings, for finite arbitrary complex amplitudes, real clock frequencies, positive clock Gaussian widths, charged widths>=1, one common real neutral source B and all neutral polynomials P=1. It requires epsilon>0,h!=0 and |h|<=2pi*epsilon/3. The strong bound is attached to the actual original Hamiltonian action on its proved domain, with the required smaller strip |h|<=pi*epsilon/3. No second H action on Bpsi is assumed. For the actual original nonautonomous evolution, bounded central-difference pure-momentum observables have initial derivatives. Their initial derivatives converge as the central parameter tends to zero through nonzero values to the original fullResponse; their initial values converge to the original momentum expectation. These derivative/limit statements hold for the original general finite family and actual couplings. The restricted common-real/P1/unit-coupling bound yields a lower bound on the limit and an eventual lower bound with any positive tolerance. It asserts neither an unbounded-expectation time derivative nor exchange of limits nor a trajectory-wide response bound. For arbitrary nonnegative mass2/quartic/vacuum, including zero couplings, the actual common-real-source weighted Gaussian energy has a derived nonnegative three-even-moment decomposition, integrability, b-squared finite-increment monotonicity, and actual field derivative 0<=L E_L<=4E. A further exact attachment derives original profile coefficients c_i*w_i, full Joint integrability by unit-potential domination, and equality of the original literal Joint integral with that weighted energy. All required L1 precedes Fubini. The literal Joint integral has no pi/4 prefactor. Weighted finite-kernel/clock/Hilbert response attachment remains open; a weighted full Hamiltonian inequality is not inferred from the unit-coupling bound. The actual minimal closed growing-output graph is stable under the bounded inverse-clock defect D=epsilon/C, with a constructed growing-form action. Derived nonnegative real part of the actual shifted multiplier gives Re<Gx,Dx>>=0 on every actual Dom G. Clock/growing mixed positivity and the norm bound ||Gx||<=||Gx+r Cx|| for r>=0 require an actual growing-form representative of Cx. A separate finite-source theorem constructs that representative from the existing actual Cpsi Hamiltonian graph, proving the mixed positivity and norm bound on the original finite sourced family with arbitrary complex sources/polynomials and |h|<=epsilon/10. The two remaining static kinetic rows are not controlled by this clock-only result; no one-H graph bound, common H/G operator core or stronger forward-domain propagation is claimed. General neutral sources/polynomials in the full response, arbitrary weighted physical response, general curved metrics/testfields and Einstein dynamics, microscopic law/phase selection, same-model interacting Standard Model QFT, physical regulator limits and empirical identification remain open. The earlier phase/harmonic identification still requires revision; a physical TOE is not proved. This checkpoint adds 48 theorems in 9 modules, preserves 3210 parent source/script hashes and adds 11 for 3221 total; root extends 8842 to 8851 lines. All 10 analytic artifacts and 23 numerical files remain unchanged. Standard axioms only.'
PARENT = 'data/quantum_common_real_integrated_response_audit.json'
PARENT_SHA = '9af6468f7339a4d78ed3bbe2d933c9d4fc14e5e881c261fc6e947687ee667174'
REPORT = 'data/quantum_hamiltonian_response_dynamics_audit.json'
SCRIPTS = ['scripts/quantum_hamiltonian_response_dynamics_audit.py',
           'scripts/verify_quantum_hamiltonian_response_dynamics.py']
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
    assert len(old)==3210 and len(hashes)==3210+len(EXPECTED)+2
    assert all(hashes[p]==h for p,h in old.items())
    assert all(sha(root/p)==h for p,h in hashes.items())
    additions={'UnifiedTheory/Audit/'+n+'.lean' for n in EXPECTED}|set(SCRIPTS)
    assert set(hashes)-set(old)==additions
    assert [Path(x['source']).stem for x in report['modules']]==list(EXPECTED)
    logs=overlay/'quantum-hamiltonian-response-dynamics-audit'
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
    assert text.endswith(suffix) and len(text.splitlines())==8842+len(EXPECTED)
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
