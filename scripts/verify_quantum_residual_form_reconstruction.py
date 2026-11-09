#!/usr/bin/env python3
"""Independently verify the residual-form-reconstruction audit and preserved evidence."""
import argparse
import hashlib
import json
from pathlib import Path
import re

EXPECTED = {
    'KFCausalClockFloorResidualFormSplit': 7,
    'KFCausalClockFloorResidualStaticPotentialDecomposition': 6,
    'KFCausalClockFloorPositiveVacuumThreeOperatorDomain': 5,
    'KFCausalFiniteResidualStaticPotentialDomination': 5,
    'KFCausalFiniteFullHamiltonianDomination': 5,
    'KFCausalClockFloorRadialResolventRoot': 10,
    'KFCausalClockFloorRadialResolventGrowing': 7,
    'KFCausalClockFloorGrowingFormReconstruction': 5,
    'KFCausalClockFloorRadialResolventLeibniz': 16,
    'KFCausalClockFloorRadialResolventResidual': 15,
    'KFCausalClockFloorResidualFormReconstruction': 9,
    'KFCausalClockFloorRadialResolventAveragedForm': 11,
}
EXTRA_ANALYTIC = {}
SCOPE = 'Unconditional residual, growing, and full eight-row form reconstruction and radial-resolvent regularization for all real couplings m,g,k and times t under 0<epsilon,h!=0,abs(h)<=pi*epsilon/3, together with positive-vacuum three-operator domain decomposition and finite-packet full Hamiltonian domination. Specifically, the completed residual-output closure Tres(t) splits into the static closure T and exp(t)*Tpot with exact form-inner-product identity, operator decomposition S(t)=T+exp(2*t)*P on DomT intersect DomP, and under positive vacuum k>0 the closed-graph equivalences DomTres(t)=DomT, DomS(t)=DomT intersect DomP, and DomH(t)=DomG intersect DomT intersect DomP with H(t)f=G f+T f+exp(2*t)*P f; on the original finite sourced packet family for abs(h)<=epsilon/10,m,g>=0,k>0, this yields literal quadratic and norm lower bounds on S(t)f=T f+exp(2*t)*P f and H(t)f=G f+S(t)f in terms of T f,exp(2*t)*P f,G f, and f. Independently of coupling signs, the radial resolvent regularizer J_N=(I+N^(-1)*Kr)^(-1) lifts to the radial square-root closure Kr^(1/2) and to the completed growing, residual, and full eight-row form spaces with explicit second-difference Leibniz defect bounded by O(N^(-1)) in Hilbert norm, maps DomTgrow into DomKr intersect DomTgrow, DomTres(t) into DomKr intersect DomTres(t), and DomEavg(t) into DomKr intersect DomEavg(t), converges strongly to the identity in the growing, residual, and full eight-row form norms along N=n+1, characterizes the ranges of the reference-to-growing and reference-to-residual form lifts as the intersections with Dom(Kr^(1/2)), and proves the unconditional form-domain identities DomTgrow=Dom(Kr^(1/2)) intersect DomTpot and DomEavg(t)=Dom(Kr^(1/2)) intersect DomTres(t)=DomTgrow intersect DomTres(t) for all real m,g,k,t. Operator-level radial resolvent invariance of DomT, DomP, DomS(t), DomG, and DomH(t), extension of the mixed static/potential and full Hamiltonian domination bounds beyond the finite packet family to all operator domains, simultaneous operator graph core, uniform G_N*(1+H(s))^(-1), stronger evolved domains, differing complex neutral sources across packets, general neutral polynomials in the complex-source response bound, trajectory-wide unbounded-momentum derivatives, general curved gravity, interacting Standard Model dynamics in the same model, microscopic law and phase selection, controlled physical limits, and empirical identification remain open; the earlier phase/harmonic identification still requires revision. A physical TOE is not proved. This checkpoint adds101 theorems in12 modules, preserves3452 parent source/script hashes and adds14 for3466 total; exact root extends from9044 to9056 lines. All12 parent analytic artifacts and23 numerical files remain unchanged. Standard axioms only.'
PARENT = 'data/quantum_complex_hamiltonian_response_audit.json'
PARENT_SHA = '5f906cebd18d2334fe2339b607b72f42648080e64f1820dc827f83e771125746'
REPORT = 'data/quantum_residual_form_reconstruction_audit.json'
SCRIPTS = ['scripts/quantum_residual_form_reconstruction_audit.py',
           'scripts/verify_quantum_residual_form_reconstruction.py']
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
    assert len(old)==3452 and len(hashes)==3452+len(EXPECTED)+2
    assert all(hashes[p]==h for p,h in old.items())
    assert all(sha(root/p)==h for p,h in hashes.items())
    additions={'UnifiedTheory/Audit/'+n+'.lean' for n in EXPECTED}|set(SCRIPTS)
    assert set(hashes)-set(old)==additions
    assert [Path(x['source']).stem for x in report['modules']]==list(EXPECTED)
    logs=overlay/'quantum-residual-form-reconstruction-audit'
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
    assert text.endswith(suffix) and len(text.splitlines())==9044+len(EXPECTED)
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
