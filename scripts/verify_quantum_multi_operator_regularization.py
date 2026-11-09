#!/usr/bin/env python3
"""Independently verify the multi-operator-regularization audit and preserved evidence."""
import argparse
import hashlib
import json
from pathlib import Path
import re

EXPECTED = {
    'KFCausalClockFloorHamiltonianRadialCrossEstimate': 7,
    'KFCausalClockFloorResidualRadialCrossEstimate': 8,
    'KFCausalClockFloorThreeOperatorCrossEstimate': 6,
    'KFCausalClockFloorUnconditionalFormDomainSynthesis': 8,
    'KFCausalClockFloorTwoTimeFormTransfer': 14,
    'KFCausalClockFloorUnconditionalThreeOperatorDecomposition': 8,
    'KFCausalClockFloorUnconditionalTwoTimeEvolution': 11,
    'KFCausalClockFloorUnconditionalHamiltonianCrossEstimate': 6,
    'KFCausalClockFloorUnconditionalTwoTimeCrossEstimate': 7,
    'KFCausalFiniteThreeOperatorTimeEvolutionDomination': 7,
    'KFCausalClockFloorGaussianPotentialForm': 8,
    'KFCausalClockFloorGaussianPotentialDomain': 6,
    'KFCausalClockFloorGaussianResidualForm': 8,
    'KFCausalClockFloorGaussianMultiOperatorApproximation': 7,
    'KFCausalClockFloorGaussianUnconditionalMultiOperatorApproximation': 8,
    'KFCausalClockFloorRadialResolventOperator': 9,
    'KFCausalClockFloorRadialResolventStaticForm': 11,
    'KFCausalClockFloorRadialResolventStaticRoot': 8,
    'KFCausalClockFloorRadialResolventMultiChannelSynthesis': 12,
    'KFCausalClockFloorPotentialClockApproximation': 10,
    'KFCausalClockFloorPotentialClockCore': 3,
    'KFCausalClockFloorResidualClockAccretivity': 8,
    'KFCausalClockFloorHamiltonianClockCore': 19,
    'KFCausalClockFloorResidualClockCore': 19,
    'KFCausalClockFloorStaticClockCore': 24,
}
EXTRA_ANALYTIC = {}
SCOPE = 'Unconditional three-operator Hamiltonian decomposition, two-time form and operator evolution, multi-channel radial-resolvent and clock-Gaussian regularization, and multi-operator half-clock graph cores for all real couplings m,g,k and times t,s under 0<epsilon,h!=0,abs(h)<=pi*epsilon/3. Specifically, on DomH(t), Re<S(t)x,Kr x>>=-(h^2/epsilon^2)*norm(x)^2 and exp(4*t)*norm(Kr x)^2+norm(S(t)x)^2<=norm(H(t)x)^2+2*exp(2*t)*(h^2/epsilon^2)*norm(x)^2; on DomKr intersect DomS(t), H(t)f=S(t)f+exp(2*t)*Kr f; at m=g=k=0, S(0)=T and DomT intersect DomKr lies in DomH(0); on DomT intersect DomKr intersect DomP, Re<P f,Kr f>>=0 and norm(Kr f)^2+norm(P f)^2<=norm(Kr f+P f)^2. Unconditionally in m,g,k, DomTres(t)=DomTres(s), DomEavg(t)=DomEavg(s)=(Dom(Kr^(1/2)) intersect DomTpot) intersect DomTres(0), residualFormEquiv(t,s) transfers ResidualForm(t) to ResidualForm(s) with time-invariant staticLift, potentialLift, and growingProject, and all common operator intersections DomH(t) intersect DomT, DomH(t) intersect DomG, DomH(t) intersect DomP, and DomS(t) intersect DomG coincide with the time-independent domain D_uncond=(DomT intersect DomKr intersect DomP) intersect DomTres(0) (=DomT intersect DomKr intersect DomP for k>0), on which H(t)x=T x+exp(2*t)*(Kr x+P x), H(t)x-H(s)x=(exp(2*t)-exp(2*s))*G x, S(t)x-S(s)x=(exp(2*t)-exp(2*s))*P x, and norm(T x)^2+2*exp(4*s)*norm(Kr x)^2<=2*norm(H(s)x)^2+2*exp(4*s)*norm(P x)^2+4*exp(2*s)*(h^2/epsilon^2)*norm(x)^2; on the finite sourced packet family for abs(h)<=epsilon/10,m,g>=0,k>0, exp(4*s)*norm(H(t)psi)^2 is dominated by norm(H(s)psi)^2 and norm(psi)^2. Furthermore, the clock-Gaussian multiplier action(epsilon,a,0) preserves DomP, DomTres(t), and DomEavg(t) with P(action(epsilon,a,0)f)=action(epsilon,a,-h)(P f) and provides simultaneous 6-operator graph approximation across T,Kr,P,G,S(t),H(t) on D_uncond as a->0+; the radial resolvent J_N=(I+N^(-1)*Kr)^(-1) commutes with Kr on DomKr with Kr(J_N f)=N*(f-J_N f), lifts to StaticForm and RootForm, preserves Dom(T^(1/2)), maps DomT into DomKr intersect Dom(T^(1/2)), and maps every u in FormSpace(t) into the 7-way joint domain DomKr intersect DomEavg(t) intersect DomTgrow intersect DomTres(t) intersect DomTstat intersect DomTpot intersect Dom(T^(1/2)) with exact regularized 3-channel energy identity; and inverse-clock accretivity and positive shifted resolvents hold for P,S(t),T, and H(t), proving that Dom(A) intersect Dom(clockHalf) is a simultaneous graph core for both A and clockHalf for each A in {G,P,S(t),T,H(t)}. Operator-level radial resolvent invariance of DomT, DomP, DomS(t), DomG, and DomH(t), extension of the mixed static/potential domination bound beyond the finite packet family to all of DomT intersect DomP without a norm(P x)^2 term on the right-hand side, a single simultaneous graph core for H(t) and G together, uniform G_N*(1+H(s))^(-1), stronger evolved domains, differing complex neutral sources across packets, general neutral polynomials in the complex-source response bound, trajectory-wide unbounded-momentum derivatives, general curved gravity, interacting Standard Model dynamics in the same model, microscopic law and phase selection, controlled physical limits, and empirical identification remain open; the earlier phase/harmonic identification still requires revision. A physical TOE is not proved. This checkpoint adds242 theorems in25 modules, preserves3466 parent source/script hashes and adds27 for3493 total; exact root extends from9056 to9081 lines. All12 parent analytic artifacts and23 numerical files remain unchanged. Standard axioms only.'
PARENT = 'data/quantum_residual_form_reconstruction_audit.json'
PARENT_SHA = '936439f227bc513efbaef63f2bec1f4b538337038dd31e1c32bde72b8ca2723c'
REPORT = 'data/quantum_multi_operator_regularization_audit.json'
SCRIPTS = ['scripts/quantum_multi_operator_regularization_audit.py',
           'scripts/verify_quantum_multi_operator_regularization.py']
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
    assert len(old)==3466 and len(hashes)==3466+len(EXPECTED)+2
    assert all(hashes[p]==h for p,h in old.items())
    assert all(sha(root/p)==h for p,h in hashes.items())
    additions={'UnifiedTheory/Audit/'+n+'.lean' for n in EXPECTED}|set(SCRIPTS)
    assert set(hashes)-set(old)==additions
    assert [Path(x['source']).stem for x in report['modules']]==list(EXPECTED)
    logs=overlay/'quantum-multi-operator-regularization-audit'
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
    assert text.endswith(suffix) and len(text.splitlines())==9056+len(EXPECTED)
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
