#!/usr/bin/env python3
"""Independently verify the hardy-joint-domain audit and preserved evidence."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess

EXPECTED = {'KFCausalLpClosedGraphFormLift': 3, 'KFCausalClockFloorPositiveVacuumFormReconstruction': 6, 'KFCausalClockFloorPositiveVacuumCommonDomain': 4, 'KFCausalIndependentRadialClockMomentRepresentative': 4, 'KFCausalOrderedStaticOutputRepresentative': 4, 'KFCausalIndependentRadialEntireLaplacian': 6, 'KFCausalIndependentRadialPulledLaplacian': 6, 'KFCausalChargedQuarticAngularLoss': 4, 'KFCausalCommonComplexQuarticNeutralIntegral': 6, 'KFCausalJointChargedNeutralReordering': 3, 'KFCausalChargedQuarticUniversalAngularLoss': 1, 'KFCausalCommonComplexQuarticJointAngular': 9, 'KFCausalChargedQuarticScoreIntegrability': 4, 'KFCausalChargedQuarticScoreIBP': 4, 'KFCausalAngularPolynomialNumber': 4, 'KFCausalAngularEntireNumber': 5, 'KFCausalAngularQuarticHardy': 5, 'KFCausalClockFloorRadialYosidaStaticLowerBound': 2}
EXTRA_ANALYTIC = {}
SCOPE = 'An actual L2 graph section is constructed by orthogonal projection of the input/output pair, and the original averaged operator graph is characterized by its almost-everywhere closed base graph. For epsilon>0,h!=0,abs(h)<=2*pi*epsilon/3 and strictly positive vacuum coupling kappa, the original full form domain is exactly the intersection of the static-root and growing-output domains. Consequently Dom H(t) intersect Dom G equals Dom T intersect Dom G, and H(t)=T+exp(2t)*G on that intersection, with the original reference-range restriction removed. This does not prove Dom H(t) subset Dom G, a simultaneous operator graph core, or propagation. The actual Q(T psi) output for original finite sourced packets is attached to a common-coordinate representative, with arbitrary neutral polynomials, linked independent radial moments and all normalizations. The ground-width specialization retains epsilon,a>0,h!=0,abs(h)<=epsilon/10 and widths>=1. The actual original numerator is identified with an entire transverse packet, its first and second derivatives along inverse complex-shear columns are derived, and the ordered static profile equals the shifted clock term minus the actual pulled-back Laplacian term. The metric is bilinear, not an adjoint. No mixed integration-by-parts bound or full operator-domain estimate is assumed or concluded. The literal original Joint common A+iD source, neutral polynomial P=1, quartic density has a single finite C>=0 selected before every finite packet count n, with 2*integral(tiltDensity)-fieldSlope(r)*integral(fieldDensity)+C*integral(energyDensity)>=0. All coherent cross terms, ci*wi amplitudes and neutral Gaussian normalization remain. Actual full-Joint polynomial integrability, neutral moments, measure reordering, polar comparison and Fubini are proved under beta>0,Re(gamma)>0,positive widths and 8*beta*Im(r)^2<2*Re(gamma)*wi. The finite C is not computed. For the actual coherent charged marginal, polynomial-weighted marginal, radial derivative and real-a cooling derivative are integrable under alpha>0,abs(Im(r))<Re(r),positive widths and strict Gaussian margins. The actual whole-line weighted identity integral(v*h*f_prime)=-E-L*F-T and Cooling>=(scoreRate+1/Re(r))*E+(scoreRate/2)*(L*F+T) are proved; no boundary cancellation premise is supplied. The literal circle number form is nonnegative for every complex polynomial, and for exp(A(z))*B(z) with complex polynomials A,B. Finite Taylor values and derivatives converge with an explicit continuous integrable majorant, justifying the dominated-convergence step. Its degree-two specialization proves T>=(d-4)*E for the actual quartic unit-circle integrals with every real d,q,mu,L. Exact positive three-point quartic cubature preserves the same inequality for W_sigma(x)=x^4+6*sigma*x^2+3*sigma^2, all sigma>=0, including zero. Attaching this Hardy bound and the score integrals to the same charged/Joint object and completing the clock-response inequality remain separate, as does unrestricted physical response. For the actual radial Yosida cutoff M_N, derivativeSymbol^2<=(4/epsilon)*M_N and the symmetric static row has the uniform lower pairing loss -(h^2/epsilon)*norm(inverseL*f)^2, derived by a pointwise square and genuine L2 integration. This checkpoint does not yet include the full-H cutoff test or radial H-domain domination. The full interacting mixed estimate, uniform G_N*(1+H(s))^(-1), full H/G domination, zero-vacuum form reconstruction and stronger evolved domains remain unproved. General curved gravity, interacting Standard Model dynamics in the same model, microscopic law/phase selection, controlled physical limits and empirical identification remain open. Earlier phase/harmonic identification requires revision. A physical TOE is not proved. This checkpoint adds80 theorems in18 modules, preserves3347 parent source/script hashes and adds20 for3367 total; the exact root extends from8953 to8971 lines. All12 parent analytic artifacts and23 numerical files remain unchanged. Standard axioms only.'
PARENT = 'data/quantum_shifted_output_tilt_audit.json'
PARENT_SHA = 'a3865945e78147f94146e70a181f47b91ebf340f9a188935c73aa4f5943d0042'
REPORT = 'data/quantum_hardy_joint_domain_audit.json'
SCRIPTS = ['scripts/quantum_hardy_joint_domain_audit.py',
           'scripts/verify_quantum_hardy_joint_domain.py']
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
    assert len(old)==3347 and len(hashes)==3347+len(EXPECTED)+2
    assert all(hashes[p]==h for p,h in old.items())
    assert all(sha(root/p)==h for p,h in hashes.items())
    additions={'UnifiedTheory/Audit/'+n+'.lean' for n in EXPECTED}|set(SCRIPTS)
    assert set(hashes)-set(old)==additions
    assert [Path(x['source']).stem for x in report['modules']]==list(EXPECTED)
    logs=overlay/'quantum-hardy-joint-domain-audit'
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
    assert text.endswith(suffix) and len(text.splitlines())==8953+len(EXPECTED)
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
