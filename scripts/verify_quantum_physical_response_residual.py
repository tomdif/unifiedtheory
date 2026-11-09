#!/usr/bin/env python3
"""Independently verify the physical-response-residual audit and preserved evidence."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess

EXPECTED = {'KFCausalClockFloorStaticPotentialOutputClosure': 5, 'KFCausalClockFloorStaticPotentialHamiltonian': 4, 'KFCausalClockFloorHamiltonianRadialSum': 5, 'KFCausalIndependentRadialTransverseRegularity': 4, 'KFCausalIndependentRadialPhysicalPolynomial': 9, 'KFCausalIndependentRadialTransverseIBP': 9, 'KFCausalPhysicalComplexShearMetric': 4, 'KFCausalPhysicalClockMetric': 6, 'KFCausalChargedQuarticCorrectedBound': 4, 'KFCausalQuarticResponseClockCoefficients': 7, 'KFCausalCommonComplexQuarticResponseMarginal': 7, 'KFCausalFiniteChannelCoolingSplit': 4, 'KFCausalChargedQuarticPhysicalBound': 1, 'KFCausalCommonComplexQuarticJointResponse': 4, 'KFCausalCommonComplexQuarticActualBound': 2}
EXTRA_ANALYTIC = {}
SCOPE = 'The original full Hamiltonian has the exact operator identity H(t)=exp(2t)*Kr+S(t) and DomH(t)=DomKr intersection DomS(t), for epsilon>0,h!=0,abs(h)<=pi*epsilon/3 and arbitrary original real potential parameters. S(t) is the self-adjoint Hamiltonian associated to the literal graph closure of original static rows0-2 and time-weighted ordered-potential rows5-7 on original reference sources. No abstract residual is substituted. Primitive closed orbit graphs establish closability even at zero couplings; actual reference form density and the already-derived full-H radial domain establish residual variational pairings, then self-adjoint maximality proves the exact intersection domain. This does not prove S(t)=T+exp(2t)*P on separate operator domains or DomH subset DomG. Actual small complex shear packets have five-dimensional polynomial L2 and weighted coherent cross-width L1, with exact arbitrary neutral-source/polynomial attachment. Their real directional and mixed-second derivatives are derived polynomial jets. Weighted full-space first and mixed-second integration by parts follows with no boundary or derivative-integrability premise, retaining finite coherent interference. The physical shear uses the complex bilinear transpose, not the adjoint: for norm(delta)<=1/20 its inverse Gram perturbation is at most328/1521. The actual clock quotient C/Cprime differs from1 by at most1/18; the normalized metric perturbation is at most7753/27378<1/3. Consequently (2/(3*C))*norm(x)^2<=Re(inner(x,B*x))<=(4/(3*C))*norm(x)^2. The actual half-clock inverse supplies this delta when abs(h)<=epsilon/10. A universal quartic corrected response bound is now attached to the ORIGINAL full Joint spatialFieldResponse j=2 for a common arbitrary complex neutral source A+iD and P=1. There exists K>=0, chosen before all packet counts, coefficients, widths, source parameters and physical clock/width parameters, such that integral(response)<=K*fraction(epsilon,s)*integral(energy). Hypotheses are alpha,beta,epsilon>0,32*beta<=alpha,abs(y)<=pi*epsilon/3 and all wi>=1. The actual scale derivative, exact neutral mass/mean/variance and dilation Jacobian are retained. All full-Joint Fubini and integrability hypotheses are derived. The score, angular Hardy and field Young estimates combine through a polynomial coefficient certificate, including zero imaginary shift and zero coherent energy without division by either. One admissible existential K is1200+25*C4/4, where C4 is the universal angular loss. Distinct neutral sources, nonconstant neutral polynomials and unrestricted physical response remain outside this theorem. Clock-space/Hilbert propagation attachments are separate. The full mixed operator estimate, potential-domain control, full H/G domination, simultaneous operator graph core, uniform G_N*(1+H(s))^(-1) and stronger evolved domains remain open. General curved gravity, interacting Standard Model dynamics in the same model, microscopic law/phase selection, controlled physical limits and empirical identification remain open. Earlier phase/harmonic identification requires revision. A physical TOE is not proved. This checkpoint adds75 theorems in15 modules, preserves3379 parent source/script hashes and adds17 for3396 total; the exact root extends from8979 to8994 lines. All12 parent analytic artifacts and23 numerical files remain unchanged. Standard axioms only.'
PARENT = 'data/quantum_full_h_radial_domain_audit.json'
PARENT_SHA = 'c6bdae7896ff1f66c57d2167dc9c81b13348a273b7eb7a2badc7b8de1dcb9951'
REPORT = 'data/quantum_physical_response_residual_audit.json'
SCRIPTS = ['scripts/quantum_physical_response_residual_audit.py',
           'scripts/verify_quantum_physical_response_residual.py']
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
    assert len(old)==3379 and len(hashes)==3379+len(EXPECTED)+2
    assert all(hashes[p]==h for p,h in old.items())
    assert all(sha(root/p)==h for p,h in hashes.items())
    additions={'UnifiedTheory/Audit/'+n+'.lean' for n in EXPECTED}|set(SCRIPTS)
    assert set(hashes)-set(old)==additions
    assert [Path(x['source']).stem for x in report['modules']]==list(EXPECTED)
    logs=overlay/'quantum-physical-response-residual-audit'
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
    assert text.endswith(suffix) and len(text.splitlines())==8979+len(EXPECTED)
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
