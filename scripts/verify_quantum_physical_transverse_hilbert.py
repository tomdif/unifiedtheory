#!/usr/bin/env python3
"""Independently verify the physical-transverse-hilbert audit and preserved evidence."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess

EXPECTED = {'KFCausalFormContractiveResolventTransfer': 2, 'KFCausalIndependentRadialTransverseMeasure': 6, 'KFCausalIndependentRadialRealShearMeasure': 7, 'KFCausalIndependentRadialMomentumMeasure': 5, 'KFCausalIndependentRadialPhysicalMeasure': 6, 'KFCausalIndependentRadialIntegralCompletion': 7, 'KFCausalIndependentRadialMetricLaplacian': 7, 'KFCausalOrderedStaticTransverseProfile': 4, 'KFCausalFiniteChannelJointClockDerivative': 3, 'KFCausalCommonComplexQuarticClockKernel': 2, 'KFCausalCommonComplexQuarticPotentialResponse': 4, 'KFCausalClockFloorRadialResolventRegularizer': 8, 'KFCausalOrderedStaticTransverseIntegral': 4}
EXTRA_ANALYTIC = {}
SCOPE = 'The original common-complex-source/P=1 quartic Hilbert response satisfies potentialResponse(0,4,0)>=-(M/epsilon)*potentialEnergy(0,4,0), with a universal existential M>=0 chosen before all state data, M=2+K/4. Actual pi/4 normalization and half-clock displacement are retained. Genuine full clock integration by parts retains changing amplitudes and derives L1; no endpoint or desired-bound premise is introduced. Assumptions: epsilon>0,h!=0,abs(h)<=2*pi*epsilon/3, positive longitudinal widths, charged widths>=1, one common arbitrary complex neutral source and P=1. The generic finite-channel derivative supplier allows arbitrary fixed source/polynomial arrays and derives compact Gaussian domination from physical width floors. Raw quartic Joint energy and response equal the original weighted Wick family at couplings(0,4,0) through actual integrals and derivative uniqueness. No mass-channel or unrestricted-neutral-profile uniform response is inferred. The original Product is reordered into unchanged clock q and five real transverse coordinates. Constant momentum scaling has exact Jacobian abs(c)^(-2), including signed c!=0. The actual real shear has determinant1: two reciprocal Fourier dilations cancel two position dilations and the neutral lower triangular shear contributes1. A proved measure-preserving skew product handles the q-dependent flow; actual whole-space L1 equivalence and integral change of variables are proved. The inverse chart exactly identifies the original mixed coordinates, real reference coordinate and physical field. The bilinear inverse metric contracts all25 Hessian entries, including neutral cross terms, to the literal physical Laplacian. Arbitrary neutral polynomials, complex neutral sources and coherent charged widths are retained. Actual original shifted source/static representatives equal the constructed family. The original weighted potential/static pairing is integrable, the transformed pairing is jointly integrable, and the original integral equals abs(momentumScale h)^(-2) times the iterated actual pairedDensity integral. The attachment assumes epsilon>0,h!=0,abs(h)<=epsilon/10, positive longitudinal widths and charged widths>=1, with arbitrary real potential coefficients. Actual finite-family five-dimensional completion derives all L1 and integration by parts. For norm(delta)<=1/20,m,g>=0,kappa>0, the fixed-clock relative lower loss is (2*h^2/epsilon)*(12+(m+3*g)/kappa). Its whole-clock lower bound and all-domain extension remain separate. A conditional abstract closed-form resolvent transfer proves bounded difference-energy contraction from an explicitly supplied selfadjoint Hilbert contraction and actual form lift/contraction. It supplies no physical static heat preservation. Separately, the actual radial regularizer J_N=I-N^(-1)*M_N maps every Hilbert vector into DomKr with Kr*J_Nf=M_Nf, is contractive, and converges strongly to the identity along N=n+1, without static/potential-domain premises. No residual form reconstruction is inferred. Prior actual half-clock preservation, exact residual operator domain split and radial domination remain unchanged. Transverse static preservation, full potential-domain control, DomS subset DomP, full H/G domination, simultaneous operator graph core, uniform G_N*(1+H(s))^(-1), stronger evolved domains and unrestricted response remain open. General curved gravity, interacting Standard Model dynamics in the same model, microscopic law and phase selection, controlled physical limits and empirical identification remain open. Earlier phase/harmonic identification requires revision. A physical TOE is not proved. This checkpoint adds65 theorems in13 modules, preserves3403 parent source/script hashes and adds15 for3418 total; exact root extends from8999 to9012 lines. All12 parent analytic artifacts and23 numerical files remain unchanged. Standard axioms only.'
PARENT = 'data/quantum_potential_clock_metric_audit.json'
PARENT_SHA = '63d9b80130c3b0762fd42da9333a47d02dfdf07334d7076c5cd737d70b7f3d7d'
REPORT = 'data/quantum_physical_transverse_hilbert_audit.json'
SCRIPTS = ['scripts/quantum_physical_transverse_hilbert_audit.py',
           'scripts/verify_quantum_physical_transverse_hilbert.py']
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
    assert len(old)==3403 and len(hashes)==3403+len(EXPECTED)+2
    assert all(hashes[p]==h for p,h in old.items())
    assert all(sha(root/p)==h for p,h in hashes.items())
    additions={'UnifiedTheory/Audit/'+n+'.lean' for n in EXPECTED}|set(SCRIPTS)
    assert set(hashes)-set(old)==additions
    assert [Path(x['source']).stem for x in report['modules']]==list(EXPECTED)
    logs=overlay/'quantum-physical-transverse-hilbert-audit'
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
    assert text.endswith(suffix) and len(text.splitlines())==8999+len(EXPECTED)
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
