#!/usr/bin/env python3
"""Independently verify the shifted-output-tilt audit and preserved evidence."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess

EXPECTED = {'KFCausalClockFloorPositiveVacuumJointClosed': 5, 'KFCausalAngularGaussianTiltKernel': 5, 'KFCausalAngularQuarticQuadraticTilt': 9, 'KFCausalIndependentRadialComplexBaseline': 2, 'KFCausalBroadPairedGaussianOutputBaseline': 5, 'KFCausalIndependentRadialShiftedBaseline': 3, 'KFCausalIndependentRadialMomentOutputRepresentative': 2}
EXTRA_ANALYTIC = {}
SCOPE = 'For positive vacuum coupling kappa>0, the original weighted joint energy graph is itself closed. The retained nonzero Q output controls the intermediate vector in the actual Phi*Q and Phi^2*Q compositions. The generic weighted statement needs only nonzero seventh weight, allowing zero other weights. It uses closed primitive clock, momentum, Q, Phi and Phi^2 graphs; no separate closure-domain equality is assumed. The literal closedEnergy therefore equals initialEnergy and its graph/domain are exactly the original weighted natural graph/domain. No clock strip restriction is needed for this base closure statement. Zero vacuum and reconstruction of the averaged full-form range remain separate. Actual quadratic Gaussian tilt mixing is proved by shifted Gaussian zero/first moments and explicit product L1 domination. The same finite circle constant survives both neutral smoothing and quadratic tilt mixing: for every sigma,d>=0 and real q,mu,l, the literal circle energy E=integral exp(d*cos(theta)^2-q*cos(theta))*[(mu+l*cos(theta))^4+6*sigma*(mu+l*cos(theta))^2+3*sigma^2] satisfies 2*Tilt-l*deriv_l(E)+C*E>=0, where Tilt has the factor2*d*cos(theta)^2-q*cos(theta). The actual field derivative is derived; zero sigma/d and arbitrary signed linear tilt are included. C is finite but not evaluated. Original coherent charged polar/Abel attachment, Hardy/score/clock assembly and final physical response remain open. The actual broad paired ordered Gaussian output now equals the explicit holomorphic baseline almost everywhere in straightened clock coordinates. The proof starts with the actual physical Fourier representative, applies the null-set-preserving real mixed chart, and uses exact complex-flow quadratic and clock-prefactor identities. Output(h) corresponds to q-i*h/2, and output(2*h) to q-i*h. The normalization pi/(4*W*alpha) and full neutral shear are retained, with no extra inverse-clock factor. No arbitrary L2 representative is analytically continued. The generic attachment assumes positive epsilon,a,alpha,W,wL,wR, pi^2/alpha=alpha*c^2 and abs(h)<=2*pi*epsilon/3. Specialization to groundWidth(h) and momentumScale(h), under h!=0,abs(h)<=epsilon/10 and original widths>=1, gives actual half/full output representatives for every radial moment order, field-power order, complex source, clock source and neutral polynomial. The bounded multiplier actions and the original natural exponential graphs are retained. Attachment of Q(Tf), the interacting static/growing mixed estimate, joint full H/G control, uniform G_N*(1+H(s))^(-1), stronger evolved domains and unrestricted physical response remain open. General curved gravity, interacting Standard Model dynamics in the same model, microscopic law/phase selection, controlled physical limits and empirical identification remain unproved. Earlier phase/harmonic identification requires revision. A physical TOE is not proved. This checkpoint adds31 theorems in7 modules, preserves3338 parent source/script hashes and adds9 for3347 total; the root extends from8946 to8953 lines. All12 parent analytic artifacts and23 numerical files remain unchanged. Standard axioms only.'
PARENT = 'data/quantum_potential_angular_closure_audit.json'
PARENT_SHA = 'b8cba3f6218676f2cf62877060de3e33a6d319d6db587198393bbfc038766839'
REPORT = 'data/quantum_shifted_output_tilt_audit.json'
SCRIPTS = ['scripts/quantum_shifted_output_tilt_audit.py',
           'scripts/verify_quantum_shifted_output_tilt.py']
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
    assert len(old)==3338 and len(hashes)==3338+len(EXPECTED)+2
    assert all(hashes[p]==h for p,h in old.items())
    assert all(sha(root/p)==h for p,h in hashes.items())
    additions={'UnifiedTheory/Audit/'+n+'.lean' for n in EXPECTED}|set(SCRIPTS)
    assert set(hashes)-set(old)==additions
    assert [Path(x['source']).stem for x in report['modules']]==list(EXPECTED)
    logs=overlay/'quantum-shifted-output-tilt-audit'
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
    assert text.endswith(suffix) and len(text.splitlines())==8946+len(EXPECTED)
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
