#!/usr/bin/env python3
"""Check the actual shifted outputs, quadratic angular tilt and positive-vacuum joint closure and preserved evidence."""
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
    parser.add_argument('--baseline-overlay',required=True,type=Path)
    args=parser.parse_args()
    root=Path(__file__).resolve().parents[1]
    overlay=args.overlay.resolve(); baseline=args.baseline_overlay.resolve()
    assert overlay.is_dir() and baseline.is_dir() and overlay!=baseline
    env=os.environ.copy()
    env['LEAN_PATH']=str(overlay)+os.pathsep+str(baseline)+os.pathsep+env['LEAN_PATH']
    logs=overlay/'quantum-shifted-output-tilt-audit'
    logs.mkdir(exist_ok=False)
    assert sha(root/PARENT)==PARENT_SHA
    parent=json.loads((root/PARENT).read_text())
    hashes=dict(parent['source_sha256'])
    assert len(hashes)==3338 and all(sha(root/p)==h for p,h in hashes.items())
    additions=['UnifiedTheory/Audit/'+n+'.lean' for n in EXPECTED]+SCRIPTS
    assert not set(additions)&set(hashes)
    hashes.update({p:sha(root/p) for p in additions})
    analytic={k:v for k,v in parent.items() if k.startswith('analytic_')}
    assert len(analytic)==12 and not set(analytic)&set(EXTRA_ANALYTIC)
    analytic.update(EXTRA_ANALYTIC)
    assert all(sha(root/v['path'])==v['sha256'] for v in analytic.values())
    evidence=parent['numerical_evidence']
    numerical=[v for v in evidence.values() if isinstance(v,dict) and 'path' in v]
    assert len(numerical)==23 and all(sha(root/v['path'])==v['sha256'] for v in numerical)
    text=(root/'UnifiedTheory.lean').read_text()
    suffix=''.join('import UnifiedTheory.Audit.'+n+'\n' for n in EXPECTED)
    assert text.endswith(suffix)
    assert hashlib.sha256(text[:-len(suffix)].encode()).hexdigest()==parent['root_check']['source_sha256']
    assert len(text.splitlines())==8946+len(EXPECTED)
    root_hash=sha(root/'UnifiedTheory.lean')
    checks=[]; done=set()
    for name in EXPECTED:
        source='UnifiedTheory/Audit/'+name+'.lean'
        body=(root/source).read_text()
        needed=set(re.findall(r'^import UnifiedTheory\.Audit\.(\S+)',body,re.M))&set(EXPECTED)
        assert needed<=done,(name,needed-done)
        output=overlay/'UnifiedTheory/Audit'/(name+'.olean')
        assert not output.exists() and not output.is_symlink()
        output.parent.mkdir(parents=True,exist_ok=True)
        command=['lean','-j1','-o',str(output),source]
        result=subprocess.run(command,cwd=root,env=env,text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
        log=logs/(name+'.log'); log.write_text(result.stdout)
        assert result.returncode==0,str(log)
        audits=dependencies(result.stdout)
        assert set(audits)==declarations(name,body)
        assert output.is_file() and not output.is_symlink()
        checks.append(dict(source=source,command=command,exit_code=0,log_sha256=sha(log),audited_declarations=audits))
        done.add(name)
        print(name+': clean; '+str(len(audits))+' theorem dependency lists',flush=True)
    result=subprocess.run(['lean','-j1','UnifiedTheory.lean'],cwd=root,env=env,text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
    log=logs/'root-import.log'; log.write_text(result.stdout)
    assert result.returncode==0 and not result.stdout.strip(),str(log)
    assert sha(root/'UnifiedTheory.lean')==root_hash and sha(root/PARENT)==PARENT_SHA
    assert all(sha(root/p)==h for p,h in hashes.items())
    assert all(sha(root/v['path'])==v['sha256'] for v in [*analytic.values(),*numerical])
    assert all(not (root/'.lake/build/lib/lean/UnifiedTheory/Audit'/(n+'.olean')).exists() for n in EXPECTED)
    report=dict(**analytic,modules=checks,new_lean_theorem_count=sum(EXPECTED.values()),
        source_sha256=hashes,numerical_evidence=evidence,previous_report=dict(path=PARENT,sha256=PARENT_SHA),
        root_check=dict(command=['lean','-j1','UnifiedTheory.lean'],exit_code=0,empty_log=True,
            source_sha256=root_hash,log_sha256=sha(log),appended_imports=list(EXPECTED)),
        lean_toolchain=(root/'lean-toolchain').read_text().strip(),scope=SCOPE)
    target=root/REPORT
    assert not target.exists()
    target.write_text(json.dumps(report,indent=2)+'\n')
    print('Root passed; '+str(sum(EXPECTED.values()))+' theorem audits; '+str(len(hashes))+' source/script hashes.',flush=True)
    print(target,flush=True)


if __name__=='__main__':
    main()
