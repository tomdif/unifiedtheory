#!/usr/bin/env python3
"""Check the actual potential domains, global quartic circle loss and ordered Fourier output and preserved evidence."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess

EXPECTED = {'KFCausalClockFloorPotentialOutputClosure': 5, 'KFCausalClockFloorPotentialHamiltonian': 6, 'KFCausalClockFloorGrowingPotentialSum': 5, 'KFCausalAngularQuarticMomentPolynomial': 4, 'KFCausalAngularQuarticCircle': 9, 'KFCausalAngularQuarticCircleCompact': 3, 'KFCausalAngularCosineEndpoint': 4, 'KFCausalAngularQuarticCircleEndpoint': 6, 'KFCausalAngularQuarticCircleLoss': 4, 'KFCausalAngularQuarticGaussianMoments': 7, 'KFCausalAngularQuarticGaussianSmoothing': 7, 'KFCausalBroadPairedGaussianOutputProfile': 4, 'KFCausalBroadPairedGaussianOutputFourier': 5}
EXTRA_ANALYTIC = {}
SCOPE = 'The actual growing Hamiltonian G is proved equal to the natural operator sum Kr+P, where Kr is the previously identified maximal radial multiplier and P is the self-adjoint Hamiltonian of the literal closure of the original three ordered-potential rows on the original reference form. For epsilon>0, h!=0, abs(h)<=pi*epsilon/3 and arbitrary original mass/quartic/vacuum parameters, DomG=DomKr intersect DomP and norm(Kr x)^2+norm(Px)^2<=norm(Gx)^2 on every DomG vector. The potential closure has actual dense reference image and receives the growing-form projection. Dense variational testing identifies Px=Gx-Krx; self-adjoint maximality supplies the reverse operator inclusion. Zero couplings are included. No separate-domain equality or joint operator core is assumed. For the response route, actual singular Gamma moment convergence is attached to the exact quartic polynomial. The literal cosine-circle integral has its proved endpoint change of variables, including the full Jacobian and normalization. Large positive tilt has a nonnegative linked quartic defect uniformly for all real field coefficients. Strict positivity and actual parameter continuity give a finite compact-tilt loss; reflection extends it to every signed tilt. Thus one finite C>=0 satisfies 2*tilt-l*d_l(energy)+C*energy>=0 for every real z, mu and l in the actual circle energy integral exp(-z*cos(theta))*(mu+l*cos(theta))^4. The field derivative is derived by dominated differentiation, and the zero field pair is included. Actual Gaussian moments, polynomial product integrability and Fubini prove neutral Gaussian smoothing of energy, field slope, tilt and defect. The same universal C works for weight x^4+6*sigma*x^2+3*sigma^2 for every sigma>=0, including zero. No desired moment limit, change of variables, response inequality or Gaussian mixture identity is assumed. The finite constant is not evaluated. Quadratic tilt mixing, the actual Abel marginal attachment, Hardy/score/clock assembly and final common-complex physical response remain separate open proof obligations. The actual broad paired Gaussian ordered output now has a proved physical representative for all positive widths. Its actual partial Fourier representative is derived from slice Gaussian integrability and fiber Plancherel, retaining pi*w/(alpha*r^2), the clock amplitude and the neutral shear. This does not yet identify its straightened-clock representative with the holomorphic baseline, or supply the full interacting static/growing mixed estimate. The original full-form range restriction, joint full H/G graph control, uniform G_N*(1+H(s))^(-1) estimate and stronger evolved domains remain open. General differing sources and neutral polynomials remain outside the response result. General curved gravity, interacting Standard Model dynamics in the same model, microscopic law/phase selection, controlled physical limits and empirical identification remain unproved. Earlier phase/harmonic identification requires revision. A physical TOE is not proved. This checkpoint adds 69 theorems in 13 modules, preserves3323 parent source/script hashes and adds15 for3338 total; the root extends from8933 to8946 lines. All12 parent analytic artifacts and23 numerical files remain unchanged. Standard axioms only.'
PARENT = 'data/quantum_gaussian_common_graph_audit.json'
PARENT_SHA = 'c177880f88ab71b4b372280c5e2869e855f5a27c60a9bb1fb931c881aa3b5976'
REPORT = 'data/quantum_potential_angular_closure_audit.json'
SCRIPTS = ['scripts/quantum_potential_angular_closure_audit.py',
           'scripts/verify_quantum_potential_angular_closure.py']
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
    logs=overlay/'quantum-potential-angular-closure-audit'
    logs.mkdir(exist_ok=False)
    assert sha(root/PARENT)==PARENT_SHA
    parent=json.loads((root/PARENT).read_text())
    hashes=dict(parent['source_sha256'])
    assert len(hashes)==3323 and all(sha(root/p)==h for p,h in hashes.items())
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
    assert len(text.splitlines())==8933+len(EXPECTED)
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
