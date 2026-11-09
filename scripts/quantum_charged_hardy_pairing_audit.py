#!/usr/bin/env python3
"""Check the actual charged Hardy attachment, original mixed pairing and transverse line integration by parts and preserved evidence."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess

EXPECTED = {'KFCausalOrderedStaticPotentialPairing': 7, 'KFCausalComplexGaussianLineIBP': 6, 'KFCausalIndependentRadialTransverseLines': 7, 'KFCausalChargedQuarticScoreAttachment': 3, 'KFCausalChargedQuarticHardy': 4, 'KFCausalQuarticFieldSlopeBound': 3}
EXTRA_ANALYTIC = {}
SCOPE = 'The original finite-packet potential/static pairing is now the literal common mixed-chart integral. Primitive reversed exponential graphs move Q; graph uniqueness identifies the actual second outputs with original rows7,5,6 at field powers0,2,4; the proved static zero-charge sector removes the projection. The actual half output is physicalField^k times the original sourced numerator, and Q(T psi) is its proved ordered static profile. Actual Hilbert outputs establish absolute integrability. The physical hypotheses retain epsilon>0,h!=0,abs(h)<=epsilon/10,positive packet clock widths and reciprocal charged widths>=1, with arbitrary finite complex sources and neutral polynomials. A finite coherent complex quadratic Gaussian on the real line has derived polynomial-weighted L2 regularity, genuine derivatives of every finite jet, cross-term L1 and polarized polynomial-weight integration by parts, assuming only positive real quadratic coefficients. The actual complex-sheared transverse packet is exactly such a line packet. Its line widths have positive real parts from the original normalized shear, alpha>0,wL>0,wR>=1 and norm(delta)<=1/5. The actual half-clock shift gives norm(delta)<=1/20 under abs(h)<=epsilon/10. Coherent coordinate-line derivatives and weighted whole-line IBP therefore require no boundary condition, derivative premise or independent Gaussian-jet substitution. Full five-dimensional transverse Fubini, the physical metric coercivity estimate and the final mixed bound remain separate. The literal charged quartic energy, field and tilt now equal the exact actual one-dimensional score marginals by measure-preserving reordering with original Gaussian L1. The derived cooling/score inequality is consequently expressed in the same charged integrals. The entire-circle Hardy inequality passes to the full coherent charged integral: T>=d*integral(v^2*energyDensity)-4*E, for sigma,d>=0,Re(p)>0,positive widths and d<2*Re(p)*wi. The stronger radius lower bound is weakened to v^2 before polar integration, so no extra u^2 integrability premise is imposed. The exact same v^2 moment and bound attach to the actual score marginal under alpha>0,abs(Im(r))<Re(r) and the corresponding strict margins. For W_sigma(x)=x^4+6*sigma*x^2+3*sigma^2, the pointwise bound sigma*(W_prime)^2<=4*W^2 holds for sigma>=0. For sigma,a>0 and real R,v,x, R*v*W_prime>=-a*v^2*W-R^2/(a*sigma)*W. This absorbs a linked field term without dividing by the coherent energy. The physical coefficient and clock-response assembly remain open. The original full-H cutoff test, full H/G domination, simultaneous operator graph core, uniform G_N*(1+H(s))^(-1), stronger evolved domains and unrestricted physical response remain unproved. Positive-vacuum form reconstruction and the previous scoped bounds remain unchanged. General curved gravity, interacting Standard Model dynamics in the same model, microscopic law/phase selection, controlled physical limits and empirical identification remain open. Earlier phase/harmonic identification requires revision. A physical TOE is not proved. This checkpoint adds30 theorems in6 modules, preserves3367 parent source/script hashes and adds8 for3375 total; the exact root extends from8971 to8977 lines. All12 parent analytic artifacts and23 numerical files remain unchanged. Standard axioms only.'
PARENT = 'data/quantum_hardy_joint_domain_audit.json'
PARENT_SHA = 'b73cc0ddee18ee47af2224a971db9c73bfc15e137c2f707603e25b51020478d7'
REPORT = 'data/quantum_charged_hardy_pairing_audit.json'
SCRIPTS = ['scripts/quantum_charged_hardy_pairing_audit.py',
           'scripts/verify_quantum_charged_hardy_pairing.py']
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
    logs=overlay/'quantum-charged-hardy-pairing-audit'
    logs.mkdir(exist_ok=False)
    assert sha(root/PARENT)==PARENT_SHA
    parent=json.loads((root/PARENT).read_text())
    hashes=dict(parent['source_sha256'])
    assert len(hashes)==3367 and all(sha(root/p)==h for p,h in hashes.items())
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
    assert len(text.splitlines())==8971+len(EXPECTED)
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
