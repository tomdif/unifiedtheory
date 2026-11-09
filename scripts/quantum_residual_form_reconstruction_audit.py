#!/usr/bin/env python3
"""Check unconditional growing/residual/full form reconstruction, positive-vacuum three-operator domain decomposition, finite-packet full Hamiltonian domination, and preserved evidence."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess

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
    assert names==printed and len(names)==EXPECTED[name],(name,len(names),len(printed),EXPECTED[name])
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
    logs=overlay/'quantum-residual-form-reconstruction-audit'
    logs.mkdir(exist_ok=False)
    assert sha(root/PARENT)==PARENT_SHA
    parent=json.loads((root/PARENT).read_text())
    hashes=dict(parent['source_sha256'])
    assert len(hashes)==3452 and all(sha(root/p)==h for p,h in hashes.items())
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
    assert len(text.splitlines())==9044+len(EXPECTED)
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
