#!/usr/bin/env python3
"""Check the actual Gaussian common graph approximation and endpoint moments and preserved evidence."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess

EXPECTED = {'KFCausalClockFloorRadialYosidaStrongLimit': 2, 'KFCausalClockFloorGrowingRadialCrossEstimate': 5, 'KFCausalClockFloorGaussianGrowingTransport': 9, 'KFCausalClockFloorGaussianGrowingForm': 5, 'KFCausalClockFloorGaussianGrowingOutputPairing': 4, 'KFCausalClockFloorGaussianGrowingRadialPairing': 9, 'KFCausalClockFloorGaussianGrowingApproximation': 3, 'KFCausalClockFloorGaussianGrowingDomain': 4, 'KFCausalClockFloorGaussianStaticCommutation': 5, 'KFCausalClockFloorGaussianCommonDomainApproximation': 4, 'KFCausalAngularQuarticEndpoint': 9, 'KFCausalAngularGammaMomentBounds': 9, 'KFCausalAngularGammaMomentConvergence': 4}
EXTRA_ANALYTIC = {'analytic_common_complex_quartic_finite_angular_loss': {'path': 'data/quantum_common_complex_quartic_finite_angular_loss_20261022.txt', 'sha256': '88c301c66d2da58e0c9a014788d2240cde24a1df02521ef59de6cde6ca5854bb', 'status': 'Independently reviewed analytic existence proof candidate, not a Lean response theorem. For a common arbitrary complex neutral source, P=1 and the original strict coherent width margins, the repeated-linear quartic channel has a finite universal angular loss C4. Actual singular endpoint moments and a uniformly positive limiting quartic supply large-tilt positivity; compactness handles bounded tilt. Neutral Gaussian smoothing, tilt Gaussian mixing, actual Abel-circle constraints and degree-two Hardy control yield the finite response coefficient 1200+(25/4)*C4. C4 is not evaluated; the old536 coefficient is not claimed. Full circle/Abel/Hardy/clock attachment, general source classes and evolved uniform response remain open.'}}
SCOPE = 'Actual centered Gaussian clock multipliers now preserve the growing Hamiltonian domain, with an exact operator identity on every DomG vector. With M_y=exp[-a*(chart+i*y)^2], a>=0, G M_0 x=M_-h Gx+M_0 Krx-M_-h Krx. The hypotheses are epsilon>0, h!=0 and abs(h)<=pi*epsilon/3, with arbitrary original mass/quartic/vacuum parameters. The proof retains the original simultaneous weighted graph closure, natural half-clock shifts, actual charge-averaged sections and the growing output closure. The previously proved radial inclusion supplies the second root graph and its exact form pairing; no separate potential-domain assumption is used. The actual Gaussian action converges strongly to the identity, including its L2 section lift. It commutes with the actual maximal static multiplier T through the proved complementary Fourier representation and hence with the identified original static Hamiltonian. For every x in DomT intersect DomG, the explicit sequence a_n=1/(n+1) stays in that intersection and (M_0 x,T M_0 x,G M_0 x) converges to (x,Tx,Gx). This is simultaneous Gaussian graph approximation, not a proof of a joint finite-packet operator core or removal of the original full-form range restriction. Separately, the actual rational radial cutoffs converge strongly to Kr on its full maximal domain. Passing the proved cutoff pairing inequality to the limit gives norm(Kr x)^2<=Re inner(Gx,Kr x), then norm(Kr x)^2+norm((G-Kr)x)^2<=norm(Gx)^2 for every DomG vector. Identification of this remainder with a separately completed potential Hamiltonian is not part of this checkpoint. For the response route, nine Lean theorems prove the exact endpoint quartic SOS, global lower bound (1+s^4)/108, and stability under five coefficient errors at most1/1080, yielding (1+s^4)/216 uniformly for all real s. Thirteen further Lean theorems prove actual singular endpoint kernel integrability, its exact correction integral4z, an endpoint-tail bound4z*(2z)^j*exp(-z) tending to zero, interior dominated convergence and actual Gamma moment convergence for every natural j. The normalizer is eventually positive and actual normalized moments converge to Gamma(j+1/2)/Gamma(1/2). No desired moment limit is assumed. The new independently reviewed analytic artifact uses these endpoint ideas, compact bounded-tilt positivity, linked Gaussian mixtures, the Abel-circle marginal and degree-two Hardy control to obtain a finite universal quartic loss C4 and an analytic response coefficient1200+(25/4)*C4 for common complex neutral source and P=1 under the original strict margins. C4 is not evaluated; no536 quartic constant is claimed. The actual coefficient attachment, circle pushforward, compact positive-energy bound, mixtures, Hardy/score/clock assembly and final physical response are not yet fully Lean-certified. Joint full H/G operator control, the uniform G_N*(1+H(s))^(-1) estimate, stronger evolved domains, the original full-form range restriction and the interacting static/growing mixed estimate remain open. General mixed/differing neutral sources and general neutral polynomials remain outside the proved response bounds. General curved gravity, interacting Standard Model dynamics in the same model, microscopic law/phase selection, controlled physical limits and empirical identification remain unproved. Earlier phase/harmonic identification requires revision. A physical TOE is not proved. This checkpoint adds 72 theorems in 13 modules, preserves3308 parent source/script hashes and adds15 for3323 total; the root extends from8920 to8933 lines. All11 parent analytic artifacts and23 numerical files remain unchanged, with one new reviewed analytic artifact for12 total. Standard axioms only.'
PARENT = 'data/quantum_growing_radial_domination_audit.json'
PARENT_SHA = 'd63cf0d35676342776cd9acb338602b183ff899b0bdbb85dab32943ff4757640'
REPORT = 'data/quantum_gaussian_common_graph_audit.json'
SCRIPTS = ['scripts/quantum_gaussian_common_graph_audit.py',
           'scripts/verify_quantum_gaussian_common_graph.py']
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
    logs=overlay/'quantum-gaussian-common-graph-audit'
    logs.mkdir(exist_ok=False)
    assert sha(root/PARENT)==PARENT_SHA
    parent=json.loads((root/PARENT).read_text())
    hashes=dict(parent['source_sha256'])
    assert len(hashes)==3308 and all(sha(root/p)==h for p,h in hashes.items())
    additions=['UnifiedTheory/Audit/'+n+'.lean' for n in EXPECTED]+SCRIPTS
    assert not set(additions)&set(hashes)
    hashes.update({p:sha(root/p) for p in additions})
    analytic={k:v for k,v in parent.items() if k.startswith('analytic_')}
    assert len(analytic)==11 and not set(analytic)&set(EXTRA_ANALYTIC)
    analytic.update(EXTRA_ANALYTIC)
    assert all(sha(root/v['path'])==v['sha256'] for v in analytic.values())
    evidence=parent['numerical_evidence']
    numerical=[v for v in evidence.values() if isinstance(v,dict) and 'path' in v]
    assert len(numerical)==23 and all(sha(root/v['path'])==v['sha256'] for v in numerical)
    text=(root/'UnifiedTheory.lean').read_text()
    suffix=''.join('import UnifiedTheory.Audit.'+n+'\n' for n in EXPECTED)
    assert text.endswith(suffix)
    assert hashlib.sha256(text[:-len(suffix)].encode()).hexdigest()==parent['root_check']['source_sha256']
    assert len(text.splitlines())==8920+len(EXPECTED)
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
