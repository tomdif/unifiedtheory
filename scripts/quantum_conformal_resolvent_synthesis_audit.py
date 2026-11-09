#!/usr/bin/env python3
"""Check uniform component/form resolvent domination, radial-resolvent and clock-Gaussian half-clock commutation, two-time form norm equivalence and sesquilinear resolvent comparison, unconditional static three-operator graph core, 4D conformal wave-variation-Bianchi continuum synthesis, and preserved evidence."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess

EXPECTED = {
    'KFCausalClockFloorGrowingComponentResolventBounds': 18,
    'KFCausalClockFloorHamiltonianComponentResolventBounds': 18,
    'KFCausalClockFloorUnconditionalOperatorFormEnergy': 41,
    'KFCausalClockFloorHamiltonianResolventFormBounds': 28,
    'KFCausalClockFloorRadialResolventSelfAdjointCommutation': 9,
    'KFCausalClockFloorRadialResolventClockCommutation': 25,
    'KFCausalClockFloorRadialResolventClockCore': 8,
    'KFCausalClockFloorGaussianClockCommutation': 18,
    'KFCausalClockFloorTwoTimeFormNormBounds': 14,
    'KFCausalClockFloorTwoTimeResolventDifference': 9,
    'KFCausalClockFloorTwoTimeFormResolventComparison': 16,
    'KFCausalFiniteThreeOperatorResolventRegularity': 22,
    'KFCausalClockFloorDisplacedMultiOperatorDomain': 21,
    'KFCausalClockFloorStaticThreeOperatorCore': 13,
    'KFCausalConformal4DLinearSuperpositionLimit': 32,
    'KFCausalConformal4DCoupledWaveVariationSynthesis': 26,
    'KFCausalConformal4DLorentzianBianchiTraceSynthesis': 15,
}
EXTRA_ANALYTIC = {}
SCOPE = 'Uniform component and form-energy resolvent domination, radial-resolvent and clock-Gaussian half-clock commutation, two-time form-norm equivalence and sesquilinear resolvent comparison, unconditional three-operator graph core for the static Hamiltonian T, and 4D conformal wave-variation-Bianchi continuum-limit synthesis under 0<epsilon,h!=0,abs(h)<=pi*epsilon/3. Specifically, for every a>0 and f in Hilbert, R_G(a)f lies in DomKr intersect DomP intersect Dom(clockHalf) with norm(Kr(R_G(a)f))^2+norm(P(R_G(a)f))^2+a^2*norm(R_G(a)f)^2<=norm(f)^2 and norm(Kr(J_N(R_G(a)f)))<=norm(f); unconditionally in real m,g,k,t, R_{H(t)}(a)f lies in DomKr intersect DomS(t) intersect Dom(clockHalf) with exp(4*t)*norm(Kr(R_{H(t)}(a)f))^2+norm(S(t)(R_{H(t)}(a)f))^2<=(1+2*exp(2*t)*(h^2/epsilon^2)*a^(-2))*norm(f)^2 and uniform radial Yosida bound exp(4*t)*norm(Kr(J_N(R_{H(t)}(a)f)))^2<=(1+2*exp(2*t)*(h^2/epsilon^2)*a^(-2))*norm(f)^2; every x in DomH(t) lies in Dom(T^(1/2)) intersect Dom(Kr^(1/2)) intersect DomTpot intersect DomTgrow intersect DomTres(t) with Re<H(t)x,x>=norm(T^(1/2)x)^2+exp(2*t)*norm(Kr^(1/2)x)^2+exp(2*t)*norm(PB(potentialLift(residualProject u)))^2, yielding norm(T^(1/2)(R_{H(t)}(a)f))^2+exp(2*t)*norm(Kr^(1/2)(R_{H(t)}(a)f))^2+a*norm(R_{H(t)}(a)f)^2<=a^(-1)*norm(f)^2 and analogous square-root resolvent bounds for R_{S(t)}(a) and R_G(a). Furthermore, the radial resolvent J_N=(I+N^(-1)*Kr)^(-1) and radial Yosida operator M_N=N*(I-J_N) are self-adjoint, positive, mutually commuting, satisfy J_N-J_{N_prime}=(N_prime^(-1)-N^(-1))*M_N*J_{N_prime}, commute with inverseL, defectOperator, and GaussianGrowingTransport, preserve Dom(clockHalf) and Dom(clockOperator), and map every u in FormSpace(t) with JT_t u in Dom(clockHalf) into the 8-way joint domain Dom(clockHalf) intersect DomKr intersect DomEavg(t) intersect DomTgrow intersect DomTres(t) intersect DomTstat intersect DomTpot intersect Dom(T^(1/2)); the clock-Gaussian multiplier action(epsilon,a,0) commutes with inverseL and defectOperator, maps all of Hilbert into Dom(clockHalf) intersect Dom(clockOperator) for a>0, and approximates every f in D_uncond intersect Dom(clockHalf) simultaneously in norm, clockHalf, T, Kr, P, G, S(t), and H(t) as a->0+. Between any two times s,t, residualFormTransfer(s,t) and formTransfer(s,t) satisfy sharp two-sided form-energy bounds with constants min(1,exp(2*(t-s))) and max(1,exp(2*(t-s))), two-time second resolvent difference bounds hold on D_uncond and on the finite sourced packet family, and the exact two-time form pairing identity <f,R_{H(s)}(a)g>-<R_{H(t)}(a)f,g>=(exp(2*t)-exp(2*s))*(<GB u_t,GB u_s>+<PB u_t,PB u_s>) holds for all f,g in Hilbert. Every ambient displaced state and the displaced static source core lie in D_uncond intersect Dom(clockHalf) for all real m,g,k, proving that D_uncond=DomH(t) intersect DomG=(DomT intersect DomKr intersect DomP) intersect DomTres(0) is an unconditional graph core for the static Hamiltonian T. In the curved 4D conformal diamond, the discrete BDG operator is linear over arbitrary probe superpositions and finite sums, separates Box_g phi(0)=8 from -(1/2)*R(0)=-6*c across two probes, converges jointly with its temporal difference quotient and derivative to (8-6*c,-6) uniquely determining the affine curvature and wave-curvature jets, and equates the BDG temporal variation limit -6 with (1/2)*(d/dc)Tr_g(G)|_0=-6 via the 4D Lorentzian contracted Bianchi identity Tr_g(G)=-R=-12*c. Operator-level radial resolvent invariance of DomT, DomP, DomS(t), DomG, and DomH(t), full operator-norm bound on P(a+H(t))^(-1) without form pairing, proving D_uncond is also a graph core for H(t) and G, differing complex neutral sources across packets, general neutral polynomials in the complex-source response bound, trajectory-wide unbounded-momentum derivatives, general non-conformal curved 4D gravity, interacting Standard Model dynamics in the same model, microscopic law and phase selection, controlled physical limits, and empirical identification remain open; the earlier phase/harmonic identification still requires revision. A physical TOE is not proved. This checkpoint adds333 theorems in17 modules, preserves3493 parent source/script hashes and adds19 for3512 total; exact root extends from9081 to9098 lines. All12 parent analytic artifacts and23 numerical files remain unchanged. Standard axioms only.'
PARENT = 'data/quantum_multi_operator_regularization_audit.json'
PARENT_SHA = '456663b71c3f99127bd6e8fb9b3dd5bff7792b17b7d3f3e507c408b67ed7b9cd'
REPORT = 'data/quantum_conformal_resolvent_synthesis_audit.json'
SCRIPTS = ['scripts/quantum_conformal_resolvent_synthesis_audit.py',
           'scripts/verify_quantum_conformal_resolvent_synthesis.py']
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
    logs=overlay/'quantum-conformal-resolvent-synthesis-audit'
    logs.mkdir(exist_ok=False)
    assert sha(root/PARENT)==PARENT_SHA
    parent=json.loads((root/PARENT).read_text())
    hashes=dict(parent['source_sha256'])
    assert len(hashes)==3493 and all(sha(root/p)==h for p,h in hashes.items())
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
    assert len(text.splitlines())==9081+len(EXPECTED)
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
