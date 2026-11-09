#!/usr/bin/env python3
"""Check unconditional full-strip potential-resolvent radial-root/growing-form regularity, growing radial-Yosida coercive accretivity and resolvent radial smoothing, exact growing-potential and Hamiltonian-residual second resolvent identities on Hilbert, 5-way Hamiltonian-resolvent three-operator synthesis, simultaneous Gaussian growing-clock core for G and P, second-power operator-graph cores Dom(A^2) for all 5 Hamiltonians, evolved form-core closure invariance, arbitrary-source affine and arbitrary-degree neutral-polynomial basis expansion with monomial amplitude absorption, 4D gravito-electric/gravito-magnetic Weyl decomposition, tidal bivector and gravitational-wave probe extraction, complete 20-component 4D Riemann curvature reconstruction, and preserved evidence."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess

EXPECTED = {
    'KFCausalClockFloorPotentialResolventRadialRootRegularity': 22,
    'KFCausalClockFloorGrowingRadialYosidaAccretivity': 31,
    'KFCausalClockFloorGrowingResolventRadialRegularity': 21,
    'KFCausalClockFloorGrowingPotentialSecondResolventIdentity': 32,
    'KFCausalClockFloorHamiltonianResidualSecondResolventIdentity': 34,
    'KFCausalClockFloorHamiltonianResolventThreeOperatorSynthesis': 27,
    'KFCausalClockFloorGrowingPotentialGaussianClockCore': 27,
    'KFCausalClockFloorSecondPowerOperatorCores': 32,
    'KFCausalClockFloorEvolvedFormCoreInvariance': 17,
    'KFCausalReciprocalNeutralArbitrarySourceAffinePolynomialDecomposition': 49,
    'KFCausalCommonComplexLinearMonomialAmplitudeAbsorption': 42,
    'KFCausalReciprocalNeutralArbitraryDegreePolynomialDecomposition': 38,
    'KFCausalCurved4DWeylElectricMagneticDecomposition': 41,
    'KFCausalCurved4DTidalWeylProbeExtraction': 30,
    'KFCausalCurved4DTwentyComponentRiemannMasterSynthesis': 14,
}
EXTRA_ANALYTIC = {}
SCOPE = 'Unconditional full-strip potential-resolvent radial-root and growing-form regularity, growing radial-Yosida coercive accretivity and resolvent radial smoothing, unconditional growing-potential and Hamiltonian-residual second resolvent identities on all of Hilbert, 5-way Hamiltonian-resolvent three-operator synthesis, simultaneous Gaussian growing-clock core for G and P, second-power operator-graph cores Dom(A^2) for all 5 Hamiltonians, evolved form-core closure invariance, arbitrary-source affine and arbitrary-degree neutral-polynomial monomial basis expansion with amplitude absorption, 4D gravito-electric/gravito-magnetic Weyl decomposition, tidal bivector and transverse-traceless gravitational-wave probe extraction, and complete 20-component 4D Riemann curvature reconstruction. Specifically, on the full strip 0<epsilon,h!=0,abs(h)<=pi*epsilon/3 and for all real m,g,k,t, the potential resolvent R_P(a) (a>0) satisfies norm(M_N^(1/2)(R_P(a)f))<=a^(-1)*norm(M_N^(1/2)f) and maps Dom(Kr^(1/2)) into Dom(Kr^(1/2)) intersect DomP subseteq DomTgrow with norm(Kr^(1/2)(R_P(a)f))<=a^(-1)*norm(Kr^(1/2)f) and norm(Tgrow(R_P(a)f))^2<=a^(-2)*norm(Kr^(1/2)f)^2+a^(-1)*norm(f)^2; the growing Hamiltonian G=Kr+P satisfies coercive Yosida and resolvent accretivity norm(M_N x)^2<=Re<Gx,M_N x> and norm(M_N^(1/2)x)^2<=Re<Gx,J_N x> on DomG (plus quadratic accretivity norm(M_N^(1/2)(M_N x))^2<=Re<Gx,M_N(M_N x)> and norm(Kr^(1/2)(J_N x))^2<=Re<Gx,J_N(J_N x)> on abs(h)<=pi*epsilon/4), yielding parabolic smoothing norm(Kr(R_G(a)f))<=min(norm(f),a^(-1/2)*norm(Kr^(1/2)f)) on Dom(Kr^(1/2)) and maximal radial contraction norm(Kr(R_G(a)f))<=min(norm(f),a^(-1)*norm(Kr f)) on DomKr. On all of Hilbert, the exact second resolvent identities R_P(a)f-R_G(a)f=R_P(a)(Kr(R_G(a)f)) and R_{S(t)}(a)f-R_{H(t)}(a)f=exp(2t)*R_{S(t)}(a)(Kr(R_{H(t)}(a)f)) hold unconditionally with explicit Hilbert, operator, form-channel, and clockHalf bounds; on DomH(t), exp(2t)*norm(M_N x)^2-(h^2/epsilon^2)*norm(x)^2<=Re<H(t)x,M_N x>, and R_{H(t)}(a)f satisfies the 5-way equivalence R_{H(t)}(a)f in DomP iff R_{H(t)}(a)f in DomT iff R_{H(t)}(a)f in DomG iff R_{H(t)}(a)f in commonOperatorDomain iff R_{S(t)}(a)(f-exp(2t)*Kr(R_{H(t)}(a)f)) in DomP with mutual norm domination among P,T,G. The smooth Gaussian growing clock core DomG intersect Dom(clockOperator) intersect Dom(clockHalf) is an unconditional operator-graph core for G (abs(h)<=pi*epsilon/3) and simultaneously for P (abs(h)<=pi*epsilon/4); the second-power domains Dom(A^2)={x in DomA | Ax in DomA} are unconditional operator-graph cores for all 5 Hamiltonians A in {T,P,G,S(t),H(t)} with 10-domain simultaneous regularity on Dom(H(t)^2); and formEvolution(s,t):VT(s)<->VT(t) preserves topological closures of all form cores with two-sided exponential difference bounds across all 5 channels. For finite sourced packet families with arbitrary differing complex source arrays b:Fin n->C, all 9 state, momentum, output, lift, and Hamiltonian maps are linear in P:Fin n->C[X] over Finset.sum, satisfy degree-r monomial amplitude absorption (a,C(c_i)*X^r)=(a*c,X^r) preserving all 14 energy and response functionals, and decompose any quadratic or degree-M polynomial profile P_i(X)=sum_{r<M} C(c_{r,i})*X^r into M unit-monomial profiles X^r. In 4D linearized Lorentzian geometry, weylTensor4D splits into the symmetric spatially traceless gravito-electric tensor E_{ab}=C_{0a0b} (E_{11}+E_{22}+E_{33}=0) and trace-free cyclic-Bianchi gravito-magnetic tensor B_{abc}=C_{0abc}, with exact 4D double-dual spatial Weyl reconstruction (C_{1212}=-E_{33},C_{1313}=-E_{22},C_{2323}=-E_{11},C_{1213}=E_{23},etc.), explicit transverse-traceless plus and cross gravitational-wave solutions (G_{mu nu}=0, nonvanishing pure-Weyl curvature E_{11}=-E_{22}=A, E_{12}=B) extracted by bivector tidal probes, and complete 10+5+5=20-component reconstruction and uniqueness of R_metric from (G_{mu nu},E_{ab},B_{abc}). Direct fixed-N invariance J_N(DomP) subseteq DomP without passing through R_P(a), unconditional membership R_{H(t)}(a)f in DomP for k<=0 without form pairing, proving D_uncond is a graph core for H(t) and G unconditionally, differing complex neutral sources at non-zero potential coupling in the response lower bound, higher-degree neutral-polynomial response lower bounds, trajectory-wide unbounded-momentum derivatives, nonlinear curved 4D gravity, interacting Standard Model dynamics in the same model, microscopic law and phase selection, controlled physical limits, and empirical identification remain open; the earlier phase/harmonic identification still requires revision. A physical TOE is not proved. This checkpoint adds457 theorems in15 modules, preserves3549 parent source/script hashes and adds17 for3566 total; exact root extends from9131 to9146 lines. All12 parent analytic artifacts and23 numerical files remain unchanged. Standard axioms only.'
PARENT = 'data/quarter_strip_resolvent_weyl_ricci_synthesis_audit.json'
PARENT_SHA = 'd681ef079f63f7aaf8ef7246b25f4af6beaa070f3d1a45ba9f0eef4d7dbc6d83'
REPORT = 'data/second_resolvent_weyl_twenty_component_synthesis_audit.json'
SCRIPTS = ['scripts/second_resolvent_weyl_twenty_component_synthesis_audit.py',
           'scripts/verify_second_resolvent_weyl_twenty_component_synthesis.py']
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
    logs=overlay/'second-resolvent-weyl-twenty-component-synthesis-audit'
    logs.mkdir(exist_ok=False)
    assert sha(root/PARENT)==PARENT_SHA
    parent=json.loads((root/PARENT).read_text())
    hashes=dict(parent['source_sha256'])
    assert len(hashes)==3549 and all(sha(root/p)==h for p,h in hashes.items())
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
    assert len(text.splitlines())==9131+len(EXPECTED)
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
