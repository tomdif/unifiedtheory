#!/usr/bin/env python3
"""Check unconditional operator-level radial-resolvent invariance of DomT and DomT intersect DomKr with explicit O(N^(-1/2)) commutator, shifted radial-resolvent adjoint pairing and unconditional DomG=DomKr intersect DomP decomposition, positive-vacuum time-independent operator domains and two-time resolvent continuity, multi-operator radial-resolvent synthesis, arbitrary-source and scalar-polynomial response, evolved form-energy regularity, curved 4D conformal diamond master synthesis, and preserved evidence."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess

EXPECTED = {
    'KFCausalClockFloorRadialYosidaSecondDerivative': 14,
    'KFCausalClockFloorRadialResolventStaticFormPairing': 23,
    'KFCausalClockFloorRadialResolventStaticDomain': 21,
    'KFCausalClockFloorRadialResolventShiftedPairing': 21,
    'KFCausalClockFloorRadialResolventShiftedOrderedTransport': 18,
    'KFCausalClockFloorRadialResolventPotentialDomain': 19,
    'KFCausalClockFloorRadialResolventGrowingDomain': 19,
    'KFCausalClockFloorPositiveVacuumTwoTimeOperatorDomain': 53,
    'KFCausalClockFloorPositiveVacuumTwoTimeResolventContinuity': 36,
    'KFCausalClockFloorRadialResolventStaticRadialCore': 36,
    'KFCausalClockFloorRadialResolventMultiOperatorSynthesis': 32,
    'KFCausalReciprocalNeutralArbitrarySourceClockKineticResponse': 56,
    'KFCausalCommonComplexScalarPolynomialHamiltonianResponse': 52,
    'KFCausalClockFloorEvolvedFormEnergyRegularity': 63,
    'KFCausalConformal4DAnisotropicSpatialProbeSynthesis': 38,
    'KFCausalConformal4DOffDiagonalShearCurvatureSynthesis': 21,
    'KFCausalConformal4DCurvedDiamondMasterSynthesis': 10,
}
EXTRA_ANALYTIC = {}
SCOPE = 'Unconditional operator-level radial-resolvent and Yosida invariance of DomT and DomT intersect DomKr with explicit O(N^(-1/2)) commutator rate, shifted radial-resolvent Schwarz reflection and two-shift ordered transport, unconditional operator-level decomposition DomG=DomKr intersect DomP with Gx=Krx+Px and reduction J_N f in DomG iff J_N f in DomP, positive-vacuum time-independent operator-intersection domains and two-time resolvent continuity, 7-operator radial-resolvent synthesis on D_uncond, arbitrary-source zero-coupling and common-complex scalar-polynomial Hamiltonian response bounds, trajectory-wide evolved form-energy regularity, and curved 4D conformal diamond anisotropic/off-diagonal/master synthesis under 0<epsilon,h!=0,abs(h)<=pi*epsilon/3. Specifically, the second symmetric directional derivative of the radial Yosida symbol satisfies abs(d_{q_i}^2 m_N(x))<=6/epsilon uniformly in N>0, yielding integration-by-parts on StaticForm and proving unconditionally for all h!=0 and N>0 that x in DomT implies J_N x in DomT intersect DomKr intersect Dom(clockHalf) and M_N x in DomT intersect Dom(clockHalf) with explicit commutator bound norm(T(J_N x)-J_N(T x))<=3*N^(-1)*(abs(h)*sqrt(N/epsilon)/sqrt(epsilon))*sqrt(norm(T x)*norm(x))+N^(-1)*(6*h^2/epsilon^2)*norm(x)->0, so DomT intersect DomKr is an unconditional operator-graph core for T. On the complex strip abs(y)<=pi*epsilon/6, Schwarz reflection conj(line(epsilon,h,N,y,x))=line(epsilon,h,N,-y,x) yields <J_N^(y) f,g>=<f,J_N^(-y) g>, general two-shift contour transport (y_0,y_1) with y_1=y_0-h/2 preserves all ordered clock and matter factor graphs, and unconditionally DomG=DomKr intersect DomP with Gx=Krx+Px and D_uncond=DomT intersect DomKr intersect DomP=DomT intersect DomG, reducing J_N x in D_uncond on DomT to J_N x in DomP. Unconditionally, Dom(T^(1/2)) lies in Dom(clockHalf) with norm(clockHalf f)<=sqrt(2)*norm(T^(1/2) f) and norm(clockHalf x)^2<=2*norm(x)*norm(T x) on DomT; under positive vacuum k>0, all operator-intersection domains equal D_uncond=DomT intersect DomKr intersect DomP time-independently, and two-time operator and resolvent differences converge strongly in Hilbert, static-root, clockHalf, radial, and Hamiltonian norms as s->t. Arbitrary complex source arrays with constant neutral polynomials satisfy the exact zero-coupling full Hamiltonian response bound >=-(1/(4*epsilon))*fullEnergy, common-complex-source response extends to all packet-dependent degree-0 complex polynomials P_i=C(d_i), and nonautonomous evolution U(s,t) preserves the 5-operator form domain with explicit exponential bounds on all 5 form-energy channels. In the 4D curved conformal diamond, finite probe sums and 4-axis/off-diagonal polarization probes reconstruct all 10 symmetric Hessian components from G_{mu nu} and satisfy simultaneous BDG wave-curvature extraction, coupled matter-curvature Euler-Lagrange stationarity, and contracted Bianchi conservation. Unconditional operator-level radial-resolvent invariance of DomP without the forward-shift form hypothesis, full operator-norm bound on P(a+H(t))^(-1) without form pairing, proving D_uncond is a graph core for H(t) and G unconditionally, differing complex neutral sources at non-zero potential coupling, higher-degree neutral polynomials in the complex-source response bound, trajectory-wide unbounded-momentum derivatives, general non-conformal curved 4D gravity, interacting Standard Model dynamics in the same model, microscopic law and phase selection, controlled physical limits, and empirical identification remain open; the earlier phase/harmonic identification still requires revision. A physical TOE is not proved. This checkpoint adds532 theorems in17 modules, preserves3512 parent source/script hashes and adds19 for3531 total; exact root extends from9098 to9115 lines. All12 parent analytic artifacts and23 numerical files remain unchanged. Standard axioms only.'
PARENT = 'data/quantum_conformal_resolvent_synthesis_audit.json'
PARENT_SHA = 'd091412ba6ffefc5405f43e03ddcdbdb8e7a3444fb179c26e4652ef8e4a8fade'
REPORT = 'data/radial_resolvent_domain_conformal_master_audit.json'
SCRIPTS = ['scripts/radial_resolvent_domain_conformal_master_audit.py',
           'scripts/verify_radial_resolvent_domain_conformal_master.py']
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
    logs=overlay/'radial-resolvent-domain-conformal-master-audit'
    logs.mkdir(exist_ok=False)
    assert sha(root/PARENT)==PARENT_SHA
    parent=json.loads((root/PARENT).read_text())
    hashes=dict(parent['source_sha256'])
    assert len(hashes)==3512 and all(sha(root/p)==h for p,h in hashes.items())
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
    assert len(text.splitlines())==9098+len(EXPECTED)
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
