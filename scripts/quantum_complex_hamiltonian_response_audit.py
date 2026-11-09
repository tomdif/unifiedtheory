#!/usr/bin/env python3
"""Check the common-complex-source weighted Hamiltonian response, finite-packet potential/static operator bound, radial resolvent potential-form convergence, and preserved evidence."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess

EXPECTED = {
    'KFCausalAngularMassCircle': 9,
    'KFCausalAngularMassCircleCompact': 3,
    'KFCausalAngularMassMomentPolynomial': 4,
    'KFCausalAngularMassCircleLoss': 10,
    'KFCausalAngularMassGaussianSmoothing': 7,
    'KFCausalAngularMassQuadraticTilt': 9,
    'KFCausalAngularMassHardy': 4,
    'KFCausalChargedMassAngularLoss': 2,
    'KFCausalChargedMassScoreIBP': 3,
    'KFCausalChargedMassScoreAttachment': 2,
    'KFCausalChargedMassHardy': 4,
    'KFCausalChargedMassCorrectedBound': 4,
    'KFCausalChargedMassPhysicalBound': 1,
    'KFCausalCommonComplexMassNeutralIntegral': 3,
    'KFCausalCommonComplexMassJointEnergy': 3,
    'KFCausalCommonComplexMassResponseMarginal': 5,
    'KFCausalCommonComplexMassJointResponse': 4,
    'KFCausalCommonComplexMassActualBound': 2,
    'KFCausalCommonComplexMassClockKernel': 2,
    'KFCausalCommonComplexMassPotentialResponse': 4,
    'KFCausalCommonComplexGaussianWeightedTransport': 6,
    'KFCausalCommonComplexGaussianPotentialResponse': 2,
    'KFCausalCommonComplexGaussianHamiltonianResponse': 2,
    'KFCausalCommonComplexGaussianInitialResponse': 2,
    'KFCausalOrderedStaticIntegratedLower': 6,
    'KFCausalOrderedStaticPotentialHilbertBound': 4,
    'KFCausalFinitePotentialStaticGraph': 5,
    'KFCausalFinitePotentialStaticMixedBound': 5,
    'KFCausalClockFloorRadialResolventShifted': 5,
    'KFCausalClockFloorRadialResolventSections': 3,
    'KFCausalClockFloorRadialResolventPotential': 5,
    'KFCausalClockFloorRadialResolventPotentialForm': 5,
}
EXTRA_ANALYTIC = {}
SCOPE = 'For one common arbitrary complex neutral source A+iD and constant neutral polynomial P=1, the mass channel(2,0,0), vacuum channel(0,0,1), and arbitrary nonnegative weighted couplings mass2,quartic,vacuum>=0(including zero) now satisfy universal existential lower bounds on the original Hilbert potential response, full Hamiltonian response, strong DomH(t) pairing, and initial central-difference momentum expectation derivatives. Specifically, literal quadratic circle integrals, compact bounded-tilt control, singular endpoint Gamma-moment polynomial coercivity, neutral Gaussian smoothing, quadratic tilt mixing, and entire-circle Hardy modes(Tilt>=(d-2)*Energy) pass to the coherent charged packet, combine with proved one-dimensional charged score IBP and quadratic field Young inequalities to give the state-independent clock-fraction bound on the raw mass Joint response, and attach at(2,0,0) via genuine L1 and derivative uniqueness to yield potentialResponse(2,0,0)>=-(M/epsilon)*potentialEnergy(2,0,0). Combining(2,0,0), the prior(0,4,0) bound, and exact exp(A^2/(2*beta)) translation on(0,0,1) with the linear Wick decomposition gives universal existential K,M>=0(chosen before all coupling, packet-count, width, amplitude, and source parameters) such that potentialResponse>=-(M/epsilon)*potentialEnergy under epsilon>0,h!=0,abs(h)<=2*pi*epsilon/3,a_i>0,w_i>=1, fullResponse>=-(M/epsilon)*fullEnergy, strong operator pairing (-2/h)*Im<H(t)psi,Bpsi>>=-(M/epsilon)*Re<H(t)psi,psi> on DomH(t) under abs(h)<=pi*epsilon/3, and the corresponding regulator-limit and eventual lower bounds for initial derivatives of bounded momentum expectations along the nonautonomous evolution. Differing neutral sources across packets, general neutral polynomials, and trajectory-wide unbounded-momentum derivatives remain open. Separately, the five-dimensional potential/static lower bound integrates over the whole clock and attaches through actual ordered/reversed, radial, growing, potential, and static graphs to the closed potential Hamiltonian P and maximal static operator T on the original finite sourced packet family: Re<P*psi,T*psi>>=-((2*h^2/epsilon)*(12+(m+3*g)/k))*Re<psi,P*psi> for epsilon>0,h!=0,abs(h)<=epsilon/10,m,g>=0,k>0, retaining arbitrary source and polynomial arrays; extension beyond the finite packet family to all operator domains remains open. Finally, the shifted radial complement regularizers J_N=I-N^(-1)*M_N are bounded by2 on the complex strip and L2 orbit sections, preserve the literal original potential-output closure T_pot, map every potential-form vector into DomKr intersect DomT_pot, and converge strongly to the identity in the completed PotentialForm graph norm along N=n+1; potential operator domain invariance and residual form reconstruction are not claimed. Transverse static preservation, full potential-domain control, DomS subset DomP, full H/G domination, simultaneous operator graph core, uniform G_N*(1+H(s))^(-1), stronger evolved domains, general curved gravity, interacting Standard Model dynamics in the same model, microscopic law and phase selection, controlled physical limits, and empirical identification remain open; the earlier phase/harmonic identification still requires revision. A physical TOE is not proved. This checkpoint adds135 theorems in32 modules, preserves3418 parent source/script hashes and adds34 for3452 total; exact root extends from9012 to9044 lines. All12 parent analytic artifacts and23 numerical files remain unchanged. Standard axioms only.'
PARENT = 'data/quantum_physical_transverse_hilbert_audit.json'
PARENT_SHA = '4b4ce9c358eed1fa41cc81e592f33fbe038f47694e8d8a92b7a749c0069aa1e2'
REPORT = 'data/quantum_complex_hamiltonian_response_audit.json'
SCRIPTS = ['scripts/quantum_complex_hamiltonian_response_audit.py',
           'scripts/verify_quantum_complex_hamiltonian_response.py']
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
    logs=overlay/'quantum-complex-hamiltonian-response-audit'
    logs.mkdir(exist_ok=False)
    assert sha(root/PARENT)==PARENT_SHA
    parent=json.loads((root/PARENT).read_text())
    hashes=dict(parent['source_sha256'])
    assert len(hashes)==3418 and all(sha(root/p)==h for p,h in hashes.items())
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
    assert len(text.splitlines())==9012+len(EXPECTED)
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
