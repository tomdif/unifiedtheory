#!/usr/bin/env python3
"""Independently verify the sm-quantum-gravitational-resolvent-bianchi-synthesis audit and preserved evidence."""
import argparse
import hashlib
import json
from pathlib import Path
import re

EXPECTED = {
    'KFCausalClockFloorStaticResidualSecondResolventIdentity': 36,
    'KFCausalClockFloorFullFiveResolventChainSynthesis': 37,
    'KFCausalClockFloorSMForcedGaugeResolventBridge': 37,
    'KFCausalClockFloorPositiveVacuumResolventRegularity': 31,
    'KFCausalClockFloorPositiveVacuumUnconditionalCoreBridge': 30,
    'KFCausalClockFloorSMAnomalyCancellationQuantumBridge': 30,
    'KFCausalClockFloorIteratedResolventSecondPowerCore': 30,
    'KFCausalClockFloorSMElectroweakHiggsPotentialBridge': 31,
    'KFCausalClockFloorSMHilbertBridgeMasterSynthesis': 28,
    'KFCausalCommonComplexDegreeMPolynomialResponseLowerBound': 38,
    'KFCausalSMThreeGenerationFiberMultiPacketInstantiation': 37,
    'KFCausalSMYukawaHierarchyMultiPacketSynthesis': 37,
    'KFCausalCurved4DDifferentialBianchiIdentity': 32,
    'KFCausalCurved4DYangMillsStressEnergyCoupling': 33,
    'KFCausalCurved4DSMEinsteinWeylYangMillsMasterSynthesis': 24,
}
EXTRA_ANALYTIC = {}
SCOPE = 'Static-residual and full five-operator second resolvent chain synthesis, Standard Model forced-gauge and Weinberg-angle resolvent bridge, positive-vacuum (k > 0) unconditional resolvent regularity and simultaneous five-operator clock core bridge, Standard Model quantum anomaly cancellation and positive-vacuum hypercharge trace bridge, iterated resolvent mapping into second-power cores Dom(A^2) across all 5 Hamiltonians, Standard Model electroweak-Higgs potential and spectral-gap mass bridge, 16-component and 126-component SM-QM-QG Hilbert evolution master synthesis, arbitrary-degree neutral polynomial response lower bounds, Standard Model three-generation fiber and Yukawa/CKM hierarchy multi-packet instantiation, 4D linearized differential Bianchi identity and differentiated Weyl-Ricci-scalar split, 4D conformal traceless nonabelian Yang-Mills stress-energy coupling, and Standard Model Einstein-Weyl-Yang-Mills holographic master synthesis. Specifically, on 0<epsilon,h!=0,abs(h)<=pi*epsilon/3 and for all real m,g,k,t, the static resolvent R_T(a) satisfies Re<Tx,x>=norm(Tstat x)^2>=0, norm(T(R_T(a)f))^2+a^2*norm(R_T(a)f)^2<=norm(f)^2, norm(Tstat(R_T(a)f))^2+a*norm(R_T(a)f)^2<=a^(-1)*norm(f)^2, and norm(clockHalf(R_T(a)f))^2<=2*a^(-1)*norm(f)^2; on Dom(S(t)) intersect DomP = Dom(S(t)) intersect DomT, S(t)x=Tx+exp(2t)*Px and R_T(a)f-R_{S(t)}(a)f=exp(2t)*R_T(a)(P(R_{S(t)}(a)f)); on Dom(H(t)) intersect DomG = Dom(H(t)) intersect DomT, H(t)x=Tx+exp(2t)*Gx and R_T(a)f-R_{H(t)}(a)f=exp(2t)*R_T(a)(G(R_{H(t)}(a)f))=exp(2t)*R_T(a)(K(R_{H(t)}(a)f))+exp(2t)*R_T(a)(P(R_{H(t)}(a)f)); and unconditionally on Hilbert, R_P(a)f-R_{H(t)}(a)f=R_P(a)(K(R_G(a)f))+(R_G(a)f-R_{S(t)}(a)f)+exp(2t)*R_{S(t)}(a)(K(R_{H(t)}(a)f)) and sum_{A in {T,P,G,S(t),H(t)}} norm(R_A(a)f)^2 <= 5*a^(-2)*norm(f)^2. Connecting LayerA/B/C Standard Model modules: (1) SMForced, SMUniqueness, WeinbergAngle, and SMHilbertInstantiation force N_c=3, N_w=2, totalFermionsCartan 3 2=15, singleGenDim=16, and Weinberg partition weights (3/8,5/8) with ratio 3/5=gutNormalization^(-1) across 16-component and 15-component 5-resolvent tuples; (2) in the positive-vacuum regime 0<k, Dom(Tgrow)=Dom(Kroot) intersect potentialDomain, Dom(Eavg(t))=Dom(Tstat) intersect Dom(Kroot) intersect potentialDomain is time-invariant, positiveVacuumCoreDomain=unconditionalCoreDomain lies in all 10 domains with simultaneous 5-operator core approximation, and AnomalyCancellation + AnomalyConstraints + ProtonStability prove that any nontrivial anomaly-free charge assignment (y_Q!=0) has trY2=120*y_Q^2>0 and trY4=2280*y_Q^4>0, yielding exact positive SM vacuum scales smQuadVacuumScale=10/3>0 and smQuartVacuumScale=95/54>0 that automatically activate the positive-vacuum clock-floor core and resolvent theorems alongside Q_p=1, Q_n=0, and dim-6 proton stability; (3) for all 5 Hamiltonians A in {T,P,G,S(t),H(t)} and any a,b>0, the iterated resolvent R_A(a)(R_A(b)f) lies unconditionally in Dom(A^2) (and in all 10 domains for H(t)) with A(A(R_A(a)(R_A(b)f)))=f-(a+b)*R_A(b)f+a^2*R_A(a)(R_A(b)f) and 3-tier bounds (a^(-1)*b^(-1)*norm(f), 2*b^(-1)*norm(f), 4*norm(f)), while HiggsPotentialForm, HiggsMassDerived, SMGaugeDynamics, SMTensorDecomposition, SMGaugeFiniteRep, SMSeeSawSubspace, SMQMBridgeCapstone, and SMQGLink connect the spectral-gap Higgs potential (lambda=(log(5/3))^2/2, m_H=log(5/3)*v in (120,130) GeV for d=4), Gell-Mann-Nishijima Q=T_3+Y conservation, and 16-dim / 126-dim unitary and formEvolution bounds with Bekenstein-Hawking ceilings maxEntropy 16=4*log 2 < log 126 <= A/4; (4) degree-M neutral polynomial profiles P_i(X)=C(c_{0,i})+sum_{r<M} C(d_{r,i})*X^(r+1) (sum_i C_i*d_{r,i}=0) reduce exactly to the constant channel across all 9 packet maps and energy/response functionals with universal Cauchy-Schwarz lower bound cauchySchwarzWeightRatio(C), instantiated via GenerationsFromFiber, ThreeGenerations, and YukawaFromFiber at n=generationCount 3=3 where cauchySchwarzWeightRatio=3=nAngles 3 and massless democratic Yukawa eigenvectors (w_0+w_1+w_2=0) are simultaneously zero-mass Yukawa modes and vacuum-decoupled neutral packet states; (5) in 4D linearized Lorentzian geometry, dR_metric satisfies the differential second Bianchi identity and differentiated Weyl-Ricci-scalar split dWeylTensor4D with conformal invariance, while GaugeConnection, NonabelianYangMills, YangMillsVariational, CouplingUnification, and Build5_WilsonYMSynthesis yield a symmetric 4D Yang-Mills stress-energy tensor T^{YM}_{mu nu} with exact 4D conformal tracelessness sum_mu sign(mu)*T^{YM}_{mu mu}=0, forcing zero scalar curvature and Einstein trace on linearized 4D Einstein-Yang-Mills solutions alongside nonabelian Bianchi identities and small-case chamber gap sqrt(7)/15>0. Direct fixed-N invariance J_N(DomP) subseteq DomP without passing through R_P(a), unconditional single-resolvent membership R_{H(t)}(a)f in DomP for k<=0 without form pairing, differing complex neutral sources at non-zero potential coupling in the response lower bound, trajectory-wide unbounded-momentum derivatives, nonlinear curved 4D gravity, full continuum 4D interacting Yang-Mills-Wightman QFT and Haar/cluster/continuum limits (R1-R4), dynamical derivation of the Wolfenstein parameter epsilon, microscopic law and phase selection, controlled physical limits, and empirical identification remain open; the earlier phase/harmonic identification still requires revision. A physical TOE is not proved. This checkpoint adds491 theorems in15 modules, preserves3566 parent source/script hashes and adds17 for3583 total; exact root extends from9146 to9161 lines. All12 parent analytic artifacts and23 numerical files remain unchanged. Standard axioms only.'
PARENT = 'data/second_resolvent_weyl_twenty_component_synthesis_audit.json'
PARENT_SHA = 'b92c138a6d70d006d57543a325cde45e0b90ab8b537205667f938d988b2d9f6b'
REPORT = 'data/sm_quantum_gravitational_resolvent_bianchi_synthesis_audit.json'
SCRIPTS = ['scripts/sm_quantum_gravitational_resolvent_bianchi_synthesis_audit.py',
           'scripts/verify_sm_quantum_gravitational_resolvent_bianchi_synthesis.py']
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
    parsed=re.findall(r"'([^']+)' (?:depends on axioms:\s*\[([^\]]*)\]|does not depend on any axioms)",log)
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
    assert len(old)==3566 and len(hashes)==3566+len(EXPECTED)+2
    assert all(hashes[p]==h for p,h in old.items())
    assert all(sha(root/p)==h for p,h in hashes.items())
    additions={'UnifiedTheory/Audit/'+n+'.lean' for n in EXPECTED}|set(SCRIPTS)
    assert set(hashes)-set(old)==additions
    assert [Path(x['source']).stem for x in report['modules']]==list(EXPECTED)
    logs=overlay/'sm-quantum-gravitational-resolvent-bianchi-synthesis-audit'
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
    assert text.endswith(suffix) and len(text.splitlines())==9146+len(EXPECTED)
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
