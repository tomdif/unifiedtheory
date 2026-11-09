#!/usr/bin/env python3
"""Independently verify the complete-toe-repo-synthesis audit and preserved evidence."""
import argparse
import hashlib
import json
from pathlib import Path
import re

EXPECTED = {
    'KFCausalClockFloorPotentialResolventYosidaInvarianceBridge': 35,
    'KFCausalClockFloorFiveOperatorFirstResolventIdentity': 34,
    'KFCausalClockFloorSMFineStructureBornRuleResolventBridge': 35,
    'KFCausalClockFloorIteratedHamiltonianResolventUnconditionalDomination': 32,
    'KFCausalClockFloorArbitraryCouplingIteratedCoreApproximation': 32,
    'KFCausalClockFloorYangMillsR1R2R3R4ContinuumBridge': 32,
    'KFCausalClockFloorHigherPowerOperatorCores': 32,
    'KFCausalClockFloorSMNeutrinoSeesawStrongCPBridge': 32,
    'KFCausalClockFloorFrameworkCapstone2026MasterBridge': 32,
    'KFCausalArbitrarySourceDegreeMPolynomialSuperpositionSynthesis': 37,
    'KFCausalNonAbelianBRSTMultiPacketGaugeInvarianceBridge': 40,
    'KFCausalSMFrameworkAtomicCrossSectorMultiPacketSynthesis': 38,
    'KFCausalCurved4DLovelockCosmologicalConstantSynthesis': 31,
    'KFCausalCurved4DGravitonTTModesWeylPolarizationBridge': 32,
    'KFCausalTOECompleteRepoSynthesisMasterCapstone': 33,
}
EXTRA_ANALYTIC = {}
SCOPE = 'Resolvent-regularized potential-domain radial-Yosida approximation and invariance bridge, unconditional five-operator first resolvent (Hilbert) identity and resolvent commutativity, Standard Model fine-structure unification coupling and Born-rule SO(2) quadratic uniqueness bridge, unconditional iterated Hamiltonian resolvent 10-domain domination and second-resolvent identities for arbitrary real couplings, arbitrary-coupling three-tier second-power graph core convergence and two-time common-core approximation, Yang-Mills R1-R4 SO(10) Haar / centroid-parity / exponential-decay / continuum-limit bridge, inductive r-th power operator domains Dom(A^r) and iterated resolvent powers across all 5 Hamiltonians, Standard Model neutrino see-saw scale and Strong CP parity-averaging bridge, FrameworkCapstone 2026 atomic and cross-sector evolution bridge, arbitrary-source degree-M polynomial superposition decomposition and triangle/reverse-triangle bounds, nonabelian BRST nilpotency (Q^2 = 0) and multi-packet gauge invariance bridge, Standard Model framework atomic cross-sector multi-packet Cauchy-Schwarz synthesis, 4D Lovelock uniqueness and Sorkin causal-set cosmological constant Einstein-Yang-Mills synthesis, 4D graviton transverse-traceless polarization modes and Weyl electric-magnetic equipartition bridge, and Grand Complete-Repository TOE Synthesis Master Capstone. Specifically, on 0<epsilon,h!=0,abs(h)<=pi*epsilon/3 and for all real m,g,k,t: (1) for every x in DomP and a,N>0, the resolvent-regularized radial-Yosida state potentialResolventRadialYosidaApprox a N x := R_P(a)(J_N(Px+a*x)) lies in DomP (and in DomG=DomK intersect DomP on the quarter-strip abs(h)<=pi*epsilon/4) with (P+a*I)(potentialResolventRadialYosidaApprox a N x)=J_N(Px+a*x) in DomK and fixed-shift graph convergence fixedShiftPotentialRadialYosidaSeq a x n -> x and P(fixedShiftPotentialRadialYosidaSeq a x n) -> Px as n -> infty; across all 5 Hamiltonians A in {T,P,G,S(t),H(t)}, the first resolvent identity R_A(a)f-R_A(b)f=(b-a)*R_A(a)(R_A(b)f), commutativity R_A(a)(R_A(b)f)=R_A(b)(R_A(a)f), Dom(A^2) membership of R_A(a)f-R_A(b)f, and two-parameter (a,b) cross-operator second resolvent identities hold unconditionally and are instantiated via FineStructureFromGap and BornRuleUnique at (alpha_unification=3/(32*pi), gamma_4=log(5/3)) alongside SO(2) phase-invariance uniqueness of quadratic Born weights; (2) for arbitrary real m,g,k,t (including k<=0) and a,b>0, both iteratedHamiltonianResolvent t a b f := R_{H(t)}(a)(R_{H(t)}(b)f) and H(t)(R_{H(t)}(a)(R_{H(t)}(b)f)) belong unconditionally to all 10 operator and form domains with unconditional second-resolvent identities, while iteratedYosida R a f := a^2*R_A(a)(R_A(a)f) satisfies simultaneous 3-tier convergence in Hilbert, Graph(A), and Graph(A^2) across all 5 Hamiltonians, and R2b_SO10HaarConcreteConstruction + R1_Closure_via_R2b + R3_MassGapExponentialDecay + R4_ContinuumLimitConvergence connect the Mathlib-backed SO(10) probability Haar measure haarMeasureSO10, centroid-parity block splitting, exponential correlation decay exp(-2*(sqrt(7)/15)*t), and rho -> infty chamber continuum convergence to the clock-floor resolvent/core hierarchy at yangMillsGapShift > 0; (3) inductive r-th power domains operatorPowerDomain A r (Dom(A^r)) and r-fold iterated resolvents R_A(a)^r f in Dom(A^r) hold across all 5 Hamiltonians, NeutrinoScale (m_nu=y^2*v^2/M_R) and StrongCP (parity-odd topological density tilde(F)*F and parity-averaging theta_eff=0) connect to 126-component see-saw evolution, and FrameworkCapstone (canonicalAtoms: N_W=2,N_c=3,N_g=3,d_eff=4,N_total=5,disc=7,h(E_8)=30,N_infl=60, 6 rational PDG corrections, 17+ cross-sector relations, Omega_DM*h^2=3/25, n_s=29/30, r=1/300, and honest negative boundaries) connects to multi-component unitary and formEvolution bounds; (4) degree-M polynomial profiles decompose into the constant channel plus M monomial channels across all 9 packet maps with triangle/reverse-triangle bounds for arbitrary differing complex sources b : Fin n -> C, Clay4_NonAbelianBRST proves nonabelian BRST nilpotency Q(Q X)=0 over any LieRing L (and MatRealTen) paired with multi-packet gauge-mode invariance, and uniform multi-packet weights on Fin N achieve exact Cauchy-Schwarz ratios N in {2,3,4,5,7,30} across all canonical atomic sectors; (5) LovelockComplete + CosmologicalConstant prove 4D Lovelock completeness a*G_{mu nu}+Lambda*g_{mu nu} and Sorkin scaling Lambda=1/sqrt(rho*V)>0, forcing scalar curvature R=4*Lambda>0 and R_{mu nu}=Lambda*eta_{mu nu}+kappa*T^{YM}_{mu nu} on 4D conformally traceless Einstein-Lovelock-Yang-Mills solutions, while GravitonTTModes proves gravitonTTModes(d)=d*(d-3)/2 (2 modes in d=4 with 10+5*2=20 Riemann components) and gravitonPolarizationJet4D(A,B) injects into pure-Weyl vacuum solutions with electric-magnetic energy equipartition 2*(A^2+B^2). Direct fixed-N invariance J_N(DomP) subseteq DomP without R_P(a), single-resolvent R_{H(t)}(a)f in DomP for k<=0 without iteration or form pairing, trajectory-wide unbounded-momentum derivatives, nonlinear curved 4D gravity, full continuum 4D OS/Wightman nonperturbative QFT beyond the chamber/cluster reduction, dynamical derivation of the Wolfenstein parameter epsilon and absolute mass scales, microscopic law and phase selection, controlled physical limits, and empirical identification remain open; the earlier phase/harmonic identification still requires revision. A physical TOE is not proved. This checkpoint adds507 theorems in15 modules, preserves3583 parent source/script hashes and adds17 for3600 total; exact root extends from9161 to9176 lines. All12 parent analytic artifacts and23 numerical files remain unchanged. Standard axioms only.'
PARENT = 'data/sm_quantum_gravitational_resolvent_bianchi_synthesis_audit.json'
PARENT_SHA = '58c5b4e3f0a444b97d89355ceacefd68ecc93cb6979c4b4236617b4c0e22b117'
REPORT = 'data/complete_toe_repo_synthesis_audit.json'
SCRIPTS = ['scripts/complete_toe_repo_synthesis_audit.py',
           'scripts/verify_complete_toe_repo_synthesis.py']
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
    assert len(old)==3583 and len(hashes)==3583+len(EXPECTED)+2
    assert all(hashes[p]==h for p,h in old.items())
    assert all(sha(root/p)==h for p,h in hashes.items())
    additions={'UnifiedTheory/Audit/'+n+'.lean' for n in EXPECTED}|set(SCRIPTS)
    assert set(hashes)-set(old)==additions
    assert [Path(x['source']).stem for x in report['modules']]==list(EXPECTED)
    logs=overlay/'complete-toe-repo-synthesis-audit'
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
    assert text.endswith(suffix) and len(text.splitlines())==9161+len(EXPECTED)
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
