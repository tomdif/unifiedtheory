#!/usr/bin/env python3
"""Independently verify the grand-unified-ten-checkpoint-synthesis audit and preserved evidence."""
import argparse
import hashlib
import json
from pathlib import Path
import re

EXPECTED = {
    'KFCausalClockFloorIteratedPotentialResolventYosidaGraphCore': 35,
    'KFCausalClockFloorFiveOperatorIteratedResolventCommutativity': 38,
    'KFCausalClockFloorSMAlphaRunningOctonionFineStructureBridge': 33,
    'KFCausalClockFloorArbitraryCouplingIteratedThreeOperatorSynthesis': 32,
    'KFCausalClockFloorOsterwalderSchraderWightmanReconstructionBridge': 32,
    'KFCausalClockFloorHaagRuelleKugoOjimaConfinementBridge': 32,
    'KFCausalClockFloorHigherPowerYosidaGraphConvergence': 31,
    'KFCausalClockFloorSMPrecisionEWHiggsTwoLoopProtonLifetimeBridge': 31,
    'KFCausalClockFloorCosmologyDarkMatterBaryogenesisBridge': 31,
    'KFCausalArbitrarySourceDominantConstantModeResponseLowerBound': 37,
    'KFCausalSMCKMDefectAlgebraPMNSCPPhaseMultiPacketBridge': 38,
    'KFCausalDimensionTripleCoincidenceNoExtraDimensionsMultiPacketBridge': 37,
    'KFCausalCurved4DVariationalEinsteinOstrogradskyStabilityBridge': 32,
    'KFCausalCurved4DSchwarzschildBirkhoffHawkingThermodynamicsBridge': 33,
    'KFCausalTOEGrandUnifiedTenCheckpointMasterSynthesis': 33,
}
EXTRA_ANALYTIC = {}
SCOPE = 'Second-power potential-domain radial-Yosida graph core and 3-tier convergence, five-operator triple and (r,s)-fold iterated resolvent commutativity and squared-resolvent Hilbert difference identities, Standard Model alpha running and octonion fine-structure resolvent bridge, arbitrary-coupling two-time iterated Hamiltonian resolvent differences and 5-domain stability, Osterwalder-Schrader / Wightman / Schwinger / cluster / constructive measure bridge, Haag-Ruelle scattering and Kugo-Ojima BRST confinement / Slavnov-Taylor bridge, higher-power Dom(A^r) Yosida identity contraction and graph convergence across all 5 Hamiltonians, Standard Model precision electroweak / two-loop Higgs / proton lifetime / muon g-2 bridge, cosmology dark-matter relic / Sakharov baryogenesis / Starobinsky inflation bridge, arbitrary-source dominant-constant-mode degree-M response lower bounds, CKM defect algebra and PMNS Dirac CP phase multi-packet bridge, d=4 dimension triple coincidence and no-extra-dimensions multi-packet synthesis, 4D variational Einstein and Ostrogradsky stability bridge, exact nonlinear 4D Schwarzschild vacuum solution + Birkhoff uniqueness + Hawking / Bekenstein-Hawking black-hole thermodynamics bridge, and Grand Unified Ten-Checkpoint TOE Master Synthesis. Specifically, on 0<epsilon,h!=0,abs(h)<=pi*epsilon/3 and for all real m,g,k,s,t: (1) for every x in Dom(P^2) and a,b,N>0, iteratedPotentialResolventRadialYosidaApprox a b N x lies in Dom(P^2) (and in DomG on abs(h)<=pi*epsilon/4) with simultaneous 3-tier convergence (z_n -> x, P z_n -> P x, P^2 z_n -> P^2 x) as n -> infty; across all 5 Hamiltonians A in {T,P,G,S(t),H(t)}, triple and (r,s)-fold iterated resolvents commute R_A(a)^r(R_A(b)^s f)=R_A(b)^s(R_A(a)^r f) and squared resolvents satisfy R_A(a)^2 f - R_A(b)^2 f = (b-a)*(R_A(a)^2(R_A(b)f) + R_A(a)(R_A(b)^2 f)) in Dom(A^3) (with 10-domain membership for H(t)), instantiated via AlphaGUT, AlphaRunning, FineStructureIRFromGap, and FineStructureOctonionBridge at alpha_GUT=3/(32*pi), Dyson-resummed alpha_J4(q^2), and alpha_IR=gamma_4/70=gamma_4/C(8,4) (70=35+35); (2) twoTimeIteratedHamiltonianResolventDiff s t a b f and twoTimeIteratedHamiltonianYosidaDiff s t a f belong unconditionally to all 5 time-independent operator/form domains (DomK, DomTstat, DomKroot, DomTpot, Dom(clockHalf)) with telescoping bounds and two-time 3-tier secondPowerGraph convergence, while LatticeReflectionPositivity, CL1_ContinuumLimit, CL2_WightmanAxioms, CL3_SchwingerFunctions, CL3_ClusterDecomposition, CL3_ConstructiveMeasure, Clay2_HaagRuelleConstruction, Clay4_KugoOjima, Clay4_KOConfinement, and Clay4_SlavnovTaylor connect reflection positivity, the chamber spectrum {(5-sqrt(7))/30,(5+sqrt(7))/30,3/5}, exponential cluster decay gamma_cluster=log(5-sqrt(7))>0, Haag-Ruelle wavepacket surjectivity (chamber W7), Kugo-Ojima BRST quartet decoupling and Delta_L^chamber(0)=55/3, and Slavnov-Taylor sums STsum=0 to the clock-floor resolvent/core hierarchy; (3) iteratedResolventPower R s maps Dom(A^r) into Dom(A^(r+s)) and iteratedIdentityPower R a r f := a^r*R_A(a)^r f in Dom(A^r) is a uniform contraction converging to x at rate O(r*a^(-1)*norm(Ax)) across all 5 Hamiltonians, connected via PrecisionEW, HiggsTwoLoop, ProtonLifetime, MuonG2Prediction, DarkMatterRelic, Baryogenesis, and InflationAudit to one-loop EW beta splitting b_1-b_2=109/15, two-virtual-line Feshbach residue 9/16, quartic proton lifetime scaling M_X^4, dark-matter relic brackets m_DM in (123,128) GeV, Sakharov baryogenesis (3*y_Q+y_L=0, nPhases 3=1), and Starobinsky inflation (N_e=60, n_s=29/30, r=1/300=3*(1-n_s)^2); (4) arbitrary differing complex source arrays b : Fin n -> C with degree-M polynomial profiles satisfy dominant-constant-mode lower bounds (1-theta)*norm(Phi(c_0)) <= norm(Phi(degreeM)) and (1/2)*norm(Phi(c_0))^2 - (sum_r norm(Phi(d_r)))^2 <= norm(Phi(degreeM))^2 across all normed packet maps, connected via CKMFromDefects, CKMRefined, WolfensteinA (A=sqrt(6)/3, lambda=sqrt(5)/10), PMNSCPPhase (delta_CP=-pi/2, J^2=1936/1771875), DimensionTripleCoincidence (unique d=4 solving n^2-1=15, (2-n)^2=4, and 1-n/4=0), and NoExtraDimensions (CS(4)^2-1=CS(15)=15); (5) VariationalEinstein and Ostrogradsky prove higher-derivative instability and classify all 6 Riemann contractions to derive G_{mu nu}+Lambda*g_{mu nu}=0 variationally, while SchwarzschildSolution, BirkhoffUniqueness, HawkingTemperature, and BekensteinHawking verify the exact nonlinear 4D Schwarzschild vacuum metric f(r)=1-2M/r (f\'\'/2+f\'/r=0, R_{mu nu}=0, G_{mu nu}=0), orthonormal Weyl electric components (-2M/r^3,M/r^3,M/r^3) with Kretschmann invariant K=48*M^2/r^6=8*(E_r^2+E_theta^2+E_phi^2) and horizon identity K(2M)*S_BH^2=12*pi^2, Hawking temperature T_H=1/(8*pi*M), and Sorkin de Sitter entropy 16*S_dS^2=rho*V. Direct fixed-N invariance J_N(DomP) subseteq DomP without R_P(a), single-resolvent R_{H(t)}(a)f in DomP for k<=0 without iteration or form pairing, arbitrary-source potential response lower bounds without constant-mode dominance, trajectory-wide unbounded-momentum derivatives, general non-symmetric dynamical nonlinear 4D Einstein PDE evolution, full infinite-volume 4D continuum OS/Wightman QFT beyond the chamber/cluster reduction, first-principles derivation of absolute dimensionful scales, microscopic phase selection, controlled physical limits, and empirical identification remain open; the earlier phase/harmonic identification still requires revision. A physical TOE is not proved. This checkpoint adds505 theorems in15 modules, preserves3600 parent source/script hashes and adds17 for3617 total; exact root extends from9176 to9191 lines. All12 parent analytic artifacts and23 numerical files remain unchanged. Standard axioms only.'
PARENT = 'data/complete_toe_repo_synthesis_audit.json'
PARENT_SHA = '1aa1badf11bf7596eb4b0cb3a9aca390464a7d06d88cb628ddbadf5235b2a8b6'
REPORT = 'data/grand_unified_ten_checkpoint_synthesis_audit.json'
SCRIPTS = ['scripts/grand_unified_ten_checkpoint_synthesis_audit.py',
           'scripts/verify_grand_unified_ten_checkpoint_synthesis.py']
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
    assert len(old)==3600 and len(hashes)==3600+len(EXPECTED)+2
    assert all(hashes[p]==h for p,h in old.items())
    assert all(sha(root/p)==h for p,h in hashes.items())
    additions={'UnifiedTheory/Audit/'+n+'.lean' for n in EXPECTED}|set(SCRIPTS)
    assert set(hashes)-set(old)==additions
    assert [Path(x['source']).stem for x in report['modules']]==list(EXPECTED)
    logs=overlay/'grand-unified-ten-checkpoint-synthesis-audit'
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
    assert text.endswith(suffix) and len(text.splitlines())==9176+len(EXPECTED)
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
