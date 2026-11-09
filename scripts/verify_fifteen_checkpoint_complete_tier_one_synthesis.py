#!/usr/bin/env python3
"""Independently verify the fifteen-checkpoint-complete-tier-one-synthesis audit and preserved evidence."""
import argparse
import hashlib
import json
from pathlib import Path
import re

EXPECTED = {
    'KFCausalClockFloorHigherPowerPotentialResolventYosidaThreeParameterCocycle': 10,
    'KFCausalClockFloorFiveOperatorFourParameterHigherPowerCocycleAndYosida': 9,
    'KFCausalClockFloorSMHiggsMassBranchingBaryonHVPWeinbergCompleteAuditBridge': 8,
    'KFCausalClockFloorThreeTrajectoryCrossTimeHigherPowerResolventCocycle': 7,
    'KFCausalClockFloorSU5EmbeddingSU2RepTightenedBracketsHaarTwirlAnomalyBridge': 6,
    'KFCausalClockFloorChoiPetzTraceDistanceContractivitySSAUmegakiBridge': 6,
    'KFCausalClockFloorArbitraryOrderThreeFactorMultiPowerYosidaComposition': 9,
    'KFCausalClockFloorGaussianStatesLevelStatisticsQuantumAEPTDesignsTomographyBridge': 5,
    'KFCausalClockFloorBornUniquenessCPTAntilinearWedderburnQMScopeBridge': 5,
    'KFCausalArbitrarySourceWeightedProjectorExpectationAndCrossGramDecomposition': 6,
    'KFCausalBB84CHSHMonogamyMerminN6PironioAcinTsirelsonTeleportationBridge': 5,
    'KFCausalChargeSectorsFarFieldMultiParticleStructuralConcreteMultiBodyBridge': 5,
    'KFCausalCurved4DCausalBridgeCensusExactRegimePhysicalSelectionSubstrateBridge': 5,
    'KFCausalCurved4DCapstoneConditionalEinsteinMatterBranchPredictionsTOERankingBridge': 5,
    'KFCausalTOEFifteenCheckpointCompleteTierOneMasterSynthesis': 6,
}
EXTRA_ANALYTIC = {}
SCOPE = 'Three-parameter higher-power potential-resolvent radial-Yosida tier cocycles and double-difference bounds, five-operator four-parameter higher-power quadrilateral cocycles and double differences, Standard Model Higgs mass / branching / baryon / HVP / Weinberg complete audit bridge, three-trajectory cross-time higher-power resolvent and Yosida cocycles and double differences across all 10 first/second-power domains, SU(5) embedding / SU(2) representation / tightened numerical brackets / Haar twirl / anomaly cancellation bridge, Choi-Petz / trace-distance contractivity / SSA / Umegaki relative entropy bridge, arbitrary-order three-factor multi-power Yosida composition (r+s+q) and three-parameter (a,b,d) cocycles across all 5 Hamiltonians, Gaussian states / level statistics / concurrence / quantum AEP / unitary t-designs / quantum tomography / Wigner-Yanase bridge, Born uniqueness / CPT antilinearity / Wedderburn 2D exclusion / no-broadcasting / QM scope bridge, arbitrary-source spectral-weighted projector expectation and Rayleigh-Ritz sandwich bounds, BB84 / CHSH monogamy / Mermin N=6 / Pironio-Acin / Tsirelson / teleportation / thermo-temporal bridge, charge sectors / dynamical stability / far-field / multi-particle / structural / concrete many-body bridge, curved 4D causal bridge / theorem census / exact regime / physical selection / substrate bridge, curved 4D Capstone / ConditionalEinstein / CausalSetKPDerivation / MatterBranch / TOECandidateRanking / UnifiedBranch / MasterCapstone / Predictions bridge, and Fifteen-Checkpoint Complete Tier-One TOE Master Synthesis achieving 100% (659/659) transitive bridge coverage of all non-Audit modules imported by UnifiedTheory.lean. Specifically, on 0<epsilon,h!=0,abs(h)<=pi*epsilon/3 and for all real m,g,k,s,t: (1) for every m,r,j>=0 with j<=m and x in Dom(P^(m+1)), three-parameter (a,b,d) and three-cutoff (J1,J2,J3) potential-resolvent and identity-Yosida tier differences satisfy exact 3-step cyclic cocycles and double-difference Dom(P^(r+2))/Dom(P^r) regularity with four-parameter rate bounds, while across any FourParameterFiveOperatorSystem (T,P,G,S(t),H(t)) at (a,b,c,d), cross-resolvent and cross-Yosida differences satisfy exact 4-step quadrilateral cocycles and double-difference bounds, connected via 21 SM/GUT/Higgs/Flavor/HVP/Baryon modules (AuditSummary..WeinbergAtMZ) to 38 zero-sorry audit items, theta_C=arcsin((sqrt(5)-1)/4), m_H=(sqrt(5)/2)*m_Z, and sin^2(theta_W)(M_Z)=2181/9430; (2) three-trajectory cross-time differences across (s1,t1),(s2,t2),(s3,t3) satisfy exact 3-step cyclic cocycles and double-difference 10-domain and 8-domain regularity, connected via 10 SU(5)/SU(2)/TightenedBrackets/HaarTwirl/Anomaly modules and 13 Choi/Petz/TraceDistance/SSA/Umegaki modules to 5bar+10=15, Wigner-Eckart, tightened e^22,e^52 brackets, Haar twirl Schur projections, and trace-distance/Umegaki data processing; (3) across all 5 Hamiltonians A in {T,P,G,S(t),H(t)}, three-factor multi-power Yosida composition (r+s+q) and three-parameter (a,b,d) differences satisfy exact associativity, cyclic cocycles, and two-step Cauchy rate bounds, connected via 7 Gaussian/LevelStatistics/QuantumAEP/TDesigns/Tomography/WignerYanase modules and 16 Born/CPT/Wedderburn/NoBroadcasting/QMScope modules; (4) for any pairwise orthogonal projector family {P_i}_{i<Q} with sum P_i + R = I and weights w_i, arbitrary-source mode and degree-M polynomial superpositions satisfy exact Q-channel spectral-weighted decompositions and Rayleigh-Ritz bounds w_min*E(Psi) <= sum_i w_i*E(P_i Psi) + w_R*E(R Psi) <= w_max*E(Psi), connected via 10 BB84/CHSH/MerminN6/PironioAcin/Tsirelson/Teleportation/ThermoTemporal modules and 7 ChargeSectors/DynamicalStability/FarField/MultiParticle/Structural/ConcreteMultiBody modules; (5) 8 LayerA causal-bridge/census/exact-regime/normalization/physical-selection/primitives-forced/rotation-invariance/substrate-bridge modules and 9 top-level/synthesis modules (Basic, Capstone, ConditionalEinstein, CausalSetKPDerivation, MatterBranch, TOECandidateRanking, UnifiedBranch, MasterCapstone, Predictions) complete 659/659 (100%) transitive non-Audit module coverage. Direct fixed-N invariance J_N(DomP) subseteq DomP without R_P(a), single-resolvent R_{H(t)}(a)f in DomP for k<=0 without iteration or form pairing, trajectory-wide unbounded-momentum derivatives, general non-symmetric dynamical nonlinear 4D Einstein PDE evolution, full infinite-volume 4D continuum OS/Wightman QFT beyond the chamber/cluster reduction, first-principles derivation of absolute dimensionful scales, microscopic phase selection, controlled physical limits, and empirical identification remain open; the earlier phase/harmonic identification still requires revision. A physical TOE is not proved. This checkpoint adds97 theorems in15 modules, preserves3685 parent source/script hashes and adds17 for3702 total; exact root extends from9251 to9266 lines. All12 parent analytic artifacts and23 numerical files remain unchanged. Standard axioms only.'
PARENT = 'data/fourteen_checkpoint_complete_tier_one_synthesis_audit.json'
PARENT_SHA = '590b4d62277723f3eefd1ad50c774b4f706df21ed2a28fc4d0134c6b1857753b'
REPORT = 'data/fifteen_checkpoint_complete_tier_one_synthesis_audit.json'
SCRIPTS = ['scripts/fifteen_checkpoint_complete_tier_one_synthesis_audit.py',
           'scripts/verify_fifteen_checkpoint_complete_tier_one_synthesis.py']
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
    assert len(old)==3685 and len(hashes)==3685+len(EXPECTED)+2
    assert all(hashes[p]==h for p,h in old.items())
    assert all(sha(root/p)==h for p,h in hashes.items())
    additions={'UnifiedTheory/Audit/'+n+'.lean' for n in EXPECTED}|set(SCRIPTS)
    assert set(hashes)-set(old)==additions
    assert [Path(x['source']).stem for x in report['modules']]==list(EXPECTED)
    logs=overlay/'fifteen-checkpoint-complete-tier-one-synthesis-audit'
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
    assert text.endswith(suffix) and len(text.splitlines())==9251+len(EXPECTED)
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
