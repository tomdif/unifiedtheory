#!/usr/bin/env python3
"""Independently verify the fourteen-checkpoint-complete-tier-one-synthesis audit and preserved evidence."""
import argparse
import hashlib
import json
from pathlib import Path
import re

EXPECTED = {
    'KFCausalClockFloorHigherPowerPotentialResolventYosidaTwoParameterCauchyRate': 12,
    'KFCausalClockFloorFiveOperatorThreeParameterHigherPowerCocycleAndYosida': 10,
    'KFCausalClockFloorSMAdjointCarrierFeshbachChamberMacMahonLatticeBridge': 10,
    'KFCausalClockFloorTwoTimeCrossTrajectoryHigherPowerResolventComparison': 9,
    'KFCausalClockFloorPhaseABDMultiPlaquetteFeshbachRGPeterWeylKP8Bridge': 9,
    'KFCausalClockFloorPeierlsBogoliubovGibbsSpohnJordanWignerETHBridge': 9,
    'KFCausalClockFloorArbitraryOrderMultiPowerYosidaCompositionDefect': 12,
    'KFCausalClockFloorQuantumErrorCorrectionKnillLaflammeStabilizerGottesmanKnillBridge': 6,
    'KFCausalClockFloorQuantumAlgorithmsDeutschSimonShorMetrologyZenoJarzynskiBridge': 6,
    'KFCausalArbitrarySourceMutuallyOrthogonalProjectorParsevalDecomposition': 12,
    'KFCausalContextualityKCBSGHZHardyConwayKochenPRBoxMultiPacketBridge': 6,
    'KFCausalEntanglementConcurrenceNielsenMajorizationQuantumCapacityMultiPacketBridge': 5,
    'KFCausalCurved4DBianchiLinearizedEinsteinLovelockWeylAntiGravityBridge': 5,
    'KFCausalCurved4DLohmillerSlotineSubBridge1PredictionESechNoGoBridge': 5,
    'KFCausalTOEFourteenCheckpointCompleteTierOneMasterSynthesis': 6,
}
EXTRA_ANALYTIC = {}
SCOPE = 'Two-parameter higher-power potential-resolvent radial-Yosida tier differences and four-parameter Cauchy rate bounds, five-operator three-parameter higher-power cross-resolvent and cross-Yosida cocycles, Standard Model adjoint carrier / Feshbach coupled / Chamber polynomial / MacMahon / exact lattice matching bridge, two-time cross-trajectory higher-power resolvent and Yosida differences across all 10 first/second-power domains, constructive Phase A/B/D/E multi-plaquette Feshbach RG / Peter-Weyl / KP8 / continuum scaling bridge, Peierls-Bogoliubov / Gibbs-MaxEntropy / Spohn inequality / Jordan-Wigner / ETH bridge, arbitrary-order multi-power Yosida composition (r1+r2) and two-exponent Cauchy rates across all 5 Hamiltonians, quantum error correction Knill-Laflamme / stabilizer / Gottesman-Knill / Solovay-Kitaev / Margolus-Levitin bridge, quantum algorithms Deutsch-Jozsa / Simon / Shor / Heisenberg metrology / quantum Zeno / Jarzynski-Crooks bridge, arbitrary-source mutually orthogonal projector family Parseval decomposition, contextuality KCBS / GHZ-Mermin / Hardy / Conway-Kochen / PR-box multi-packet bridge, entanglement concurrence / Nielsen majorization / entanglement of formation / quantum capacity / Choi-Jamiolkowski multi-packet bridge, curved 4D Bianchi / linearized Einstein / Lovelock / Weyl conformal / anti-gravity no-go bridge, curved 4D Lohmiller-Slotine SubBridge1 / Prediction E / sech^2 soliton / static n>=3 no-go bridge, and Fourteen-Checkpoint Complete Tier-One TOE Master Synthesis. Specifically, on 0<epsilon,h!=0,abs(h)<=pi*epsilon/3 and for all real m,g,k,s,t: (1) for every m,r,j>=0 with j<=m and x in Dom(P^(m+1)), the two-parameter potential-resolvent tier difference arbitraryOrderPotentialResolventYosidaTierSub P (R a) (R b) J (r+1) j x belongs to Dom(P^(r+2)) and arbitraryOrderPotentialIdentityYosidaTierSub P (R a) (R b) J a b r j x belongs to Dom(P^r) with two-parameter and joint four-parameter ((a,J1),(b,J2)) Cauchy rate bounds and strong convergence as n->infinity, while across any ThreeParameterFiveOperatorSystem (T,P,G,S(t),H(t)) at (a,b,c), cross-resolvent and cross-Yosida differences satisfy exact 3-step cyclic triangle cocycles, connected via AdjointCarrierSpinor, AdjointDimension, AdjointMasslessMeasure, AdjointRunningDeterminant, AdjointUnificationObstruction, FeshbachCoupled, ChamberPolynomialTheory, MacMahonBridge, and LatticeMatchingExact to adjoint dimensions 3+8=11 vs 15, det_2x2=15, alpha_GUT=1/42, kappa(1)=5/4, discriminant 41>0, MacMahon M(1)=1, M(2)=20, M(3)=980, and exact 11-step RG matching; (2) cross-trajectory higher-power differences crossTrajectoryResolventSub s1 t1 s2 t2 a b r f1 f2 and crossTrajectoryIdentitySub s1 t1 s2 t2 a b r f1 f2 lie unconditionally in all 10 first/second-power domains with exact 3-step cyclic cocycles and four-parameter Cauchy bounds, connected via Phase_A2..Phase_E3_PeterWeyl_Mathlib, PeierlsBogoliubov, MaxEntropyPrinciple, SpohnInequality, JordanWigner, and EigenstateThermalization to multi-plaquette Feshbach Block_RG, Peter-Weyl orthogonality, KP8 polymer convergence, continuum scaling r_phys=sigma*xi^2, Peierls-Bogoliubov convexity, Gibbs max-entropy, Spohn entropy production >=0, Jordan-Wigner CAR, and ETH off-diagonal O(1/d) suppression; (3) across all 5 Hamiltonians A in {T,P,G,S(t),H(t)}, iteratedOperatorPower A n respects semigroup composition (r1+r2) and satisfies two-exponent Cauchy bounds norm(A^n((a R_A(a))^(r1+r2) x - (a R_A(a))^r1 x)) <= r2*a^(-1)*norm(A^(n+1) x) and joint ((a,r1),(b,r2)) bounds, connected via KnillLaflamme, StabilizerCode, GottesmanKnill, SolovayKitaev, MargolusLevitin, DeutschJozsa, SimonAlgorithm, ShorPeriodFinding, QuantumMetrology, QuantumZeno, and JarzynskiCrooks to Knill-Laflamme QEC, 5-qubit stabilizer code, Gottesman-Knill Clifford closure, Solovay-Kitaev/Dawson-Nielsen recursion, Margolus-Levitin/Mandelstam-Tamm speed limits, Deutsch-Jozsa, Simon, Shor period finding, Heisenberg 1/N metrology, Zeno O(1/N) freeze, and Jarzynski/Crooks fluctuation theorems; (4) for any pairwise orthogonal projector family {P_i}_{i<K} with sum P_i + R = I, arbitrary-source mode and degree-M polynomial superpositions satisfy exact K-channel + residual Parseval identity E(Psi)=sum_i E(P_i Psi)+E(R Psi), connected via ContextualityKCBS, GHZMermin, HardyParadox, FreeWillConwayKochen, PopescuRohrlich, Concurrence, NielsenMajorization, EntanglementOfFormation, QuantumCapacity, and ChoiJamiolkowski to KCBS sqrt(5)>2, GHZ +1!=-1, Hardy 9%, Conway-Kochen 33-ray and 101-0, PR-box 4>2*sqrt(2), Wootters concurrence, Nielsen majorization, entanglement of formation, coherent information capacity, and Choi-Jamiolkowski isomorphism; (5) BianchiIdentity, LinearizedEinstein, LovelockUnique, WeylTensor4D, AntiGravityNoGo, LohmillerSlotineSubBridge1, LohmillerSlotinePredictionE, LohmillerSlotineSechSoliton, and LohmillerSlotineStaticNoGo prove contracted Bianchi div G=0, linearized Einstein box h_bar=-16*pi*T, Lovelock uniqueness, 4D Weyl dim=10 (10+10=20), anti-gravity no-go (DEC, ADM, Raychaudhuri, Fermat), Lohmiller-Slotine V\'\'=(sigma\')^2/2>=0, Prediction E xi_eff=1/6-e^(-2*sigma)/(6*c_0), exact 1D sech^2 soliton E_1D=-1/24, and Derrick-Pohozaev static no-go for n>=3. Direct fixed-N invariance J_N(DomP) subseteq DomP without R_P(a), single-resolvent R_{H(t)}(a)f in DomP for k<=0 without iteration or form pairing, trajectory-wide unbounded-momentum derivatives, general non-symmetric dynamical nonlinear 4D Einstein PDE evolution, full infinite-volume 4D continuum OS/Wightman QFT beyond the chamber/cluster reduction, first-principles derivation of absolute dimensionful scales, microscopic phase selection, controlled physical limits, and empirical identification remain open; the earlier phase/harmonic identification still requires revision. A physical TOE is not proved. This checkpoint adds122 theorems in15 modules, preserves3668 parent source/script hashes and adds17 for3685 total; exact root extends from9236 to9251 lines. All12 parent analytic artifacts and23 numerical files remain unchanged. Standard axioms only.'
PARENT = 'data/thirteen_checkpoint_complete_tier_one_synthesis_audit.json'
PARENT_SHA = 'c522f56f477cb363768764239ac466cf7699378a025163ac0880672f00120ba3'
REPORT = 'data/fourteen_checkpoint_complete_tier_one_synthesis_audit.json'
SCRIPTS = ['scripts/fourteen_checkpoint_complete_tier_one_synthesis_audit.py',
           'scripts/verify_fourteen_checkpoint_complete_tier_one_synthesis.py']
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
    assert len(old)==3668 and len(hashes)==3668+len(EXPECTED)+2
    assert all(hashes[p]==h for p,h in old.items())
    assert all(sha(root/p)==h for p,h in hashes.items())
    additions={'UnifiedTheory/Audit/'+n+'.lean' for n in EXPECTED}|set(SCRIPTS)
    assert set(hashes)-set(old)==additions
    assert [Path(x['source']).stem for x in report['modules']]==list(EXPECTED)
    logs=overlay/'fourteen-checkpoint-complete-tier-one-synthesis-audit'
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
    assert text.endswith(suffix) and len(text.splitlines())==9236+len(EXPECTED)
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
