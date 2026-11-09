#!/usr/bin/env python3
"""Independently verify the thirteen-checkpoint-complete-tier-one-synthesis audit and preserved evidence."""
import argparse
import hashlib
import json
from pathlib import Path
import re

EXPECTED = {
    'KFCausalClockFloorHigherPowerPotentialResolventYosidaArbitraryOrderConvergence': 30,
    'KFCausalClockFloorFiveOperatorTwoParameterHigherPowerCrossResolvent': 26,
    'KFCausalClockFloorSMAsymptoticFreedomCasimirVEVUnificationBridge': 20,
    'KFCausalClockFloorTwoTimeEvolvedHigherPowerResolventDifference': 18,
    'KFCausalClockFloorPolymerBrydgesFederbushBorgsImbrieWeingartenBridge': 17,
    'KFCausalClockFloorLieTrotterGoldenThompsonLiebThirringMerminWagnerBridge': 10,
    'KFCausalClockFloorArbitraryOrderTwoParameterYosidaCauchyRate': 17,
    'KFCausalClockFloorQuantumChannelsChoiKrausHolevoCramerRaoHelstromBridge': 9,
    'KFCausalClockFloorNoCloningNoDeletionPeresHorodeckiTeleportationBridge': 7,
    'KFCausalArbitrarySourceOrthogonalProjectionResidualEnergyDecomposition': 16,
    'KFCausalHodgeStarFourDChiralityFermionRepMultiPacketBridge': 7,
    'KFCausalGUTEmbeddingChamberSpin10UnifiedSelectionMultiPacketBridge': 7,
    'KFCausalCurved4DGravitationalPlaneWavesNullConeHauptvermutungBridge': 6,
    'KFCausalCurved4DLohmillerSlotineConformalLaplacianGaussianWidthBridge': 5,
    'KFCausalTOEThirteenCheckpointCompleteTierOneMasterSynthesis': 6,
}
EXTRA_ANALYTIC = {}
SCOPE = 'Higher-power potential-resolvent radial-Yosida arbitrary-order m-tier convergence, five-operator two-parameter higher-power cross-resolvent difference identities, Standard Model asymptotic freedom / Casimir scaling / forced VEV / Coleman-Weinberg / single-integer unification bridge, two-time evolved higher-power resolvent and Yosida identity differences across all 10 first/second-power domains, constructive polymer / Brydges-Federbush / Borgs-Imbrie / SO(10) Weingarten / graded BRST Super-Jacobi / Faddeev-Popov bridge, Lie-Trotter / Golden-Thompson / Ando / Lieb-Thirring / Mermin-Wagner / Lieb-Schultz-Mattis bridge, arbitrary-order two-parameter Yosida Cauchy rate and kthPowerGraphNormSq defect convergence across all 5 Hamiltonians, quantum channels Choi-Kraus / Kraus CPTP / Stinespring dephasing / Holevo / Quantum Cramer-Rao / Helstrom-BB84 bridge, no-cloning / no-deletion / quantum teleportation / Peres-Horodecki PPT / CKW monogamy / Information Causality Tsirelson bridge, arbitrary-source orthogonal-projection and complementary residual-energy multi-packet decomposition, 4D Hodge star / chirality / anomaly-driven fermion representation and generation counting multi-packet bridge, SU(5) and SO(10) GUT embedding / Chamber-Spin(10) / unified selection-to-spectral J4 / packet realization functor multi-packet bridge, curved 4D linearized gravitational plane waves / Malament null-cone conformal uniqueness / Hauptvermutung / fully derived 4-branch unification bridge, curved 4D Lohmiller-Slotine C3 conformal and chartwise SPD Laplace-Beltrami convergence and Gaussian width backreaction dynamics bridge, and Thirteen-Checkpoint Complete Tier-One TOE Master Synthesis. Specifically, on 0<epsilon,h!=0,abs(h)<=pi*epsilon/3 and for all real m,g,k,s,t: (1) for every m,r,j>=0 with j<=m and x in Dom(P^(m+1)), the j-th operator-power radial-Yosida potential-resolvent tier states P^j(R_P(a)^r(J_n x)) and P^j((a R_P(a))^r(J_n x)) belong to Dom(P^r), satisfy exact left-inverse collapse and graph-norm contractivity, and converge simultaneously across all m+1 tiers j=0..m as n->infinity and a->infinity, while across any TwoParameterFiveOperatorSystem (T,P,G,S(t),H(t)) at parameters (a,b), (r+1)-fold cross-resolvent differences belong to intersection domains with O(a^(-r)+b^(-r)) norm bounds and O(r*(a^(-1)+b^(-1))) cross-Yosida difference rate bounds, connected via AsymptoticFreedom, CasimirScaling, VEVForced, CWHierarchy, and Unification to beta_0(3,6)=21>0 (n_f<=16), C_F(3)/C_F(2)=16/9, hypercharge-Casimir factor 32/9, forced K-sector VEV phi(k_0)=1, Coleman-Weinberg hierarchy 0<v<M_P, and single-integer unification d_spatial=N_c=N_g=3, N_w=2, 15 and 45 Weyl fermions; (2) higherPowerResolventSubOfEvolvedState s t a b r f lies unconditionally in Dom(H(t)^(r+3)) and all 10 first/second-power domains while higherPowerIdentitySubOfEvolvedState s t a b r f lies in Dom(H(t)^(r+2)) and all 10 first/second-power domains with O((r+1)*(a^(-1)+b^(-1))) Cauchy rate bounds and unconditional two-time weak continuity, connected via PolymerExpansion, BrydgesFederbush, BorgsImbrie, WeingartenDiagonal, HigherWeingartens, OrderFourWeingarten_SO10, BRSTSuperJacobi, FaddeevPopovInvariance, LieTrotter, GoldenThompson, AndoInterpolation, LiebThirring, MerminWagner, and LiebSchultzMattis to constructive polymer weights, Brydges-Federbush tree-graph bounds, Borgs-Imbrie contour merging, SO(10) diagonal (1/10, Frobenius=10) and order-4 Collins-Sniady Weingarten integrals, graded BRST nilpotency Q^2=0, Faddeev-Popov measure invariance (Q_trace_chamber=0), Lie-Trotter product convergence, Golden-Thompson / Ando trace bounds, Lieb-Thirring inequalities, Mermin-Wagner d<=2 IR divergence vs d=3 finiteness, and Lieb-Schultz-Mattis O(1/N) twist energy decay; (3) for every n,r>=0 and x in Dom(A^(n+1)) across all 5 Hamiltonians A in {T,P,G,S(t),H(t)}, iteratedOperatorPower A n is additive/subtractive and satisfies two-parameter Yosida Cauchy rate bounds norm(A^n((a R_A(a))^r x - (b R_A(b))^r x)) <= r*(a^(-1)+b^(-1))*norm(A^(n+1) x) and kthPowerGraphNormSq Cauchy and O(a^(-2)) defect convergence to 0, connected via ChoiKraus, Kraus, StinespringDephasing, HolevoBound, QuantumCramerRao, HelstromBound, NoCloning, NoDeletion, QuantumTeleportation, PeresHorodecki, NoBroadcasting, CKWMonogamy, and InformationCausalityTsirelson to Choi-Kraus complete positivity, Kraus CPTP trace preservation, Stinespring dephasing dilation, Holevo bound, pure/mixed SLD Quantum Cramer-Rao bounds, Helstrom discrimination & BB84 security, no-cloning, no-deletion, exact BBCJPW quantum teleportation, Peres-Horodecki PPT separability, CKW 3-tangle monogamy, and Information Causality Tsirelson bound 2*sqrt(2); (4) for any orthogonal projection P and complementary projection I-P, arbitrary-source mode and degree-M polynomial superpositions satisfy exact sesquilinear and hilbertEnergy Pythagorean decompositions E(Psi)=E(P Psi)+E((I-P) Psi), anchor-mode vs residual-tail energy splitting, and antipodal projected dominance bounds, connected via HodgeStarFourD, ChiralityFromHodge, FermionRepForced, FermionCountFromAnomaly, GUTEmbedding, ChamberSpin10Bridge, UnifiedSelectionSpectralTheorem, and PacketRealizationFunctor to 4D Hodge star involution (*^2=id, 3+3=6 self-dual/anti-self-dual split), anomaly-forced 12+3=15 fermion counting and (N_c,N_w)=(3,2) uniqueness, SU(5) (5bar+10=15) and SO(10) (16=10+5+1) GUT anomaly cancellation, Chamber-Spin(10) co-realization, unified selection (a,b)=(7,3) <-> Spin-inclusion -> J4 characteristic polynomial, and typed-packet co-cone realization [2,3,4,5,7]; (5) GravitationalPlaneWaves, NullConeConformal, NullConeGeneral, Hauptvermutung, DerivedUnification, LohmillerSlotineSubBridge2, LohmillerSlotineSubBridge2_Conformal, and LohmillerSlotineGaussianWidthDynamics prove linearized gravitational plane waves in TT gauge (ttModeCount 4 = 2, ttModeCount 3 = 0, ttModeCount 2 = 0), general (n+1) and 3+1 Malament null-cone conformal uniqueness, causal-set Hauptvermutung (lambdaSq = 1/(rho V), derived Poisson variance Var = rho V, conformal factor fixing Omega^4 = 1 -> Omega = 1), fully derived 4-branch unification from LorentzianMetric (div G = 0, alpha = 2 in 3+1, 4x4 perturbation dim = 16), C3 1D/nD smooth, conformal, diagonal, and chartwise SPD divergence-form Laplace-Beltrami convergence, and Gaussian width backreaction dynamics (sigma_prime * exp(sigma) / sigma = C, frozen-width solution vs free Schrodinger dispersion, two-sided doubling-time bounds exp(sigma_0)/(2C) <= int <= exp(2*sigma_0)/C, and exact Ei time parameterization int_{sigma(0)}^{sigma(t)} (exp(s)/s) ds = C*t). Direct fixed-N invariance J_N(DomP) subseteq DomP without R_P(a), single-resolvent R_{H(t)}(a)f in DomP for k<=0 without iteration or form pairing, trajectory-wide unbounded-momentum derivatives, general non-symmetric dynamical nonlinear 4D Einstein PDE evolution, full infinite-volume 4D continuum OS/Wightman QFT beyond the chamber/cluster reduction, first-principles derivation of absolute dimensionful scales, microscopic phase selection, controlled physical limits, and empirical identification remain open; the earlier phase/harmonic identification still requires revision. A physical TOE is not proved. This checkpoint adds201 theorems in15 modules, preserves3651 parent source/script hashes and adds17 for3668 total; exact root extends from9221 to9236 lines. All12 parent analytic artifacts and23 numerical files remain unchanged. Standard axioms only.'
PARENT = 'data/twelve_checkpoint_complete_tier_one_synthesis_audit.json'
PARENT_SHA = '26418e39107f332d9d4b8ebe44e090fb75396725340cef76d2e94f9d592904cf'
REPORT = 'data/thirteen_checkpoint_complete_tier_one_synthesis_audit.json'
SCRIPTS = ['scripts/thirteen_checkpoint_complete_tier_one_synthesis_audit.py',
           'scripts/verify_thirteen_checkpoint_complete_tier_one_synthesis.py']
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
    assert len(old)==3651 and len(hashes)==3651+len(EXPECTED)+2
    assert all(hashes[p]==h for p,h in old.items())
    assert all(sha(root/p)==h for p,h in hashes.items())
    additions={'UnifiedTheory/Audit/'+n+'.lean' for n in EXPECTED}|set(SCRIPTS)
    assert set(hashes)-set(old)==additions
    assert [Path(x['source']).stem for x in report['modules']]==list(EXPECTED)
    logs=overlay/'thirteen-checkpoint-complete-tier-one-synthesis-audit'
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
    assert text.endswith(suffix) and len(text.splitlines())==9221+len(EXPECTED)
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
