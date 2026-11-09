#!/usr/bin/env python3
"""Independently verify the twenty-two-checkpoint-complete-tier-one-synthesis audit and preserved evidence."""
import argparse
import hashlib
import json
from pathlib import Path
import re

EXPECTED = {
    'KFCausalClockFloorHigherPowerPotentialResolventYosidaTenParameterDecagon': 10,
    'KFCausalClockFloorFiveOperatorElevenParameterHigherPowerHendecagonCocycleAndYosida': 7,
    'KFCausalClockFloorTenParameterDecagonElevenParameterHendecagonUnconditionalStaticDomainCoreBridge': 6,
    'KFCausalClockFloorEightByEightMixedInitialFinalHigherPowerResolventPlaquetteGrid': 7,
    'KFCausalClockFloorEightByEightPlaquetteStaticResidualSecondResolventTwoTimeFormIsomorphismBridge': 6,
    'KFCausalClockFloorEightByEightPlaquettePolymerBorgsImbrieKoteckyPreissWeingartenVolterraBridge': 6,
    'KFCausalClockFloorArbitraryOrderTenFactorMultiPowerYosidaComposition': 9,
    'KFCausalClockFloorTenFactorYosidaVelocityCommutatorUmegakiAndoLiebGoldenThompsonBridge': 5,
    'KFCausalClockFloorTenFactorYosidaStinespringPetzTraceDistanceQuantumSteinAEPBridge': 5,
    'KFCausalArbitrarySourceMultiChannelThreeProfileTernaryQuadraticPencilGL3DeterminantScalingAndRamanujanSixDirectionPerfectReconstruction': 6,
    'KFCausalMultiChannelThreeByThreeGL3GramDeterminantRamanujanE8EisensteinDiscriminantMockModularBlackHoleEntropySMGUTBridge': 5,
    'KFCausalMultiChannelThreeByThreeGL3GramDeterminantRamanujanSixDirectionBellCHSHTsirelsonPhaseFaithfulnessNoGoBridge': 5,
    'KFCausalCurved4DEightByEightPlaquetteLohmillerSlotineConformalLaplacianBianchiEinsteinBridge': 5,
    'KFCausalCurved4DTenFactorYosidaRamanujanDiscriminantCapstoneConditionalEinsteinSpectralRigidityUnifiedForcingBridge': 5,
    'KFCausalTOETwentyTwoCheckpointCompleteTierOneMasterSynthesis': 6,
}
EXTRA_ANALYTIC = {}
SCOPE = 'Direct fixed-N unconditional static operator domain Dom(T) invariance J_N(Dom(T)) subseteq Dom(T) cap Dom(K) cap Dom(clockHalf) cap Dom(Tstat) cap Dom(Kroot), M_N(Dom(T)) subseteq Dom(T) cap Dom(clockHalf) cap Dom(Tstat), explicit O(N^{-1/2}) commutator bound ||T J_N x - J_N T x|| <= (3 N^-1 |h| sqrt(N/epsilon) / sqrt(epsilon)) sqrt(||T x|| ||x||) + N^-1 (6 h^2/epsilon^2) ||x||, unconditional static graph core (staticRadialGraph).topologicalClosure = (T).graph and (staticRadialClockGraph).topologicalClosure = (T).graph, and simultaneous six-norm convergence on Dom(T) cap Dom(K) without R_T(a), ten-parameter (a,b,c,d,e,f_param,g_param,h_param,i_param,j_param) higher-power potential-resolvent radial-Yosida cyclic decagon cocycles and twenty-parameter ((a,J1),...,(j_param,J10)) Cauchy rate bounds, five-operator (T,P,G,S,H) eleven-parameter (a,b,c,d,e,f_param,g_param,h_param,i_param,j_param,k_param) higher-power cross-resolvent hendecagon cocycles and common-domain Yosida cross-rate bounds, ten-parameter decagon / eleven-parameter hendecagon / unconditional static domain core QQG / inflaton / slow-roll / dimension / gauge / Volterra bridge, eight-by-eight (s1,s2,s3,s4,s5,s6,s7,s8)x(t1,t2,t3,t4,t5,t6,t7,t8) (7x7=49 elementary plaquettes) mixed initial-and-final higher-power resolvent and identity plaquette grids with exact 2D Stokes / Green boundary cancellation across all 8 time-independent and 10 equal-outer-final-time domains, exact static-residual second resolvent identity R_T(a)f - R_{S(t)}(a)f = e^{2t} R_T(a)(P R_{S(t)}(a)f), potential-residual zero-time identity R_P(a)f_0 - R_{S(0)}(a)f_0 = R_P(a)(T R_{S(0)}(a)f_0), and continuous linear two-time completed energy-form evolution isomorphism twoTimeFormEvolutionEquiv s t : VT s ~=L[C] VT t with two-sided exponential form-energy bounds e^{-2|t-s|}||Eavg s f||^2 <= ||Eavg t (U s t f)||^2 <= e^{2|t-s|}||Eavg s f||^2 and Wightman / OS / Clay continuum bridge, eight-by-eight plaquette Polymer / Borgs-Imbrie / Kotecky-Preiss / Weingarten / Volterra SO(10) bridge, arbitrary-order ten-factor multi-power (r,s,q,p,l,u,v_pow,w_pow,z_pow,y_pow) and ten-parameter (a,b,d,e,c,f_param,g_param,h_param,i_param,j_param) Yosida composition defect calculus across all 5 Hamiltonians, ten-factor Yosida quantum-velocity commutator error / Umegaki / Ando / Lieb / Golden-Thompson bridge, ten-factor Yosida Stinespring / Petz / trace-distance / Quantum Stein / AEP bridge, finite Q-channel three-profile ternary quadratic variance pencil Var_Q(a w1 + b w2 + c w3, x) = a^2 V1 + b^2 V2 + c^2 V3 + 2ab C12 + 2ac C13 + 2bc C23 >= 0, exact GL_3(R) determinant scaling Det3_Q(A(w1,w2,w3), x) = (det A)^2 Det3_Q(w1,w2,w3,x), SL_3(R) unimodular and 3D shear invariance, and Ramanujan Six-Direction Perfect-Set Reconstruction ((1,1,1),(-1,1,1),(1,-1,1),(1,1,-1),(2,1,1),(1,2,1)) of all 3 spectral covariances and all 3 channel variances, multi-channel 3x3 GL_3(R) Gram determinant / Ramanujan E_8-Eisenstein 1728 Delta = (1 + 240 s_3)^3 - (1 - 504 s_5)^2 = 144(5 s_3 + 7 s_5) + 1728(100 s_3^2 + 8000 s_3^3 - 147 s_5^2) modular discriminant / Dabholkar-Murthy-Zagier single-centered mock-modular + multi-centered Appell-Lerch BPS black-hole microstate entropy / Bekenstein-Hawking saturation / SM / GUT / CKM / PMNS / proton decay / dark matter bridge, multi-channel 3x3 GL_3(R) Gram determinant / Ramanujan Six-Direction Bell / CHSH / Tsirelson / phase faithfulness / no-go bridge, curved 4D eight-by-eight plaquette / 3x3 GL_3(R) Gram determinant Lohmiller-Slotine / conformal Laplacian / Bianchi / Einstein bridge, curved 4D ten-factor Yosida / Ramanujan E_8-Eisenstein discriminant / BPS black-hole entropy Capstone / ConditionalEinstein / spectral rigidity / unified forcing bridge, and Twenty-Two-Checkpoint Complete Tier-One TOE Master Synthesis. Specifically, on 0<epsilon,h!=0,abs(h)<=pi*epsilon/3 and for all real m,g,k,s,t: (1) directly at fixed N>0 without R_T(a), every x in Dom(T) satisfies J_N x in Dom(T) cap Dom(K) cap Dom(clockHalf) cap Dom(Tstat) cap Dom(Kroot), M_N x in Dom(T) cap Dom(clockHalf) cap Dom(Tstat), ||T J_N x - J_N T x|| <= (3 N^-1 |h| sqrt(N/epsilon) / sqrt(epsilon)) sqrt(||T x|| ||x||) + N^-1 (6 h^2/epsilon^2) ||x||, (staticRadialGraph).topologicalClosure = (T).graph, (staticRadialClockGraph).topologicalClosure = (T).graph, and simultaneous six-norm convergence on Dom(T) cap Dom(K), while ten-parameter (a..j_param) and twenty-parameter ((a,J1),...,(j_param,J10)) potential-resolvent and identity-Yosida tier differences satisfy exact 10-step cyclic decagon cocycles, Dom(P^(r+2))/Dom(P^r) regularity, and nine-hop Cauchy rate bounds, and across any ElevenParameterFiveOperatorSystem (T,P,G,S(t),H(t)) at (a..k_param), cross-resolvent and cross-Yosida differences satisfy exact 11-step hendecagon cocycles and ten-hop bounds; (2) for all real m,g,k,t,s in R and a>0, every f with R_{S(t)}(a)f in Dom(P) satisfies the exact static-residual second resolvent identity R_T(a)f - R_{S(t)}(a)f = e^{2t} R_T(a)(P R_{S(t)}(a)f) with Hilbert, T, Tstat, and clockHalf norm bounds, every f_0 with R_{S(0)}(a)f_0 in Dom(T) satisfies R_P(a)f_0 - R_{S(0)}(a)f_0 = R_P(a)(T R_{S(0)}(a)f_0), and twoTimeFormEvolutionEquiv s t : VT s ~=L[C] VT t intertwines AJ s and AJ t with U s t and satisfies e^{-2|t-s|}||u||^2 <= ||twoTimeFormEvolution s t u||^2 <= e^{2|t-s|}||u||^2 and e^{-2|t-s|}||Eavg s f_ev||^2 <= ||Eavg t (U s t f_ev)||^2 <= e^{2|t-s|}||Eavg s f_ev||^2, while on an 8x8 grid (s1..s8)x(t1..t8), the 7x7 sum of 49 elementary mixed initial-and-final higher-power resolvent and identity plaquettes satisfies exact 2D Stokes / Green boundary cancellation to the outer plaquette (s1,s8; t1,t8) canceling 36 interior vertices and 84 interior edges, 8-initial and 8-final octagon cocycles, 8-domain regularity, and equal-outer-final-time Dom(H(t)^(r+2)) + 10-domain regularity; (3) across all 5 Hamiltonians A in {T,P,G,S(t),H(t)}, ten-factor multi-power (r,s,q,p,l,u,v_pow,w_pow,z_pow,y_pow) and ten-parameter (a,b,d,e,c,f_param,g_param,h_param,i_param,j_param) Yosida compositions preserve Dom(A^n), commute with A^n, contract kthPowerGraphNormSq A n, and satisfy ((r/a + s/b + q/d + p/e + l/c + u/f_param + v_pow/g_param + w_pow/h_param + z_pow/i_param + y_pow/j_param)^2) * kthPowerGraphNormSq A (n+1) x defect bounds; (4) for any Q-channel operator family {P_q}_{q in Fin Q} with weight profiles w1,w2,w3, the ternary quadratic variance pencil Var_Q(a w1 + b w2 + c w3, x) = a^2 V1 + b^2 V2 + c^2 V3 + 2ab C12 + 2ac C13 + 2bc C23 >= 0 satisfies exact GL_3(R) determinant scaling Det3_Q(A(w1,w2,w3), x) = (det A)^2 Det3_Q(w1,w2,w3,x), SL_3(R) shear invariance, GL_3(R)-scaled Hadamard and Popoviciu bounds, and Ramanujan Six-Direction Perfect-Set Reconstruction (8 C12 = D1 - D2 - D3 + D4, 8 C13 = D1 - D2 + D3 - D4, 8 C23 = D1 + D2 - D3 - D4, 4(V1+V2+V3) = D1+D2+D3+D4, 6 V1 = 2 D5 - 3 D1 + D2, 6 V2 = 2 D6 - 3 D1 + D3, 12 V3 = 15 D1 + D2 + D3 + 3 D4 - 4 D5 - 4 D6), paired with the Ramanujan E_8-Eisenstein modular discriminant identity (1 + 240 s_3)^3 - (1 - 504 s_5)^2 = 144(5 s_3 + 7 s_5) + 1728(100 s_3^2 + 8000 s_3^3 - 147 s_5^2), 1728-divisibility, and Dabholkar-Murthy-Zagier mock-modular + Appell-Lerch BPS black-hole microstate entropy & Bekenstein-Hawking saturation; (5) all five fronts are synthesized with the curved 4D Bianchi/Einstein/Lohmiller-Slotine/Capstone/Spectral-Rigidity hierarchy and 100% (659/659) direct non-Audit module coverage. Direct fixed-N strong-operator invariance J_N(DomP) subseteq DomP without R_P(a) (beyond the proved four-domain invariance, two-sided potential-pairing domination, Dom(G) radial-Yosida contraction/rate, Dom(H(t))/Dom(S(t)) radial-Yosida quadratic lower bound and rate, and unconditional Dom(T) invariance/commutator/core), single-resolvent R_{H(t)}(a)f in DomP for k<=0 without iteration (beyond the proved 14-domain regularity, unconditional R_G(a)f in DomP, 5-way DomP <-> DomG <-> DomT equivalence, shifted-source residual-resolvent criterion, unconditional static graph core, and static-residual second resolvent identity), trajectory-wide unbounded-momentum derivatives beyond the energy-controlled H(t)-domain quantum-velocity commutator bound, general non-symmetric dynamical nonlinear 4D Einstein PDE evolution, full infinite-volume 4D continuum OS/Wightman QFT beyond the chamber/cluster reduction, first-principles derivation of absolute dimensionful scales, microscopic phase selection, controlled physical limits, and empirical identification remain open; the earlier phase/harmonic identification still requires revision. A physical TOE is not proved. This checkpoint adds93 theorems in15 modules, preserves3804 parent source/script hashes and adds17 for3821 total; exact root extends from9356 to9371 lines. All12 parent analytic artifacts and23 numerical files remain unchanged. Standard axioms only.'
PARENT = 'data/twenty_one_checkpoint_complete_tier_one_synthesis_audit.json'
PARENT_SHA = '93c5d5c9effdeb27d962481d1faafa9cc97ab72a9703aaf5cc9aa7024671d2f7'
REPORT = 'data/twenty_two_checkpoint_complete_tier_one_synthesis_audit.json'
SCRIPTS = ['scripts/twenty_two_checkpoint_complete_tier_one_synthesis_audit.py',
           'scripts/verify_twenty_two_checkpoint_complete_tier_one_synthesis.py']
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
    assert len(old)==3804 and len(hashes)==3804+len(EXPECTED)+2
    assert all(hashes[p]==h for p,h in old.items())
    assert all(sha(root/p)==h for p,h in hashes.items())
    additions={'UnifiedTheory/Audit/'+n+'.lean' for n in EXPECTED}|set(SCRIPTS)
    assert set(hashes)-set(old)==additions
    assert [Path(x['source']).stem for x in report['modules']]==list(EXPECTED)
    logs=overlay/'twenty-two-checkpoint-complete-tier-one-synthesis-audit'
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
    assert text.endswith(suffix) and len(text.splitlines())==9356+len(EXPECTED)
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
