#!/usr/bin/env python3
"""Independently verify the twenty-four-checkpoint-complete-tier-one-synthesis audit and preserved evidence."""
import argparse
import hashlib
import json
from pathlib import Path
import re

EXPECTED = {
    'KFCausalClockFloorHigherPowerPotentialResolventYosidaTwelveParameterDodecagon': 10,
    'KFCausalClockFloorFiveOperatorThirteenParameterHigherPowerTridecagonCocycleAndYosida': 7,
    'KFCausalClockFloorTwelveParameterDodecagonThirteenParameterTridecagonWideStripPotentialDomainInvarianceBridge': 6,
    'KFCausalClockFloorTenByTenMixedInitialFinalHigherPowerResolventPlaquetteGrid': 7,
    'KFCausalClockFloorTenByTenPlaquetteStrongTwoTimeResolventNormContinuityAndTrajectoryEnergyBridge': 6,
    'KFCausalClockFloorTenByTenPlaquettePolymerBorgsImbrieKoteckyPreissWeingartenVolterraBridge': 6,
    'KFCausalClockFloorArbitraryOrderTwelveFactorMultiPowerYosidaComposition': 9,
    'KFCausalClockFloorTwelveFactorYosidaVelocityCommutatorUmegakiAndoLiebGoldenThompsonBridge': 5,
    'KFCausalClockFloorTwelveFactorYosidaStinespringPetzTraceDistanceQuantumSteinAEPBridge': 5,
    'KFCausalArbitrarySourceMultiChannelMockThetaBilateralTripleProductConstantTermAndRademacherCardyEntropy': 6,
    'KFCausalMultiChannelMockThetaBilateralTripleProductRademacherCardyEntropyOctonionE8SMGUTBridge': 5,
    'KFCausalMultiChannelMockThetaBilateralTripleProductRademacherCardyEntropyBellCHSHTsirelsonPhaseFaithfulnessNoGoBridge': 5,
    'KFCausalCurved4DTenByTenPlaquetteTwentyComponentRiemannWeylRicciDecompositionBianchiEinsteinBridge': 5,
    'KFCausalCurved4DTwelveFactorYosidaWeylRiemannReconstructionMockThetaCapstoneConditionalEinsteinSpectralRigidityUnifiedForcingBridge': 5,
    'KFCausalTOETwentyFourCheckpointCompleteTierOneMasterSynthesis': 6,
}
EXTRA_ANALYTIC = {}
SCOPE = 'Wide-strip (|h| <= pi*epsilon/3) forward half-shift (h/2,0) variational pairing, wide-strip variational Dom(P) and Dom(G) regularizer criterion without R_P(a) or quarter-strip restriction, wide-strip half-shift commutator convergence shiftedResolvent (-h/2) f - action f -> 0, and seven-operator wide-strip evaluation, twelve-parameter (a,b,c,d,e,f_param,g_param,h_param,i_param,j_param,k_param,l_param) higher-power potential-resolvent radial-Yosida cyclic dodecagon cocycles and twenty-four-parameter ((a,J1),...,(l_param,J12)) Cauchy rate bounds, five-operator (T,P,G,S,H) thirteen-parameter (a,b,c,d,e,f_param,g_param,h_param,i_param,j_param,k_param,l_param,m_param) higher-power cross-resolvent tridecagon cocycles and common-domain Yosida cross-rate bounds, twelve-parameter dodecagon / thirteen-parameter tridecagon / wide-strip potential-domain invariance QQG / inflaton / slow-roll / dimension / gauge / Volterra bridge, ten-by-ten (s1,s2,s3,s4,s5,s6,s7,s8,s9,s10)x(t1,t2,t3,t4,t5,t6,t7,t8,t9,t10) (9x9=81 elementary plaquettes) mixed initial-and-final higher-power resolvent and identity plaquette grids with exact 2D Stokes / Green boundary cancellation across all 8 time-independent and 10 equal-outer-final-time domains, unconditional strong Hilbert-norm and operator-norm two-time resolvent Lipschitz continuity ||R_{H(s)}(a)f - R_{H(t)}(a)f|| <= |e^{2t} - e^{2s}| (2 e^{-(t+s)} a^{-1} ||f||) and ||R_{H(s)}(a) - R_{H(t)}(a)|| <= |e^{2t} - e^{2s}| (2 e^{-(t+s)} a^{-1}) and strong/operator-norm convergence R_{H(s)}(a)f -> R_{H(t)}(a)f and R_{H(s)}(a) -> R_{H(t)}(a) for all real m,g,k with Wightman / OS / Clay continuum bridge, ten-by-ten plaquette Polymer / Borgs-Imbrie / Kotecky-Preiss / Weingarten / Volterra SO(10) bridge, arbitrary-order twelve-factor multi-power (r,s,q,p,l,u,v_pow,w_pow,z_pow,y_pow,x_pow,d_pow) and twelve-parameter (a,b,d,e,c,f_param,g_param,h_param,i_param,j_param,k_param,l_param) Yosida composition defect calculus across all 5 Hamiltonians, twelve-factor Yosida quantum-velocity commutator error / Umegaki / Ando / Lieb / Golden-Thompson bridge, twelve-factor Yosida Stinespring / Petz / trace-distance / Quantum Stein / AEP bridge, fifth-order Mock Theta Conjecture (MTC_0/MTC_1) bilateral triple-product constant-term decomposition mtc0ClearedDifference = J2_5 * mtc0ThetaReducedResidual and mtc1ClearedDifference = J1_5 * mtc1ThetaReducedResidual, five-fold Euler residue-partition factorization qfac = J2_5*(P1_5*P4_5) and qfac = J1_5*(P2_5*P3_5), joint two-conjecture eliminant identity, and Rademacher-Cardy saddle-point black-hole microstate entropy bound 2 pi^2 C_eff / beta + beta Delta - 2 pi sqrt(2 C_eff Delta) = (sqrt(2 pi^2 C_eff / beta) - sqrt(beta Delta))^2 >= 0, multi-channel Mock Theta bilateral triple-product / Rademacher-Cardy / octonion / E_8 / SM / GUT / CKM / PMNS / proton decay / dark matter bridge, multi-channel Mock Theta bilateral triple-product / Rademacher-Cardy Bell / CHSH / Tsirelson / phase faithfulness / no-go bridge, curved 4D ten-by-ten plaquette / full 20-component algebraic 4D Riemann-Weyl-Ricci-Hessian curvature decomposition reconstructHessianFromRiemann4D(fullRiemannFromHessianAndWeyl4D H W) = H and reconstructWeylFromRiemann4D(fullRiemannFromHessianAndWeyl4D H W) = W (10 + 10 = 20) / off-diagonal shear Bianchi channel cancellation / on-shell stress-energy conservation bridge, curved 4D twelve-factor Yosida / 20-component Weyl-Riemann reconstruction / Mock Theta bilateral split / Rademacher-Cardy Capstone / ConditionalEinstein / spectral rigidity / unified forcing bridge, and Twenty-Four-Checkpoint Complete Tier-One TOE Master Synthesis. Specifically, on 0<epsilon,h!=0,abs(h)<=pi*epsilon/3 and for all real m,g,k,s,t: (1) on the full wide strip abs(h)<=pi*epsilon/3, both abs(h/2)<=pi*epsilon/6 and abs(0)<=pi*epsilon/6 hold, yielding the wide-strip symmetric half-shift variational pairing <outputActionLp 0 (PB (domainFormLift x)), PB v> = <shiftedResolvent (-h/2) (P x), PJ v>, the wide-strip variational Dom(P) and Dom(G) regularizer criterion without R_P(a) or quarter-strip restriction, strong half-shift commutator convergence shiftedResolvent (-h/2) f - action f -> 0, and seven-operator wide-strip evaluation, while twelve-parameter (a..l_param) and twenty-four-parameter ((a,J1),...,(l_param,J12)) potential-resolvent and identity-Yosida tier differences satisfy exact 12-step cyclic dodecagon cocycles, Dom(P^(r+2))/Dom(P^r) regularity, and eleven-hop Cauchy rate bounds, and across any ThirteenParameterFiveOperatorSystem (T,P,G,S(t),H(t)) at (a..m_param), cross-resolvent and cross-Yosida differences satisfy exact 13-step tridecagon cocycles and twelve-hop bounds; (2) for all real m,g,k,t,s in R and a>0 (including k<=0), ||R_{H(s)}(a)f - R_{H(t)}(a)f|| <= |e^{2t} - e^{2s}| (2 e^{-(t+s)} a^{-1} ||f||) and ||R_{H(s)}(a) - R_{H(t)}(a)|| <= |e^{2t} - e^{2s}| (2 e^{-(t+s)} a^{-1}) with strong and operator-norm convergence R_{H(s)}(a)f -> R_{H(t)}(a)f and R_{H(s)}(a) -> R_{H(t)}(a) as s -> t, while on a 10x10 grid (s1..s10)x(t1..t10), the 9x9 sum of 81 elementary mixed initial-and-final higher-power resolvent and identity plaquettes satisfies exact 2D Stokes / Green boundary cancellation to the outer plaquette (s1,s10; t1,t10) canceling 64 interior vertices and 144 interior edges, 10-initial and 10-final decagon cocycles, 8-domain regularity, and equal-outer-final-time Dom(H(t)^(r+2)) + 10-domain regularity; (3) across all 5 Hamiltonians A in {T,P,G,S(t),H(t)}, twelve-factor multi-power (r,s,q,p,l,u,v_pow,w_pow,z_pow,y_pow,x_pow,d_pow) and twelve-parameter (a,b,d,e,c,f_param,g_param,h_param,i_param,j_param,k_param,l_param) Yosida compositions preserve Dom(A^n), commute with A^n, contract kthPowerGraphNormSq A n, and satisfy ((r/a + s/b + q/d + p/e + l/c + u/f_param + v_pow/g_param + w_pow/h_param + z_pow/i_param + y_pow/j_param + x_pow/k_param + d_pow/l_param)^2) * kthPowerGraphNormSq A (n+1) x defect bounds; (4) under five-fold Euler residue-partition factorization qfac = P0_5*P1_5*P2_5*P3_5*P4_5 with J2_5 = P0_5*P2_5*P3_5 and J1_5 = P0_5*P1_5*P4_5 and bilateral constant-term decompositions Phi1 - 1 = B0_lead + B0_tail and Phi2 - 1 = B1_lead + B1_tail, the fifth-order Mock Theta Conjecture differences factor as mtc0ClearedDifference = J2_5 * mtc0ThetaReducedResidual and mtc1ClearedDifference = J1_5 * mtc1ThetaReducedResidual with exact J5_10 eliminant cancellation, while the Rademacher-Cardy saddle-point exponent satisfies 2 pi^2 C_eff / beta + beta Delta - 2 pi sqrt(2 C_eff Delta) = (sqrt(2 pi^2 C_eff / beta) - sqrt(beta Delta))^2 >= 0; (5) for any 10-component symmetric 4x4 conformal Hessian H and any 10-component Lorentzian trace-free Weyl tensor W (10 + 10 = 20), the full 20-component 4D Riemann tensor fullRiemannFromHessianAndWeyl4D H W has Lorentzian Ricci contraction fullRicciTensor4D H and scalar contraction fullScalarCurvature4D H, and both H and W are reconstructed simultaneously and exactly via reconstructHessianFromRiemann4D(fullRiemannFromHessianAndWeyl4D H W) = H and reconstructWeylFromRiemann4D(fullRiemannFromHessianAndWeyl4D H W) = W, synthesized with 100% (659/659) direct non-Audit module coverage. Unconditional fixed-N strong-operator invariance J_N(DomP) subseteq DomP without the wide-strip half-shift variational pairing hypothesis (beyond the proved four-domain invariance, two-sided potential-pairing domination, Dom(G) radial-Yosida contraction/rate, Dom(H(t))/Dom(S(t)) radial-Yosida quadratic lower bound and rate, unconditional Dom(T) invariance/commutator/core, unconditional Dom(G) = Dom(K) cap Dom(P) seven-operator resolvent invariance, and wide-strip half-shift variational Dom(P)/Dom(G) regularization), single-resolvent R_{H(t)}(a)f in DomP for k<=0 without iteration (beyond the proved 14-domain regularity, unconditional R_G(a)f in DomP, 5-way DomP <-> DomG <-> DomT equivalence, shifted-source residual-resolvent criterion, static-residual second resolvent identity, unconditional strong/operator-norm two-time resolvent continuity, and positive-vacuum k>0 domain stability), trajectory-wide unbounded-momentum derivatives beyond the energy-controlled H(t)-domain quantum-velocity commutator bound, general non-conformal dynamical nonlinear 4D Einstein-Weyl PDE evolution beyond the 20-component algebraic Riemann-Weyl-Ricci-Hessian reconstruction and linearized Bianchi/stress-energy conservation, full infinite-volume 4D continuum OS/Wightman QFT beyond the chamber/cluster reduction, first-principles derivation of absolute dimensionful scales, microscopic phase selection, controlled physical limits, and empirical identification remain open; the earlier phase/harmonic identification still requires revision. A physical TOE is not proved. This checkpoint adds93 theorems in15 modules, preserves3838 parent source/script hashes and adds17 for3855 total; exact root extends from9386 to9401 lines. All12 parent analytic artifacts and23 numerical files remain unchanged. Standard axioms only.'
PARENT = 'data/twenty_three_checkpoint_complete_tier_one_synthesis_audit.json'
PARENT_SHA = 'bafdb27421f18d702ed18dc676eccc8c83913ffe9ffb486ac535e6c0e5d4451a'
REPORT = 'data/twenty_four_checkpoint_complete_tier_one_synthesis_audit.json'
SCRIPTS = ['scripts/twenty_four_checkpoint_complete_tier_one_synthesis_audit.py',
           'scripts/verify_twenty_four_checkpoint_complete_tier_one_synthesis.py']
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
    assert len(old)==3838 and len(hashes)==3838+len(EXPECTED)+2
    assert all(hashes[p]==h for p,h in old.items())
    assert all(sha(root/p)==h for p,h in hashes.items())
    additions={'UnifiedTheory/Audit/'+n+'.lean' for n in EXPECTED}|set(SCRIPTS)
    assert set(hashes)-set(old)==additions
    assert [Path(x['source']).stem for x in report['modules']]==list(EXPECTED)
    logs=overlay/'twenty-four-checkpoint-complete-tier-one-synthesis-audit'
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
    assert text.endswith(suffix) and len(text.splitlines())==9386+len(EXPECTED)
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
