#!/usr/bin/env python3
"""Independently verify the twenty-six-checkpoint-complete-tier-one-synthesis audit and preserved evidence."""
import argparse
import hashlib
import json
from pathlib import Path
import re

EXPECTED = {
    'KFCausalClockFloorHigherPowerPotentialResolventYosidaFourteenParameterTetradecagon': 10,
    'KFCausalClockFloorFiveOperatorFifteenParameterHigherPowerPentadecagonCocycleAndYosida': 7,
    'KFCausalClockFloorFourteenParameterTetradecagonFifteenParameterPentadecagonWideStripGrowingConvergenceBridge': 6,
    'KFCausalClockFloorTwelveByTwelveMixedInitialFinalHigherPowerResolventPlaquetteGrid': 7,
    'KFCausalClockFloorTwelveByTwelvePlaquetteUnconditionalUniformTwoTimeYosidaGeneratorLipschitzContinuityBridge': 6,
    'KFCausalClockFloorTwelveByTwelvePlaquettePolymerBorgsImbrieKoteckyPreissWeingartenVolterraBridge': 6,
    'KFCausalClockFloorArbitraryOrderFourteenFactorMultiPowerYosidaComposition': 9,
    'KFCausalClockFloorFourteenFactorYosidaVelocityCommutatorUmegakiAndoLiebGoldenThompsonBridge': 5,
    'KFCausalClockFloorFourteenFactorYosidaStinespringPetzTraceDistanceQuantumSteinAEPBridge': 5,
    'KFCausalArbitrarySourceMultiChannelEulerPartitionReciprocalBoundsAndKloostermanTwoChannelHierarchy': 6,
    'KFCausalMultiChannelEulerPartitionReciprocalKloostermanHierarchyOctonionE8SMGUTBridge': 5,
    'KFCausalMultiChannelEulerPartitionReciprocalKloostermanHierarchyBellCHSHTsirelsonPhaseFaithfulnessNoGoBridge': 5,
    'KFCausalCurved4DTwelveByTwelvePlaquetteThirtyFiveComponentFourthJetSecondWeylJetReconstructionBridge': 5,
    'KFCausalCurved4DFourteenFactorYosidaFourthJetSecondWeylJetEulerPartitionCapstoneConditionalEinsteinSpectralRigidityUnifiedForcingBridge': 5,
    'KFCausalTOETwentySixCheckpointCompleteTierOneMasterSynthesis': 6,
}
EXTRA_ANALYTIC = {}
SCOPE = 'Unconditional wide-strip (|h| <= pi*epsilon/3) growing-form (GV) & growing-Hamiltonian (G) output graph regularization, exact growing-form lift coherence growingLift(formLift GD x) = domainFormLift <x, hp>, fixed-N radial-plus-shifted-potential variational decomposition <GB(growingFormAction N(formLift GD x)), GB v> = <J_N(K x), GJ v> + <PB(domainFormLift <x, hp>), L_N^{h/2}(PB(growingLift v))>, and unconditional wide-strip growing-form variational pairing & operator output convergence <GB(growingFormAction J_n(formLift GD x)), GB v> -> <G x, GJ v>, J_n(K x) + L_n^{-h/2}(P x) -> G x, and J_n(K x) + J_n(P x) -> G x with zero quarter-strip hbn or hshift hypotheses, fourteen-parameter (a,b,c,d,e,f_param,g_param,h_param,i_param,j_param,k_param,l_param,m_param,n_param) higher-power potential-resolvent radial-Yosida cyclic tetradecagon cocycles and twenty-eight-parameter ((a,J1),...,(n_param,J14)) Cauchy rate bounds, five-operator (T,P,G,S,H) fifteen-parameter (a,b,c,d,e,f_param,g_param,h_param,i_param,j_param,k_param,l_param,m_param,n_param,o_param) higher-power cross-resolvent pentadecagon cocycles and common-domain Yosida cross-rate bounds, fourteen-parameter tetradecagon / fifteen-parameter pentadecagon / unconditional wide-strip growing-form convergence QQG / inflaton / slow-roll / dimension / gauge / Volterra bridge, twelve-by-twelve (s1..s12)x(t1..t12) (11x11=121 elementary plaquettes) mixed initial-and-final higher-power resolvent and identity plaquette grids with exact 2D Stokes / Green boundary cancellation across all 8 time-independent and 10 equal-outer-final-time domains, unconditional uniform-in-a two-time residual-Yosida (YS(t,a)f = f - a RS(t,a)f = S(t)(RS(t,a)f)) and Hamiltonian-Yosida (YH(t,a)f = f - a RH(t,a)f = H(t)(RH(t,a)f)) strong Hilbert-norm and operator-norm Lipschitz continuity ||YS(s,a)f - YS(t,a)f|| <= |e^{2t} - e^{2s}| e^{-(t+s)} ||f||, ||YS(s,a) - YS(t,a)|| <= |e^{2t} - e^{2s}| e^{-(t+s)}, ||YH(s,a)f - YH(t,a)f|| <= 2 |e^{2t} - e^{2s}| e^{-(t+s)} ||f||, and ||YH(s,a) - YH(t,a)|| <= 2 |e^{2t} - e^{2s}| e^{-(t+s)} and strong/operator-norm convergence YS(s,a)f -> YS(t,a)f, YS(s,a) -> YS(t,a), YH(s,a)f -> YH(t,a)f, and YH(s,a) -> YH(t,a) for all real m,g,k with Wightman / OS / Clay continuum bridge, twelve-by-twelve plaquette Polymer / Borgs-Imbrie / Kotecky-Preiss / Weingarten / Volterra SO(10) bridge, arbitrary-order fourteen-factor multi-power (r,s,q,p,l,u,v_pow,w_pow,z_pow,y_pow,x_pow,d_pow,c_pow,b_pow) and fourteen-parameter (a,b,d,e,c,f_param,g_param,h_param,i_param,j_param,k_param,l_param,m_param,n_param) Yosida composition defect calculus across all 5 Hamiltonians, fourteen-factor Yosida quantum-velocity commutator error / Umegaki / Ando / Lieb / Golden-Thompson bridge, fourteen-factor Yosida Stinespring / Petz / trace-distance / Quantum Stein / AEP bridge, analytic Euler partition generating function reciprocal partial-product bounds 1 + sum_{k=0}^{N-1} q^{k+1} <= 2 - P_N(q) <= prod_{k=0}^{N-1} (1 - q^{k+1})^{-1} <= (1 - q)/(1 - 2q) on 0 <= q < 1/2, exact reciprocal cancellation P_N(q) Q_N(q) = 1, and two-channel Rademacher-Kloosterman subleading hierarchy S_BH/c_1 - S_BH/c_2 = ((c_2 - c_1)/(c_1 c_2)) S_BH >= 0 for 2 <= c_1 <= c_2, multi-channel Euler partition reciprocal / Kloosterman two-channel hierarchy / octonion / E_8 / SM / GUT / CKM / PMNS / proton decay / dark matter bridge, multi-channel Euler partition reciprocal / Kloosterman two-channel hierarchy Bell / CHSH / Tsirelson / phase faithfulness / no-go bridge, curved 4D twelve-by-twelve plaquette / full 35-component symmetric 4th-order conformal jet L_jet (choose(4+4-1,4)=35) & 2nd-order differential Weyl jet d2W_{feabcd} (35 components, matching 35+35=70=choose(8,4)) simultaneous exact reconstruction reconstructFourthJetFromD2Riemann4D(fullD2RiemannFromFourthJetAndD2Weyl4D H L d2W) = L and reconstructD2WeylFromD2Riemann4D H (fullD2RiemannFromFourthJetAndD2Weyl4D H L d2W) = d2W / 20-component 3rd-order jet / 20-component algebraic Riemann-Weyl / off-diagonal shear Bianchi channel cancellation / on-shell stress-energy conservation bridge, curved 4D fourteen-factor Yosida / 35-component 4th-order jet & 2nd-order Weyl reconstruction / Euler partition reciprocal / Kloosterman hierarchy Capstone / ConditionalEinstein / spectral rigidity / unified forcing bridge, and Twenty-Six-Checkpoint Complete Tier-One TOE Master Synthesis. Specifically, on 0<epsilon,h!=0,abs(h)<=pi*epsilon/3 and for all real m,g,k,s,t: (1) on the full wide strip abs(h)<=pi*epsilon/3, for every x in Dom(G) = Dom(K) cap Dom(P), u = formLift GD x, and v in GV, growingLift(u) = domainFormLift <x, hp>, <GB(growingFormAction N u), GB v> = <J_N(K x), GJ v> + <PB(domainFormLift <x, hp>), L_N^{h/2}(PB(growingLift v))>, <GB(growingFormAction J_n u), GB v> -> <G x, GJ v>, J_n(K x) + L_n^{-h/2}(P x) -> G x, and J_n(K x) + J_n(P x) -> G x with zero quarter-strip hbn or hshift hypotheses, while fourteen-parameter (a..n_param) and twenty-eight-parameter ((a,J1),...,(n_param,J14)) potential-resolvent and identity-Yosida tier differences satisfy exact 14-step cyclic tetradecagon cocycles, Dom(P^(r+2))/Dom(P^r) regularity, and thirteen-hop Cauchy rate bounds, and across any FifteenParameterFiveOperatorSystem (T,P,G,S(t),H(t)) at (a..o_param), cross-resolvent and cross-Yosida differences satisfy exact 15-step pentadecagon cocycles and fourteen-hop bounds; (2) for all real m,g,k,t,s in R and a>0 (including k<=0), both the residual Yosida approximant YS(t,a)f = f - a RS(t,a)f = S(t)(RS(t,a)f) and full Hamiltonian Yosida approximant YH(t,a)f = f - a RH(t,a)f = H(t)(RH(t,a)f) satisfy unconditional uniform-in-a Hilbert-norm and operator-norm Lipschitz continuity ||YS(s,a)f - YS(t,a)f|| <= |e^{2t} - e^{2s}| e^{-(t+s)} ||f||, ||YS(s,a) - YS(t,a)|| <= |e^{2t} - e^{2s}| e^{-(t+s)}, ||YH(s,a)f - YH(t,a)f|| <= 2 |e^{2t} - e^{2s}| e^{-(t+s)} ||f||, and ||YH(s,a) - YH(t,a)|| <= 2 |e^{2t} - e^{2s}| e^{-(t+s)} with strong and operator-norm convergence YS(s,a)f -> YS(t,a)f, YS(s,a) -> YS(t,a), YH(s,a)f -> YH(t,a)f, and YH(s,a) -> YH(t,a) as s -> t, while on a 12x12 grid (s1..s12)x(t1..t12), the 11x11 sum of 121 elementary mixed initial-and-final higher-power resolvent and identity plaquettes satisfies exact 2D Stokes / Green boundary cancellation to the outer plaquette (s1,s12; t1,t12) canceling 100 interior vertices and 220 interior edges, 12-initial and 12-final dodecagon cocycles, 8-domain regularity, and equal-outer-final-time Dom(H(t)^(r+2)) + 10-domain regularity; (3) across all 5 Hamiltonians A in {T,P,G,S(t),H(t)}, fourteen-factor multi-power (r,s,q,p,l,u,v_pow,w_pow,z_pow,y_pow,x_pow,d_pow,c_pow,b_pow) and fourteen-parameter (a,b,d,e,c,f_param,g_param,h_param,i_param,j_param,k_param,l_param,m_param,n_param) Yosida compositions preserve Dom(A^n), commute with A^n, contract kthPowerGraphNormSq A n, and satisfy ((r/a + s/b + q/d + p/e + l/c + u/f_param + v_pow/g_param + w_pow/h_param + z_pow/i_param + y_pow/j_param + x_pow/k_param + d_pow/l_param + c_pow/m_param + b_pow/n_param)^2) * kthPowerGraphNormSq A (n+1) x defect bounds; (4) for all q in [0,1/2) and N in N, the Euler partition generating function partial product Q_N(q) = prod_{k=0}^{N-1} (1 - q^{k+1})^{-1} satisfies P_N(q) Q_N(q) = 1 and 1 + sum_{k=0}^{N-1} q^{k+1} <= 2 - P_N(q) <= Q_N(q) <= (1 - q)/(1 - 2q), while for all 2 <= c_1 <= c_2 the Rademacher-Kloosterman subleading channel exponents satisfy (S_BH - S_BH/c_2) - (S_BH - S_BH/c_1) = ((c_2 - c_1)/(c_1 c_2)) S_BH >= 0; (5) for any 4D Hessian H, any 35-component symmetric 4th-order conformal jet L (choose(4+4-1,4)=35), and any Lorentzian trace-free 2nd-order differential Weyl jet d2W (35 components, matching 35+35=70=choose(8,4)), fullD2RiemannFromFourthJetAndD2Weyl4D H L d2W has Lorentzian Ricci contraction fullD2Ricci4D H L and scalar contraction fullD2Scalar4D H L, and both L and d2W are reconstructed simultaneously and exactly via reconstructFourthJetFromD2Riemann4D(fullD2RiemannFromFourthJetAndD2Weyl4D H L d2W) = L and reconstructD2WeylFromD2Riemann4D H (fullD2RiemannFromFourthJetAndD2Weyl4D H L d2W) = d2W, synthesized with 100% (659/659) direct non-Audit module coverage. Unconditional fixed-N strong-operator invariance J_N(DomP) subseteq DomP without the wide-strip half-shift variational pairing hypothesis (beyond the proved four-domain invariance, two-sided potential-pairing domination, Dom(G) radial-Yosida contraction/rate, Dom(H(t))/Dom(S(t)) radial-Yosida quadratic lower bound and rate, unconditional Dom(T) invariance/commutator/core, unconditional Dom(G) = Dom(K) cap Dom(P) seven-operator resolvent invariance, wide-strip half-shift variational Dom(P)/Dom(G) regularization, and unconditional wide-strip potential-form and growing-form pairing & operator output convergence), single-resolvent R_{H(t)}(a)f in DomP for k<=0 without iteration (beyond the proved 14-domain regularity, unconditional R_G(a)f in DomP, 5-way DomP <-> DomG <-> DomT equivalence, shifted-source residual-resolvent criterion, static-residual second resolvent identity, unconditional strong/operator-norm two-time residual & Hamiltonian resolvent and Yosida generator continuity, and positive-vacuum k>0 domain stability), trajectory-wide unbounded-momentum derivatives beyond the energy-controlled H(t)-domain quantum-velocity commutator bound, general non-conformal dynamical nonlinear 4D Einstein-Weyl PDE evolution beyond the 20-component algebraic Riemann-Weyl-Ricci-Hessian, 20-component 3rd-order jet / differential Weyl, and 35-component 4th-order jet / 2nd-order Weyl reconstructions and linearized Bianchi/stress-energy conservation, full infinite-volume 4D continuum OS/Wightman QFT beyond the chamber/cluster reduction, first-principles derivation of absolute dimensionful scales, microscopic phase selection, controlled physical limits, and empirical identification remain open; the earlier phase/harmonic identification still requires revision. A physical TOE is not proved. This checkpoint adds93 theorems in15 modules, preserves3872 parent source/script hashes and adds17 for3889 total; exact root extends from9416 to9431 lines. All12 parent analytic artifacts and23 numerical files remain unchanged. Standard axioms only.'
PARENT = 'data/twenty_five_checkpoint_complete_tier_one_synthesis_audit.json'
PARENT_SHA = 'df0f5b13675df93315455a57ed95208715139367bf111f644210ffc766095510'
REPORT = 'data/twenty_six_checkpoint_complete_tier_one_synthesis_audit.json'
SCRIPTS = ['scripts/twenty_six_checkpoint_complete_tier_one_synthesis_audit.py',
           'scripts/verify_twenty_six_checkpoint_complete_tier_one_synthesis.py']
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
    assert len(old)==3872 and len(hashes)==3872+len(EXPECTED)+2
    assert all(hashes[p]==h for p,h in old.items())
    assert all(sha(root/p)==h for p,h in hashes.items())
    additions={'UnifiedTheory/Audit/'+n+'.lean' for n in EXPECTED}|set(SCRIPTS)
    assert set(hashes)-set(old)==additions
    assert [Path(x['source']).stem for x in report['modules']]==list(EXPECTED)
    logs=overlay/'twenty-six-checkpoint-complete-tier-one-synthesis-audit'
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
    assert text.endswith(suffix) and len(text.splitlines())==9416+len(EXPECTED)
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
