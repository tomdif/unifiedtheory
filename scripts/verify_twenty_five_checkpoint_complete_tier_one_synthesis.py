#!/usr/bin/env python3
"""Independently verify the twenty-five-checkpoint-complete-tier-one-synthesis audit and preserved evidence."""
import argparse
import hashlib
import json
from pathlib import Path
import re

EXPECTED = {
    'KFCausalClockFloorHigherPowerPotentialResolventYosidaThirteenParameterTridecagon': 10,
    'KFCausalClockFloorFiveOperatorFourteenParameterHigherPowerTetradecagonCocycleAndYosida': 7,
    'KFCausalClockFloorThirteenParameterTridecagonFourteenParameterTetradecagonWideStripFormConvergenceBridge': 6,
    'KFCausalClockFloorElevenByElevenMixedInitialFinalHigherPowerResolventPlaquetteGrid': 7,
    'KFCausalClockFloorElevenByElevenPlaquetteUnconditionalResidualAndHamiltonianStrongResolventContinuityBridge': 6,
    'KFCausalClockFloorElevenByElevenPlaquettePolymerBorgsImbrieKoteckyPreissWeingartenVolterraBridge': 6,
    'KFCausalClockFloorArbitraryOrderThirteenFactorMultiPowerYosidaComposition': 9,
    'KFCausalClockFloorThirteenFactorYosidaVelocityCommutatorUmegakiAndoLiebGoldenThompsonBridge': 5,
    'KFCausalClockFloorThirteenFactorYosidaStinespringPetzTraceDistanceQuantumSteinAEPBridge': 5,
    'KFCausalArbitrarySourceMultiChannelQPochhammerPartialProductWeierstrassLowerBoundAndKloostermanRademacherSubleadingGap': 6,
    'KFCausalMultiChannelQPochhammerWeierstrassKloostermanRademacherGapOctonionE8SMGUTBridge': 5,
    'KFCausalMultiChannelQPochhammerWeierstrassKloostermanRademacherGapBellCHSHTsirelsonPhaseFaithfulnessNoGoBridge': 5,
    'KFCausalCurved4DElevenByElevenPlaquetteTwentyComponentThirdJetDifferentialBianchiWeylDivergenceBridge': 5,
    'KFCausalCurved4DThirteenFactorYosidaThirdJetWeylBianchiQPochhammerCapstoneConditionalEinsteinSpectralRigidityUnifiedForcingBridge': 5,
    'KFCausalTOETwentyFiveCheckpointCompleteTierOneMasterSynthesis': 6,
}
EXTRA_ANALYTIC = {}
SCOPE = 'Unconditional wide-strip (|h| <= pi*epsilon/3) potential-form output graph & domain regularization ((J_N x, L_N^{-h/2}(PB(formLift x))) in Graph(T_pot) and J_N x in Dom(K) cap Dom(T_pot)), unconditional wide-strip output-shift commutator convergence L_n^{-h/2} z - L_n^0 z -> 0 and L_n^{h/2} z - L_n^{-h/2} z -> 0, and unconditional wide-strip variational form pairing convergence <PB(formAction J_n(formLift x)), PB v> -> <P x, PJ v> with zero hshift or quarter-strip hypotheses, thirteen-parameter (a,b,c,d,e,f_param,g_param,h_param,i_param,j_param,k_param,l_param,m_param) higher-power potential-resolvent radial-Yosida cyclic tridecagon cocycles and twenty-six-parameter ((a,J1),...,(m_param,J13)) Cauchy rate bounds, five-operator (T,P,G,S,H) fourteen-parameter (a,b,c,d,e,f_param,g_param,h_param,i_param,j_param,k_param,l_param,m_param,n_param) higher-power cross-resolvent tetradecagon cocycles and common-domain Yosida cross-rate bounds, thirteen-parameter tridecagon / fourteen-parameter tetradecagon / unconditional wide-strip form-pairing convergence QQG / inflaton / slow-roll / dimension / gauge / Volterra bridge, eleven-by-eleven (s1..s11)x(t1..t11) (10x10=100 elementary plaquettes) mixed initial-and-final higher-power resolvent and identity plaquette grids with exact 2D Stokes / Green boundary cancellation across all 8 time-independent and 10 equal-outer-final-time domains, unconditional strong Hilbert-norm and operator-norm two-time residual-resolvent and Hamiltonian-resolvent Lipschitz continuity ||R_{S(s)}(a)f - R_{S(t)}(a)f|| <= |e^{2t} - e^{2s}| (e^{-(t+s)} a^{-1} ||f||), ||R_{S(s)}(a) - R_{S(t)}(a)|| <= |e^{2t} - e^{2s}| (e^{-(t+s)} a^{-1}), ||R_{H(s)}(a)f - R_{H(t)}(a)f|| <= |e^{2t} - e^{2s}| (2 e^{-(t+s)} a^{-1} ||f||), and ||R_{H(s)}(a) - R_{H(t)}(a)|| <= |e^{2t} - e^{2s}| (2 e^{-(t+s)} a^{-1}) and strong/operator-norm convergence R_{S(s)}(a)f -> R_{S(t)}(a)f, R_{S(s)}(a) -> R_{S(t)}(a), R_{H(s)}(a)f -> R_{H(t)}(a)f, and R_{H(s)}(a) -> R_{H(t)}(a) for all real m,g,k with Wightman / OS / Clay continuum bridge, eleven-by-eleven plaquette Polymer / Borgs-Imbrie / Kotecky-Preiss / Weingarten / Volterra SO(10) bridge, arbitrary-order thirteen-factor multi-power (r,s,q,p,l,u,v_pow,w_pow,z_pow,y_pow,x_pow,d_pow,c_pow) and thirteen-parameter (a,b,d,e,c,f_param,g_param,h_param,i_param,j_param,k_param,l_param,m_param) Yosida composition defect calculus across all 5 Hamiltonians, thirteen-factor Yosida quantum-velocity commutator error / Umegaki / Ando / Lieb / Golden-Thompson bridge, thirteen-factor Yosida Stinespring / Petz / trace-distance / Quantum Stein / AEP bridge, analytic q-Pochhammer partial-product Weierstrass lower bound 1 - sum_{k=0}^{N-1} q^{k+1} <= prod_{k=0}^{N-1} (1 - q^{k+1}) <= 1, exact geometric series telescoping (1 - q) S_N(q) = q(1 - q^N), universal lower bound (1 - 2q)/(1 - q) <= prod_{k=0}^{N-1} (1 - q^{k+1}), and Rademacher-Kloosterman subleading c >= 2 channel exponential suppression gap S_BH - S_BH/c = ((c-1)/c) S_BH >= S_BH/2 >= 0, multi-channel q-Pochhammer Weierstrass / Kloosterman-Rademacher gap / octonion / E_8 / SM / GUT / CKM / PMNS / proton decay / dark matter bridge, multi-channel q-Pochhammer Weierstrass / Kloosterman-Rademacher gap Bell / CHSH / Tsirelson / phase faithfulness / no-go bridge, curved 4D eleven-by-eleven plaquette / full 20-component symmetric 3rd-order conformal jet K_jet (choose(4+3-1,3)=20) & differential Weyl 1st-jet dW_{eabcd} simultaneous exact reconstruction reconstructThirdJetFromDRiemann4D(fullDRiemannFromJetAndWeyl4D H K dW) = K and reconstructDWeylFromDRiemann4D H (fullDRiemannFromJetAndWeyl4D H K dW) = dW / off-diagonal shear Bianchi channel cancellation / on-shell stress-energy conservation bridge, curved 4D thirteen-factor Yosida / 20-component 3rd-order jet & differential Weyl reconstruction / q-Pochhammer Weierstrass / Kloosterman-Rademacher gap Capstone / ConditionalEinstein / spectral rigidity / unified forcing bridge, and Twenty-Five-Checkpoint Complete Tier-One TOE Master Synthesis. Specifically, on 0<epsilon,h!=0,abs(h)<=pi*epsilon/3 and for all real m,g,k,s,t: (1) on the full wide strip abs(h)<=pi*epsilon/3, for every x in Dom(P), u = domainFormLift x, and v in PV, ((x, PB u) in Graph(T_pot)), ((J_N x, L_N^{-h/2}(PB u)) in Graph(T_pot)), J_N x in Dom(K) cap Dom(T_pot), L_n^{-h/2} z - L_n^0 z -> 0, L_n^{h/2} z - L_n^{-h/2} z -> 0, PB(formAction J_n u) -> PB u, and <PB(formAction J_n u), PB v> -> <P x, PJ v> with zero hshift or quarter-strip hypotheses, while thirteen-parameter (a..m_param) and twenty-six-parameter ((a,J1),...,(m_param,J13)) potential-resolvent and identity-Yosida tier differences satisfy exact 13-step cyclic tridecagon cocycles, Dom(P^(r+2))/Dom(P^r) regularity, and twelve-hop Cauchy rate bounds, and across any FourteenParameterFiveOperatorSystem (T,P,G,S(t),H(t)) at (a..n_param), cross-resolvent and cross-Yosida differences satisfy exact 14-step tetradecagon cocycles and thirteen-hop bounds; (2) for all real m,g,k,t,s in R and a>0 (including k<=0), both the residual resolvent R_{S(t)}(a) and full Hamiltonian resolvent R_{H(t)}(a) satisfy unconditional Hilbert-norm and operator-norm Lipschitz continuity ||R_{S(s)}(a)f - R_{S(t)}(a)f|| <= |e^{2t} - e^{2s}| (e^{-(t+s)} a^{-1} ||f||), ||R_{S(s)}(a) - R_{S(t)}(a)|| <= |e^{2t} - e^{2s}| (e^{-(t+s)} a^{-1}), ||R_{H(s)}(a)f - R_{H(t)}(a)f|| <= |e^{2t} - e^{2s}| (2 e^{-(t+s)} a^{-1} ||f||), and ||R_{H(s)}(a) - R_{H(t)}(a)|| <= |e^{2t} - e^{2s}| (2 e^{-(t+s)} a^{-1}) with strong and operator-norm convergence R_{S(s)}(a)f -> R_{S(t)}(a)f, R_{S(s)}(a) -> R_{S(t)}(a), R_{H(s)}(a)f -> R_{H(t)}(a)f, and R_{H(s)}(a) -> R_{H(t)}(a) as s -> t, while on an 11x11 grid (s1..s11)x(t1..t11), the 10x10 sum of 100 elementary mixed initial-and-final higher-power resolvent and identity plaquettes satisfies exact 2D Stokes / Green boundary cancellation to the outer plaquette (s1,s11; t1,t11) canceling 81 interior vertices and 180 interior edges, 11-initial and 11-final hendecagon cocycles, 8-domain regularity, and equal-outer-final-time Dom(H(t)^(r+2)) + 10-domain regularity; (3) across all 5 Hamiltonians A in {T,P,G,S(t),H(t)}, thirteen-factor multi-power (r,s,q,p,l,u,v_pow,w_pow,z_pow,y_pow,x_pow,d_pow,c_pow) and thirteen-parameter (a,b,d,e,c,f_param,g_param,h_param,i_param,j_param,k_param,l_param,m_param) Yosida compositions preserve Dom(A^n), commute with A^n, contract kthPowerGraphNormSq A n, and satisfy ((r/a + s/b + q/d + p/e + l/c + u/f_param + v_pow/g_param + w_pow/h_param + z_pow/i_param + y_pow/j_param + x_pow/k_param + d_pow/l_param + c_pow/m_param)^2) * kthPowerGraphNormSq A (n+1) x defect bounds; (4) for all q in [0,1) and N in N, the q-Pochhammer partial product prod_{k=0}^{N-1} (1 - q^{k+1}) satisfies 1 - sum_{k=0}^{N-1} q^{k+1} <= prod_{k=0}^{N-1} (1 - q^{k+1}) <= 1, (1 - q) S_N(q) = q(1 - q^N), and (1 - 2q)/(1 - q) <= prod_{k=0}^{N-1} (1 - q^{k+1}), while for all c >= 2 the Rademacher-Kloosterman subleading channel exponent satisfies S_BH - S_BH/c = ((c-1)/c) S_BH >= S_BH/2 >= 0; (5) for any 4D Hessian H, any 20-component symmetric 3rd-order conformal jet K (choose(4+3-1,3)=20), and any Lorentzian trace-free differential Weyl 1st-jet dW, fullDRiemannFromJetAndWeyl4D H K dW has Lorentzian Ricci contraction fullDRicci4D H K and scalar contraction fullDScalar4D H K, and both K and dW are reconstructed simultaneously and exactly via reconstructThirdJetFromDRiemann4D(fullDRiemannFromJetAndWeyl4D H K dW) = K and reconstructDWeylFromDRiemann4D H (fullDRiemannFromJetAndWeyl4D H K dW) = dW, synthesized with 100% (659/659) direct non-Audit module coverage. Unconditional fixed-N strong-operator invariance J_N(DomP) subseteq DomP without the wide-strip half-shift variational pairing hypothesis (beyond the proved four-domain invariance, two-sided potential-pairing domination, Dom(G) radial-Yosida contraction/rate, Dom(H(t))/Dom(S(t)) radial-Yosida quadratic lower bound and rate, unconditional Dom(T) invariance/commutator/core, unconditional Dom(G) = Dom(K) cap Dom(P) seven-operator resolvent invariance, wide-strip half-shift variational Dom(P)/Dom(G) regularization, and unconditional wide-strip form-pairing convergence), single-resolvent R_{H(t)}(a)f in DomP for k<=0 without iteration (beyond the proved 14-domain regularity, unconditional R_G(a)f in DomP, 5-way DomP <-> DomG <-> DomT equivalence, shifted-source residual-resolvent criterion, static-residual second resolvent identity, unconditional strong/operator-norm two-time residual & Hamiltonian resolvent continuity, and positive-vacuum k>0 domain stability), trajectory-wide unbounded-momentum derivatives beyond the energy-controlled H(t)-domain quantum-velocity commutator bound, general non-conformal dynamical nonlinear 4D Einstein-Weyl PDE evolution beyond the 20-component algebraic Riemann-Weyl-Ricci-Hessian and 20-component 3rd-order jet / differential Weyl reconstructions and linearized Bianchi/stress-energy conservation, full infinite-volume 4D continuum OS/Wightman QFT beyond the chamber/cluster reduction, first-principles derivation of absolute dimensionful scales, microscopic phase selection, controlled physical limits, and empirical identification remain open; the earlier phase/harmonic identification still requires revision. A physical TOE is not proved. This checkpoint adds93 theorems in15 modules, preserves3855 parent source/script hashes and adds17 for3872 total; exact root extends from9401 to9416 lines. All12 parent analytic artifacts and23 numerical files remain unchanged. Standard axioms only.'
PARENT = 'data/twenty_four_checkpoint_complete_tier_one_synthesis_audit.json'
PARENT_SHA = '4ba3c89645f6a03f7ca8eef2609e54dd78246d17841b9cfe41245909df5c7c15'
REPORT = 'data/twenty_five_checkpoint_complete_tier_one_synthesis_audit.json'
SCRIPTS = ['scripts/twenty_five_checkpoint_complete_tier_one_synthesis_audit.py',
           'scripts/verify_twenty_five_checkpoint_complete_tier_one_synthesis.py']
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
    assert len(old)==3855 and len(hashes)==3855+len(EXPECTED)+2
    assert all(hashes[p]==h for p,h in old.items())
    assert all(sha(root/p)==h for p,h in hashes.items())
    additions={'UnifiedTheory/Audit/'+n+'.lean' for n in EXPECTED}|set(SCRIPTS)
    assert set(hashes)-set(old)==additions
    assert [Path(x['source']).stem for x in report['modules']]==list(EXPECTED)
    logs=overlay/'twenty-five-checkpoint-complete-tier-one-synthesis-audit'
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
    assert text.endswith(suffix) and len(text.splitlines())==9401+len(EXPECTED)
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
