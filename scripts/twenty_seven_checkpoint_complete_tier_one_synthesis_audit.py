#!/usr/bin/env python3
"""Check unconditional wide-strip (|h| <= pi*epsilon/3) time-dependent residual-form (SV t), residual-Hamiltonian (S(t)), and full-Hamiltonian (H(t)) output graph regularization, exact residual-to-static and residual-to-potential form lift coherence staticLift t (formLift (SD t) <f, hfS>) = staticDomainFormLift <f, hfT> and potentialLift t (formLift (SD t) <f, hfS>) = potentialDomainFormLift <f, hfP>, unconditional wide-strip residual-form variational pairing convergence <SB t (residualFormAction J_{n+1}(formLift (SD t) x_res)), SB t v_res> -> <S(t) x_res, SJ t v_res>, and unconditional wide-strip operator output convergence for both S(t) and H(t) (T <J_{n+1} f, ...> + e^{2t} L_{n+1}^{-h/2}(P f) -> S(t) f, J_{n+1}(T f) + e^{2t} J_{n+1}(P f) -> S(t) f, T <J_{n+1} f, ...> + e^{2t}(K <J_{n+1} f, ...> + L_{n+1}^{-h/2}(P f)) -> H(t) f, and J_{n+1}(T f) + e^{2t}(J_{n+1}(K f) + J_{n+1}(P f)) -> H(t) f with zero quarter-strip hbn or hshift hypotheses), fifteen-parameter higher-power potential-resolvent radial-Yosida pentadecagon cocycles and thirty-parameter Cauchy rate bounds, five-operator sixteen-parameter higher-power hexadecagon cocycles and Yosida bounds, fifteen-parameter pentadecagon / sixteen-parameter hexadecagon / unconditional wide-strip residual-and-full-Hamiltonian convergence QQG / inflaton / slow-roll / dimension / gauge / Volterra bridge, thirteen-by-thirteen (12x12=144 elementary plaquettes) mixed initial-and-final higher-power resolvent plaquette grids and 2D Stokes boundary cancellation, unconditional residual-Yosida (YS(t,a)) and Hamiltonian-Yosida (YH(t,a)) Pythagorean energy-split & contraction bounds ||YS(t,a)f||^2 + a^2 ||RS(t,a)f||^2 <= ||f||^2, ||YS(t,a)|| <= 1, ||YH(t,a)f||^2 + a^2 ||RH(t,a)f||^2 <= ||f||^2, ||YH(t,a)|| <= 1 and uniform-in-(a,b) two-time two-factor Yosida composition Lipschitz continuity ||YS(s,a)(YS(s,b)f) - YS(t,a)(YS(t,b)f)|| <= 2 |e^{2t} - e^{2s}| e^{-(t+s)} ||f|| and ||YH(s,a)(YH(s,b)f) - YH(t,a)(YH(t,b)f)|| <= 4 |e^{2t} - e^{2s}| e^{-(t+s)} ||f|| with Wightman / OS / Clay continuum bridge, thirteen-by-thirteen plaquette Polymer / Borgs-Imbrie / Kotecky-Preiss / Weingarten / Volterra SO(10) bridge, arbitrary-order fifteen-factor multi-power (r,s,q,p,l,u,v_pow,w_pow,z_pow,y_pow,x_pow,d_pow,c_pow,b_pow,a_pow) and fifteen-parameter (a,b,d,e,c,f_param,g_param,h_param,i_param,j_param,k_param,l_param,m_param,n_param,o_param) Yosida composition defect calculus across all 5 Hamiltonians, fifteen-factor Yosida quantum-velocity commutator error / Umegaki / Ando / Lieb / Golden-Thompson bridge, fifteen-factor Yosida Stinespring / Petz / trace-distance / Quantum Stein / AEP bridge, analytic Euler distinct-parts (fermionic) partition partial product D_N(q) = prod_{k=0}^{N-1} (1 + q^{k+1}), exact bosonic-fermionic partial-product identities P_N(q) D_N(q) = P_N(q^2) and D_N(q) = P_N(q^2) Q_N(q), Pauli exclusion sandwich bounds 1 + sum_{k=0}^{N-1} q^{k+1} <= D_N(q) <= Q_N(q) <= (1 - q)/(1 - 2q), and three-channel Rademacher-Kloosterman subleading telescoping cocycle (S_BH/c_1 - S_BH/c_2) + (S_BH/c_2 - S_BH/c_3) = S_BH/c_1 - S_BH/c_3 = ((c_3 - c_1)/(c_1 c_3)) S_BH >= 0 for 2 <= c_1 <= c_2 <= c_3, multi-channel Euler distinct-partition / Kloosterman three-channel cocycle / octonion / E_8 / SM / GUT / CKM / PMNS / proton decay / dark matter bridge, multi-channel Euler distinct-partition / Kloosterman three-channel cocycle Bell / CHSH / Tsirelson / phase faithfulness / no-go bridge, curved 4D thirteen-by-thirteen plaquette / full 56-component symmetric 5th-order conformal jet M_jet (choose(4+5-1,5)=56) & 3rd-order differential Weyl jet d3W_{gfeabcd} (56 components, matching choose(8,3)=choose(8,5)=56 and 56+56=112) simultaneous exact reconstruction (reconstructFifthJetFromD3Riemann4D and reconstructD3WeylFromD3Riemann4D) / 35-component 4th-order jet / 20-component 3rd-order jet / 20-component algebraic Riemann-Weyl / off-diagonal shear Bianchi / on-shell stress-energy conservation bridge, curved 4D fifteen-factor Yosida / 56-component 5th-order jet & 3rd-order Weyl reconstruction / Euler distinct-partition / Kloosterman three-channel cocycle Capstone / ConditionalEinstein / spectral rigidity / unified forcing bridge, Twenty-Seven-Checkpoint Complete Tier-One TOE Master Synthesis, and preserved evidence."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess

EXPECTED = {
    'KFCausalClockFloorHigherPowerPotentialResolventYosidaFifteenParameterPentadecagon': 10,
    'KFCausalClockFloorFiveOperatorSixteenParameterHigherPowerHexadecagonCocycleAndYosida': 7,
    'KFCausalClockFloorFifteenParameterPentadecagonSixteenParameterHexadecagonWideStripResidualHamiltonianConvergenceBridge': 6,
    'KFCausalClockFloorThirteenByThirteenMixedInitialFinalHigherPowerResolventPlaquetteGrid': 7,
    'KFCausalClockFloorThirteenByThirteenPlaquetteUnconditionalYosidaContractionAndTwoFactorCompositionContinuityBridge': 6,
    'KFCausalClockFloorThirteenByThirteenPlaquettePolymerBorgsImbrieKoteckyPreissWeingartenVolterraBridge': 6,
    'KFCausalClockFloorArbitraryOrderFifteenFactorMultiPowerYosidaComposition': 9,
    'KFCausalClockFloorFifteenFactorYosidaVelocityCommutatorUmegakiAndoLiebGoldenThompsonBridge': 5,
    'KFCausalClockFloorFifteenFactorYosidaStinespringPetzTraceDistanceQuantumSteinAEPBridge': 5,
    'KFCausalArbitrarySourceMultiChannelEulerDistinctPartitionBosonicFermionicIdentityAndKloostermanThreeChannelCocycle': 6,
    'KFCausalMultiChannelEulerDistinctPartitionKloostermanThreeChannelOctonionE8SMGUTBridge': 5,
    'KFCausalMultiChannelEulerDistinctPartitionKloostermanThreeChannelBellCHSHTsirelsonPhaseFaithfulnessNoGoBridge': 5,
    'KFCausalCurved4DThirteenByThirteenPlaquetteFiftySixComponentFifthJetThirdWeylJetReconstructionBridge': 5,
    'KFCausalCurved4DFifteenFactorYosidaFifthJetThirdWeylJetEulerDistinctPartitionCapstoneConditionalEinsteinSpectralRigidityUnifiedForcingBridge': 5,
    'KFCausalTOETwentySevenCheckpointCompleteTierOneMasterSynthesis': 6,
}
EXTRA_ANALYTIC = {}
SCOPE = 'Unconditional wide-strip (|h| <= pi*epsilon/3) time-dependent residual-form (SV t), residual-Hamiltonian (S(t)), and full-Hamiltonian (H(t)) output graph regularization, exact residual-to-static and residual-to-potential form lift coherence staticLift t (formLift (SD t) <f, hfS>) = staticDomainFormLift <f, hfT> and potentialLift t (formLift (SD t) <f, hfS>) = potentialDomainFormLift <f, hfP>, unconditional wide-strip residual-form variational pairing convergence <SB t (residualFormAction J_{n+1}(formLift (SD t) x_res)), SB t v_res> -> <S(t) x_res, SJ t v_res>, and unconditional wide-strip operator output convergence for both S(t) and H(t) (T <J_{n+1} f, ...> + e^{2t} L_{n+1}^{-h/2}(P f) -> S(t) f, J_{n+1}(T f) + e^{2t} J_{n+1}(P f) -> S(t) f, T <J_{n+1} f, ...> + e^{2t}(K <J_{n+1} f, ...> + L_{n+1}^{-h/2}(P f)) -> H(t) f, and J_{n+1}(T f) + e^{2t}(J_{n+1}(K f) + J_{n+1}(P f)) -> H(t) f with zero quarter-strip hbn or hshift hypotheses), fifteen-parameter (a..o_param) higher-power potential-resolvent radial-Yosida cyclic pentadecagon cocycles and thirty-parameter ((a,J1),...,(o_param,J15)) Cauchy rate bounds, five-operator (T,P,G,S(t),H(t)) sixteen-parameter (a..p_param) higher-power hexadecagon cocycles and Yosida bounds, fifteen-parameter pentadecagon / sixteen-parameter hexadecagon / unconditional wide-strip residual-and-full-Hamiltonian convergence QQG / inflaton / slow-roll / dimension / gauge / Volterra bridge, thirteen-by-thirteen (s1..s13)x(t1..t13) (12x12=144 elementary plaquettes) mixed initial-and-final higher-power resolvent and identity plaquette grids with exact 2D Stokes / Green boundary cancellation across all 8 time-independent and 10 equal-outer-final-time domains, unconditional residual-Yosida (YS(t,a)f = f - a RS(t,a)f) and Hamiltonian-Yosida (YH(t,a)f = f - a RH(t,a)f) Pythagorean energy-split & contraction bounds ||YS(t,a)f||^2 + a^2 ||RS(t,a)f||^2 <= ||f||^2, ||YS(t,a)|| <= 1, ||YH(t,a)f||^2 + a^2 ||RH(t,a)f||^2 <= ||f||^2, ||YH(t,a)|| <= 1 and uniform-in-(a,b) two-time two-factor Yosida composition Lipschitz continuity ||YS(s,a)(YS(s,b)f) - YS(t,a)(YS(t,b)f)|| <= 2 |e^{2t} - e^{2s}| e^{-(t+s)} ||f||, ||(YS(s,a)).comp (YS(s,b)) - (YS(t,a)).comp (YS(t,b))|| <= 2 |e^{2t} - e^{2s}| e^{-(t+s)}, ||YH(s,a)(YH(s,b)f) - YH(t,a)(YH(t,b)f)|| <= 4 |e^{2t} - e^{2s}| e^{-(t+s)} ||f||, and ||(YH(s,a)).comp (YH(s,b)) - (YH(t,a)).comp (YH(t,b))|| <= 4 |e^{2t} - e^{2s}| e^{-(t+s)} with Wightman / OS / Clay continuum bridge, thirteen-by-thirteen plaquette Polymer / Borgs-Imbrie / Kotecky-Preiss / Weingarten / Volterra SO(10) bridge, arbitrary-order fifteen-factor multi-power (r,s,q,p,l,u,v_pow,w_pow,z_pow,y_pow,x_pow,d_pow,c_pow,b_pow,a_pow) and fifteen-parameter (a,b,d,e,c,f_param,g_param,h_param,i_param,j_param,k_param,l_param,m_param,n_param,o_param) Yosida composition defect calculus across all 5 Hamiltonians, fifteen-factor Yosida quantum-velocity commutator error / Umegaki / Ando / Lieb / Golden-Thompson bridge, fifteen-factor Yosida Stinespring / Petz / trace-distance / Quantum Stein / AEP bridge, analytic Euler distinct-parts (fermionic) partition partial product D_N(q) = prod_{k=0}^{N-1} (1 + q^{k+1}), exact bosonic-fermionic partial-product identities P_N(q) D_N(q) = P_N(q^2) and D_N(q) = P_N(q^2) Q_N(q), Pauli exclusion sandwich bounds 1 + sum_{k=0}^{N-1} q^{k+1} <= D_N(q) <= Q_N(q) <= (1 - q)/(1 - 2q), and three-channel Rademacher-Kloosterman subleading telescoping cocycle (S_BH/c_1 - S_BH/c_2) + (S_BH/c_2 - S_BH/c_3) = S_BH/c_1 - S_BH/c_3 = ((c_3 - c_1)/(c_1 c_3)) S_BH >= 0 for 2 <= c_1 <= c_2 <= c_3, multi-channel Euler distinct-partition / Kloosterman three-channel cocycle / octonion / E_8 / SM / GUT / CKM / PMNS / proton decay / dark matter bridge, multi-channel Euler distinct-partition / Kloosterman three-channel cocycle Bell / CHSH / Tsirelson / phase faithfulness / no-go bridge, curved 4D thirteen-by-thirteen plaquette / full 56-component symmetric 5th-order conformal jet M_jet (choose(4+5-1,5)=56) & 3rd-order differential Weyl jet d3W_{gfeabcd} (56 components, matching choose(8,3)=choose(8,5)=56 and 56+56=112) simultaneous exact reconstruction reconstructFifthJetFromD3Riemann4D(fullD3RiemannFromFifthJetAndD3Weyl4D H M_jet d3W) = M_jet and reconstructD3WeylFromD3Riemann4D H (fullD3RiemannFromFifthJetAndD3Weyl4D H M_jet d3W) = d3W / 35-component 4th-order jet / 20-component 3rd-order jet / 20-component algebraic Riemann-Weyl / off-diagonal shear Bianchi channel cancellation / on-shell stress-energy conservation bridge, curved 4D fifteen-factor Yosida / 56-component 5th-order jet & 3rd-order Weyl reconstruction / Euler distinct-partition / Kloosterman three-channel cocycle Capstone / ConditionalEinstein / spectral rigidity / unified forcing bridge, and Twenty-Seven-Checkpoint Complete Tier-One TOE Master Synthesis. Specifically, on 0<epsilon,h!=0,abs(h)<=pi*epsilon/3 and for all real m,g,k,s,t: (1) on the full wide strip abs(h)<=pi*epsilon/3, for every x_res in Dom(S(t)), v_res in SV(t), and f in commonOperatorDomain = Dom(T) cap Dom(K) cap Dom(P) cap Dom(K^(1/2)), staticLift t (formLift (SD t) <f, hfS>) = staticDomainFormLift <f, hfT>, potentialLift t (formLift (SD t) <f, hfS>) = potentialDomainFormLift <f, hfP>, <SB t (residualFormAction J_{n+1}(formLift (SD t) x_res)), SB t v_res> -> <S(t) x_res, SJ t v_res>, T <J_{n+1} f, ...> + e^{2t} L_{n+1}^{-h/2}(P f) -> S(t) f, J_{n+1}(T f) + e^{2t} J_{n+1}(P f) -> S(t) f, T <J_{n+1} f, ...> + e^{2t}(K <J_{n+1} f, ...> + L_{n+1}^{-h/2}(P f)) -> H(t) f, and J_{n+1}(T f) + e^{2t}(J_{n+1}(K f) + J_{n+1}(P f)) -> H(t) f with zero quarter-strip hbn or hshift hypotheses, while fifteen-parameter (a..o_param) and thirty-parameter ((a,J1),...,(o_param,J15)) potential-resolvent and identity-Yosida tier differences satisfy exact 15-step cyclic pentadecagon cocycles, Dom(P^(r+2))/Dom(P^r) regularity, and fourteen-hop Cauchy rate bounds, and across all 5 operators (T,P,G,S(t),H(t)) at (a..p_param), higher-power resolvent and identity differences satisfy exact 16-step hexadecagon cocycles and Dom(A^(r+2)) regularity; (2) for all real m,g,k,t,s in R and a,b>0, both YS(t,a) and YH(t,a) satisfy unconditional Pythagorean energy-split bounds ||YS(t,a)f||^2 + a^2 ||RS(t,a)f||^2 <= ||f||^2 and ||YH(t,a)f||^2 + a^2 ||RH(t,a)f||^2 <= ||f||^2, contraction bounds ||YS(t,a)|| <= 1 and ||YH(t,a)|| <= 1, and uniform-in-(a,b) two-time two-factor composition Lipschitz continuity ||YS(s,a)(YS(s,b)f) - YS(t,a)(YS(t,b)f)|| <= 2 |e^{2t} - e^{2s}| e^{-(t+s)} ||f||, ||(YS(s,a)).comp (YS(s,b)) - (YS(t,a)).comp (YS(t,b))|| <= 2 |e^{2t} - e^{2s}| e^{-(t+s)}, ||YH(s,a)(YH(s,b)f) - YH(t,a)(YH(t,b)f)|| <= 4 |e^{2t} - e^{2s}| e^{-(t+s)} ||f||, and ||(YH(s,a)).comp (YH(s,b)) - (YH(t,a)).comp (YH(t,b))|| <= 4 |e^{2t} - e^{2s}| e^{-(t+s)}, while on a 13x13 grid (s1..s13)x(t1..t13), the 12x12 sum of 144 elementary mixed initial-and-final higher-power resolvent and identity plaquettes satisfies exact 2D Stokes / Green boundary cancellation to the outer plaquette (s1,s13; t1,t13) canceling 121 interior vertices and 264 interior edges, 13-initial and 13-final tridecagon cocycles, 8-domain regularity, and equal-outer-final-time Dom(H(t)^(r+2)) + 10-domain regularity; (3) across all 5 Hamiltonians A in {T,P,G,S(t),H(t)}, fifteen-factor multi-power (r,s,q,p,l,u,v_pow,w_pow,z_pow,y_pow,x_pow,d_pow,c_pow,b_pow,a_pow) and fifteen-parameter (a,b,d,e,c,f_param,g_param,h_param,i_param,j_param,k_param,l_param,m_param,n_param,o_param) Yosida compositions preserve Dom(A^n), commute with A^n, contract kthPowerGraphNormSq A n, and satisfy ((r/a + s/b + q/d + p/e + l/c + u/f_param + v_pow/g_param + w_pow/h_param + z_pow/i_param + y_pow/j_param + x_pow/k_param + d_pow/l_param + c_pow/m_param + b_pow/n_param + a_pow/o_param)^2) * kthPowerGraphNormSq A (n+1) x defect bounds; (4) for all q in [0,1/2) and N in N, the Euler distinct-parts (fermionic) partition partial product D_N(q) = prod_{k=0}^{N-1} (1 + q^{k+1}) satisfies P_N(q) D_N(q) = P_N(q^2), D_N(q) = P_N(q^2) Q_N(q), 1 + sum_{k=0}^{N-1} q^{k+1} <= D_N(q) <= Q_N(q) <= (1 - q)/(1 - 2q), and Q_N(q) - D_N(q) = (1 - P_N(q^2)) Q_N(q) >= 0, while for all 2 <= c_1 <= c_2 <= c_3 the Rademacher-Kloosterman subleading channel exponents satisfy (S_BH/c_1 - S_BH/c_2) + (S_BH/c_2 - S_BH/c_3) = S_BH/c_1 - S_BH/c_3 = ((c_3 - c_1)/(c_1 c_3)) S_BH >= 0; (5) for any 4D Hessian H, any 56-component symmetric 5th-order conformal jet M_jet (choose(4+5-1,5)=56), and any Lorentzian trace-free 3rd-order differential Weyl jet d3W (56 components, matching choose(8,3)=choose(8,5)=56 and 56+56=112), fullD3RiemannFromFifthJetAndD3Weyl4D H M_jet d3W has Lorentzian Ricci contraction fullD3Ricci4D H M_jet and scalar contraction fullD3Scalar4D H M_jet, and both M_jet and d3W are reconstructed simultaneously and exactly via reconstructFifthJetFromD3Riemann4D(fullD3RiemannFromFifthJetAndD3Weyl4D H M_jet d3W) = M_jet and reconstructD3WeylFromD3Riemann4D H (fullD3RiemannFromFifthJetAndD3Weyl4D H M_jet d3W) = d3W, synthesized with 100% (659/659) direct non-Audit module coverage. Unconditional fixed-N strong-operator invariance J_N(DomP) subseteq DomP without the wide-strip half-shift variational pairing hypothesis (beyond the proved four-domain invariance, two-sided potential-pairing domination, Dom(G) radial-Yosida contraction/rate, Dom(H(t))/Dom(S(t)) radial-Yosida quadratic lower bound and rate, unconditional Dom(T) invariance/commutator/core, unconditional Dom(G) = Dom(K) cap Dom(P) seven-operator resolvent invariance, wide-strip half-shift variational Dom(P)/Dom(G) regularization, and unconditional wide-strip potential-form, growing-form, residual-form, and full-Hamiltonian pairing & operator output convergence), single-resolvent R_{H(t)}(a)f in DomP for k<=0 without iteration (beyond the proved 14-domain regularity, unconditional R_G(a)f in DomP, 5-way DomP <-> DomG <-> DomT equivalence, shifted-source residual-resolvent criterion, static-residual second resolvent identity, unconditional strong/operator-norm two-time residual & Hamiltonian resolvent and single/two-factor Yosida generator continuity, and positive-vacuum k>0 domain stability), trajectory-wide unbounded-momentum derivatives beyond the energy-controlled H(t)-domain quantum-velocity commutator bound, general non-conformal dynamical nonlinear 4D Einstein-Weyl PDE evolution beyond the 20-component algebraic Riemann-Weyl-Ricci-Hessian, 20-component 3rd-order jet / differential Weyl, 35-component 4th-order jet / 2nd-order Weyl, and 56-component 5th-order jet / 3rd-order Weyl reconstructions and linearized Bianchi/stress-energy conservation, full infinite-volume 4D continuum OS/Wightman QFT beyond the chamber/cluster reduction, first-principles derivation of absolute dimensionful scales, microscopic phase selection, controlled physical limits, and empirical identification remain open; the earlier phase/harmonic identification still requires revision. A physical TOE is not proved. This checkpoint adds93 theorems in15 modules, preserves3889 parent source/script hashes and adds17 for3906 total; exact root extends from9431 to9446 lines. All12 parent analytic artifacts and23 numerical files remain unchanged. Standard axioms only.'
PARENT = 'data/twenty_six_checkpoint_complete_tier_one_synthesis_audit.json'
PARENT_SHA = 'eae0749fc3c1817df12c58edd3ec8fe4946bcfed5bdcd1f99ac48af381f6f765'
REPORT = 'data/twenty_seven_checkpoint_complete_tier_one_synthesis_audit.json'
SCRIPTS = ['scripts/twenty_seven_checkpoint_complete_tier_one_synthesis_audit.py',
           'scripts/verify_twenty_seven_checkpoint_complete_tier_one_synthesis.py']
ALLOWED = {'propext','Classical.choice','Quot.sound'}
BAD = r': error|: warning|sorryAx|PANIC'


def sha(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()


def declarations(name, source):
    prefix='UnifiedTheory.Audit.'+name+'.'
    names={prefix+n for n in re.findall(r'^theorem (\S+)',source,re.M)}
    printed={prefix+n for n in re.findall(r'^#print axioms (\S+)',source,re.M)}
    assert names==printed and len(names)==EXPECTED[name],(name,len(names),len(printed),EXPECTED[name])
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
    parser.add_argument('--baseline-overlay',required=True,type=Path)
    args=parser.parse_args()
    root=Path(__file__).resolve().parents[1]
    overlay=args.overlay.resolve(); baseline=args.baseline_overlay.resolve()
    assert overlay.is_dir() and baseline.is_dir() and overlay!=baseline
    env=os.environ.copy()
    env['LEAN_PATH']=str(overlay)+os.pathsep+str(baseline)+os.pathsep+env['LEAN_PATH']
    logs=overlay/'twenty-seven-checkpoint-complete-tier-one-synthesis-audit'
    logs.mkdir(exist_ok=False)
    assert sha(root/PARENT)==PARENT_SHA
    parent=json.loads((root/PARENT).read_text())
    hashes=dict(parent['source_sha256'])
    assert len(hashes)==3889 and all(sha(root/p)==h for p,h in hashes.items())
    additions=['UnifiedTheory/Audit/'+n+'.lean' for n in EXPECTED]+SCRIPTS
    assert not set(additions)&set(hashes)
    hashes.update({p:sha(root/p) for p in additions})
    analytic={k:v for k,v in parent.items() if k.startswith('analytic_')}
    assert len(analytic)==12 and not set(analytic)&set(EXTRA_ANALYTIC)
    analytic.update(EXTRA_ANALYTIC)
    assert all(sha(root/v['path'])==v['sha256'] for v in analytic.values())
    evidence=parent['numerical_evidence']
    numerical=[v for v in evidence.values() if isinstance(v,dict) and 'path' in v]
    assert len(numerical)==23 and all(sha(root/v['path'])==v['sha256'] for v in numerical)
    text=(root/'UnifiedTheory.lean').read_text()
    suffix=''.join('import UnifiedTheory.Audit.'+n+'\n' for n in EXPECTED)
    assert text.endswith(suffix)
    assert hashlib.sha256(text[:-len(suffix)].encode()).hexdigest()==parent['root_check']['source_sha256']
    assert len(text.splitlines())==9431+len(EXPECTED)
    root_hash=sha(root/'UnifiedTheory.lean')
    checks=[]; done=set()
    for name in EXPECTED:
        source='UnifiedTheory/Audit/'+name+'.lean'
        body=(root/source).read_text()
        needed=set(re.findall(r'^import UnifiedTheory\.Audit\.(\S+)',body,re.M))&set(EXPECTED)
        assert needed<=done,(name,needed-done)
        output=overlay/'UnifiedTheory/Audit'/(name+'.olean')
        assert not output.exists() and not output.is_symlink()
        output.parent.mkdir(parents=True,exist_ok=True)
        command=['lean','-j1','-o',str(output),source]
        result=subprocess.run(command,cwd=root,env=env,text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
        log=logs/(name+'.log'); log.write_text(result.stdout)
        assert result.returncode==0,str(log)
        audits=dependencies(result.stdout)
        assert set(audits)==declarations(name,body)
        assert output.is_file() and not output.is_symlink()
        checks.append(dict(source=source,command=command,exit_code=0,log_sha256=sha(log),audited_declarations=audits))
        done.add(name)
        print(name+': clean; '+str(len(audits))+' theorem dependency lists',flush=True)
    result=subprocess.run(['lean','-j1','UnifiedTheory.lean'],cwd=root,env=env,text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
    log=logs/'root-import.log'; log.write_text(result.stdout)
    assert result.returncode==0 and not result.stdout.strip(),str(log)
    assert sha(root/'UnifiedTheory.lean')==root_hash and sha(root/PARENT)==PARENT_SHA
    assert all(sha(root/p)==h for p,h in hashes.items())
    assert all(sha(root/v['path'])==v['sha256'] for v in [*analytic.values(),*numerical])
    assert all(not (root/'.lake/build/lib/lean/UnifiedTheory/Audit'/(n+'.olean')).exists() for n in EXPECTED)
    report=dict(**analytic,modules=checks,new_lean_theorem_count=sum(EXPECTED.values()),
        source_sha256=hashes,numerical_evidence=evidence,previous_report=dict(path=PARENT,sha256=PARENT_SHA),
        root_check=dict(command=['lean','-j1','UnifiedTheory.lean'],exit_code=0,empty_log=True,
            source_sha256=root_hash,log_sha256=sha(log),appended_imports=list(EXPECTED)),
        lean_toolchain=(root/'lean-toolchain').read_text().strip(),scope=SCOPE)
    target=root/REPORT
    assert not target.exists()
    target.write_text(json.dumps(report,indent=2)+'\n')
    print('Root passed; '+str(sum(EXPECTED.values()))+' theorem audits; '+str(len(hashes))+' source/script hashes.',flush=True)
    print(target,flush=True)


if __name__=='__main__':
    main()
