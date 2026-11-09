#!/usr/bin/env python3
"""Independently verify the twenty-one-checkpoint-complete-tier-one-synthesis audit and preserved evidence."""
import argparse
import hashlib
import json
from pathlib import Path
import re

EXPECTED = {
    'KFCausalClockFloorHigherPowerPotentialResolventYosidaNineParameterNonagon': 10,
    'KFCausalClockFloorFiveOperatorTenParameterHigherPowerDecagonCocycleAndYosida': 7,
    'KFCausalClockFloorNineParameterNonagonTenParameterDecagonDirectHamiltonianYosidaRateBridge': 6,
    'KFCausalClockFloorSevenBySevenMixedInitialFinalHigherPowerResolventPlaquetteGrid': 7,
    'KFCausalClockFloorSevenBySevenPlaquetteUnconditionalStaticGraphCoreTwoTimeEvolutionWightmanOSBridge': 6,
    'KFCausalClockFloorSevenBySevenPlaquettePolymerBorgsImbrieKoteckyPreissWeingartenVolterraBridge': 6,
    'KFCausalClockFloorArbitraryOrderNineFactorMultiPowerYosidaComposition': 9,
    'KFCausalClockFloorNineFactorYosidaVelocityCommutatorUmegakiAndoLiebGoldenThompsonBridge': 5,
    'KFCausalClockFloorNineFactorYosidaStinespringPetzTraceDistanceQuantumSteinAEPBridge': 5,
    'KFCausalArbitrarySourceMultiChannelThreeProfileSylvesterGramDeterminantAndHadamardInequality': 6,
    'KFCausalMultiChannelThreeByThreeGramDeterminantSMGUTCKMPMNSBaryonProtonDecayDarkMatterBridge': 5,
    'KFCausalMultiChannelThreeByThreeGramDeterminantBellCHSHTsirelsonPhaseFaithfulnessNoGoBridge': 5,
    'KFCausalCurved4DSevenBySevenPlaquetteLohmillerSlotineConformalLaplacianBianchiEinsteinBridge': 5,
    'KFCausalCurved4DNineFactorYosidaCapstoneConditionalEinsteinSpectralRigidityUnifiedForcingBridge': 5,
    'KFCausalTOETwentyOneCheckpointCompleteTierOneMasterSynthesis': 6,
}
EXTRA_ANALYTIC = {}
SCOPE = 'Direct fixed-N full-Hamiltonian Dom(H(t)) and residual Dom(S(t)) radial-Yosida quadratic lower bound Re <H(t) x, M_N x> >= e^{2t}||M_N x||^2 - (h^2/epsilon^2)||x||^2, explicit M_N norm bound ||M_N x|| <= ||H(t) x||/e^{2t} + (|h|/epsilon ||x||)/e^t, regularized pairing inequality Re <H(t) x, J_N x> + N^-1 e^{2t}||M_N x||^2 <= Re <H(t) x, x> + N^-1 (h^2/epsilon^2)||x||^2, O(N^-1) regularizer rate ||x - J_N x|| <= N^-1 (||H(t) x||/e^{2t} + (|h|/epsilon ||x||)/e^t), and residual pairing lower bound Re <S(t) y, M_N y> >= -(h^2/epsilon^2)||y||^2 without R_{H(t)}(a) or R_{S(t)}(a), nine-parameter (a,b,c,d,e,f_param,g_param,h_param,i_param) higher-power potential-resolvent radial-Yosida cyclic nonagon cocycles and eighteen-parameter ((a,J1),(b,J2),(c,J3),(d,J4),(e,J5),(f_param,J6),(g_param,J7),(h_param,J8),(i_param,J9)) Cauchy rate bounds, five-operator (T,P,G,S,H) ten-parameter (a,b,c,d,e,f_param,g_param,h_param,i_param,j_param) higher-power cross-resolvent decagon cocycles and common-domain Yosida cross-rate bounds, nine-parameter nonagon / ten-parameter decagon / direct Hamiltonian Yosida rate QQG / inflaton / slow-roll / dimension / gauge / Volterra bridge, seven-by-seven (s1,s2,s3,s4,s5,s6,s7)x(t1,t2,t3,t4,t5,t6,t7) (6x6=36 elementary plaquettes) mixed initial-and-final higher-power resolvent and identity plaquette grids with exact 2D Stokes / Green boundary cancellation across all 8 time-independent and 10 equal-outer-final-time domains, unconditional static graph core (commonOperatorClockStaticGraph).topologicalClosure = (T).graph and exact two-time evolution decomposition S(t)x - S(s)x = (e^{2t} - e^{2s})Px and H(t)x - H(s)x = (e^{2t} - e^{2s})(Kx + Px) for all real m,g,k,t,s in R (including k<=0) and Wightman / OS / Clay continuum bridge, seven-by-seven plaquette Polymer / Borgs-Imbrie / Kotecky-Preiss / Weingarten / Volterra SO(10) bridge, arbitrary-order nine-factor multi-power (r,s,q,p,l,u,v_pow,w_pow,z_pow) and nine-parameter (a,b,d,e,c,f_param,g_param,h_param,i_param) Yosida composition defect calculus across all 5 Hamiltonians, nine-factor Yosida quantum-velocity commutator error / Umegaki / Ando / Lieb / Golden-Thompson bridge, nine-factor Yosida Stinespring / Petz / trace-distance / Quantum Stein / AEP bridge, finite Q-channel three-profile 3x3 Sylvester-Jacobi spectral covariance Gram determinant Det3_Q(w1,w2,w3,x), orthogonal residual profile w_{1 perp 2}(q) = Var_Q(w2,x)w1(q) - Cov_Q(w1,w2,x)w2(q), partial covariance minor PartialCov_Q(w1,w3|w2,x) = Var_Q(w2,x)Cov_Q(w1,w3,x) - Cov_Q(w1,w2,x)Cov_Q(w2,w3,x), Sylvester factorization Det_Q(w1,w2,x)*Det_Q(w3,w2,x) - PartialCov_Q(w1,w3|w2,x)^2 = Var_Q(w2,x)*Det3_Q(w1,w2,w3,x), partial Cauchy-Schwarz inequality PartialCov_Q(w1,w3|w2,x)^2 <= Det_Q(w1,w2,x)*Det_Q(w3,w2,x), Hadamard 3x3 determinant inequality 0 <= Det3_Q(w1,w2,w3,x) <= Var_Q(w1,x)*Det_Q(w2,w3,x) <= Var_Q(w1,x)*Var_Q(w2,x)*Var_Q(w3,x), trilateral shift invariance, and sharp 3x3 Popoviciu bounds, multi-channel 3x3 Gram determinant SM / GUT / CKM / PMNS / baryon / proton decay / dark matter bridge, multi-channel 3x3 Gram determinant Bell / CHSH / Tsirelson / phase faithfulness / no-go bridge, curved 4D seven-by-seven plaquette / 3x3 Gram determinant Lohmiller-Slotine / conformal Laplacian / Bianchi / Einstein bridge, curved 4D nine-factor Yosida Capstone / ConditionalEinstein / spectral rigidity / unified forcing bridge, and Twenty-One-Checkpoint Complete Tier-One TOE Master Synthesis. Specifically, on 0<epsilon,h!=0,abs(h)<=pi*epsilon/3 and for all real m,g,k,s,t: (1) directly at fixed N>0 without R_{H(t)}(a) or R_{S(t)}(a), every x in Dom(H(t)) and y in Dom(S(t)) satisfy x in Dom(K) cap Dom(S(t)), e^{2t}||M_N x||^2 - (h^2/epsilon^2)||x||^2 <= Re <H(t) x, M_N x>, -(h^2/epsilon^2)||x||^2 <= Re <H(t) x, M_N x>, ||M_N x|| <= ||H(t) x||/e^{2t} + (|h|/epsilon ||x||)/e^t, Re <H(t) x, J_N x> + N^-1 e^{2t}||M_N x||^2 <= Re <H(t) x, x> + N^-1 (h^2/epsilon^2)||x||^2, ||x - J_N x|| <= N^-1 (||H(t) x||/e^{2t} + (|h|/epsilon ||x||)/e^t), -(h^2/epsilon^2)||y||^2 <= Re <S(t) y, M_N y>, and Re <S(t) y, J_N y> <= Re <S(t) y, y> + N^-1 (h^2/epsilon^2)||y||^2, while for every m,r,j>=0 with j<=m and x in Dom(P^(m+1)), nine-parameter (a..i_param) and eighteen-parameter ((a,J1),...,(i_param,J9)) potential-resolvent and identity-Yosida tier differences satisfy exact 9-step cyclic nonagon cocycles, Dom(P^(r+2))/Dom(P^r) regularity, and eight-hop Cauchy rate bounds, and across any TenParameterFiveOperatorSystem (T,P,G,S(t),H(t)) at (a..j_param), cross-resolvent and cross-Yosida differences satisfy exact 10-step decagon cocycles and nine-hop bounds; (2) for any real m,g,k,t,s in R (including k<=0 without iteration), the common operator domain is an operator core for the static clock Hamiltonian T via (commonOperatorClockStaticGraph).topologicalClosure = (T).graph and every x in commonOperatorDomain satisfies the exact two-time evolution decomposition S(t)x - S(s)x = (e^{2t} - e^{2s})Px and H(t)x - H(s)x = (e^{2t} - e^{2s})(Kx + Px) along with the 5-way single-resolvent criterion R_{H(t)}(a)f in commonOperatorDomain <-> R_{S(t)}(a)(f - e^{2t} K R_{H(t)}(a)f) in Dom(P), while on a 7x7 grid (s1..s7)x(t1..t7), the 6x6 sum of 36 elementary mixed initial-and-final higher-power resolvent and identity plaquettes satisfies exact 2D Stokes / Green boundary cancellation to the outer plaquette (s1,s7; t1,t7) canceling 25 interior vertices and 60 interior edges, 7-initial and 7-final heptagon cocycles, 8-domain regularity with ((a1^-1)^(r+2)+(g1^-1)^(r+2))||f1||+((a7^-1)^(r+2)+(g7^-1)^(r+2))||f7|| and 2||f1||+2||f7|| bounds, and equal-outer-final-time Dom(H(t)^(r+2)) + 10-domain regularity; (3) across all 5 Hamiltonians A in {T,P,G,S(t),H(t)}, nine-factor multi-power (r,s,q,p,l,u,v_pow,w_pow,z_pow) and nine-parameter (a,b,d,e,c,f_param,g_param,h_param,i_param) Yosida compositions preserve Dom(A^n), commute with A^n, contract kthPowerGraphNormSq A n, and satisfy ((r/a + s/b + q/d + p/e + l/c + u/f_param + v_pow/g_param + w_pow/h_param + z_pow/i_param)^2) * kthPowerGraphNormSq A (n+1) x defect bounds, paired on Dom(H(t)) with the exact quantum-velocity commutator pairing <H(t) x, D x> = <h_out x, R(h_out x)> and energy-controlled classical-velocity error |(-2/h) Im <H(t) x, D x> - v_cl(x)| <= (20|h|/epsilon^2) Re <H(t) x, x>; (4) for any Q-channel operator family {P_q}_{q in Fin Q} with weight profiles w1 in [w1_min,w1_max], w2 in [w2_min,w2_max], w3 in [w3_min,w3_max], the 3x3 Sylvester-Jacobi spectral covariance Gram determinant Det3_Q(w1,w2,w3,x) and partial covariance minor PartialCov_Q(w1,w3|w2,x) satisfy exact orthogonal residual projection Cov_Q(w_{1 perp 2},w2,x)=0, Sylvester factorization Det_Q(w1,w2,x)*Det_Q(w3,w2,x) - PartialCov_Q(w1,w3|w2,x)^2 = Var_Q(w2,x)*Det3_Q(w1,w2,w3,x), partial Cauchy-Schwarz PartialCov_Q(w1,w3|w2,x)^2 <= Det_Q(w1,w2,x)*Det_Q(w3,w2,x), Hadamard 3x3 determinant inequality 0 <= Det3_Q(w1,w2,w3,x) <= Var_Q(w1,x)*Det_Q(w2,w3,x) <= Var_Q(w1,x)*Var_Q(w2,x)*Var_Q(w3,x), trilateral shift invariance, and the sharp 3x3 Popoviciu bound Det3_Q(w1,w2,w3,x) <= ((w1_max-w1_min)/2)^2 ((w2_max-w2_min)/2)^2 ((w3_max-w3_min)/2)^2 E_Q(x)^6; (5) all five fronts are synthesized with the curved 4D Bianchi/Einstein/Lohmiller-Slotine/Capstone/Spectral-Rigidity hierarchy and 100% (659/659) direct non-Audit module coverage. Direct fixed-N strong-operator invariance J_N(DomP) subseteq DomP without R_P(a) (beyond the proved four-domain invariance, two-sided potential-pairing domination, Dom(G) radial-Yosida contraction/rate, and Dom(H(t))/Dom(S(t)) radial-Yosida quadratic lower bound and rate), single-resolvent R_{H(t)}(a)f in DomP for k<=0 without iteration (beyond the proved 14-domain regularity, unconditional R_G(a)f in DomP, 5-way DomP <-> DomG <-> DomT equivalence, shifted-source residual-resolvent criterion, and unconditional static graph core), trajectory-wide unbounded-momentum derivatives beyond the energy-controlled H(t)-domain quantum-velocity commutator bound, general non-symmetric dynamical nonlinear 4D Einstein PDE evolution, full infinite-volume 4D continuum OS/Wightman QFT beyond the chamber/cluster reduction, first-principles derivation of absolute dimensionful scales, microscopic phase selection, controlled physical limits, and empirical identification remain open; the earlier phase/harmonic identification still requires revision. A physical TOE is not proved. This checkpoint adds93 theorems in15 modules, preserves3787 parent source/script hashes and adds17 for3804 total; exact root extends from9341 to9356 lines. All12 parent analytic artifacts and23 numerical files remain unchanged. Standard axioms only.'
PARENT = 'data/twenty_checkpoint_complete_tier_one_synthesis_audit.json'
PARENT_SHA = '6bab0de95361ad48ab524ad656abb656274acdb529057c12e3634ace8af0a37f'
REPORT = 'data/twenty_one_checkpoint_complete_tier_one_synthesis_audit.json'
SCRIPTS = ['scripts/twenty_one_checkpoint_complete_tier_one_synthesis_audit.py',
           'scripts/verify_twenty_one_checkpoint_complete_tier_one_synthesis.py']
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
    assert len(old)==3787 and len(hashes)==3787+len(EXPECTED)+2
    assert all(hashes[p]==h for p,h in old.items())
    assert all(sha(root/p)==h for p,h in hashes.items())
    additions={'UnifiedTheory/Audit/'+n+'.lean' for n in EXPECTED}|set(SCRIPTS)
    assert set(hashes)-set(old)==additions
    assert [Path(x['source']).stem for x in report['modules']]==list(EXPECTED)
    logs=overlay/'twenty-one-checkpoint-complete-tier-one-synthesis-audit'
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
    assert text.endswith(suffix) and len(text.splitlines())==9341+len(EXPECTED)
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
