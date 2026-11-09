#!/usr/bin/env python3
"""Independently verify the nineteen-checkpoint-complete-tier-one-synthesis audit and preserved evidence."""
import argparse
import hashlib
import json
from pathlib import Path
import re

EXPECTED = {
    'KFCausalClockFloorHigherPowerPotentialResolventYosidaSevenParameterHeptagon': 10,
    'KFCausalClockFloorFiveOperatorEightParameterHigherPowerOctagonCocycleAndYosida': 7,
    'KFCausalClockFloorSevenParameterHeptagonEightParameterOctagonDirectGrowingFormInvarianceBridge': 6,
    'KFCausalClockFloorFiveByFiveMixedInitialFinalHigherPowerResolventPlaquetteGrid': 7,
    'KFCausalClockFloorFiveByFivePlaquetteSingleResolventFourteenDomainWightmanOSContinuumBridge': 6,
    'KFCausalClockFloorFiveByFivePlaquettePolymerBorgsImbrieKoteckyPreissWeingartenVolterraBridge': 6,
    'KFCausalClockFloorArbitraryOrderSevenFactorMultiPowerYosidaComposition': 9,
    'KFCausalClockFloorSevenFactorYosidaVelocityCommutatorUmegakiAndoLiebGoldenThompsonBridge': 5,
    'KFCausalClockFloorSevenFactorYosidaStinespringPetzTraceDistanceQuantumSteinAEPBridge': 5,
    'KFCausalArbitrarySourceMultiChannelCenteredProjectorCovarianceAndCauchySchwarzBound': 6,
    'KFCausalMultiChannelProjectorCovarianceSMGUTCKMPMNSBaryonProtonDecayDarkMatterBridge': 5,
    'KFCausalMultiChannelProjectorCovarianceBellCHSHTsirelsonPhaseFaithfulnessNoGoBridge': 5,
    'KFCausalCurved4DFiveByFivePlaquetteLohmillerSlotineConformalLaplacianBianchiEinsteinBridge': 5,
    'KFCausalCurved4DSevenFactorYosidaCapstoneConditionalEinsteinSpectralRigidityUnifiedForcingBridge': 5,
    'KFCausalTOENineteenCheckpointCompleteTierOneMasterSynthesis': 6,
}
EXTRA_ANALYTIC = {}
SCOPE = 'Direct fixed-N four-domain (Dom(K), Dom(K_root), Dom(T_pot), Dom(T_grow)) invariance of J_N on Dom(P) without R_P(a) together with two-sided potential-pairing domination 0 <= Re <P x, J_N x> <= Re <P x, x> and radial-resolvent accretivity 0 <= Re <P x, M_N x> on Dom(P), seven-parameter (a,b,c,d,e,f_param,g_param) higher-power potential-resolvent radial-Yosida cyclic heptagon cocycles and fourteen-parameter ((a,J1),(b,J2),(c,J3),(d,J4),(e,J5),(f_param,J6),(g_param,J7)) Cauchy rate bounds, five-operator (T,P,G,S,H) eight-parameter (a,b,c,d,e,f_param,g_param,h_param) higher-power cross-resolvent octagon cocycles and common-domain Yosida cross-rate bounds, seven-parameter heptagon / eight-parameter octagon / direct growing-form invariance QQG / inflaton / slow-roll / dimension / gauge / Volterra bridge, five-by-five (s1,s2,s3,s4,s5)x(t1,t2,t3,t4,t5) (4x4=16 elementary plaquettes) mixed initial-and-final higher-power resolvent and identity plaquette grids with exact 2D Stokes / Green boundary cancellation across all 8 time-independent and 10 equal-outer-final-time domains, unconditional single-resolvent 14-domain regularity R_{H(t)}(a) f (with three-channel energy split), unconditional single growing-resolvent 3-domain regularity R_G(a) f in Dom(G) cap Dom(K) cap Dom(P), and unconditional 5-way operator-domain equivalence Dom(P) <-> Dom(G) <-> Dom(T) <-> commonOperatorDomain without iteration for all real m,g,k,t,s in R (including k<=0) and Wightman / OS / Clay continuum bridge, five-by-five plaquette Polymer / Borgs-Imbrie / Kotecky-Preiss / Weingarten / Volterra SO(10) bridge, arbitrary-order seven-factor multi-power (r,s,q,p,l,u,v_pow) and seven-parameter (a,b,d,e,c,f_param,g_param) Yosida composition defect calculus across all 5 Hamiltonians, seven-factor Yosida quantum-velocity commutator error / Umegaki / Ando / Lieb / Golden-Thompson bridge, seven-factor Yosida Stinespring / Petz / trace-distance / Quantum Stein / AEP bridge, finite Q-channel normalized spectral covariance functional, exact QxQ double-sum Lagrange pairwise co-spread identity, sum/difference variance polarization, bilateral shift invariance, and Q-channel arithmetic-mean / Popoviciu covariance envelope bounds, multi-channel projector covariance SM / GUT / CKM / PMNS / baryon / proton decay / dark matter bridge, multi-channel projector covariance Bell / CHSH / Tsirelson / phase faithfulness / no-go bridge, curved 4D five-by-five plaquette / multi-channel covariance Lohmiller-Slotine / conformal Laplacian / Bianchi / Einstein bridge, curved 4D seven-factor Yosida Capstone / ConditionalEinstein / spectral rigidity / unified forcing bridge, and Nineteen-Checkpoint Complete Tier-One TOE Master Synthesis. Specifically, on 0<epsilon,h!=0,abs(h)<=pi*epsilon/3 and for all real m,g,k,s,t: (1) directly at fixed N>0 without R_P(a), every x in Dom(P) satisfies x in Dom(K_root) cap Dom(T_pot) cap Dom(T_grow), J_N x in Dom(K) cap Dom(K_root) cap Dom(T_pot) cap Dom(T_grow), 0 <= Re <P x, J_N x> <= Re <P x, x>, and 0 <= Re <P x, M_N x>, while for every m,r,j>=0 with j<=m and x in Dom(P^(m+1)), seven-parameter (a,b,c,d,e,f_param,g_param) and fourteen-parameter ((a,J1),...,(g_param,J7)) potential-resolvent and identity-Yosida tier differences satisfy exact 7-step cyclic heptagon cocycles, Dom(P^(r+2))/Dom(P^r) regularity, and six-hop Cauchy rate bounds, and across any EightParameterFiveOperatorSystem (T,P,G,S(t),H(t)) at (a,b,c,d,e,f_param,g_param,h_param), cross-resolvent and cross-Yosida differences satisfy exact 8-step octagon cocycles and seven-hop bounds; (2) for any f in Hilbert, a>0, and any real m,g,k,t,s in R (including k<=0 without iteration), the single resolvent R_{H(t)}(a) f belongs unconditionally to all 10 base domains with three-channel form-energy split, R_G(a) f belongs unconditionally to Dom(G) cap Dom(K) cap Dom(P) with three-term energy bound, and for any x in Hilbert the 5 operator domains Dom(P), Dom(G), Dom(T), Dom(K) cap Dom(T), and commonOperatorDomain are unconditionally equivalent (upgrading 10-domain membership to 14-domain membership), while on a 5x5 grid (s1..s5)x(t1..t5), the 4x4 sum of 16 elementary mixed initial-and-final higher-power resolvent and identity plaquettes satisfies exact 2D Stokes / Green boundary cancellation to the outer plaquette (s1,s5; t1,t5) canceling 9 interior vertices and 24 interior edges, 5-initial and 5-final pentagon cocycles, 8-domain regularity with ((a1^-1)^(r+2)+(g1^-1)^(r+2))||f1||+((a5^-1)^(r+2)+(g5^-1)^(r+2))||f5|| and 2||f1||+2||f5|| bounds, and equal-outer-final-time Dom(H(t)^(r+2)) + 10-domain regularity; (3) across all 5 Hamiltonians A in {T,P,G,S(t),H(t)}, seven-factor multi-power (r,s,q,p,l,u,v_pow) and seven-parameter (a,b,d,e,c,f_param,g_param) Yosida compositions preserve Dom(A^n), commute with A^n, contract kthPowerGraphNormSq A n, and satisfy ((r/a + s/b + q/d + p/e + l/c + u/f_param + v_pow/g_param)^2) * kthPowerGraphNormSq A (n+1) x defect bounds, paired on Dom(H(t)) with the exact quantum-velocity commutator pairing <H(t) x, D x> = <h_out x, R(h_out x)> and energy-controlled classical-velocity error |(-2/h) Im <H(t) x, D x> - v_cl(x)| <= (20|h|/epsilon^2) Re <H(t) x, x>; (4) for any Q-channel operator family {P_q}_{q in Fin Q} with weight profiles w1 in [w1_min,w1_max] and w2 in [w2_min,w2_max], the homogeneous degree-4 spectral covariance functional E_Q(x)*M_{1,2}(x)-M1(w1,x)*M1(w2,x) satisfies 2*Cov_Q(w1,w2,x) = sum_{q1,q2} (w1(q1)-w1(q2))(w2(q1)-w2(q2)) E(P_{q1} x) E(P_{q2} x), is symmetric, reduces on the diagonal to Var_Q(w,x), satisfies Var_Q(w1+-w2,x) = Var_Q(w1,x) +- 2*Cov_Q(w1,w2,x) + Var_Q(w2,x), is invariant under independent shifts (w1+c1,w2+c2), and obeys 2*|Cov_Q(w1,w2,x)| <= Var_Q(w1,x)+Var_Q(w2,x) <= (((w1_max-w1_min)/2)^2+((w2_max-w2_min)/2)^2) E_Q(x)^2; (5) all five fronts are synthesized with the curved 4D Bianchi/Einstein/Lohmiller-Slotine/Capstone/Spectral-Rigidity hierarchy and 100% (659/659) direct non-Audit module coverage. Direct fixed-N strong-operator invariance J_N(DomP) subseteq DomP without R_P(a) (beyond the proved four-domain Dom(K) cap Dom(K_root) cap Dom(T_pot) cap Dom(T_grow) invariance and two-sided potential-pairing domination), single-resolvent R_{H(t)}(a)f in DomP for k<=0 without iteration (beyond the proved 14-domain regularity, unconditional R_G(a)f in DomP, and 5-way DomP <-> DomG <-> DomT equivalence), trajectory-wide unbounded-momentum derivatives beyond the energy-controlled H(t)-domain quantum-velocity commutator bound, general non-symmetric dynamical nonlinear 4D Einstein PDE evolution, full infinite-volume 4D continuum OS/Wightman QFT beyond the chamber/cluster reduction, first-principles derivation of absolute dimensionful scales, microscopic phase selection, controlled physical limits, and empirical identification remain open; the earlier phase/harmonic identification still requires revision. A physical TOE is not proved. This checkpoint adds93 theorems in15 modules, preserves3753 parent source/script hashes and adds17 for3770 total; exact root extends from9311 to9326 lines. All12 parent analytic artifacts and23 numerical files remain unchanged. Standard axioms only.'
PARENT = 'data/eighteen_checkpoint_complete_tier_one_synthesis_audit.json'
PARENT_SHA = '2555199582a3f1b1f3af30e5e64359d9dbe8fe639b100a6d0cc6763e5bfe23a4'
REPORT = 'data/nineteen_checkpoint_complete_tier_one_synthesis_audit.json'
SCRIPTS = ['scripts/nineteen_checkpoint_complete_tier_one_synthesis_audit.py',
           'scripts/verify_nineteen_checkpoint_complete_tier_one_synthesis.py']
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
    assert len(old)==3753 and len(hashes)==3753+len(EXPECTED)+2
    assert all(hashes[p]==h for p,h in old.items())
    assert all(sha(root/p)==h for p,h in hashes.items())
    additions={'UnifiedTheory/Audit/'+n+'.lean' for n in EXPECTED}|set(SCRIPTS)
    assert set(hashes)-set(old)==additions
    assert [Path(x['source']).stem for x in report['modules']]==list(EXPECTED)
    logs=overlay/'nineteen-checkpoint-complete-tier-one-synthesis-audit'
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
    assert text.endswith(suffix) and len(text.splitlines())==9311+len(EXPECTED)
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
