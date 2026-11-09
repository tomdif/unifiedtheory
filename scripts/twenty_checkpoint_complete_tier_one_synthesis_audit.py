#!/usr/bin/env python3
"""Check direct fixed-N growing-domain radial-Yosida lower bound Re <G x, J_N x> + N^-1 ||M_N x||^2 <= Re <G x, x>, radial-resolvent contraction ||M_N x|| <= ||G x||, and O(N^-1) regularizer rate ||x - J_N x|| <= N^-1 ||G x|| on Dom(G) without R_G(a) or R_P(a), eight-parameter higher-power potential-resolvent radial-Yosida octagon cocycles and sixteen-parameter Cauchy rate bounds, five-operator nine-parameter higher-power nonagon cocycles and common-domain Yosida cross-rate bounds, eight-parameter octagon / nine-parameter nonagon / direct growing-domain Yosida rate QQG / inflaton / slow-roll / dimension / gauge / Volterra bridge, six-by-six (5x5=25 elementary plaquettes) mixed initial-and-final higher-power resolvent plaquette grids and 2D Stokes boundary cancellation, unconditional shifted-source residual-resolvent identity R_{H(t)}(a) f = R_{S(t)}(a)(f - e^{2t} K R_{H(t)}(a) f) and 5-way operator-domain criterion R_{H(t)}(a) f in commonOperatorDomain <-> R_{S(t)}(a)(f - e^{2t} K R_{H(t)}(a) f) in Dom(P) for all real m,g,k,t,s in R and Wightman / OS / Clay continuum bridge, six-by-six plaquette Polymer / Borgs-Imbrie / Kotecky-Preiss / Weingarten / Volterra SO(10) bridge, arbitrary-order eight-factor multi-power (r,s,q,p,l,u,v_pow,w_pow) and eight-parameter (a,b,d,e,c,f_param,g_param,h_param) Yosida composition defect calculus across all 5 Hamiltonians, eight-factor Yosida quantum-velocity commutator error / Umegaki / Ando / Lieb / Golden-Thompson bridge, eight-factor Yosida Stinespring / Petz / trace-distance / Quantum Stein / AEP bridge, finite Q-channel 2x2 spectral covariance Gram determinant Det_Q(w1,w2,x) = Var_Q(w1,x)*Var_Q(w2,x) - Cov_Q(w1,w2,x)^2 >= 0, multiplicative Cauchy-Schwarz inequality Cov_Q(w1,w2,x)^2 <= Var_Q(w1,x)*Var_Q(w2,x), GL_2(R) determinant scaling Det_Q(alpha*w1+beta*w2,gamma*w1+delta*w2,x) = (alpha*delta-beta*gamma)^2 Det_Q(w1,w2,x), and sharp multiplicative Popoviciu bound, multi-channel Gram determinant SM / GUT / CKM / PMNS / baryon / proton decay / dark matter bridge, multi-channel Gram determinant Bell / CHSH / Tsirelson / phase faithfulness / no-go bridge, curved 4D six-by-six plaquette / multi-channel Gram determinant Lohmiller-Slotine / conformal Laplacian / Bianchi / Einstein bridge, curved 4D eight-factor Yosida Capstone / ConditionalEinstein / spectral rigidity / unified forcing bridge, Twenty-Checkpoint Complete Tier-One TOE Master Synthesis, and preserved evidence."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess

EXPECTED = {
    'KFCausalClockFloorHigherPowerPotentialResolventYosidaEightParameterOctagon': 10,
    'KFCausalClockFloorFiveOperatorNineParameterHigherPowerNonagonCocycleAndYosida': 7,
    'KFCausalClockFloorEightParameterOctagonNineParameterNonagonDirectGrowingYosidaRateBridge': 6,
    'KFCausalClockFloorSixBySixMixedInitialFinalHigherPowerResolventPlaquetteGrid': 7,
    'KFCausalClockFloorSixBySixPlaquetteShiftedSourceResidualResolventCriterionWightmanOSBridge': 6,
    'KFCausalClockFloorSixBySixPlaquettePolymerBorgsImbrieKoteckyPreissWeingartenVolterraBridge': 6,
    'KFCausalClockFloorArbitraryOrderEightFactorMultiPowerYosidaComposition': 9,
    'KFCausalClockFloorEightFactorYosidaVelocityCommutatorUmegakiAndoLiebGoldenThompsonBridge': 5,
    'KFCausalClockFloorEightFactorYosidaStinespringPetzTraceDistanceQuantumSteinAEPBridge': 5,
    'KFCausalArbitrarySourceMultiChannelSpectralCovarianceGramDeterminantAndCauchySchwarzInequality': 6,
    'KFCausalMultiChannelGramDeterminantSMGUTCKMPMNSBaryonProtonDecayDarkMatterBridge': 5,
    'KFCausalMultiChannelGramDeterminantBellCHSHTsirelsonPhaseFaithfulnessNoGoBridge': 5,
    'KFCausalCurved4DSixBySixPlaquetteLohmillerSlotineConformalLaplacianBianchiEinsteinBridge': 5,
    'KFCausalCurved4DEightFactorYosidaCapstoneConditionalEinsteinSpectralRigidityUnifiedForcingBridge': 5,
    'KFCausalTOETwentyCheckpointCompleteTierOneMasterSynthesis': 6,
}
EXTRA_ANALYTIC = {}
SCOPE = 'Direct fixed-N growing-domain radial-Yosida lower bound Re <G x, J_N x> + N^-1 ||M_N x||^2 <= Re <G x, x>, radial-resolvent contraction ||M_N x|| <= ||G x||, O(N^-1) regularizer rate ||x - J_N x|| <= N^-1 ||G x||, and J_N x in Dom(G) <-> J_N x in Dom(P) on Dom(G) without R_G(a) or R_P(a), eight-parameter (a,b,c,d,e,f_param,g_param,h_param) higher-power potential-resolvent radial-Yosida cyclic octagon cocycles and sixteen-parameter ((a,J1),(b,J2),(c,J3),(d,J4),(e,J5),(f_param,J6),(g_param,J7),(h_param,J8)) Cauchy rate bounds, five-operator (T,P,G,S,H) nine-parameter (a,b,c,d,e,f_param,g_param,h_param,i_param) higher-power cross-resolvent nonagon cocycles and common-domain Yosida cross-rate bounds, eight-parameter octagon / nine-parameter nonagon / direct growing-domain Yosida rate QQG / inflaton / slow-roll / dimension / gauge / Volterra bridge, six-by-six (s1,s2,s3,s4,s5,s6)x(t1,t2,t3,t4,t5,t6) (5x5=25 elementary plaquettes) mixed initial-and-final higher-power resolvent and identity plaquette grids with exact 2D Stokes / Green boundary cancellation across all 8 time-independent and 10 equal-outer-final-time domains, unconditional shifted-source residual-resolvent identity R_{H(t)}(a) f = R_{S(t)}(a)(f - e^{2t} K R_{H(t)}(a) f) and 5-way operator-domain criterion R_{H(t)}(a) f in commonOperatorDomain <-> R_{S(t)}(a)(f - e^{2t} K R_{H(t)}(a) f) in Dom(P) for all real m,g,k,t,s in R (including k<=0) and Wightman / OS / Clay continuum bridge, six-by-six plaquette Polymer / Borgs-Imbrie / Kotecky-Preiss / Weingarten / Volterra SO(10) bridge, arbitrary-order eight-factor multi-power (r,s,q,p,l,u,v_pow,w_pow) and eight-parameter (a,b,d,e,c,f_param,g_param,h_param) Yosida composition defect calculus across all 5 Hamiltonians, eight-factor Yosida quantum-velocity commutator error / Umegaki / Ando / Lieb / Golden-Thompson bridge, eight-factor Yosida Stinespring / Petz / trace-distance / Quantum Stein / AEP bridge, finite Q-channel 2x2 spectral covariance Gram determinant Det_Q(w1,w2,x) = Var_Q(w1,x)*Var_Q(w2,x) - Cov_Q(w1,w2,x)^2 >= 0, multiplicative Cauchy-Schwarz inequality Cov_Q(w1,w2,x)^2 <= Var_Q(w1,x)*Var_Q(w2,x), GL_2(R) determinant scaling Det_Q(alpha*w1+beta*w2,gamma*w1+delta*w2,x) = (alpha*delta-beta*gamma)^2 Det_Q(w1,w2,x), and sharp multiplicative Popoviciu bound, multi-channel Gram determinant SM / GUT / CKM / PMNS / baryon / proton decay / dark matter bridge, multi-channel Gram determinant Bell / CHSH / Tsirelson / phase faithfulness / no-go bridge, curved 4D six-by-six plaquette / multi-channel Gram determinant Lohmiller-Slotine / conformal Laplacian / Bianchi / Einstein bridge, curved 4D eight-factor Yosida Capstone / ConditionalEinstein / spectral rigidity / unified forcing bridge, and Twenty-Checkpoint Complete Tier-One TOE Master Synthesis. Specifically, on 0<epsilon,h!=0,abs(h)<=pi*epsilon/3 and for all real m,g,k,s,t: (1) directly at fixed N>0 without R_G(a) or R_P(a), every x in Dom(G) satisfies x in Dom(K) cap Dom(P), ||M_N x||^2 <= Re <G x, M_N x>, 0 <= Re <G x, M_N x>, ||M_N x|| <= ||G x||, Re <G x, J_N x> + N^-1 ||M_N x||^2 <= Re <G x, x>, ||x - J_N x|| <= N^-1 ||G x||, and J_N x in Dom(G) <-> J_N x in Dom(P), while for every m,r,j>=0 with j<=m and x in Dom(P^(m+1)), eight-parameter (a,b,c,d,e,f_param,g_param,h_param) and sixteen-parameter ((a,J1),...,(h_param,J8)) potential-resolvent and identity-Yosida tier differences satisfy exact 8-step cyclic octagon cocycles, Dom(P^(r+2))/Dom(P^r) regularity, and seven-hop Cauchy rate bounds, and across any NineParameterFiveOperatorSystem (T,P,G,S(t),H(t)) at (a,b,c,d,e,f_param,g_param,h_param,i_param), cross-resolvent and cross-Yosida differences satisfy exact 9-step nonagon cocycles and eight-hop bounds; (2) for any f in Hilbert, a>0, and any real m,g,k,t,s in R (including k<=0 without iteration), the single resolvent R_{H(t)}(a) f satisfies the unconditional shifted-source residual-resolvent identity R_{H(t)}(a) f = R_{S(t)}(a)(f - e^{2t} K R_{H(t)}(a) f) and the 5-way operator-domain criterion R_{H(t)}(a) f in commonOperatorDomain <-> R_{H(t)}(a) f in Dom(T) <-> R_{H(t)}(a) f in Dom(G) <-> R_{H(t)}(a) f in Dom(P) <-> R_{S(t)}(a)(f - e^{2t} K R_{H(t)}(a) f) in Dom(P), while on a 6x6 grid (s1..s6)x(t1..t6), the 5x5 sum of 25 elementary mixed initial-and-final higher-power resolvent and identity plaquettes satisfies exact 2D Stokes / Green boundary cancellation to the outer plaquette (s1,s6; t1,t6) canceling 16 interior vertices and 40 interior edges, 6-initial and 6-final hexagon cocycles, 8-domain regularity with ((a1^-1)^(r+2)+(g1^-1)^(r+2))||f1||+((a6^-1)^(r+2)+(g6^-1)^(r+2))||f6|| and 2||f1||+2||f6|| bounds, and equal-outer-final-time Dom(H(t)^(r+2)) + 10-domain regularity; (3) across all 5 Hamiltonians A in {T,P,G,S(t),H(t)}, eight-factor multi-power (r,s,q,p,l,u,v_pow,w_pow) and eight-parameter (a,b,d,e,c,f_param,g_param,h_param) Yosida compositions preserve Dom(A^n), commute with A^n, contract kthPowerGraphNormSq A n, and satisfy ((r/a + s/b + q/d + p/e + l/c + u/f_param + v_pow/g_param + w_pow/h_param)^2) * kthPowerGraphNormSq A (n+1) x defect bounds, paired on Dom(H(t)) with the exact quantum-velocity commutator pairing <H(t) x, D x> = <h_out x, R(h_out x)> and energy-controlled classical-velocity error |(-2/h) Im <H(t) x, D x> - v_cl(x)| <= (20|h|/epsilon^2) Re <H(t) x, x>; (4) for any Q-channel operator family {P_q}_{q in Fin Q} with weight profiles w1 in [w1_min,w1_max] and w2 in [w2_min,w2_max], the 2x2 spectral covariance Gram determinant Det_Q(w1,w2,x) = Var_Q(w1,x)*Var_Q(w2,x) - Cov_Q(w1,w2,x)^2 satisfies the exact quadratic variance pencil completing-the-square identity Var_Q(Var_Q(w2,x)*w1 - Cov_Q(w1,w2,x)*w2,x) = Var_Q(w2,x)*Det_Q(w1,w2,x), is nonnegative Det_Q(w1,w2,x)>=0, yields the multiplicative Cauchy-Schwarz inequality Cov_Q(w1,w2,x)^2 <= Var_Q(w1,x)*Var_Q(w2,x), transforms under GL_2(R) as Det_Q(alpha*w1+beta*w2,gamma*w1+delta*w2,x) = (alpha*delta-beta*gamma)^2 Det_Q(w1,w2,x), and obeys the sharp multiplicative Popoviciu bound Cov_Q(w1,w2,x)^2 <= ((w1_max-w1_min)/2)^2 ((w2_max-w2_min)/2)^2 E_Q(x)^4; (5) all five fronts are synthesized with the curved 4D Bianchi/Einstein/Lohmiller-Slotine/Capstone/Spectral-Rigidity hierarchy and 100% (659/659) direct non-Audit module coverage. Direct fixed-N strong-operator invariance J_N(DomP) subseteq DomP without R_P(a) (beyond the proved four-domain invariance, two-sided potential-pairing domination, and Dom(G) radial-Yosida contraction/rate), single-resolvent R_{H(t)}(a)f in DomP for k<=0 without iteration (beyond the proved 14-domain regularity, unconditional R_G(a)f in DomP, 5-way DomP <-> DomG <-> DomT equivalence, and shifted-source residual-resolvent criterion), trajectory-wide unbounded-momentum derivatives beyond the energy-controlled H(t)-domain quantum-velocity commutator bound, general non-symmetric dynamical nonlinear 4D Einstein PDE evolution, full infinite-volume 4D continuum OS/Wightman QFT beyond the chamber/cluster reduction, first-principles derivation of absolute dimensionful scales, microscopic phase selection, controlled physical limits, and empirical identification remain open; the earlier phase/harmonic identification still requires revision. A physical TOE is not proved. This checkpoint adds93 theorems in15 modules, preserves3770 parent source/script hashes and adds17 for3787 total; exact root extends from9326 to9341 lines. All12 parent analytic artifacts and23 numerical files remain unchanged. Standard axioms only.'
PARENT = 'data/nineteen_checkpoint_complete_tier_one_synthesis_audit.json'
PARENT_SHA = '3f5687603bf4f4d081769a2650a6898989ba6493d4e51ebb47744aabe5505cd9'
REPORT = 'data/twenty_checkpoint_complete_tier_one_synthesis_audit.json'
SCRIPTS = ['scripts/twenty_checkpoint_complete_tier_one_synthesis_audit.py',
           'scripts/verify_twenty_checkpoint_complete_tier_one_synthesis.py']
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
    logs=overlay/'twenty-checkpoint-complete-tier-one-synthesis-audit'
    logs.mkdir(exist_ok=False)
    assert sha(root/PARENT)==PARENT_SHA
    parent=json.loads((root/PARENT).read_text())
    hashes=dict(parent['source_sha256'])
    assert len(hashes)==3770 and all(sha(root/p)==h for p,h in hashes.items())
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
    assert len(text.splitlines())==9326+len(EXPECTED)
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
