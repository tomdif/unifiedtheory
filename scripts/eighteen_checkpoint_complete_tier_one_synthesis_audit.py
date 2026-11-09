#!/usr/bin/env python3
"""Check direct fixed-N potential-form and radial-domain invariance of J_N on Dom(P) without R_P(a), six-parameter higher-power potential-resolvent radial-Yosida hexagon cocycles and twelve-parameter Cauchy rate bounds, five-operator seven-parameter higher-power heptagon cocycles and common-domain Yosida cross-rate bounds, six-parameter hexagon / seven-parameter heptagon / direct potential-form invariance QQG / inflaton / slow-roll / dimension / gauge / Volterra bridge, four-by-four (3x3=9 elementary plaquettes) mixed initial-and-final higher-power resolvent plaquette grids and 2D Stokes boundary cancellation, unconditional single-resolvent 10-domain regularity R_{H(t)}(a) f without iteration for all real m,g,k,t,s in R and Wightman / OS / Clay continuum bridge, four-by-four plaquette Polymer / Borgs-Imbrie / Kotecky-Preiss / Weingarten / Volterra SO(10) bridge, arbitrary-order six-factor multi-power (r,s,q,p,l,u) and six-parameter (a,b,d,e,c,f_param) Yosida composition defect calculus across all 5 Hamiltonians, six-factor Yosida quantum-velocity commutator error / Umegaki / Ando / Lieb / Golden-Thompson bridge, six-factor Yosida Stinespring / Petz / trace-distance / Quantum Stein / AEP bridge, finite Q-channel normalized spectral variance functional, exact QxQ double-sum Lagrange pairwise spread identity, and Q-channel Bhatia-Davis / Popoviciu variance envelope bounds, multi-channel projector variance SM / GUT / CKM / PMNS / baryon / proton decay / dark matter bridge, multi-channel projector variance Bell / CHSH / Tsirelson / phase faithfulness / no-go bridge, curved 4D four-by-four plaquette / multi-channel variance Lohmiller-Slotine / conformal Laplacian / Bianchi / Einstein bridge, curved 4D six-factor Yosida Capstone / ConditionalEinstein / spectral rigidity / unified forcing bridge, Eighteen-Checkpoint Complete Tier-One TOE Master Synthesis, and preserved evidence."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess

EXPECTED = {
    'KFCausalClockFloorHigherPowerPotentialResolventYosidaSixParameterHexagon': 10,
    'KFCausalClockFloorFiveOperatorSevenParameterHigherPowerHeptagonCocycleAndYosida': 7,
    'KFCausalClockFloorSixParameterHexagonSevenParameterHeptagonDirectPotentialFormInvarianceBridge': 6,
    'KFCausalClockFloorFourByFourMixedInitialFinalHigherPowerResolventPlaquetteGrid': 7,
    'KFCausalClockFloorFourByFourPlaquetteSingleResolventTenDomainWightmanOSContinuumBridge': 6,
    'KFCausalClockFloorFourByFourPlaquettePolymerBorgsImbrieKoteckyPreissWeingartenVolterraBridge': 6,
    'KFCausalClockFloorArbitraryOrderSixFactorMultiPowerYosidaComposition': 9,
    'KFCausalClockFloorSixFactorYosidaVelocityCommutatorUmegakiAndoLiebGoldenThompsonBridge': 5,
    'KFCausalClockFloorSixFactorYosidaStinespringPetzTraceDistanceQuantumSteinAEPBridge': 5,
    'KFCausalArbitrarySourceMultiChannelCenteredProjectorVarianceAndPopoviciuBound': 6,
    'KFCausalMultiChannelProjectorVarianceSMGUTCKMPMNSBaryonProtonDecayDarkMatterBridge': 5,
    'KFCausalMultiChannelProjectorVarianceBellCHSHTsirelsonPhaseFaithfulnessNoGoBridge': 5,
    'KFCausalCurved4DFourByFourPlaquetteLohmillerSlotineConformalLaplacianBianchiEinsteinBridge': 5,
    'KFCausalCurved4DSixFactorYosidaCapstoneConditionalEinsteinSpectralRigidityUnifiedForcingBridge': 5,
    'KFCausalTOEEighteenCheckpointCompleteTierOneMasterSynthesis': 6,
}
EXTRA_ANALYTIC = {}
SCOPE = 'Direct fixed-N potential-form and radial-domain invariance of J_N on Dom(P) without R_P(a) together with linear and quadratic radial-Yosida / radial-resolvent accretivity on Dom(P), six-parameter (a,b,c,d,e,f_param) higher-power potential-resolvent radial-Yosida cyclic hexagon cocycles and twelve-parameter ((a,J1),(b,J2),(c,J3),(d,J4),(e,J5),(f_param,J6)) Cauchy rate bounds, five-operator (T,P,G,S,H) seven-parameter (a,b,c,d,e,f_param,g_param) higher-power cross-resolvent heptagon cocycles and common-domain Yosida cross-rate bounds, six-parameter hexagon / seven-parameter heptagon / direct potential-form invariance QQG / inflaton / slow-roll / dimension / gauge / Volterra bridge, four-by-four (s1,s2,s3,s4)x(t1,t2,t3,t4) (3x3=9 elementary plaquettes) mixed initial-and-final higher-power resolvent and identity plaquette grids with exact 2D Stokes / Green boundary cancellation across all 8 time-independent and 10 equal-outer-final-time domains, unconditional single-resolvent 10-domain regularity R_{H(t)}(a) f without iteration for all real m,g,k,t,s in R (including k<=0) and Wightman / OS / Clay continuum bridge, four-by-four plaquette Polymer / Borgs-Imbrie / Kotecky-Preiss / Weingarten / Volterra SO(10) bridge, arbitrary-order six-factor multi-power (r,s,q,p,l,u) and six-parameter (a,b,d,e,c,f_param) Yosida composition defect calculus across all 5 Hamiltonians, six-factor Yosida quantum-velocity commutator error / Umegaki / Ando / Lieb / Golden-Thompson bridge, six-factor Yosida Stinespring / Petz / trace-distance / Quantum Stein / AEP bridge, finite Q-channel normalized spectral variance functional, exact QxQ double-sum Lagrange pairwise spread identity, shift invariance, and Q-channel Bhatia-Davis / Popoviciu variance envelope bounds, multi-channel projector variance SM / GUT / CKM / PMNS / baryon / proton decay / dark matter bridge, multi-channel projector variance Bell / CHSH / Tsirelson / phase faithfulness / no-go bridge, curved 4D four-by-four plaquette / multi-channel variance Lohmiller-Slotine / conformal Laplacian / Bianchi / Einstein bridge, curved 4D six-factor Yosida Capstone / ConditionalEinstein / spectral rigidity / unified forcing bridge, and Eighteen-Checkpoint Complete Tier-One TOE Master Synthesis. Specifically, on 0<epsilon,h!=0,abs(h)<=pi*epsilon/3 and for all real m,g,k,s,t: (1) directly at fixed N>0 without R_P(a), every x in Dom(P) satisfies x in Dom(T_pot), J_N x in Dom(K) cap Dom(T_pot), 0 <= Re <P x, J_N x>, and 0 <= Re <P x, M_N x> (with quadratic accretivity on abs(h)<=pi*epsilon/4), while for every m,r,j>=0 with j<=m and x in Dom(P^(m+1)), six-parameter (a,b,c,d,e,f_param) and twelve-parameter ((a,J1),...,(f_param,J6)) potential-resolvent and identity-Yosida tier differences satisfy exact 6-step cyclic hexagon cocycles, Dom(P^(r+2))/Dom(P^r) regularity, and five-hop Cauchy rate bounds, and across any SevenParameterFiveOperatorSystem (T,P,G,S(t),H(t)) at (a,b,c,d,e,f_param,g_param), cross-resolvent and cross-Yosida differences satisfy exact 7-step heptagon cocycles and six-hop bounds; (2) for any f in Hilbert, a>0, and any real m,g,k,t,s in R (including k<=0 without iteration), the single resolvent R_{H(t)}(a) f belongs unconditionally to all 10 operator, form, and clock domains (Dom(H(t)), Dom(K), Dom(S(t)), Dom(E_avg(s)), Dom(T_stat), Dom(K_root), Dom(T_pot), Dom(T_grow), Dom(T_res(s)), Dom(clockHalf)), and on a 4x4 grid (s1,s2,s3,s4)x(t1,t2,t3,t4), the 3x3 sum of 9 elementary mixed initial-and-final higher-power resolvent and identity plaquettes satisfies exact 2D Stokes / Green boundary cancellation to the outer plaquette (s1,s4; t1,t4), 4-initial and 4-final quadrangle cocycles, 8-domain regularity with ((a1^-1)^(r+2)+(g1^-1)^(r+2))||f1||+((a4^-1)^(r+2)+(g4^-1)^(r+2))||f4|| and 2||f1||+2||f4|| bounds, and equal-outer-final-time Dom(H(t)^(r+2)) + 10-domain regularity; (3) across all 5 Hamiltonians A in {T,P,G,S(t),H(t)}, six-factor multi-power (r,s,q,p,l,u) and six-parameter (a,b,d,e,c,f_param) Yosida compositions preserve Dom(A^n), commute with A^n, contract kthPowerGraphNormSq A n, and satisfy ((r/a + s/b + q/d + p/e + l/c + u/f_param)^2) * kthPowerGraphNormSq A (n+1) x defect bounds, paired on Dom(H(t)) with the exact quantum-velocity commutator pairing <H(t) x, D x> = <h_out x, R(h_out x)> and energy-controlled classical-velocity error |(-2/h) Im <H(t) x, D x> - v_cl(x)| <= (20|h|/epsilon^2) Re <H(t) x, x>; (4) for any Q-channel operator family {P_q}_{q in Fin Q} with weights in [w_min,w_max], the homogeneous degree-4 spectral variance functional E_Q(x)*M2(x)-M1(x)^2 satisfies 2*Var_Q(x) = sum_{q1,q2} (w_{q1}-w_{q2})^2 E(P_{q1} x) E(P_{q2} x), is shift-invariant, satisfies E_Q(x)*BD_Q(x)+Var_Q(x)=(w_max*E_Q(x)-M1(x))(M1(x)-w_min*E_Q(x)), and obeys 0 <= Var_Q(x) <= (w_max*E_Q(x)-M1(x))(M1(x)-w_min*E_Q(x)) <= ((w_max-w_min)/2)^2 E_Q(x)^2; (5) all five fronts are synthesized with the curved 4D Bianchi/Einstein/Lohmiller-Slotine/Capstone/Spectral-Rigidity hierarchy and 100% (659/659) direct non-Audit module coverage. Direct fixed-N strong-operator invariance J_N(DomP) subseteq DomP without R_P(a) (beyond the proved Dom(K) cap Dom(T_pot) form invariance and accretivity), single-resolvent R_{H(t)}(a)f in DomP for k<=0 without iteration (beyond the proved 10-domain regularity including Dom(T_pot)), trajectory-wide unbounded-momentum derivatives beyond the energy-controlled H(t)-domain quantum-velocity commutator bound, general non-symmetric dynamical nonlinear 4D Einstein PDE evolution, full infinite-volume 4D continuum OS/Wightman QFT beyond the chamber/cluster reduction, first-principles derivation of absolute dimensionful scales, microscopic phase selection, controlled physical limits, and empirical identification remain open; the earlier phase/harmonic identification still requires revision. A physical TOE is not proved. This checkpoint adds93 theorems in15 modules, preserves3736 parent source/script hashes and adds17 for3753 total; exact root extends from9296 to9311 lines. All12 parent analytic artifacts and23 numerical files remain unchanged. Standard axioms only.'
PARENT = 'data/seventeen_checkpoint_complete_tier_one_synthesis_audit.json'
PARENT_SHA = '69c5e32fca72dcc1b9559229a52835ffcbdf63e8d507b34ab0aa989643bb0d18'
REPORT = 'data/eighteen_checkpoint_complete_tier_one_synthesis_audit.json'
SCRIPTS = ['scripts/eighteen_checkpoint_complete_tier_one_synthesis_audit.py',
           'scripts/verify_eighteen_checkpoint_complete_tier_one_synthesis.py']
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
    logs=overlay/'eighteen-checkpoint-complete-tier-one-synthesis-audit'
    logs.mkdir(exist_ok=False)
    assert sha(root/PARENT)==PARENT_SHA
    parent=json.loads((root/PARENT).read_text())
    hashes=dict(parent['source_sha256'])
    assert len(hashes)==3736 and all(sha(root/p)==h for p,h in hashes.items())
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
    assert len(text.splitlines())==9296+len(EXPECTED)
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
