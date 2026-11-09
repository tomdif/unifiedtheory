#!/usr/bin/env python3
"""Check five-parameter higher-power potential-resolvent radial-Yosida pentagon cocycles and ten-parameter Cauchy rate bounds, five-operator six-parameter higher-power hexagon cocycles and common-domain Yosida cross-rate bounds, five-parameter pentagon / six-parameter hexagon QQG / inflaton / slow-roll / causal foundation / dimension / gauge bridge, three-by-three mixed initial-and-final higher-power resolvent plaquette grids and 2D Stokes boundary cancellation, three-by-three plaquette alpha_s / Ando / CKM / Wilson / CL / Wightman / causal SO(10) bridge, three-by-three plaquette Choi / classical DPI / Clay physical Z / dark matter / diagonal entropy bridge, arbitrary-order five-factor multi-power (r,s,q,p,l) and five-parameter (a,b,d,e,c) Yosida composition defect calculus across all 5 Hamiltonians, five-factor Yosida disc-fusion / E8-Zamolodchikov / Feynman / Holevo / Ando / Lieb bridge, five-factor Yosida Lindblad / log-sum / muon g-2 / octonion / operator entropy / PMNS / partial trace bridge, normalized three-channel spectral variance functional, exact Lagrange pairwise channel-spread identity, and Bhatia-Davis / Popoviciu variance envelope bounds, centered projector variance Phase A/C/E / cluster / DLR / Pirogov-Sinai / KP / Weingarten / poset bridge, centered projector variance proton decay / quantum Stein / Volterra SO(10) / rpow / spectral FC bridge, curved 4D three-by-three plaquette / spectral variance trace resolvent / Umegaki / Yang-Mills / Bekenstein / bipartite bridge, curved 4D five-factor Yosida bit commitment / candidate operator / LHV / no-go / phase faithfulness / spectral rigidity bridge, Seventeen-Checkpoint Complete Tier-One TOE Master Synthesis, and preserved evidence."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess

EXPECTED = {
    'KFCausalClockFloorHigherPowerPotentialResolventYosidaFiveParameterPentagon': 10,
    'KFCausalClockFloorFiveOperatorSixParameterHigherPowerHexagonCocycleAndYosida': 7,
    'KFCausalClockFloorFiveParameterPentagonQQGInflatonSlowRollCausalFoundationDimensionGaugeBridge': 6,
    'KFCausalClockFloorThreeByThreeMixedInitialFinalHigherPowerResolventPlaquetteGrid': 7,
    'KFCausalClockFloorThreeByThreePlaquetteAlphaSAndoCKMWilsonCLWightmanCausalSO10Bridge': 6,
    'KFCausalClockFloorThreeByThreePlaquetteChoiClassicalDPIClayPhysicalZDarkMatterDiagonalEntropyBridge': 6,
    'KFCausalClockFloorArbitraryOrderFiveFactorMultiPowerYosidaComposition': 9,
    'KFCausalClockFloorFiveFactorYosidaDiscFusionE8ZamolodchikovFeynmanHolevoAndoLiebBridge': 5,
    'KFCausalClockFloorFiveFactorYosidaLindbladLogSumMuonG2OctonionOperatorEntropyPMNSPartialTraceBridge': 5,
    'KFCausalArbitrarySourceCenteredProjectorVarianceAndSpectralSpreadDecomposition': 6,
    'KFCausalCenteredProjectorVariancePhaseACEClusterDLRPirogovSinaiKPWeingartenPosetBridge': 5,
    'KFCausalCenteredProjectorVarianceProtonDecayQuantumSteinVolterraSO10RpowSpectralBridge': 5,
    'KFCausalCurved4DThreeByThreePlaquetteSpectralRelTraceResolventUmegakiYMBekensteinBipartiteBridge': 5,
    'KFCausalCurved4DFiveFactorYosidaBitCommitmentCandidateLHVNoGoPhaseFaithfulnessSpectralRigidityBridge': 5,
    'KFCausalTOESeventeenCheckpointCompleteTierOneMasterSynthesis': 6,
}
EXTRA_ANALYTIC = {}
SCOPE = 'Five-parameter (a,b,c,d,e) higher-power potential-resolvent radial-Yosida cyclic pentagon cocycles and ten-parameter ((a,J1),(b,J2),(c,J3),(d,J4),(e,J5)) Cauchy rate bounds, five-operator (T,P,G,S,H) six-parameter (a,b,c,d,e,f_param) higher-power cross-resolvent hexagon cocycles and common-domain Yosida cross-rate bounds, five-parameter pentagon / six-parameter hexagon QQG / inflaton / slow-roll / causal foundation / dimension / gauge bridge, three-by-three (s1,s2,s3)x(t1,t2,t3) mixed initial-and-final higher-power resolvent and identity plaquette grids with exact 2D Stokes / Green boundary cancellation across all 8 time-independent and 10 equal-outer-final-time domains, three-by-three plaquette alpha_s / Ando / CKM / Wilson / CL / Wightman / causal SO(10) bridge, three-by-three plaquette Choi / classical DPI / Clay physical Z / dark matter / diagonal entropy bridge, arbitrary-order five-factor multi-power (r,s,q,p,l) and five-parameter (a,b,d,e,c) Yosida composition defect calculus across all 5 Hamiltonians, five-factor Yosida disc-fusion / E8-Zamolodchikov / Feynman / Holevo / Ando / Lieb bridge, five-factor Yosida Lindblad / log-sum / muon g-2 / octonion / operator entropy / PMNS / partial trace bridge, normalized three-channel spectral variance functional, exact Lagrange pairwise channel-spread identity, shift invariance, and Bhatia-Davis / Popoviciu variance envelope bounds, centered projector variance Phase A/C/E / cluster / DLR / Pirogov-Sinai / KP / Weingarten / poset bridge, centered projector variance proton decay / quantum Stein / Volterra SO(10) / rpow / spectral FC bridge, curved 4D three-by-three plaquette / spectral variance trace resolvent / Umegaki / Yang-Mills / Bekenstein / bipartite bridge, curved 4D five-factor Yosida bit commitment / candidate operator / LHV / no-go / phase faithfulness / spectral rigidity bridge, and Seventeen-Checkpoint Complete Tier-One TOE Master Synthesis achieving 100% (659/659) direct non-Audit module import and theorem-bridge coverage across UnifiedTheory/Audit/. Specifically, on 0<epsilon,h!=0,abs(h)<=pi*epsilon/3 and for all real m,g,k,s,t: (1) for every m,r,j>=0 with j<=m and x in Dom(P^(m+1)), five-parameter (a,b,c,d,e) and ten-parameter ((a,J1),(b,J2),(c,J3),(d,J4),(e,J5)) potential-resolvent and identity-Yosida tier differences satisfy exact 5-step cyclic pentagon cocycles, four-hop decomposition, Dom(P^(r+2))/Dom(P^r) regularity, and four-hop Cauchy rate bounds, while across any SixParameterFiveOperatorSystem (T,P,G,S(t),H(t)) at (a,b,c,d,e,f_param), cross-resolvent and cross-Yosida differences satisfy exact 6-step hexagon cocycles and five-hop bounds, bridged with all 24 QQG/Inflaton/SlowRoll/CausalFoundation/Dimension/FineStructure/Volterra modules; (2) on a 3x3 grid (s1,s2,s3)x(t1,t2,t3), the 2x2 sum of elementary mixed initial-and-final higher-power resolvent and identity plaquettes satisfies exact 2D Stokes / Green boundary cancellation to the outer plaquette (s1,s3; t1,t3), 3-initial and 3-final cyclic cocycles, 8-domain regularity with ((a1^-1)^(r+2)+(e1^-1)^(r+2))||f1||+((a3^-1)^(r+2)+(e3^-1)^(r+2))||f3|| and 2||f1||+2||f3|| bounds, and equal-outer-final-time Dom(H(t)^(r+2)) + 10-domain regularity, bridged with all 44 AlphaS/Ando/CKM/Wilson/CL/Wightman/CausalSO10/Choi/ClassicalDPI/Clay/DarkMatter/DiagonalEntropy modules; (3) across all 5 Hamiltonians A in {T,P,G,S(t),H(t)}, five-factor multi-power (r,s,q,p,l) and five-parameter (a,b,d,e,c) Yosida compositions preserve Dom(A^n), commute with A^n, contract kthPowerGraphNormSq A n, and satisfy ((r/a + s/b + q/d + p/e + l/c)^2) * kthPowerGraphNormSq A (n+1) x defect bounds, bridged with all 40 DiscFusion/E8Zamolodchikov/Feynman/Holevo/Ando/Lieb/Lindblad/LogSum/MuonG2/Octonion/OperatorEntropy/PMNS/PartialTrace modules; (4) for mutually orthogonal projections (P1,P2,P_res) with weights in [w_min,w_max], the homogeneous degree-4 spectral variance functional E(x)*M2(x)-M1(x)^2 equals the exact Lagrange pairwise channel-spread sum, is shift-invariant, satisfies E(x)*BD(x)-Var(x)=(w_max*E(x)-M1(x))(M1(x)-w_min*E(x)), and obeys 0 <= Var(x) <= E(x)*BD(x) <= ((w_max-w_min)/2)^2 E(x)^2, bridged with all 42 PhaseACE/Cluster/DLR/PirogovSinai/KP/Weingarten/Poset/ProtonDecay/QuantumStein/VolterraSO10/Rpow/SpectralFC modules; (5) curved 4D plaquette grids, spectral variance, and five-factor Yosida hierarchies are bridged with all 34 SpectralRelEntropy/Stinespring/TopYukawa/TraceResolvent/Umegaki/YangMills/Bekenstein/Bipartite/BitCommitment/CandidateOperator/LHV/NoGo/PhaseFaithfulness/SpectralRigidity modules, completing 100% (659/659) direct non-Audit module coverage. Direct fixed-N invariance J_N(DomP) subseteq DomP without R_P(a), single-resolvent R_{H(t)}(a)f in DomP for k<=0 without iteration or form pairing, trajectory-wide unbounded-momentum derivatives, general non-symmetric dynamical nonlinear 4D Einstein PDE evolution, full infinite-volume 4D continuum OS/Wightman QFT beyond the chamber/cluster reduction, first-principles derivation of absolute dimensionful scales, microscopic phase selection, controlled physical limits, and empirical identification remain open; the earlier phase/harmonic identification still requires revision. A physical TOE is not proved. This checkpoint adds93 theorems in15 modules, preserves3719 parent source/script hashes and adds17 for3736 total; exact root extends from9281 to9296 lines. All12 parent analytic artifacts and23 numerical files remain unchanged. Standard axioms only.'
PARENT = 'data/sixteen_checkpoint_complete_tier_one_synthesis_audit.json'
PARENT_SHA = '84f6cdbebb925930ad114adcc1778127bd00f9e2cf96738c19e3b4b371426200'
REPORT = 'data/seventeen_checkpoint_complete_tier_one_synthesis_audit.json'
SCRIPTS = ['scripts/seventeen_checkpoint_complete_tier_one_synthesis_audit.py',
           'scripts/verify_seventeen_checkpoint_complete_tier_one_synthesis.py']
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
    logs=overlay/'seventeen-checkpoint-complete-tier-one-synthesis-audit'
    logs.mkdir(exist_ok=False)
    assert sha(root/PARENT)==PARENT_SHA
    parent=json.loads((root/PARENT).read_text())
    hashes=dict(parent['source_sha256'])
    assert len(hashes)==3719 and all(sha(root/p)==h for p,h in hashes.items())
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
    assert len(text.splitlines())==9281+len(EXPECTED)
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
