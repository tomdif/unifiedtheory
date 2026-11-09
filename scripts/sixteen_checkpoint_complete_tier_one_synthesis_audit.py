#!/usr/bin/env python3
"""Check four-parameter higher-power potential-resolvent radial-Yosida quadrangle cocycles, mixed parameter-regularizer double-difference commutators, and eight-parameter Cauchy rate bounds, five-operator five-parameter higher-power pentagon cocycles and common-domain Yosida cross-rate bounds, four-parameter quadrangle / five-operator pentagon SM Higgs / branching / baryon / HVP / Weinberg bridge, two-time mixed initial-and-final four-corner higher-power resolvent and Yosida plaquette double-differences across all 8 time-independent and 10 equal-final-time domains, two-time mixed plaquette SU(5) embedding / Haar twirl / anomaly bridge, two-time mixed plaquette Choi-Petz / trace-distance contractivity / SSA / Umegaki bridge, arbitrary-order four-factor multi-power (r,s,q,p) and four-parameter (a,b,d,e) Yosida composition defect calculus across all 5 Hamiltonians, four-factor Yosida Gaussian states / level statistics / quantum AEP / t-designs / tomography bridge, four-factor Yosida Born uniqueness / CPT antilinearity / Wedderburn 2D / QM scope bridge, three-channel and Q-channel spectral-weighted projector second moments and Bhatia-Davis / Popoviciu dispersion inequalities, Bhatia-Davis dispersion BB84 / CHSH monogamy / Mermin N=6 / Pironio-Acin / Tsirelson bridge, Bhatia-Davis dispersion charge sectors / far-field / multi-particle / concrete many-body bridge, curved 4D two-time plaquette / Bhatia-Davis causal bridge / census / exact regime / substrate bridge, curved 4D four-factor Yosida Capstone / ConditionalEinstein / Predictions / TOE ranking bridge, Sixteen-Checkpoint Complete Tier-One TOE Master Synthesis, and preserved evidence."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess

EXPECTED = {
    'KFCausalClockFloorHigherPowerPotentialResolventYosidaFourParameterQuadrangle': 10,
    'KFCausalClockFloorFiveOperatorFiveParameterHigherPowerPentagonCocycleAndYosida': 7,
    'KFCausalClockFloorFourParameterQuadrangleFiveOperatorPentagonSMHiggsBaryonBridge': 6,
    'KFCausalClockFloorTwoTimeMixedInitialFinalHigherPowerResolventPlaquette': 7,
    'KFCausalClockFloorTwoTimeMixedPlaquetteSU5EmbeddingHaarTwirlAnomalyBridge': 6,
    'KFCausalClockFloorTwoTimeMixedPlaquetteChoiPetzTraceDistanceSSAUmegakiBridge': 6,
    'KFCausalClockFloorArbitraryOrderFourFactorMultiPowerYosidaComposition': 9,
    'KFCausalClockFloorFourFactorYosidaGaussianStatesLevelStatisticsQuantumAEPTDesignsBridge': 5,
    'KFCausalClockFloorFourFactorYosidaBornUniquenessCPTAntilinearWedderburnQMScopeBridge': 5,
    'KFCausalArbitrarySourceWeightedProjectorVarianceAndBhatiaDavisInequality': 6,
    'KFCausalBhatiaDavisDispersionBB84CHSHMonogamyMerminN6PironioAcinTsirelsonBridge': 5,
    'KFCausalBhatiaDavisDispersionChargeSectorsFarFieldMultiParticleConcreteMultiBodyBridge': 5,
    'KFCausalCurved4DTwoTimePlaquetteCausalBridgeCensusExactRegimeSubstrateBridge': 5,
    'KFCausalCurved4DFourFactorYosidaCapstoneConditionalEinsteinPredictionsTOERankingBridge': 5,
    'KFCausalTOESixteenCheckpointCompleteTierOneMasterSynthesis': 6,
}
EXTRA_ANALYTIC = {}
SCOPE = 'Four-parameter (a,b,c,d) higher-power potential-resolvent radial-Yosida cyclic quadrangle cocycles, mixed parameter-regularizer double-difference commutators, and eight-parameter ((a,J1),(b,J2),(c,J3),(d,J4)) Cauchy rate bounds, five-operator (T,P,G,S,H) five-parameter (a,b,c,d,e) higher-power cross-resolvent pentagon cocycles and common-domain Yosida cross-rate bounds, four-parameter quadrangle / five-operator pentagon SM Higgs / branching / baryon / HVP / Weinberg bridge, two-time mixed initial-and-final (s1,s2; t1,t2) four-corner higher-power resolvent and Yosida plaquette double-differences across all 8 time-independent and 10 equal-final-time domains, two-time mixed plaquette SU(5) embedding / Haar twirl / anomaly bridge, two-time mixed plaquette Choi-Petz / trace-distance contractivity / SSA / Umegaki bridge, arbitrary-order four-factor multi-power (r,s,q,p) and four-parameter (a,b,d,e) Yosida composition defect calculus across all 5 Hamiltonians, four-factor Yosida Gaussian states / level statistics / quantum AEP / t-designs / tomography bridge, four-factor Yosida Born uniqueness / CPT antilinearity / Wedderburn 2D / QM scope bridge, three-channel and Q-channel spectral-weighted projector second moments and Bhatia-Davis / Popoviciu dispersion inequalities, Bhatia-Davis dispersion BB84 / CHSH monogamy / Mermin N=6 / Pironio-Acin / Tsirelson bridge, Bhatia-Davis dispersion charge sectors / far-field / multi-particle / concrete many-body bridge, curved 4D two-time plaquette / Bhatia-Davis causal bridge / census / exact regime / substrate bridge, curved 4D four-factor Yosida Capstone / ConditionalEinstein / Predictions / TOE ranking bridge, and Sixteen-Checkpoint Complete Tier-One TOE Master Synthesis. Specifically, on 0<epsilon,h!=0,abs(h)<=pi*epsilon/3 and for all real m,g,k,s,t: (1) for every m,r,j>=0 with j<=m and x in Dom(P^(m+1)), four-parameter (a,b,c,d) and eight-parameter ((a,J1),(b,J2),(c,J3),(d,J4)) potential-resolvent and identity-Yosida tier differences satisfy exact 4-step cyclic quadrangle cocycles, mixed parameter-regularizer commutator symmetry with 2*||J1(P^j x)-J2(P^j x)|| bounds, Dom(P^(r+2))/Dom(P^r) regularity, and three-hop Cauchy rate bounds, while across any FiveParameterFiveOperatorSystem (T,P,G,S(t),H(t)) at (a,b,c,d,e), cross-resolvent and cross-Yosida differences satisfy exact 5-step pentagon cocycles and four-hop bounds, bridged with the 21 SM/GUT/Higgs/Flavor/HVP/Baryon audit modules; (2) mixed initial-and-final (s1,s2; t1,t2) four-corner higher-power resolvent and Yosida plaquettes satisfy horizontal-vertical commutator symmetry, vertical and horizontal 3-time/3-trajectory plaquette stacking cocycles, 8-domain regularity with ((a^-1)^(r+2)+(c^-1)^(r+2))||f1||+((b^-1)^(r+2)+(d^-1)^(r+2))||f2|| and 2||f1||+2||f2|| bounds, and equal-final-time Dom(H(t)^(r+2)) + 10-domain regularity, bridged with the 10 SU(5)/SU(2)/HaarTwirl/Anomaly and 13 Choi/Petz/TraceDistance/SSA/Umegaki modules; (3) across all 5 Hamiltonians A in {T,P,G,S(t),H(t)}, four-factor multi-power (r,s,q,p) and four-parameter (a,b,d,e) Yosida compositions preserve Dom(A^n), commute with A^n, contract kthPowerGraphNormSq A n, and satisfy ((r/a + s/b + q/d + p/e)^2) * kthPowerGraphNormSq A (n+1) x defect bounds, bridged with the 7 Gaussian/LevelStatistics/QuantumAEP/TDesigns/Tomography and 16 Born/CPT/Wedderburn/NoBroadcasting/QMScope modules; (4) for mutually orthogonal projections (P1,P2,P_res) and Q-channel projector families {P_q} with weights in [w_min,w_max], spectral second moments are nonnegative and Bhatia-Davis / Popoviciu dispersion functionals factor as sum_i (w_max-w_i)(w_i-w_min)E(P_i x) and satisfy 0 <= BD <= ((w_max-w_min)/2)^2 E(x), bridged with the 10 BB84/CHSH/MerminN6/PironioAcin/Tsirelson and 7 ChargeSectors/FarField/MultiParticle/ConcreteMultiBody modules; (5) curved 4D causal bridge, census, exact regime, substrate counting, Capstone, ConditionalEinstein, Predictions, and TOECandidateRanking are synthesized with the two-time plaquette, Bhatia-Davis dispersion, and four-factor Yosida hierarchies. Direct fixed-N invariance J_N(DomP) subseteq DomP without R_P(a), single-resolvent R_{H(t)}(a)f in DomP for k<=0 without iteration or form pairing, trajectory-wide unbounded-momentum derivatives, general non-symmetric dynamical nonlinear 4D Einstein PDE evolution, full infinite-volume 4D continuum OS/Wightman QFT beyond the chamber/cluster reduction, first-principles derivation of absolute dimensionful scales, microscopic phase selection, controlled physical limits, and empirical identification remain open; the earlier phase/harmonic identification still requires revision. A physical TOE is not proved. This checkpoint adds93 theorems in15 modules, preserves3702 parent source/script hashes and adds17 for3719 total; exact root extends from9266 to9281 lines. All12 parent analytic artifacts and23 numerical files remain unchanged. Standard axioms only.'
PARENT = 'data/fifteen_checkpoint_complete_tier_one_synthesis_audit.json'
PARENT_SHA = '7b801ee822316b6644c3f80554c76a797d0133696544bb000ad2e1070b9ffbb5'
REPORT = 'data/sixteen_checkpoint_complete_tier_one_synthesis_audit.json'
SCRIPTS = ['scripts/sixteen_checkpoint_complete_tier_one_synthesis_audit.py',
           'scripts/verify_sixteen_checkpoint_complete_tier_one_synthesis.py']
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
    logs=overlay/'sixteen-checkpoint-complete-tier-one-synthesis-audit'
    logs.mkdir(exist_ok=False)
    assert sha(root/PARENT)==PARENT_SHA
    parent=json.loads((root/PARENT).read_text())
    hashes=dict(parent['source_sha256'])
    assert len(hashes)==3702 and all(sha(root/p)==h for p,h in hashes.items())
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
    assert len(text.splitlines())==9266+len(EXPECTED)
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
