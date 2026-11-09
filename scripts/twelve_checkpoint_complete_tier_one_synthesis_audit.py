#!/usr/bin/env python3
"""Check higher-power potential-resolvent radial-Yosida 3-tier convergence, five-operator higher-power second-resolvent and cross-resolvent difference identities, Standard Model Higgs trilinear / electroweak scale / CKM one-loop / generation stability bridge, two-time evolved higher-power resolvent trajectory regularity across all 10 first/second-power domains, BRST / Schwinger-Dyson / color-dressing / Poisson lift bridge, open quantum Lindblad / KMS detailed balance / decoherence / GNS reconstruction bridge, higher-power arbitrary-order Yosida (r+2)-tier graph convergence across all 5 Hamiltonians, quantum information von Neumann entropy / SSA / Araki-Lieb / Petz recovery bridge, quantum contextuality Kochen-Specker / PBR psi-ontic / no-cloning / no-broadcasting / no-signaling bridge, arbitrary-source multi-mode orthogonal decomposition and response bounds, gauge-selection / adjoint obstruction / hypercharge exile multi-packet bridge, sharpened SO(10) / quark-lepton unification / Freudenthal-Tits magic square multi-packet bridge, curved 4D BF source dressing / metric-gauge coupling / minimal coupling bridge, curved 4D Lohmiller-Slotine contraction / Lieb-Robinson / Margolus-Levitin / Mandelstam-Tamm quantum speed-limit bridge, Twelve-Checkpoint Complete Tier-One TOE Master Synthesis, and preserved evidence."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess

EXPECTED = {
    'KFCausalClockFloorHigherPowerPotentialResolventYosidaThreeTierConvergence': 43,
    'KFCausalClockFloorFiveOperatorHigherPowerSecondResolventCrossIdentity': 40,
    'KFCausalClockFloorSMHiggsTrilinearElectroweakScaleCKMOneLoopBridge': 35,
    'KFCausalClockFloorTwoTimeEvolvedHigherPowerResolventRegularity': 32,
    'KFCausalClockFloorBRSTSchwingerColorDressingPoissonLiftBridge': 32,
    'KFCausalClockFloorOpenQuantumLindbladKMSDecoherenceGNSBridge': 32,
    'KFCausalClockFloorHigherPowerArbitraryOrderGraphConvergence': 33,
    'KFCausalClockFloorQuantumInformationEntropySSAArakiLiebPetzBridge': 33,
    'KFCausalClockFloorQuantumContextualityKochenSpeckerPBRNoGoBridge': 33,
    'KFCausalArbitrarySourceMultiModeOrthogonalDecompositionAndResponseBounds': 39,
    'KFCausalGaugeSelectionAdjointObstructionHyperchargeExileMultiPacketBridge': 39,
    'KFCausalSO10SharpenedQuarkLeptonUnificationMagicSquareMultiPacketBridge': 39,
    'KFCausalCurved4DBFSourceDressingMetricGaugeCouplingMinimalBridge': 33,
    'KFCausalCurved4DLohmillerSlotineContractionLiebRobinsonSpeedLimitBridge': 33,
    'KFCausalTOETwelveCheckpointCompleteTierOneMasterSynthesis': 33,
}
EXTRA_ANALYTIC = {}
SCOPE = 'Higher-power potential-resolvent radial-Yosida 3-tier convergence, five-operator higher-power second-resolvent and cross-resolvent difference identities, Standard Model Higgs trilinear / electroweak scale / CKM one-loop / generation stability bridge, two-time evolved higher-power resolvent trajectory regularity across all 10 first/second-power domains, BRST / Schwinger-Dyson / color-dressing / Poisson lift bridge, open quantum Lindblad / KMS detailed balance / decoherence / GNS reconstruction bridge, higher-power arbitrary-order Yosida (r+2)-tier graph convergence across all 5 Hamiltonians, quantum information von Neumann entropy / SSA / Araki-Lieb / Petz recovery bridge, quantum contextuality Kochen-Specker / PBR psi-ontic / no-cloning / no-broadcasting / no-signaling bridge, arbitrary-source multi-mode orthogonal decomposition and response bounds, gauge-selection / adjoint obstruction / hypercharge exile multi-packet bridge, sharpened SO(10) / quark-lepton unification / Freudenthal-Tits magic square multi-packet bridge, curved 4D BF source dressing / metric-gauge coupling / minimal coupling bridge, curved 4D Lohmiller-Slotine contraction / Lieb-Robinson / Margolus-Levitin / Mandelstam-Tamm quantum speed-limit bridge, and Twelve-Checkpoint Complete Tier-One TOE Master Synthesis. Specifically, on 0<epsilon,h!=0,abs(h)<=pi*epsilon/3 and for all real m,g,k,s,t: (1) for every r>=1 and a>0, higherPowerPotentialResolventYosidaState a N r f := R_P(a)^r(J_N f) converges in 3 tiers (Hilbert, P-graph, P^2-graph) to R_P(a)^r f as N->infinity with exact resolvent-power defects, while across all 5 Hamiltonians A in {T,P,G,S(t),H(t)}, (r+1)-fold resolvent differences telescope via cross-products R_A(a)^k R_A(b)^(r-k), belong to Dom(A^(r+2)), and satisfy cross-resolvent difference identities in Dom(A^(j+k+2)) alongside Yosida-power Cauchy bounds norm(a^r R_A(a)^r x - b^r R_A(b)^r x) <= r*(a^(-1)+b^(-1))*norm(Ax) on Dom(A) and norm(A^j(a^r R_A(a)^r x - b^r R_A(b)^r x)) <= r*(a^(-1)+b^(-1))*norm(A^(j+1)x) on Dom(A^(j+1)), instantiated via HiggsTrilinear, ElectroweakScale, CKMOneLoop, and GenerationStability at lambda_3/(m_H v)=1/2, lambda_4=1/8, v(m_P)=m_P*exp(-16*pi^2*7/22), one-loop CKM hierarchies, and N_g=3 asymptotic freedom b_3=7>0; (2) evolvedHigherPowerHamiltonianResolvent s t a r f := U(s,t)(R_{H(s)}(a)^(r+2)f) satisfies 7-domain form/clock trajectory regularity and two-sided exponential trajectory bounds while higherPowerResolventOfEvolvedState s t a r f := R_{H(t)}(a)^(r+2)(U(s,t)f) lies unconditionally in all 10 first/second-power domains and in Dom(H(t)^(r+2)), connected via BRSTCohomology, SchwingerFunctions, ColorDressing, PoissonAlgebraLift, LindbladMasterEquation, KMSCondition, Decoherence, and GNSConstruction to Q_BRST^2=0, OS0-OS4 Euclidean Schwinger functions, SU(3) color dressing, canonical Poisson brackets, GKSL Lindblad trace preservation, KMS detailed balance gamma_down/gamma_up=exp(beta*omega), off-diagonal decoherence decay, and GNS Hilbert states; (3) for every r,k>=1 and x in Dom(A^r), a^k R_A(a)^k x in Dom(A^r) commutes with A^j (j<=r) and converges simultaneously across all (r+1) graph tiers j=0..r with O(k*a^(-1)*norm(A^(j+1)x)) rate on Dom(A^(r+1)) across all 5 Hamiltonians, connected via VonNeumannEntropy, StrongSubadditivity, ArakiLiebInequality, PetzRecoveryMap, KochenSpecker, PBRTheorem, NoCloning, NoBroadcasting, and NoSignaling to S(rho)>=0, SSA I(A:C|B)>=0, Araki-Lieb |S_A-S_B|<=S_{AB}, Petz recovery fidelity, Kochen-Specker 18-vector parity obstruction, PBR psi-ontic disjointness, and no-cloning / no-broadcasting / no-signaling theorems; (4) arbitrary-source multi-packet superpositions admit an exact constant-plus-fluctuation decomposition P_i = c_i psi + R_i with <psi,R_i>=0 and Pythagorean norm identity norm(sum_i w_i b_i P_i)^2 = |sum_i w_i b_i c_i|^2 + norm(sum_i w_i b_i R_i)^2 yielding unconditional lower bounds >= |sum_i w_i b_i c_i| across all 6 packet maps, connected via GaugeGroupSelection, AdjointObstruction, HyperchargeExile, SO10Unification, QuarkLeptonUnification, and MagicSquare to N_c=3, N_w=2 uniqueness, adjoint chirality obstruction, hypercharge exile to U(1), sharpened SO(10) Spin(10) 16=1+10+5bar branching, and Freudenthal-Tits magic square dim(so(10))=45; (5) BFSourceDressing, MetricGaugeCoupling, MinimalCoupling, LohmillerSlotineContraction, LiebRobinsonBound, and QuantumSpeedLimit prove exact 4D BF source dressing and trace-free stress-energy T^mu_mu=0, exact covariant minimal-coupling commutators [D_mu,D_nu]=F_{mu nu}, Lohmiller-Slotine exponential contraction V(t)<=V(0)*exp(-2*lambda*t) with unique fixed point, Lieb-Robinson causal cone suppression exp(-mu*(d-v_LR*|t|)), and unified Margolus-Levitin / Mandelstam-Tamm orthogonalization time T_orth >= max(pi/(2*Delta E), pi/(2*E)). Direct fixed-N invariance J_N(DomP) subseteq DomP without R_P(a), single-resolvent R_{H(t)}(a)f in DomP for k<=0 without iteration or form pairing, trajectory-wide unbounded-momentum derivatives, general non-symmetric dynamical nonlinear 4D Einstein PDE evolution, full infinite-volume 4D continuum OS/Wightman QFT beyond the chamber/cluster reduction, first-principles derivation of absolute dimensionful scales, microscopic phase selection, controlled physical limits, and empirical identification remain open; the earlier phase/harmonic identification still requires revision. A physical TOE is not proved. This checkpoint adds529 theorems in15 modules, preserves3634 parent source/script hashes and adds17 for3651 total; exact root extends from9206 to9221 lines. All12 parent analytic artifacts and23 numerical files remain unchanged. Standard axioms only.'
PARENT = 'data/eleven_checkpoint_complete_tier_one_synthesis_audit.json'
PARENT_SHA = '55728148c5840430e1946ad25f72f7b501f702e0187feb75dde57b0c42338473'
REPORT = 'data/twelve_checkpoint_complete_tier_one_synthesis_audit.json'
SCRIPTS = ['scripts/twelve_checkpoint_complete_tier_one_synthesis_audit.py',
           'scripts/verify_twelve_checkpoint_complete_tier_one_synthesis.py']
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
    logs=overlay/'twelve-checkpoint-complete-tier-one-synthesis-audit'
    logs.mkdir(exist_ok=False)
    assert sha(root/PARENT)==PARENT_SHA
    parent=json.loads((root/PARENT).read_text())
    hashes=dict(parent['source_sha256'])
    assert len(hashes)==3634 and all(sha(root/p)==h for p,h in hashes.items())
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
    assert len(text.splitlines())==9206+len(EXPECTED)
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
