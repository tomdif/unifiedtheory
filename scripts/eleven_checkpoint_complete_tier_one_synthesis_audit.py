#!/usr/bin/env python3
"""Check higher-power potential-resolvent radial-Yosida cores, five-operator higher-power resolvent and Yosida difference identities, Standard Model individual fermion mass / down-type hierarchy / Koide relation / GUT scale M_X bridge, two-time evolved iterated-resolvent trajectory regularity across all 10 first/second-power domains, explicit Wilson lattice action / Feshbach Schur-complement / Volterra chamber-bath decoupling / SO(10) Haar trace bridge, AQFT Bisognano-Wichmann / Reeh-Schlieder / algebraic CPT / chamber Poincare bridge, higher-power second- and third-order Yosida 3-tier graph convergence across all 5 Hamiltonians, quantum foundations Wigner / Gleason / Bell CHSH / Tsirelson operator bridge, holographic Ryu-Takayanagi / unitary Page curve / Hayden-Preskill / AMPS firewall monogamy bridge, arbitrary-source antipodal neutral-cancellation counterexample and sharp two-sided Gram/triangle bounds, discrete Ambrose-Singer holonomy and 4D Gauss-Bonnet rank-5 vanishing multi-packet bridge, Einstein-Hilbert gravitational scale fixing and discrete causal-set holography multi-packet synthesis, curved 4D Hawking-Penrose singularity focusing and discrete/general Malament causal-to-conformal metric uniqueness bridge, Christodoulou-Ruffini irreducible mass and universal Bekenstein bound black-hole mechanics bridge, Eleven-Checkpoint Complete Tier-One TOE Master Synthesis, and preserved evidence."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess

EXPECTED = {
    'KFCausalClockFloorHigherPowerPotentialResolventYosidaCore': 36,
    'KFCausalClockFloorFiveOperatorHigherPowerResolventDifference': 36,
    'KFCausalClockFloorSMIndividualFermionMassesKoideMXBridge': 35,
    'KFCausalClockFloorEvolvedIteratedResolventTrajectoryRegularity': 32,
    'KFCausalClockFloorWilsonActionFeshbachVolterraHaarBridge': 32,
    'KFCausalClockFloorAQFTBisognanoWichmannReehSchliederCPTBridge': 32,
    'KFCausalClockFloorHigherPowerSecondOrderGraphConvergence': 33,
    'KFCausalClockFloorQuantumFoundationsWignerGleasonBellTsirelsonBridge': 33,
    'KFCausalClockFloorHolographicRyuTakayanagiPageCurveFirewallBridge': 33,
    'KFCausalArbitrarySourceSharpNeutralCancellationCounterexampleAndBounds': 39,
    'KFCausalDiscreteAmbroseSingerHolonomyMultiPacketBridge': 38,
    'KFCausalEinsteinHilbertScaleFixingMultiPacketSynthesis': 38,
    'KFCausalCurved4DHawkingPenroseSingularityMalamentCausalBridge': 33,
    'KFCausalCurved4DChristodoulouIrreducibleMassBlackHoleMechanicsBridge': 33,
    'KFCausalTOEElevenCheckpointCompleteTierOneMasterSynthesis': 34,
}
EXTRA_ANALYTIC = {}
SCOPE = 'Higher-power potential-resolvent radial-Yosida cores, five-operator higher-power resolvent and Yosida difference identities, Standard Model individual fermion mass / down-type hierarchy / Koide relation / GUT scale M_X bridge, two-time evolved iterated-resolvent trajectory regularity across all 10 first/second-power domains, explicit Wilson lattice action / Feshbach Schur-complement / Volterra chamber-bath decoupling / SO(10) Haar trace bridge, AQFT Bisognano-Wichmann / Reeh-Schlieder / algebraic CPT / chamber Poincare bridge, higher-power second- and third-order Yosida 3-tier graph convergence across all 5 Hamiltonians, quantum foundations Wigner / Gleason / Bell CHSH / Tsirelson operator bridge, holographic Ryu-Takayanagi / unitary Page curve / Hayden-Preskill / AMPS firewall monogamy bridge, arbitrary-source antipodal neutral-cancellation counterexample and sharp two-sided Gram/triangle bounds, discrete Ambrose-Singer holonomy and 4D Gauss-Bonnet rank-5 vanishing multi-packet bridge, Einstein-Hilbert gravitational scale fixing and discrete causal-set holography multi-packet synthesis, curved 4D Hawking-Penrose singularity focusing and discrete/general Malament causal-to-conformal metric uniqueness bridge, Christodoulou-Ruffini irreducible mass and universal Bekenstein bound black-hole mechanics bridge, and Eleven-Checkpoint Complete Tier-One TOE Master Synthesis. Specifically, on 0<epsilon,h!=0,abs(h)<=pi*epsilon/3 and for all real m,g,k,s,t: (1) for every r,N in N and a>0, higherPowerPotentialResolventYosidaState a N r f := R_P(a)^r(J_N f) lies in Dom(P^r) (and in DomK and DomG on abs(h)<=pi*epsilon/4 for r>=1) with two-parameter and two-order commutativity, while across all 5 Hamiltonians A in {T,P,G,S(t),H(t)}, (r+1)-fold resolvent differences R_A(a)^(r+1) f - R_A(b)^(r+1) f belong to Dom(A^(r+2)) (gaining an extra power of regularity, with 10-domain membership for H(t)) and Yosida identity powers satisfy norm(a^r R_A(a)^r x - b^r R_A(b)^r x) <= r*(a^(-1)+b^(-1))*norm(Ax) on Dom(A), instantiated via FermionMassesIndividual, DownTypeHierarchy, KoideRelation, and MXFromRGRunning at J_4 ratios (5+/-sqrt(7))/18, topMass(v)=(7/10)*v, bTauEnhancement=7/3, Koide Q in (0.666,0.667), and RG e-foldings L_A in (22,23), L_B=(7/3)*L_A in (52,53); (2) evolvedIteratedHamiltonianResolvent s t a b f := U(s,t)(R_{H(s)}(a)R_{H(s)}(b)f) satisfies 7-domain form/clock trajectory regularity and two-sided exponential trajectory bounds while iteratedResolventOfEvolvedState s t a b f := R_{H(t)}(a)R_{H(t)}(b)(U(s,t)f) lies unconditionally in all 10 first/second-power domains, connected via Build1..Build6, Clay_HaarTraceIdentity, Clay3_PhysicalZ, BisognanoWichmann, ReehSchlieder, CPTFromKP, and Clay_W1_ContinuousPoincare to the 6x6 Volterra Wilson Hamiltonian H_W (H_PP=J_4, H_PQ=0, H_QQ=mu_bath*I_3), SO(10) Haar trace integral(reTrace)=0, KMS reciprocity beta_BW(a)*T_U(a)=1, Unruh-Hawking T_U(1/(4M))=T_H(M)=1/(8*pi*M), Reeh-Schlieder cyclicity, and K/P-derived CPT invariance; (3) for every x in Dom(A^2) and r>=1, a^r R_A(a)^r x in Dom(A^2) commutes with A and A^2 and converges simultaneously in 3 tiers (Hilbert, Graph(A), Graph(A^2)) with O(r*a^(-1)*norm(A^3 x)) rate on Dom(A^3) across all 5 Hamiltonians, connected via WignerTheorem, GleasonTheorem, BellTheorem, TsirelsonBound, RyuTakayanagi, PageCurve, HaydenPreskill, and AMPSFirewall to Wigner ray symmetries, Gleason frame measures, Bell CHSH 2<2*sqrt(2) and Tsirelson saturation, Ryu-Takayanagi and Page-curve entropy bounds, Hayden-Preskill decoupling recovery, and AMPS CKW monogamy exclusion; (4) antipodal non-zero sources b=![1,-1] with equal weights w=![1,1] and identical normalized packets P_0=P_1=psi yield an exact neutral-source constant-mode cancellation sum_i w_i b_i P_i = 0 while quadratic mode k=1 equals 2*psi != 0, proving that constant-mode dominance or common sources are structurally required alongside sharp two-sided triangle bounds across all 6 packet maps, connected via DiscreteAmbroseSinger, GaussBonnet4D, EinsteinHilbertScaleFixing, and DiscreteHolography to holonomySubgroup=closure(basedCurvatureSet), rank-5 generalized Kronecker vanishing in 4D, discretenessLength(c,G)^2=16*pi*c*G, and discrete 4D area-law holography entropy_bound(4,m)<m^4 for m>=9; (5) HawkingPenroseSingularity, DiscreteMalament, GeneralMalament, ChristodoulouIrreducibleMass, and BekensteinBound prove Raychaudhuri null focusing raychaudhuri_rhs <= -(1/2)*theta^2, finite conjugate-point time 0<conjugatePointTime(theta_0)=-2/theta_0<-3/theta_0, concrete Schwarzschild interior trapped surfaces (0<r<2M) with conjugate times 2*r^2/(2M+/-r), 1+1 and (n+1)-dimensional Malament causal-to-conformal metric uniqueness paired with 4D Weyl conformal invariance weylTensor4D(conformalPart)=0, Christodoulou-Ruffini mass M^2=M_irr^2+J^2/(4*M_irr^2) with Penrose ceiling Delta E <= (1-1/sqrt(2))*M, and Schwarzschild saturation S_BH=bekensteinBound(2M,M)=4*pi*M^2 with horizon invariant K(2M)*bekensteinBound(2M,M)^2=12*pi^2. Direct fixed-N invariance J_N(DomP) subseteq DomP without R_P(a), single-resolvent R_{H(t)}(a)f in DomP for k<=0 without iteration or form pairing, trajectory-wide unbounded-momentum derivatives, general non-symmetric dynamical nonlinear 4D Einstein PDE evolution, full infinite-volume 4D continuum OS/Wightman QFT beyond the chamber/cluster reduction, first-principles derivation of absolute dimensionful scales, microscopic phase selection, controlled physical limits, and empirical identification remain open; the earlier phase/harmonic identification still requires revision. A physical TOE is not proved. This checkpoint adds517 theorems in15 modules, preserves3617 parent source/script hashes and adds17 for3634 total; exact root extends from9191 to9206 lines. All12 parent analytic artifacts and23 numerical files remain unchanged. Standard axioms only.'
PARENT = 'data/grand_unified_ten_checkpoint_synthesis_audit.json'
PARENT_SHA = 'c6cf5660bec1137f34ad978a3e7d678e40770c88434b0ca6a8ae4ac650525e6b'
REPORT = 'data/eleven_checkpoint_complete_tier_one_synthesis_audit.json'
SCRIPTS = ['scripts/eleven_checkpoint_complete_tier_one_synthesis_audit.py',
           'scripts/verify_eleven_checkpoint_complete_tier_one_synthesis.py']
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
    logs=overlay/'eleven-checkpoint-complete-tier-one-synthesis-audit'
    logs.mkdir(exist_ok=False)
    assert sha(root/PARENT)==PARENT_SHA
    parent=json.loads((root/PARENT).read_text())
    hashes=dict(parent['source_sha256'])
    assert len(hashes)==3617 and all(sha(root/p)==h for p,h in hashes.items())
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
    assert len(text.splitlines())==9191+len(EXPECTED)
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
