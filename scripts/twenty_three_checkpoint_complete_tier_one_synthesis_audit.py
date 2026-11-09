#!/usr/bin/env python3
"""Check unconditional growing-Hamiltonian domain decomposition Dom(G) = Dom(K) cap Dom(P), unconditional operator core unconditionalCore = Dom(T) inf Dom(K) inf Dom(P) = Dom(T) inf Dom(G), seven-operator resolvent invariance, and simultaneous eight-norm convergence, eleven-parameter higher-power potential-resolvent radial-Yosida hendecagon cocycles and twenty-two-parameter Cauchy rate bounds, five-operator twelve-parameter higher-power dodecagon cocycles and common-domain Yosida cross-rate bounds, eleven-parameter hendecagon / twelve-parameter dodecagon / seven-operator resolvent invariance QQG / inflaton / slow-roll / dimension / gauge / Volterra bridge, nine-by-nine (8x8=64 elementary plaquettes) mixed initial-and-final higher-power resolvent plaquette grids and 2D Stokes boundary cancellation, unconditional resolvent half-clock norm bounds ||clockHalf(R_{H(t)}(a)f)|| <= sqrt(2/a)||f||, unconditional weak two-time resolvent continuity, and positive-vacuum (k>0) time-independent operator domains Dom(H(t)) cap Dom(G) = Dom(T) cap Dom(K) cap Dom(P) and two-time shifted-resolvent convergence R_{H(t)}(a)(H(s)x + a x) -> x with Wightman / OS / Clay continuum bridge, nine-by-nine plaquette Polymer / Borgs-Imbrie / Kotecky-Preiss / Weingarten / Volterra SO(10) bridge, arbitrary-order eleven-factor multi-power (r,s,q,p,l,u,v_pow,w_pow,z_pow,y_pow,x_pow) and eleven-parameter (a,b,d,e,c,f_param,g_param,h_param,i_param,j_param,k_param) Yosida composition defect calculus across all 5 Hamiltonians, eleven-factor Yosida quantum-velocity commutator error / Umegaki / Ando / Lieb / Golden-Thompson bridge, eleven-factor Yosida Stinespring / Petz / trace-distance / Quantum Stein / AEP bridge, Six-Vector Orthogonality Certificate M^T M = I_3 and (det M)^2 = 1 quantum-channel 3x3 Gram determinant conservation, unimodular scalar-zero lattice generation, short projective-root p=71 Householder reflection involution, and octahedral-to-Legendre elliptic j-invariant identity -256 * octahedralJ = legendreJ(-(j/i)^2), multi-channel Six-Vector Orthogonality / octonion Lambda^4(O) self-dual split (8 choose 4) = 70 = 35 + 35 / Ramanujan E_8-Eisenstein 1728 Delta = E_4^3 - E_6^2 modular discriminant / fifth-order Mock Theta Conjecture (MTC_0/MTC_1) factorization / DMZ BPS black-hole entropy / SM / GUT / CKM / PMNS / proton decay / dark matter bridge, multi-channel Six-Vector Orthogonality / short-root reflection Bell / CHSH / Tsirelson / phase faithfulness / no-go bridge, curved 4D nine-by-nine plaquette / Six-Vector Orthogonality / full 10-component symmetric 4x4 Hessian reconstruction from the conformal 4D Einstein tensor and polarization probes / off-diagonal shear Bianchi / on-shell stress-energy conservation bridge, curved 4D eleven-factor Yosida / short-root reflection / Mock Theta Conjecture / full 10-component Hessian reconstruction Capstone / ConditionalEinstein / spectral rigidity / unified forcing bridge, Twenty-Three-Checkpoint Complete Tier-One TOE Master Synthesis, and preserved evidence."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess

EXPECTED = {
    'KFCausalClockFloorHigherPowerPotentialResolventYosidaElevenParameterHendecagon': 10,
    'KFCausalClockFloorFiveOperatorTwelveParameterHigherPowerDodecagonCocycleAndYosida': 7,
    'KFCausalClockFloorElevenParameterHendecagonTwelveParameterDodecagonSevenOperatorResolventInvarianceBridge': 6,
    'KFCausalClockFloorNineByNineMixedInitialFinalHigherPowerResolventPlaquetteGrid': 7,
    'KFCausalClockFloorNineByNinePlaquetteTwoTimeWeakResolventContinuityPositiveVacuumDomainBridge': 6,
    'KFCausalClockFloorNineByNinePlaquettePolymerBorgsImbrieKoteckyPreissWeingartenVolterraBridge': 6,
    'KFCausalClockFloorArbitraryOrderElevenFactorMultiPowerYosidaComposition': 9,
    'KFCausalClockFloorElevenFactorYosidaVelocityCommutatorUmegakiAndoLiebGoldenThompsonBridge': 5,
    'KFCausalClockFloorElevenFactorYosidaStinespringPetzTraceDistanceQuantumSteinAEPBridge': 5,
    'KFCausalArbitrarySourceMultiChannelSixVectorOrthogonalityCertificateShortRootHouseholderReflectionAndOctahedralLegendreJInvariant': 6,
    'KFCausalMultiChannelSixVectorOrthogonalityOctonionE8EisensteinMathlibModularFormMockThetaConjectureSMGUTBridge': 5,
    'KFCausalMultiChannelSixVectorOrthogonalityShortRootReflectionBellCHSHTsirelsonPhaseFaithfulnessNoGoBridge': 5,
    'KFCausalCurved4DNineByNinePlaquetteFullTenComponentSymmetricHessianReconstructionOffDiagonalShearBianchiEinsteinBridge': 5,
    'KFCausalCurved4DElevenFactorYosidaShortRootReflectionMockThetaCapstoneConditionalEinsteinSpectralRigidityUnifiedForcingBridge': 5,
    'KFCausalTOETwentyThreeCheckpointCompleteTierOneMasterSynthesis': 6,
}
EXTRA_ANALYTIC = {}
SCOPE = 'Unconditional growing-Hamiltonian domain decomposition Dom(G) = Dom(K) cap Dom(P), unconditional operator core unconditionalCore = Dom(T) inf Dom(K) inf Dom(P) = Dom(T) inf Dom(G), seven-operator resolvent invariance, and simultaneous eight-norm convergence on unconditionalCore, eleven-parameter (a,b,c,d,e,f_param,g_param,h_param,i_param,j_param,k_param) higher-power potential-resolvent radial-Yosida cyclic hendecagon cocycles and twenty-two-parameter ((a,J1),...,(k_param,J11)) Cauchy rate bounds, five-operator (T,P,G,S,H) twelve-parameter (a,b,c,d,e,f_param,g_param,h_param,i_param,j_param,k_param,l_param) higher-power cross-resolvent dodecagon cocycles and common-domain Yosida cross-rate bounds, eleven-parameter hendecagon / twelve-parameter dodecagon / seven-operator resolvent invariance QQG / inflaton / slow-roll / dimension / gauge / Volterra bridge, nine-by-nine (s1,s2,s3,s4,s5,s6,s7,s8,s9)x(t1,t2,t3,t4,t5,t6,t7,t8,t9) (8x8=64 elementary plaquettes) mixed initial-and-final higher-power resolvent and identity plaquette grids with exact 2D Stokes / Green boundary cancellation across all 8 time-independent and 10 equal-outer-final-time domains, unconditional resolvent half-clock norm bounds ||clockHalf(R_{H(t)}(a)f)|| <= sqrt(2/a)||f||, unconditional weak two-time resolvent continuity <f, (R_{H(s)}(a) - R_{H(t)}(a))g> -> 0, and positive-vacuum (k>0) time-independent operator domains Dom(H(t)) cap Dom(G) = Dom(T) cap Dom(K) cap Dom(P) and two-time shifted-resolvent convergence R_{H(t)}(a)(H(s)x + a x) -> x with Wightman / OS / Clay continuum bridge, nine-by-nine plaquette Polymer / Borgs-Imbrie / Kotecky-Preiss / Weingarten / Volterra SO(10) bridge, arbitrary-order eleven-factor multi-power (r,s,q,p,l,u,v_pow,w_pow,z_pow,y_pow,x_pow) and eleven-parameter (a,b,d,e,c,f_param,g_param,h_param,i_param,j_param,k_param) Yosida composition defect calculus across all 5 Hamiltonians, eleven-factor Yosida quantum-velocity commutator error / Umegaki / Ando / Lieb / Golden-Thompson bridge, eleven-factor Yosida Stinespring / Petz / trace-distance / Quantum Stein / AEP bridge, Six-Vector Orthogonality Certificate M^T M = I_3 and (det M)^2 = 1 quantum-channel 3x3 Gram determinant conservation Det3_Q(M(w1,w2,w3), x) = Det3_Q(w1,w2,w3,x), unimodular scalar-zero lattice generation, short projective-root p=71 Householder reflection involution reflectiveNorm71(R_71(x,y,z)) = reflectiveNorm71(x,y,z), and octahedral-to-Legendre elliptic j-invariant identity -256 * octahedralJ(i,j,k) = legendreJ(-(j/i)^2) on i^2+j^2+k^2=0, multi-channel Six-Vector Orthogonality / octonion Lambda^4(O) self-dual split (8 choose 4) = 70 = 35 + 35 / Ramanujan E_8-Eisenstein 1728 Delta = (1 + 240 s_3)^3 - (1 - 504 s_5)^2 modular discriminant / fifth-order Mock Theta Conjecture (MTC_0/MTC_1) factorization / DMZ BPS black-hole microstate entropy / Bekenstein-Hawking saturation / SM / GUT / CKM / PMNS / proton decay / dark matter bridge, multi-channel Six-Vector Orthogonality / short-root reflection Bell / CHSH / Tsirelson / phase faithfulness / no-go bridge, curved 4D nine-by-nine plaquette / Six-Vector Orthogonality / full 10-component symmetric 4x4 Hessian reconstruction reconstructHessianFromEinstein4D(fullEinsteinTensor4D H) = H and reconstructHessianFromProbes4D(fullEinsteinTensor4D H) = H / off-diagonal shear Bianchi channel cancellation / on-shell stress-energy conservation bridge, curved 4D eleven-factor Yosida / short-root reflection / Mock Theta Conjecture / full 10-component Hessian reconstruction Capstone / ConditionalEinstein / spectral rigidity / unified forcing bridge, and Twenty-Three-Checkpoint Complete Tier-One TOE Master Synthesis. Specifically, on 0<epsilon,h!=0,abs(h)<=pi*epsilon/3 and for all real m,g,k,s,t: (1) Dom(G) = Dom(K) cap Dom(P) and unconditionalCore = Dom(T) inf Dom(K) inf Dom(P) = Dom(T) inf Dom(G) hold unconditionally for all real m,g,k, R_G(a) preserves all 7 operator domains and J_N converges simultaneously in all 8 operator norms on unconditionalCore, while eleven-parameter (a..k_param) and twenty-two-parameter ((a,J1),...,(k_param,J11)) potential-resolvent and identity-Yosida tier differences satisfy exact 11-step cyclic hendecagon cocycles, Dom(P^(r+2))/Dom(P^r) regularity, and ten-hop Cauchy rate bounds, and across any TwelveParameterFiveOperatorSystem (T,P,G,S(t),H(t)) at (a..l_param), cross-resolvent and cross-Yosida differences satisfy exact 12-step dodecagon cocycles and eleven-hop bounds; (2) for all real m,g,k,t,s in R and a>0, R_{H(t)}(a)f in Dom(clockHalf) with ||clockHalf(R_{H(t)}(a)f)|| <= sqrt(2/a)||f|| and |<f, (R_{H(s)}(a) - R_{H(t)}(a))g>| <= |e^{2t} - e^{2s}| (2 e^{-(t+s)} a^{-1} ||f|| ||g||), and for k>0, Dom(H(t)) cap Dom(G) = Dom(T) cap Dom(K) cap Dom(P) with H(s)x -> H(t)x and R_{H(t)}(a)(H(s)x + a x) -> x as s -> t, while on a 9x9 grid (s1..s9)x(t1..t9), the 8x8 sum of 64 elementary mixed initial-and-final higher-power resolvent and identity plaquettes satisfies exact 2D Stokes / Green boundary cancellation to the outer plaquette (s1,s9; t1,t9) canceling 49 interior vertices and 112 interior edges, 9-initial and 9-final nonagon cocycles, 8-domain regularity, and equal-outer-final-time Dom(H(t)^(r+2)) + 10-domain regularity; (3) across all 5 Hamiltonians A in {T,P,G,S(t),H(t)}, eleven-factor multi-power (r,s,q,p,l,u,v_pow,w_pow,z_pow,y_pow,x_pow) and eleven-parameter (a,b,d,e,c,f_param,g_param,h_param,i_param,j_param,k_param) Yosida compositions preserve Dom(A^n), commute with A^n, contract kthPowerGraphNormSq A n, and satisfy ((r/a + s/b + q/d + p/e + l/c + u/f_param + v_pow/g_param + w_pow/h_param + z_pow/i_param + y_pow/j_param + x_pow/k_param)^2) * kthPowerGraphNormSq A (n+1) x defect bounds; (4) any 3x3 matrix M preserving the Euclidean norm on the 6 Ramanujan vectors p*(1,1,1), p*(-1,1,1), p*(1,-1,1), p*(1,1,-1), p*(2,1,1), p*(1,2,1) (p != 0) satisfies M^T M = I_3, (det M)^2 = 1, and exact quantum-channel 3x3 Gram determinant conservation Det3_Q(M(w1,w2,w3), x) = Det3_Q(w1,w2,w3,x), paired with unimodular scalar-zero lattice generation, short projective-root p=71 Householder reflection involution, octahedral-to-Legendre elliptic j-invariant identity -256 * octahedralJ(i,j,k) = legendreJ(-(j/i)^2), octonion 4-form split (8 choose 4) = 70 = 35 + 35, and fifth-order Mock Theta Conjecture (MTC_0/MTC_1) factorization; (5) all 10 independent components (4 diagonal + 6 off-diagonal pairs) of any symmetric 4x4 conformal Hessian H are reconstructed exactly via reconstructHessianFromEinstein4D(fullEinsteinTensor4D H) = H, reconstructHessianFromRicciAndScalar4D(fullRicciTensor4D H, fullScalarCurvature4D H) = H, and reconstructHessianFromProbes4D(fullEinsteinTensor4D H) = H with exact diagonal/off-diagonal Bianchi channel cancellation and on-shell stress-energy conservation, synthesized with 100% (659/659) direct non-Audit module coverage. Direct fixed-N strong-operator invariance J_N(DomP) subseteq DomP without R_P(a) (beyond the proved four-domain invariance, two-sided potential-pairing domination, Dom(G) radial-Yosida contraction/rate, Dom(H(t))/Dom(S(t)) radial-Yosida quadratic lower bound and rate, unconditional Dom(T) invariance/commutator/core, and unconditional Dom(G) = Dom(K) cap Dom(P) seven-operator resolvent invariance), single-resolvent R_{H(t)}(a)f in DomP for k<=0 without iteration (beyond the proved 14-domain regularity, unconditional R_G(a)f in DomP, 5-way DomP <-> DomG <-> DomT equivalence, shifted-source residual-resolvent criterion, static-residual second resolvent identity, unconditional weak two-time resolvent continuity, and positive-vacuum k>0 domain stability), trajectory-wide unbounded-momentum derivatives beyond the energy-controlled H(t)-domain quantum-velocity commutator bound, general non-conformal non-symmetric dynamical nonlinear 4D Einstein PDE evolution beyond the full 10-component symmetric 4x4 conformal Hessian reconstruction, full infinite-volume 4D continuum OS/Wightman QFT beyond the chamber/cluster reduction, first-principles derivation of absolute dimensionful scales, microscopic phase selection, controlled physical limits, and empirical identification remain open; the earlier phase/harmonic identification still requires revision. A physical TOE is not proved. This checkpoint adds93 theorems in15 modules, preserves3821 parent source/script hashes and adds17 for3838 total; exact root extends from9371 to9386 lines. All12 parent analytic artifacts and23 numerical files remain unchanged. Standard axioms only.'
PARENT = 'data/twenty_two_checkpoint_complete_tier_one_synthesis_audit.json'
PARENT_SHA = '46bfe977770c9bb6226448cf82031ee7efe078104375fe3cb18f6cffa1aa56ab'
REPORT = 'data/twenty_three_checkpoint_complete_tier_one_synthesis_audit.json'
SCRIPTS = ['scripts/twenty_three_checkpoint_complete_tier_one_synthesis_audit.py',
           'scripts/verify_twenty_three_checkpoint_complete_tier_one_synthesis.py']
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
    logs=overlay/'twenty-three-checkpoint-complete-tier-one-synthesis-audit'
    logs.mkdir(exist_ok=False)
    assert sha(root/PARENT)==PARENT_SHA
    parent=json.loads((root/PARENT).read_text())
    hashes=dict(parent['source_sha256'])
    assert len(hashes)==3821 and all(sha(root/p)==h for p,h in hashes.items())
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
    assert len(text.splitlines())==9371+len(EXPECTED)
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
