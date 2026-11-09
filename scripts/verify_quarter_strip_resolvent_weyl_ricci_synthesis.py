#!/usr/bin/env python3
"""Independently verify the quarter-strip-resolvent-weyl-ricci-synthesis audit and preserved evidence."""
import argparse
import hashlib
import json
from pathlib import Path
import re

EXPECTED = {
    'KFCausalClockFloorRadialYosidaQuarterStripSector': 30,
    'KFCausalClockFloorPotentialRadialYosidaAccretivity': 20,
    'KFCausalClockFloorPotentialResolventRadialRegularity': 19,
    'KFCausalClockFloorPotentialGrowingCore': 13,
    'KFCausalClockFloorStaticResolventRadialCommutator': 35,
    'KFCausalClockFloorStaticGaussianRadialSmoothing': 48,
    'KFCausalClockFloorResidualResolventRadialRootRegularity': 34,
    'KFCausalClockFloorPositiveVacuumHamiltonianGaussianCore': 13,
    'KFCausalClockFloorTwoTimeFormEvolutionIsomorphism': 27,
    'KFCausalClockFloorEvolvedResolventRegularity': 9,
    'KFCausalReciprocalNeutralArbitrarySourceMassVacuumZeroResponse': 69,
    'KFCausalCommonComplexAffineNeutralPolynomialDecomposition': 48,
    'KFCausalFiniteThreeOperatorEvolvedDomination': 30,
    'KFCausalCurved4DLinearizedMetricDecomposition': 45,
    'KFCausalCurved4DLinearizedWeylRicciSplit': 36,
    'KFCausalCurved4DGeneralProbeCurvatureExtraction': 10,
}
EXTRA_ANALYTIC = {}
SCOPE = 'Unconditional quarter-strip radial-Yosida pi/4-sectoriality and square-accretivity, unconditional potential-resolvent radial/growing regularity and DomG=DomP intersect DomKr operator-graph core for P, unconditional static resolvent-radial commutator identity and joint clock-Gaussian/radial-resolvent 6-domain smoothing, unconditional residual-resolvent preservation of Dom(Kr^(1/2)), positive-vacuum and unconditional clock-core multi-operator Gaussian graph approximation, two-time form-evolution Banach-space isomorphism and evolved resolvent regularity, arbitrary-source 3-channel (mass,quartic,vacuum) response decomposition, common-complex affine neutral-polynomial decomposition, finite superposition evolved 5-channel energy domination, and general 4D linearized Lorentzian metric conformal/traceless and Weyl-Ricci-Scalar (Kulkarni-Nomizu) curvature decomposition. Specifically, on the complex quarter-strip abs(q.im)<=pi*epsilon/8 (covering the half-shift line y=-h/2 when abs(h)<=pi*epsilon/4, including abs(h)<=pi*epsilon/6), radialComplex, multiplier, family, 1-N^(-1)*multiplier, symbol, and line satisfy abs(Im zeta)<=Re zeta and Re(zeta^2)>=0, yielding quadratic operator accretivity Re<f,M_N^((-h/2))(M_N^((-h/2))f)>>=0 and Re<f,J_N^((-h/2))(J_N^((-h/2))f)>>=0 on Hilbert, unconditional linear and quadratic radial-Yosida and radial-resolvent accretivity Re<Px,M_N(M_N x)>>=0 and Re<Px,J_N(J_N x)>>=0 on DomP for all real m,g,k, unconditional contraction norm(M_N(R_P(a)f))<=a^(-1)*norm(M_N f) and norm(J_N(R_P(a)f))<=a^(-1)*norm(J_N f) for a>0, unconditional mapping R_P(a)(DomKr) subseteq DomG=DomKr intersect DomP with norm(Kr(R_P(a)f))<=a^(-1)*norm(Kr f) and norm(G(R_P(a)f))<=a^(-1)*norm(Kr f)+2*norm(f), and an unconditional proof that DomG=DomP intersect DomKr (and DomG intersect Dom(clockHalf)) is an operator-graph core for P via R_P(a)(J_N(Px+a*x))->x in the graph of P. Under 0<epsilon,h!=0,abs(h)<=pi*epsilon/3, J_N(R_T(a)f) lies simultaneously in DomT intersect DomKr intersect Dom(clockHalf) intersect Dom(T^(1/2)) intersect Dom(Kr^(1/2)) with exact resolvent-radial commutator identity J_N(R_T(a)f)-R_T(a)(J_N f)=R_T(a)(C_N(R_T(a)f)) and explicit O(N^(-1/2)) Hilbert and T-graph norm bounds; doubly regularized vectors J_N(G_a x)=G_a(J_N x) on DomT lie simultaneously in the 6-domain intersection DomT intersect DomKr intersect Dom(clockOperator) intersect Dom(clockHalf) intersect Dom(T^(1/2)) intersect Dom(Kr^(1/2)) with C_N(G_a x)=G_a(C_N x) and diagonal convergence to x in the graph of T; and the residual resolvent R_{S(t)}(a) maps Dom(Kr^(1/2)) into Dom(Kr^(1/2)) intersect DomEavg(s) intersect DomS(t) with explicit 5-channel form-energy bounds via the bounded radial Yosida square-root multiplier M_N^(1/2) and Fatou root-domain criterion. Furthermore, centered clock-Gaussian smoothing maps commonOperatorDomain (and DomT intersect DomKr intersect DomP under k>0) into the 10-domain clock core with simultaneous 8-operator two-time graph convergence; the nonautonomous form evolution induces continuous linear isomorphisms between FormSpace(s) and FormSpace(t) with two-sided exp(+/-2*abs(t-s)) energy bounds and evolved resolvent regularity; arbitrary complex source arrays with constant neutral polynomials decompose exactly into mass, quartic, and vacuum energy/response channels with single-channel and two-channel lower bounds; common-complex-source packets satisfy n-packet superposition linearity in P:Fin n->C[X] and exact affine polynomial decomposition P_i(X)=d_{0,i}+d_{1,i}*X across all 9 state/momentum/Hamiltonian maps; finite linear combinations of sourced packets preserve all 12 operator/form domains and satisfy evolved 5-channel energy domination; and general 4D linearized metric perturbations decompose into conformalPart+tracelessPart and satisfy the exact 4D Lorentzian Weyl-Ricci-Scalar split R_metric=weylTensor4D+ricciScalarRiemannPart4D with full Riemann/Bianchi symmetries, vanishing of all 6 Lorentzian traces and conformal perturbations of weylTensor4D, reconstruction of ricciScalarRiemannPart4D from the 10-component Einstein tensor, and vacuum Einstein iff pure Weyl curvature equivalence. Unconditional operator-level radial-resolvent invariance of DomP (whether J_N maps DomP into DomP for fixed N without passing through R_P(a)), full operator-norm bound on P(a+H(t))^(-1) without form pairing, proving D_uncond is a graph core for H(t) and G unconditionally, differing complex neutral sources at non-zero potential coupling, higher-degree neutral polynomials in the complex-source response bound, trajectory-wide unbounded-momentum derivatives, nonlinear curved 4D gravity and Weyl probe extraction, interacting Standard Model dynamics in the same model, microscopic law and phase selection, controlled physical limits, and empirical identification remain open; the earlier phase/harmonic identification still requires revision. A physical TOE is not proved. This checkpoint adds486 theorems in16 modules, preserves3531 parent source/script hashes and adds18 for3549 total; exact root extends from9115 to9131 lines. All12 parent analytic artifacts and23 numerical files remain unchanged. Standard axioms only.'
PARENT = 'data/radial_resolvent_domain_conformal_master_audit.json'
PARENT_SHA = 'fd963d28115816f45844d80b0316add830e5415686001a9e8584859c771648ee'
REPORT = 'data/quarter_strip_resolvent_weyl_ricci_synthesis_audit.json'
SCRIPTS = ['scripts/quarter_strip_resolvent_weyl_ricci_synthesis_audit.py',
           'scripts/verify_quarter_strip_resolvent_weyl_ricci_synthesis.py']
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
    parsed=re.findall(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]",log)
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
    assert len(old)==3531 and len(hashes)==3531+len(EXPECTED)+2
    assert all(hashes[p]==h for p,h in old.items())
    assert all(sha(root/p)==h for p,h in hashes.items())
    additions={'UnifiedTheory/Audit/'+n+'.lean' for n in EXPECTED}|set(SCRIPTS)
    assert set(hashes)-set(old)==additions
    assert [Path(x['source']).stem for x in report['modules']]==list(EXPECTED)
    logs=overlay/'quarter-strip-resolvent-weyl-ricci-synthesis-audit'
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
    assert text.endswith(suffix) and len(text.splitlines())==9115+len(EXPECTED)
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
