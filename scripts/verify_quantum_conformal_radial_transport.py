#!/usr/bin/env python3
"""Independently verify the radial-transport audit and preserved evidence."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess

EXPECTED = {'KFCausalBDG4DSmoothCompactPartials': 10, 'KFCausalBDG4DSmoothCompactSupplier': 11, 'KFCausalConformal4DNormalizedVolume': 18, 'KFCausalConformal4DVolumePositivity': 7, 'KFCausalConformal4DVolumeHomogeneity': 6, 'KFCausalConformal4DVolumeSmoothPolynomial': 10, 'KFCausalConformal4DRadialScale': 7, 'KFCausalConformal4DRadialJacobian': 10, 'KFCausalConformal4DRadialInverse': 9, 'KFCausalConformal4DRadialInverseOrigin': 3, 'KFCausalConformal4DVolumeReflection': 9, 'KFCausalConformal4DTransformedProfile': 14, 'KFCausalConformal4DRadialPushforward': 5, 'KFCausalConformal4DConePushforward': 6, 'KFCausalConformal4DFixedParameterLimit': 5, 'KFCausalConformal4DCriticalHessian': 3, 'KFCausalConformal4DTransformedProfileJets': 10, 'KFCausalConformal4DDiamondAffine': 9, 'KFCausalConformal4DDiamondMeasure': 10, 'KFCausalConformal4DBallAxialIntegral': 5, 'KFCausalConformal4DRadialAxialIntegral': 3, 'KFCausalConformal4DCoordinateVolume': 4, 'KFCausalConformal4DCovariantWaveTest': 6, 'KFCausalConformal4DPhysicalCurvatureLimit': 4, 'KFCausalChargedEvenMomentImaginaryBound': 10, 'KFCausalChargedEvenMomentFamily': 8, 'KFCausalChargedEvenMomentMonotonicity': 4}
EXTRA_ANALYTIC = {'analytic_real_scaling_defect': {'path': 'data/quantum_whole_response_real_scaling_defect_20261021.txt', 'sha256': 'ab6f96670a22b5eeac6a48b793305509bc9b24e6df7f9ff2579c9625ae5c5c5c', 'status': 'Independently reviewed analytic reduction, not Lean verified. The full actual-clock response is exactly a real scaling term plus a linked imaginary/field defect; the unrestricted lower bound remains open.'}, 'analytic_linked_defect': {'path': 'data/quantum_whole_response_linked_defect_20261021.txt', 'sha256': 'cfd10263fb0ea1775d174b6f7d0dd3b3ab5125355aa6e4463709b960d7254864', 'status': 'Independently reviewed analytic operator identity, not Lean verified. All finite-width cross terms and linked neutral derivatives are retained; the remaining weighted numerical-range estimate is not assumed or proved.'}, 'analytic_unitary_flow': {'path': 'data/quantum_whole_response_unitary_flow_20261021.txt', 'sha256': 'd73b1dc86aabdf597e07935b74b9b7fb2897ed977d01bc3a508fc7a4c8ce45c0', 'status': 'Independently reviewed analytic construction, not Lean verified. An actual determinant-one real flow and Gaussian analytic continuation yield a selfadjoint generator representation, scalar bound and exact full linked quartic target. The unrestricted quartic estimate remains open.'}, 'analytic_common_real_source_response': {'path': 'data/quantum_common_real_source_quartic_response_20261021.txt', 'sha256': '0144aa4c2ed9f9db24d6f98984ebe994a0247218b38b623ace4501fbffce07bd', 'status': 'Independently reviewed analytic proof, not Lean verified as a full response theorem. Arbitrary finite charged widths with one common real neutral source and P=1 obey a full quartic response bound with constant536. The all-order charged moment components are formalized separately; the full positive-series attachment and unrestricted complex-source/polynomial bound remain open.'}}
SCOPE = 'The actual compact temporal-conformal operator converges to 8−6c for every fixed |c|≤1/54. The proof constructs the exact normalized volume polynomial, derives uniform positivity and positive radial Jacobian, builds an actual smooth inverse covering a fixed chart, constructs the original cutoff pushforward with a support collar, and proves the exact measure substitution. A smooth compact symmetric profile supplies the BDG limit with actual derivatives, support and bounds; no desired-limit premise is introduced. Its actual Hessian is computed, giving the explicit fixed-parameter value without differentiating an asymptotic limit. Direct Lebesgue integration over the explicit Minkowski diamond equals the original boosted parameter volume, with time-orientation reversal, determinant-one transport and all integrability suppliers derived. The actual coordinate covariant wave operator and connection curvature give 8−6c=Box_g(phi)(0)−R(0)phi(0)/2, and the literal metric-density coordinate-diamond operator has that limit. This is one temporal conformal family and one fixed compact field; conformal curve chronology, a general curved-spacetime limit and variational Einstein dynamics remain open. Actual all-order even charged moments of arbitrary finite correlated widths have derived integrability, exact Gram integrals and a genuine imaginary-derivative lower bound with loss(l+2)/2. The actual finite-increment functions b^(2n+2)I_(m+n) are monotone on 0<b<a for m≤2 and all n. This is not the unrestricted full quartic response estimate. Four new separately hashed research notes are analytic, not Lean verified full response theorems. The common-real-source P=1 constant 536 response proof is independently reviewed analytically; its complete infinite positive-series attachment is still absent in Lean. All six prior analytic artifacts and 23 numerical files are preserved. A common H/G operator core, forward stronger-domain propagation, microscopic law/phase selection, same-model interacting Standard Model dynamics, controlled physical regulator limits and empirical identification remain open. The earlier phase/harmonic incompatibility still requires revision. A physical TOE is not proved. Standard axioms only. This checkpoint adds 206 theorems in 27 modules, preserving 3154 parent hashes and adding 29 source/script hashes for 3183 total; the root extends 8794 to 8821 lines.'
PARENT = 'data/quantum_compact_curvature_variation_audit.json'
PARENT_SHA = '5b8a6b0141449b5517b0fae96560c963472ea4149a83e2d84bffe7b6aee20318'
REPORT = 'data/quantum_conformal_radial_transport_audit.json'
SCRIPTS = ['scripts/quantum_conformal_radial_transport_audit.py',
           'scripts/verify_quantum_conformal_radial_transport.py']
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
    assert len(old)==3154 and len(hashes)==3154+len(EXPECTED)+2
    assert all(hashes[p]==h for p,h in old.items())
    assert all(sha(root/p)==h for p,h in hashes.items())
    additions={'UnifiedTheory/Audit/'+n+'.lean' for n in EXPECTED}|set(SCRIPTS)
    assert set(hashes)-set(old)==additions
    assert [Path(x['source']).stem for x in report['modules']]==list(EXPECTED)
    logs=overlay/'quantum-conformal-radial-transport-audit'
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
    assert text.endswith(suffix) and len(text.splitlines())==8794+len(EXPECTED)
    assert hashlib.sha256(text[:-len(suffix)].encode()).hexdigest()==parent['root_check']['source_sha256']
    assert report['root_check']==dict(command=['lean','-j1','UnifiedTheory.lean'],exit_code=0,empty_log=True,
        source_sha256=sha(root/'UnifiedTheory.lean'),log_sha256=sha(logs/'root-import.log'),appended_imports=list(EXPECTED))
    assert not (logs/'root-import.log').read_text().strip()
    old_analytic={k:v for k,v in parent.items() if k.startswith('analytic_')}
    new_analytic={k:v for k,v in report.items() if k.startswith('analytic_')}
    assert len(old_analytic)==6 and new_analytic==dict(**old_analytic,**EXTRA_ANALYTIC)
    assert all(sha(root/v['path'])==v['sha256'] for v in new_analytic.values())
    assert report['numerical_evidence']==parent['numerical_evidence']
    numerical=[v for v in report['numerical_evidence'].values() if isinstance(v,dict) and 'path' in v]
    assert len(numerical)==23 and all(sha(root/v['path'])==v['sha256'] for v in numerical)
    assert report['scope']==SCOPE and report['lean_toolchain']==(root/'lean-toolchain').read_text().strip()
    print('Verified '+str(sum(EXPECTED.values()))+' Lean theorems, '+str(len(hashes))+' source/script hashes,')
    print('exact root extension, all23 numerical files and all analytic artifacts; standard axioms only.')


if __name__=='__main__':
    main()
