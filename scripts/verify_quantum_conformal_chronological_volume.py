#!/usr/bin/env python3
"""Independently verify the chronological-volume audit and preserved evidence."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess

EXPECTED = {'KFCausalConformal4DTimelikeTangents': 6, 'KFCausalMinkowski4DTimelikeCurves': 6, 'KFCausalConformal4DChronology': 6, 'KFCausalConformal4DChronologicalCurvatureLimit': 4, 'KFCausalChargedGaussianMomentSeries': 7, 'KFCausalCommonRealGaussianEnergy': 7, 'KFCausalCommonRealGaussianMonotonicity': 4, 'KFCausalOriginalCommonRealGaussianEnergy': 3}
EXTRA_ANALYTIC = {}
SCOPE = 'Forty-three new Lean theorems close the actual chronological-domain identification for the fixed temporal conformal compact-test benchmark and establish the actual positive charged Gaussian moment series. The metric quadratic form is proved equal to Omega squared times the Minkowski form; strict future metric tangents imply actual Minkowski future tangents. On |time|<=2 and |c|<=1/54, Omega=1+c*time^2>=25/27. Actual C1 future-timelike curves imply future displacement by a separating functional, Cauchy-Schwarz and the mean-value theorem; actual straight curves supply the converse in the endpoint slab. Diamonds defined by the existence of these actual curves are proved equal to the explicit coordinate diamonds on the original cutoff support. Their literal metric-density integral therefore equals the parameter volume there. The operator using these genuine chronological volumes equals the original operator and converges to the actual coordinate Box_g(phi)(0)-R(0)*phi(0)/2=8-6c for every fixed |c|<=1/54. No desired continuum limit or chronological-domain identity is a premise. The actual Gaussian-weighted charged norm has derived integrability under the strict per-width margins. A nonnegative HasSum identity and frozen finite-increment moment bounds prove b^2 times each weighted even moment is monotone for orders zero through two, retaining all coherent finite-width cross terms. For one common real neutral source and P=1, the actual neutral quartic integral decomposes into three nonnegative charged weighted energies. Its finite-increment b^2 monotonicity and actual field-slope derivative bound 0<=L*E_L<=4E are proved. The exact original positive joint density and its full product-measure integral equal this energy, with the original width factors retained. The actual imaginary derivative and full clock-response attachment remain open in Lean. This result is local to one temporal conformal family and one original compact field. For negative c the metric matrix may degenerate far outside the proved positive slab; no global Lorentzian spacetime is asserted. A separate fully four-coordinate outer-integral identification, general metrics and fields, the variational Einstein equations, unrestricted quartic response, a common H/G operator core and forward stronger-domain propagation, microscopic law and phase selection, same-model interacting Standard Model QFT, physical regulator limits and empirical identification remain open. The earlier phase/harmonic incompatibility still requires revision. A physical TOE is not proved. The parent 206 theorems remain intact; this checkpoint adds 43 in 8 modules, preserving 3183 parent source/script hashes and adding 10 for 3193 total, with the root extended 8821 to 8829 lines. All 10 analytic artifacts and 23 numerical files are unchanged; the separately reviewed common-real-source P=1 response proof is still not a full Lean response theorem. Standard axioms only.'
PARENT = 'data/quantum_conformal_radial_transport_audit.json'
PARENT_SHA = 'b1e4892bc61cef03a4a045549a07b137802b19ff79c6e280784b1098579756ab'
REPORT = 'data/quantum_conformal_chronological_volume_audit.json'
SCRIPTS = ['scripts/quantum_conformal_chronological_volume_audit.py',
           'scripts/verify_quantum_conformal_chronological_volume.py']
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
    assert len(old)==3183 and len(hashes)==3183+len(EXPECTED)+2
    assert all(hashes[p]==h for p,h in old.items())
    assert all(sha(root/p)==h for p,h in hashes.items())
    additions={'UnifiedTheory/Audit/'+n+'.lean' for n in EXPECTED}|set(SCRIPTS)
    assert set(hashes)-set(old)==additions
    assert [Path(x['source']).stem for x in report['modules']]==list(EXPECTED)
    logs=overlay/'quantum-conformal-chronological-volume-audit'
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
    assert text.endswith(suffix) and len(text.splitlines())==8821+len(EXPECTED)
    assert hashlib.sha256(text[:-len(suffix)].encode()).hexdigest()==parent['root_check']['source_sha256']
    assert report['root_check']==dict(command=['lean','-j1','UnifiedTheory.lean'],exit_code=0,empty_log=True,
        source_sha256=sha(root/'UnifiedTheory.lean'),log_sha256=sha(logs/'root-import.log'),appended_imports=list(EXPECTED))
    assert not (logs/'root-import.log').read_text().strip()
    old_analytic={k:v for k,v in parent.items() if k.startswith('analytic_')}
    new_analytic={k:v for k,v in report.items() if k.startswith('analytic_')}
    assert len(old_analytic)==10 and new_analytic==dict(**old_analytic,**EXTRA_ANALYTIC)
    assert all(sha(root/v['path'])==v['sha256'] for v in new_analytic.values())
    assert report['numerical_evidence']==parent['numerical_evidence']
    numerical=[v for v in report['numerical_evidence'].values() if isinstance(v,dict) and 'path' in v]
    assert len(numerical)==23 and all(sha(root/v['path'])==v['sha256'] for v in numerical)
    assert report['scope']==SCOPE and report['lean_toolchain']==(root/'lean-toolchain').read_text().strip()
    print('Verified '+str(sum(EXPECTED.values()))+' Lean theorems, '+str(len(hashes))+' source/script hashes,')
    print('exact root extension, all23 numerical files and all analytic artifacts; standard axioms only.')


if __name__=='__main__':
    main()
