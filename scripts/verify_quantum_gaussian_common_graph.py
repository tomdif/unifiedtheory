#!/usr/bin/env python3
"""Independently verify the gaussian-common-graph audit and preserved evidence."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess

EXPECTED = {'KFCausalClockFloorRadialYosidaStrongLimit': 2, 'KFCausalClockFloorGrowingRadialCrossEstimate': 5, 'KFCausalClockFloorGaussianGrowingTransport': 9, 'KFCausalClockFloorGaussianGrowingForm': 5, 'KFCausalClockFloorGaussianGrowingOutputPairing': 4, 'KFCausalClockFloorGaussianGrowingRadialPairing': 9, 'KFCausalClockFloorGaussianGrowingApproximation': 3, 'KFCausalClockFloorGaussianGrowingDomain': 4, 'KFCausalClockFloorGaussianStaticCommutation': 5, 'KFCausalClockFloorGaussianCommonDomainApproximation': 4, 'KFCausalAngularQuarticEndpoint': 9, 'KFCausalAngularGammaMomentBounds': 9, 'KFCausalAngularGammaMomentConvergence': 4}
EXTRA_ANALYTIC = {'analytic_common_complex_quartic_finite_angular_loss': {'path': 'data/quantum_common_complex_quartic_finite_angular_loss_20261022.txt', 'sha256': '88c301c66d2da58e0c9a014788d2240cde24a1df02521ef59de6cde6ca5854bb', 'status': 'Independently reviewed analytic existence proof candidate, not a Lean response theorem. For a common arbitrary complex neutral source, P=1 and the original strict coherent width margins, the repeated-linear quartic channel has a finite universal angular loss C4. Actual singular endpoint moments and a uniformly positive limiting quartic supply large-tilt positivity; compactness handles bounded tilt. Neutral Gaussian smoothing, tilt Gaussian mixing, actual Abel-circle constraints and degree-two Hardy control yield the finite response coefficient 1200+(25/4)*C4. C4 is not evaluated; the old536 coefficient is not claimed. Full circle/Abel/Hardy/clock attachment, general source classes and evolved uniform response remain open.'}}
SCOPE = 'Actual centered Gaussian clock multipliers now preserve the growing Hamiltonian domain, with an exact operator identity on every DomG vector. With M_y=exp[-a*(chart+i*y)^2], a>=0, G M_0 x=M_-h Gx+M_0 Krx-M_-h Krx. The hypotheses are epsilon>0, h!=0 and abs(h)<=pi*epsilon/3, with arbitrary original mass/quartic/vacuum parameters. The proof retains the original simultaneous weighted graph closure, natural half-clock shifts, actual charge-averaged sections and the growing output closure. The previously proved radial inclusion supplies the second root graph and its exact form pairing; no separate potential-domain assumption is used. The actual Gaussian action converges strongly to the identity, including its L2 section lift. It commutes with the actual maximal static multiplier T through the proved complementary Fourier representation and hence with the identified original static Hamiltonian. For every x in DomT intersect DomG, the explicit sequence a_n=1/(n+1) stays in that intersection and (M_0 x,T M_0 x,G M_0 x) converges to (x,Tx,Gx). This is simultaneous Gaussian graph approximation, not a proof of a joint finite-packet operator core or removal of the original full-form range restriction. Separately, the actual rational radial cutoffs converge strongly to Kr on its full maximal domain. Passing the proved cutoff pairing inequality to the limit gives norm(Kr x)^2<=Re inner(Gx,Kr x), then norm(Kr x)^2+norm((G-Kr)x)^2<=norm(Gx)^2 for every DomG vector. Identification of this remainder with a separately completed potential Hamiltonian is not part of this checkpoint. For the response route, nine Lean theorems prove the exact endpoint quartic SOS, global lower bound (1+s^4)/108, and stability under five coefficient errors at most1/1080, yielding (1+s^4)/216 uniformly for all real s. Thirteen further Lean theorems prove actual singular endpoint kernel integrability, its exact correction integral4z, an endpoint-tail bound4z*(2z)^j*exp(-z) tending to zero, interior dominated convergence and actual Gamma moment convergence for every natural j. The normalizer is eventually positive and actual normalized moments converge to Gamma(j+1/2)/Gamma(1/2). No desired moment limit is assumed. The new independently reviewed analytic artifact uses these endpoint ideas, compact bounded-tilt positivity, linked Gaussian mixtures, the Abel-circle marginal and degree-two Hardy control to obtain a finite universal quartic loss C4 and an analytic response coefficient1200+(25/4)*C4 for common complex neutral source and P=1 under the original strict margins. C4 is not evaluated; no536 quartic constant is claimed. The actual coefficient attachment, circle pushforward, compact positive-energy bound, mixtures, Hardy/score/clock assembly and final physical response are not yet fully Lean-certified. Joint full H/G operator control, the uniform G_N*(1+H(s))^(-1) estimate, stronger evolved domains, the original full-form range restriction and the interacting static/growing mixed estimate remain open. General mixed/differing neutral sources and general neutral polynomials remain outside the proved response bounds. General curved gravity, interacting Standard Model dynamics in the same model, microscopic law/phase selection, controlled physical limits and empirical identification remain unproved. Earlier phase/harmonic identification requires revision. A physical TOE is not proved. This checkpoint adds 72 theorems in 13 modules, preserves3308 parent source/script hashes and adds15 for3323 total; the root extends from8920 to8933 lines. All11 parent analytic artifacts and23 numerical files remain unchanged, with one new reviewed analytic artifact for12 total. Standard axioms only.'
PARENT = 'data/quantum_growing_radial_domination_audit.json'
PARENT_SHA = 'd63cf0d35676342776cd9acb338602b183ff899b0bdbb85dab32943ff4757640'
REPORT = 'data/quantum_gaussian_common_graph_audit.json'
SCRIPTS = ['scripts/quantum_gaussian_common_graph_audit.py',
           'scripts/verify_quantum_gaussian_common_graph.py']
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
    assert len(old)==3308 and len(hashes)==3308+len(EXPECTED)+2
    assert all(hashes[p]==h for p,h in old.items())
    assert all(sha(root/p)==h for p,h in hashes.items())
    additions={'UnifiedTheory/Audit/'+n+'.lean' for n in EXPECTED}|set(SCRIPTS)
    assert set(hashes)-set(old)==additions
    assert [Path(x['source']).stem for x in report['modules']]==list(EXPECTED)
    logs=overlay/'quantum-gaussian-common-graph-audit'
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
    assert text.endswith(suffix) and len(text.splitlines())==8920+len(EXPECTED)
    assert hashlib.sha256(text[:-len(suffix)].encode()).hexdigest()==parent['root_check']['source_sha256']
    assert report['root_check']==dict(command=['lean','-j1','UnifiedTheory.lean'],exit_code=0,empty_log=True,
        source_sha256=sha(root/'UnifiedTheory.lean'),log_sha256=sha(logs/'root-import.log'),appended_imports=list(EXPECTED))
    assert not (logs/'root-import.log').read_text().strip()
    old_analytic={k:v for k,v in parent.items() if k.startswith('analytic_')}
    new_analytic={k:v for k,v in report.items() if k.startswith('analytic_')}
    assert len(old_analytic)==11 and new_analytic==dict(**old_analytic,**EXTRA_ANALYTIC)
    assert all(sha(root/v['path'])==v['sha256'] for v in new_analytic.values())
    assert report['numerical_evidence']==parent['numerical_evidence']
    numerical=[v for v in report['numerical_evidence'].values() if isinstance(v,dict) and 'path' in v]
    assert len(numerical)==23 and all(sha(root/v['path'])==v['sha256'] for v in numerical)
    assert report['scope']==SCOPE and report['lean_toolchain']==(root/'lean-toolchain').read_text().strip()
    print('Verified '+str(sum(EXPECTED.values()))+' Lean theorems, '+str(len(hashes))+' source/script hashes,')
    print('exact root extension, all23 numerical files and all analytic artifacts; standard axioms only.')


if __name__=='__main__':
    main()
