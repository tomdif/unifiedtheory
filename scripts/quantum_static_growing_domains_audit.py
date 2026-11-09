#!/usr/bin/env python3
"""Check the original static/growing domains and ordered static outputs and preserved evidence."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess

EXPECTED = {'KFCausalCommonComplexGaussianMassResponseReduction': 8, 'KFCausalCommonComplexGaussianMassDiscriminant': 2, 'KFCausalClockFloorStaticGrowingDecomposition': 6, 'KFCausalAveragedSecondOrbitGraph': 4, 'KFCausalClockFloorDisplacedSecondDomain': 10, 'KFCausalClockFloorStaticCommonSourceCore': 3, 'KFCausalClockFloorOrderedStaticPacket': 5, 'KFCausalFiniteOrderedStaticOutput': 8}
EXTRA_ANALYTIC = {}
SCOPE = 'Forty-six new Lean theorems establish exact static/growing graph identities on the original interacting form, actual ambient common-domain states and a static graph core in that common domain, ordered static outputs of the original finite packets, and an exact linked mass-response reduction. The separate static Hamiltonian T is the previously proved maximal sigma multiplier. Using the dense original static-root source and the actual closed forms, static_reference_graph_iff characterizes T on the original reference form. Actual H(t) and G graphs yield the T output H(t)x-exp(2t)Gx, and actual H(t) and T graphs yield the G output exp(-2t)(H(t)x-Tx). Conversely, the sum graph is proved when the input has an original reference-form witness. Consequently DomH(t) intersect DomG equals DomH(t) intersect DomT, and equals (DomT intersect DomG) intersect range(J), where J is the original reference-form embedding. The range restriction is retained. An actual averaged H graph is obtained by integrating the inverse-rotated weighted second outputs of all eight continuous primitive factor orbits; compact-angle integrability and the original variational pairing are proved. Ambient displaced Gaussian states supply every premise without a zero-charge assumption, under epsilon>0, a>0, h!=0, abs(h)<=pi*epsilon/3 and zero clock-translation parameter. Their all-time H graphs give actual G graphs through two distinct times. The graph of T restricted to inputs in actual DomH(t) intersect DomG is dense in T.graph; this is T-graph density only. For original finite reciprocal-neutral sourced packets with widths at least one, arbitrary complex neutral sources and polynomials, and abs(h)<=epsilon/10, the complete static output is identified and lies in the actual ordered-exponential Q domain. The literal Q composed with T graph and both composition domains are proved, retaining neutral second derivatives and shifted clock factors. Separately, for the common complex neutral source A+iD with neutral polynomial one and identical original finite amplitudes and widths, the actual mass-channel energy and transport response obey exact quadratic interpolation in A. The all-real-A bound is equivalent to nonnegative two even defects and one linked discriminant inequality. At coefficient 536*fraction, the already proved purely imaginary response supplies the even conditions; the linked odd discriminant remains unproved. No response inequality is inferred from independent feature vectors, entrywise signs or discarded cross terms. The broad static/growing identities use abs(h)<=2*pi*epsilon/3. This checkpoint does not remove the original full-form range restriction, prove simultaneous H/G graph approximation, attach the full complex-transport differential expression or its integration by parts, establish the interacting mixed estimate or uniform G_N*(1+H(s))^(-1) control, or establish stronger evolved domains. Unrestricted response including general mixed or differing sources and neutral polynomials remains open. General curved gravity, interacting Standard Model dynamics in the same model, microscopic law/phase selection, controlled physical limits and empirical identification remain unproved. The earlier phase/harmonic identification requires revision. A physical TOE is not proved. This checkpoint adds 46 theorems in 8 modules, preserves 3277 parent source/script hashes and adds 10 for 3287 total; the root extends from 8893 to 8901 lines. All 10 analytic artifacts and 23 numerical files remain unchanged. Standard axioms only.'
PARENT = 'data/quantum_static_hamiltonian_closure_audit.json'
PARENT_SHA = '11356555532d009013bf3314f24d3f9b97bb429e5b9b33a9ae4351f5a0f91066'
REPORT = 'data/quantum_static_growing_domains_audit.json'
SCRIPTS = ['scripts/quantum_static_growing_domains_audit.py',
           'scripts/verify_quantum_static_growing_domains.py']
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
    parser.add_argument('--baseline-overlay',required=True,type=Path)
    args=parser.parse_args()
    root=Path(__file__).resolve().parents[1]
    overlay=args.overlay.resolve(); baseline=args.baseline_overlay.resolve()
    assert overlay.is_dir() and baseline.is_dir() and overlay!=baseline
    env=os.environ.copy()
    env['LEAN_PATH']=str(overlay)+os.pathsep+str(baseline)+os.pathsep+env['LEAN_PATH']
    logs=overlay/'quantum-static-growing-domains-audit'
    logs.mkdir(exist_ok=False)
    assert sha(root/PARENT)==PARENT_SHA
    parent=json.loads((root/PARENT).read_text())
    hashes=dict(parent['source_sha256'])
    assert len(hashes)==3277 and all(sha(root/p)==h for p,h in hashes.items())
    additions=['UnifiedTheory/Audit/'+n+'.lean' for n in EXPECTED]+SCRIPTS
    assert not set(additions)&set(hashes)
    hashes.update({p:sha(root/p) for p in additions})
    analytic={k:v for k,v in parent.items() if k.startswith('analytic_')}
    assert len(analytic)==10 and not set(analytic)&set(EXTRA_ANALYTIC)
    analytic.update(EXTRA_ANALYTIC)
    assert all(sha(root/v['path'])==v['sha256'] for v in analytic.values())
    evidence=parent['numerical_evidence']
    numerical=[v for v in evidence.values() if isinstance(v,dict) and 'path' in v]
    assert len(numerical)==23 and all(sha(root/v['path'])==v['sha256'] for v in numerical)
    text=(root/'UnifiedTheory.lean').read_text()
    suffix=''.join('import UnifiedTheory.Audit.'+n+'\n' for n in EXPECTED)
    assert text.endswith(suffix)
    assert hashlib.sha256(text[:-len(suffix)].encode()).hexdigest()==parent['root_check']['source_sha256']
    assert len(text.splitlines())==8893+len(EXPECTED)
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
