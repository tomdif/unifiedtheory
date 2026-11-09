#!/usr/bin/env python3
"""Audit negative clock phases and direct-response numerical evidence.

Five new pointwise clock-phase theorems support the next domain analysis.
Rechecks existing full-response, static-bound and clock-observable dynamics
declarations while preserving every previous source.
"""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess


NEW_MODULE = 'KFCausalNegativeClockFrequency'
MODULES = [(NEW_MODULE, 5), ('KFCausalStructuredProjectedHamiltonian', 8), ('KFCausalProjectedClockResponse', 6),
           ('KFCausalClockFloorExactEhrenfest', 5), ('KFCausalClockFloorUnboundedClockEhrenfest', 13)]


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--overlay', required=True, type=Path)
    args = parser.parse_args()
    root, overlay = Path(__file__).resolve().parents[1], args.overlay.resolve()
    assert 'LEAN_PATH' in os.environ and overlay.is_dir()
    env = os.environ.copy()
    env['LEAN_PATH'] = str(overlay)+os.pathsep+env['LEAN_PATH']
    logs = overlay/'independent-neutral-response-audit'
    logs.mkdir(exist_ok=True)
    previous_path = root/'data/independent_neutral_test_audit.json'
    previous_hash, previous = sha(previous_path), json.loads(previous_path.read_text())
    additions = ['scripts/independent_neutral_response_probe.py',
                 'scripts/verify_independent_neutral_response.py',
                 'scripts/independent_neutral_response_audit.py',
                 'UnifiedTheory/Audit/'+NEW_MODULE+'.lean']
    hashes = {p: sha(root/p) for p in [*previous['source_sha256'], *additions]}
    assert all(hashes[p] == h for p, h in previous['source_sha256'].items())
    evidence = dict(previous['numerical_evidence'])
    for item in evidence.values():
        if isinstance(item, dict) and 'path' in item:
            assert sha(root/item['path']) == item['sha256']
    probe_path = root/'data/independent_neutral_response_probe.json'
    validation_path = root/'data/independent_neutral_response_validation.json'
    probe, validation = [json.loads(p.read_text()) for p in [probe_path, validation_path]]
    assert all(sha(root/p) == h for p, h in probe['source_sha256'].items())
    assert sha(root/probe['prior_moment_report']['path']) == probe['prior_moment_report']['sha256']
    assert validation['probe_report_sha256'] == sha(probe_path)
    assert validation['verifier_sha256'] == sha(root/'scripts/verify_independent_neutral_response.py')
    assert len(probe['cases']) == 3 and len(validation['checks']) == 6
    for key, path in [('independent_neutral_response_report', probe_path),
                      ('independent_neutral_response_validation', validation_path)]:
        evidence[key] = dict(path=str(path.relative_to(root)), sha256=sha(path))
    root_hash = sha(root/'UnifiedTheory.lean')
    root_text = (root/'UnifiedTheory.lean').read_text()
    suffix = 'import UnifiedTheory.Audit.'+NEW_MODULE+'\n'
    assert root_text.endswith(suffix)
    assert hashlib.sha256(root_text[:-len(suffix)].encode()).hexdigest() == previous['root_check']['source_sha256']
    checks = []
    for name, count in MODULES:
        source = 'UnifiedTheory/Audit/'+name+'.lean'
        text = (root/source).read_text()
        assert not re.search(r'\b(sorry|admit|axiom|unsafe)\b', text)
        command = ['lean', '-j1', '-o', str(overlay/'UnifiedTheory/Audit'/f'{name}.olean'), source]
        result = subprocess.run(command, cwd=root, env=env, text=True,
                                stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
        log = logs/(name+'.log')
        log.write_text(result.stdout)
        assert result.returncode == 0 and not re.search(r': error|: warning|sorryAx', result.stdout), str(log)
        audits = re.findall(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]", result.stdout)
        expected = {'UnifiedTheory.Audit.'+name+'.'+n for n in re.findall(r'^#print axioms (\S+)', text, re.M)}
        declared = {'UnifiedTheory.Audit.'+name+'.'+n for n in re.findall(r'^theorem (\S+)', text, re.M)}
        assert len(audits) == count and {n for n, _ in audits} == expected == declared
        dependencies = {}
        for declaration, axioms in audits:
            used = {s.strip() for s in axioms.split(',') if s.strip()}
            assert used <= {'propext', 'Classical.choice', 'Quot.sound'}
            dependencies[declaration] = sorted(used)
        checks.append(dict(source=source, command=command, exit_code=0,
                           log_sha256=sha(log), audited_declarations=dependencies))
        print(name, ': clean;', count, 'theorem dependency lists', flush=True)
    result = subprocess.run(['lean', '-j1', 'UnifiedTheory.lean'], cwd=root, env=env, text=True,
                            stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    log = logs/'root-import.log'
    log.write_text(result.stdout)
    assert result.returncode == 0 and not result.stdout.strip(), str(log)
    assert sha(root/'UnifiedTheory.lean') == root_hash and sha(previous_path) == previous_hash
    assert all(sha(root/p) == h for p, h in hashes.items())
    for item in evidence.values():
        if isinstance(item, dict) and 'path' in item:
            assert sha(root/item['path']) == item['sha256']
    assert not (root/'.lake/build/lib/lean/UnifiedTheory/Audit'/f'{NEW_MODULE}.olean').exists()
    report = dict(new_lean_theorem_count=5, reviewed_declaration_count=32,
                  modules=checks[:1], reviewed_response_modules=checks[1:],
                  source_sha256=hashes, numerical_evidence=evidence,
                  previous_report=dict(path=str(previous_path.relative_to(root)), sha256=previous_hash),
                  root_check=dict(command=['lean', '-j1', 'UnifiedTheory.lean'], exit_code=0,
                                  empty_log=True, source_sha256=root_hash, log_sha256=sha(log)),
                  lean_toolchain=(root/'lean-toolchain').read_text().strip(),
                  scope='Five new Lean theorems prove the actual inverse clock has negative imaginary part for positive hbar in the admitted strip, identify the clock-frequency phase norm, prove its contraction for nonpositive frequencies and monotonicity, and prove pointwise decay along negative integer frequencies. These phase facts do not themselves prove a full energy comparison or a pure-momentum domain obstruction. Additionally, 32 existing public full-Hamiltonian assembly, clock/static-bound and clock-observable dynamics theorems are rechecked with standard axioms. All 1581 previous source/script hashes are preserved; the root has exactly one appended import. The bounded clock defect and unbounded positive clock already have exact expectation dynamics along the regulated averaged propagator. The response currently studied is the pure-clock-momentum commutator; its adequate energy lower bound, form/core extension, unbounded-observable domain control and expectation identity along that propagator remain open. New floating full-clock response tests retain every complex mode and all eight energy factors on the independent-neutral family. The previous adverse moment witnesses are retested on the actual response, distinguishing failure of a sufficient moment comparison from failure of a response bound. An adverse neutral-position/momentum span is tested separately. Independent direct-pairing references, boundary terms, complete-space spectra and energy-scaled refinements are checked. These finite numerical results do not certify signs, tails, a uniform lower bound, required model revision or a physical TOE.')
    target = root/'data/independent_neutral_response_audit.json'
    target.write_text(json.dumps(report, indent=2)+'\n')
    print('Root passed; 5 new and 32 existing theorem audits;', len(hashes), 'source hashes.', flush=True)
    print(target, flush=True)


if __name__ == '__main__':
    main()
