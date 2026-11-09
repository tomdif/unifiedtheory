#!/usr/bin/env python3
"""Recompile and audit agreement of the represented phase-space clock marginal, the actual quantum clock Born laws and the global limiting clock-defect expectation.

Run through the repository toolchain, using its previously verified dependencies:
  lake env python3 scripts/physical_clock_floor_probability_clock_compatibility_audit.py --overlay PATH

This does not invoke lake build. It rebuilds all three new modules in dependency
order, checks their printed axioms, checks the root import, and preserves the
preceding source hash chain. It is a scoped formal audit, not a TOE certificate.
"""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess


MODULES = [('KFCausalClockMarginalIdentification', 4), ('KFCausalClockMarginalWeakLimit', 3), ('KFCausalClockFloorProbabilityClockCompatibility', 1)]


STANDARD_AXIOMS = {'propext', 'Classical.choice', 'Quot.sound'}


def sha256(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--overlay', required=True, type=Path)
    args = parser.parse_args()
    root = Path(__file__).resolve().parents[1]
    overlay = args.overlay.resolve()
    assert 'LEAN_PATH' in os.environ, 'Run with lake env python3.'
    assert overlay.is_dir(), 'Use the verified dependency overlay.'
    env = os.environ.copy()
    env['LEAN_PATH'] = str(overlay)+os.pathsep+env['LEAN_PATH']
    logs = overlay/'physical-clock-floor-probability-clock-compatibility-audit'
    logs.mkdir(exist_ok=True)
    (overlay/'UnifiedTheory/Audit').mkdir(parents=True, exist_ok=True)
    previous_path = root/'data/physical_clock_floor_probability_limit_audit.json'
    previous_hash = sha256(previous_path)
    previous = json.loads(previous_path.read_text())
    sources = list(previous['source_sha256'])
    sources += ['UnifiedTheory/Audit/'+name+'.lean' for name, _ in MODULES]
    sources += ['scripts/physical_clock_floor_probability_clock_compatibility_audit.py']
    hashes = {p: sha256(root/p) for p in sources}
    assert all(hashes[p] == h for p, h in previous['source_sha256'].items())
    root_hash = sha256(root/'UnifiedTheory.lean')
    root_text = (root/'UnifiedTheory.lean').read_text()
    appended_imports = ''.join('import UnifiedTheory.Audit.'+name+'\n' for name, _ in MODULES)
    assert root_text.endswith(appended_imports), 'Expected only the new appended root imports.'
    assert hashlib.sha256(root_text[:-len(appended_imports)].encode()).hexdigest() == previous['root_check']['source_sha256']
    for name, _ in MODULES:
        assert 'import UnifiedTheory.Audit.'+name in root_text

    checks = []
    for name, count in MODULES:
        source = 'UnifiedTheory/Audit/'+name+'.lean'
        command = ['lean', '-j1', '-o', str(overlay/'UnifiedTheory/Audit'/f'{name}.olean'), source]
        result = subprocess.run(command, cwd=root, env=env, text=True,
                                stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
        log = logs/(name+'.log')
        log.write_text(result.stdout)
        assert result.returncode == 0, f'{name}: exit {result.returncode}; see {log}'
        assert not re.search(r': error|: warning|sorryAx', result.stdout), str(log)
        audits = re.findall(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]", result.stdout)
        assert len(audits) == count, (name, len(audits), count)
        declarations = {}
        for declaration, axioms in audits:
            used = {s.strip() for s in axioms.split(',') if s.strip()}
            assert used <= STANDARD_AXIOMS, (declaration, used)
            declarations[declaration] = sorted(used)
        checks.append(dict(source=source, command=command, exit_code=result.returncode,
                           log_sha256=sha256(log), audited_declarations=declarations))
        print(name, ': compiled;', count, 'standard-axiom audits', flush=True)

    result = subprocess.run(['lean', '-j1', 'UnifiedTheory.lean'], cwd=root, env=env, text=True,
                            stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    log = logs/'root-import.log'
    log.write_text(result.stdout)
    assert result.returncode == 0 and not result.stdout.strip(), str(log)
    assert root_hash == sha256(root/'UnifiedTheory.lean'), 'Root changed during verification.'
    assert previous_hash == sha256(previous_path), 'Previous report changed during verification.'
    assert all(sha256(root/p) == h for p, h in hashes.items()), 'Sources changed during verification.'
    report = dict(
        modules=checks, root_check=dict(command=['lean', '-j1', 'UnifiedTheory.lean'], exit_code=0,
            empty_log=True, source_sha256=root_hash, log_sha256=sha256(log)),
        audited_declaration_count=sum(n for _, n in MODULES), source_sha256=hashes,
        previous_report=dict(path=str(previous_path.relative_to(root)), sha256=previous_hash),
        lean_toolchain=(root/'lean-toolchain').read_text().strip(),
        scope='The represented ten-dimensional probability now agrees with the original quantum clock measurement and with the global limiting clock path. A continuous clock-axis coefficient map is proved to encode exactly the canonical clock-position phase. Its Euclidean phase inner product is the scalar clock-coordinate pairing. The clock marginal of a ten-dimensional probability therefore has the corresponding restricted characteristic, while the actual clock Born law has exactly the same canonical quantum characteristic. The preceding characteristic convergence theorem derives weak convergence of the actual normalized clock Born laws to the clock marginal of the represented probability. The bounded continuous clock-defect function epsilon/(exp(q)+epsilon) has Born expectation equal to the actual bounded defect-operator expectation. Weak convergence therefore identifies its limiting expectation with its mean under the represented ten-dimensional probability. The concrete theorem constructs a common semiclassical subsequence, the global clock path, kernels and probabilities at any prescribed countable family of future times, preserving all preceding tightness, weak convergence, compact time convergence, window Lipschitz bounds and comparison-rate balance. It additionally proves weak convergence of the original clock Born laws and equality of each represented defect mean with the global clock path at that observation time. No marginal agreement or clock compatibility is assumed. The fixed positive floor and width, nonnegative couplings, fixed initial time and momentum, and admissible nonzero hbar sequence are unchanged. This closes the clock-observable compatibility gap at the selected future times, not the quantum-to-classical dynamical identification. The comparison-rate limit still contains quantum energy outputs; identifying those with classical transport rates remains open. Characteristic and measure time regularity, independence from the semiclassical subsequence, neutral-position and negative-clock-momentum control, full twelve-dimensional limits, Hamiltonian phase-test domains and commutators, and uniqueness and identification of classical transport remain open. Neither fixed-hbar zero clock defect nor zero defect of the represented measures at late times is established. Floor removal, GR/QFT/Standard Model identification and empirical validity remain open. No model or preceding operator changed; all 885 predecessor source/script hashes are preserved. The TOE remains unproved.')


    target = root/'data/physical_clock_floor_probability_clock_compatibility_audit.json'
    target.write_text(json.dumps(report, indent=2)+'\n')
    print('Root import passed;', report['audited_declaration_count'],
          'audited declarations;', len(hashes), 'verified source hashes.', flush=True)
    print(target, flush=True)


if __name__ == '__main__':
    main()
