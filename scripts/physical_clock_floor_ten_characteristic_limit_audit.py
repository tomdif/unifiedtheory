#!/usr/bin/env python3
"""Recompile and audit existence of continuous normalized positive classical characteristic limits on the controlled ten-dimensional frequency family for actual evolved states.

Run through the repository toolchain, using its previously verified dependencies:
  lake env python3 scripts/physical_clock_floor_ten_characteristic_limit_audit.py --overlay PATH

This does not invoke lake build. It rebuilds all five new modules in dependency
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


MODULES = [('KFCausalCanonicalCharacteristicIncrement', 2), ('KFCausalAsymptoticCharacteristicCompactness', 4), ('KFCausalEncodedCharacteristicCompactness', 2), ('KFCausalEncodedCharacteristicLimit', 5), ('KFCausalClockFloorDisplacedTenCharacteristicLimit', 4)]


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
    logs = overlay/'physical-clock-floor-ten-characteristic-limit-audit'
    logs.mkdir(exist_ok=True)
    (overlay/'UnifiedTheory/Audit').mkdir(parents=True, exist_ok=True)
    previous_path = root/'data/physical_clock_floor_ten_test_control_audit.json'
    previous_hash = sha256(previous_path)
    previous = json.loads(previous_path.read_text())
    sources = list(previous['source_sha256'])
    sources += ['UnifiedTheory/Audit/'+name+'.lean' for name, _ in MODULES]
    sources += ['scripts/physical_clock_floor_ten_characteristic_limit_audit.py']
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
        scope='Canonical characteristic increments are bounded by the actual near-identity Weyl displacement plus its explicit ordering phase error. A continuous linear encoding bounds that phase uniformly over unit coefficient increments. A general separable-space compactness theorem extracts a continuous pointwise limit from a bounded family with eventual local equicontinuity: compactness of the countable dense restriction gives a subsequence, eventual local bounds make it Cauchy at every point, and completeness gives the continuous limit. Neither individual-term continuity nor a preexisting pointwise limit is assumed. For any separable linear frequency family, normalized quantum states with derived near-identity control and hbar tending to zero satisfy this criterion. Restricted pointwise limits have value one at zero, norm at most one, conjugation symmetry, and a real nonnegative finite difference kernel, derived from the actual Weyl Gram matrices. The actual evolved boosted states satisfy the required norm control on the ten-dimensional coefficient family by the preceding simultaneous-test theorem. For every sequence of sampling times in a fixed finite forward window, a strictly increasing subsequence and a continuous limiting characteristic on all ten coefficients therefore exist and have all the stated classical positivity properties. Fixed positive floor and initial width, fixed initial time and canonical momentum, nonnegative couplings, and nonzero hbar approaching zero within the existing strip from either or mixed signs are retained. No compactness, pointwise limit, classical evolved law, test continuity, extra moment or tail assumption is added to the concrete theorem. The ten frequencies comprise clock position, four charged positions and all five transverse momenta. Neutral position and clock momentum remain uncontrolled. A representing probability measure, full twelve-dimensional phase-space limits, a common time-dependent subsequence, Hamiltonian phase-test domain and commutator estimates, uniqueness and positive-time classical transport remain open. Fixed-hbar clock recovery, floor removal, GR/QFT/Standard Model identification and empirical validity remain open. No model or preceding operator changed; all 855 predecessor source/script hashes are preserved. The TOE remains unproved.')


    target = root/'data/physical_clock_floor_ten_characteristic_limit_audit.json'
    target.write_text(json.dumps(report, indent=2)+'\n')
    print('Root import passed;', report['audited_declaration_count'],
          'audited declarations;', len(hashes), 'verified source hashes.', flush=True)
    print(target, flush=True)


if __name__ == '__main__':
    main()
