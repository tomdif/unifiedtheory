#!/usr/bin/env python3
"""Recompile and audit the full classical matter flow, probability transport, weak Liouville equation and quantum initial-law identification.

Run through the repository toolchain, using its previously verified dependencies:
  lake env python3 scripts/physical_clock_floor_classical_transport_audit.py --overlay PATH

This does not invoke lake build. It rebuilds all nine new modules in dependency
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


MODULES = [('KFCausalClassicalMatterInitialBounds', 2), ('KFCausalClassicalMatterEvolution', 6), ('KFCausalODEWindowStability', 2), ('KFCausalClassicalMatterFlow', 4), ('KFCausalClassicalMatterLaw', 9), ('KFCausalClassicalPhysicalPhase', 11), ('KFCausalClassicalMatterInitialLaw', 9), ('KFCausalClassicalMatterLiouville', 4), ('KFCausalClassicalMatterEvolvedLaw', 8)]


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
    logs = overlay/'physical-clock-floor-classical-transport-audit'
    logs.mkdir(exist_ok=True)
    (overlay/'UnifiedTheory/Audit').mkdir(parents=True, exist_ok=True)
    previous_path = root/'data/physical_clock_floor_classical_matter_recovery_audit.json'
    previous_hash = sha256(previous_path)
    previous = json.loads(previous_path.read_text())
    sources = list(previous['source_sha256'])
    sources += ['UnifiedTheory/Audit/'+name+'.lean' for name, _ in MODULES]
    sources += ['scripts/physical_clock_floor_classical_transport_audit.py']
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
        scope="For the unchanged full classical matter candidate at epsilon>0, mass2>=0, quartic>=0 and kappa>0, constructs an actual jointly continuous all-real-time flow from the preceding global existence and uniqueness theorem. Initial-state continuity is proved using coordinate bounds uniform over bounded initial sets, compact-ball field Lipschitz bounds and two-sided Gronwall stability; it is not an assumption. Pushforward by this flow preserves probability and obeys the flow composition law. For every finite initial measure, the transported mean clock defect tends to zero by bounded dominated convergence and the preceding pointwise recovery theorem. For every C1 compactly supported real test, the transported expectation has derivative equal to the integral of the actual Hamiltonian vector field applied to the test: the weak Liouville equation on the time-extended phase space. Compact support of the test derivative bounds its generator even though the field itself is unbounded. The exact continuous inverse coordinate map identifies the original position/momentum phase space of the quantum characteristic tests with the paired canonical phase space. The already proved actual quantum initial characteristic and energy limits are identified with an explicit initial probability law in these full coordinates. The energy identification is on that law's clock-axis support, not a general principal-symbol theorem away from that support. Evolving this initial law gives a classical probability law solving Liouville, with continuous complex phase characteristics, the proved initial characteristic, and mean clock defect tending to zero. These results construct and verify a classical transport target; they do not show that positive-time quantum states or unbounded quantum energy outputs converge to it. A controlled full symbol identification of the ordered quantum Hamiltonian, positive-time quantum transport, the fixed-hbar actual quantum zero-defect limit, joint small-floor control, GR/QFT/Standard Model recovery and empirical identification remain open. No predecessor model definition or quantum operator changed. All 675 predecessor source/script hashes are preserved. The TOE remains unproved.")


    target = root/'data/physical_clock_floor_classical_transport_audit.json'
    target.write_text(json.dumps(report, indent=2)+'\n')
    print('Root import passed;', report['audited_declaration_count'],
          'audited declarations;', len(hashes), 'verified source hashes.', flush=True)
    print(target, flush=True)


if __name__ == '__main__':
    main()
