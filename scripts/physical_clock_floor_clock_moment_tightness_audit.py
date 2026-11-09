#!/usr/bin/env python3
"""Recompile and audit higher clock moments and the uniform lower log-clock tail bound for actual evolved canonical boosts on finite forward windows.

Run through the repository toolchain, using its previously verified dependencies:
  lake env python3 scripts/physical_clock_floor_clock_moment_tightness_audit.py --overlay PATH

This does not invoke lake build. It rebuilds all eight new modules in dependency
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


MODULES = [('KFCausalClockFloorPowerVelocityScalar', 5), ('KFCausalClockFloorPowerVelocityPairing', 8), ('KFCausalClockFloorPowerForm', 6), ('KFCausalClockFloorPowerVelocityOutput', 8), ('KFCausalClockFloorPowerEhrenfest', 4), ('KFCausalClockFloorClockMomentLaw', 8), ('KFCausalClockFloorDisplacedMomentWindow', 7), ('KFCausalClockFloorDisplacedClockLeftTail', 4)]


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
    logs = overlay/'physical-clock-floor-clock-moment-tightness-audit'
    logs.mkdir(exist_ok=True)
    (overlay/'UnifiedTheory/Audit').mkdir(parents=True, exist_ok=True)
    previous_path = root/'data/physical_clock_floor_displaced_initial_rate_audit.json'
    previous_hash = sha256(previous_path)
    previous = json.loads(previous_path.read_text())
    sources = list(previous['source_sha256'])
    sources += ['UnifiedTheory/Audit/'+name+'.lean' for name, _ in MODULES]
    sources += ['scripts/physical_clock_floor_clock_moment_tightness_audit.py']
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
        scope='For every fixed positive integer power of the actual bounded clock defect, the complex-shift power velocity differs from the nonpositive classical power drift by an explicit constant times abs(hbar). This estimate is proved first pointwise, then for arbitrary L2 pairings, all eight output factors, and the charge-averaged output. The actual defect powers preserve the evolving energy form and intertwine its output powers. The form-space Ehrenfest theorem gives an exact derivative and integral formula for every power on actual unitary evolved form states, with upward rate bounded by the same constant times abs(hbar) times evolved energy. The boosted initial power moments are exactly the corresponding clock-law integrals, independent of hbar and canonical momentum, and tend to zero with moment order. A weighted Markov estimate bounds the physical L2 probability in a lower log-clock half-space by a defect moment. Previously proved energy bounds make each fixed moment increase by at most an error tending to zero uniformly on each finite forward time window. Choosing moment order first, a sufficiently negative clock threshold second, and sufficiently small hbar third proves that the probability below that threshold is arbitrarily small uniformly over the whole window. The final statement uses the actual normalized canonical momentum boosts and their actual unitary evolution, with fixed positive floor and clock width, fixed canonical momentum and initial time, nonnegative mass-squared, quartic and vacuum couplings, and any nonzero hbar sequence tending to zero inside the existing strip from either or mixed signs. No moment convergence, quantum tightness, classical evolved measure or transport conclusion is assumed. This is an eventual uniform lower-tail estimate for one configuration marginal, not a full phase-space tightness theorem or identification of quantum dynamics with the classical flow. Negative clock-momentum control, general phase-test commutators, positive-time classical correspondence, fixed-hbar long-time zero clock defect, floor removal, GR/QFT/Standard Model identification and empirical validity remain open. No model or preceding operator changed; all 789 predecessor source/script hashes are preserved. The TOE remains unproved.')


    target = root/'data/physical_clock_floor_clock_moment_tightness_audit.json'
    target.write_text(json.dumps(report, indent=2)+'\n')
    print('Root import passed;', report['audited_declaration_count'],
          'audited declarations;', len(hashes), 'verified source hashes.', flush=True)
    print(target, flush=True)


if __name__ == '__main__':
    main()
