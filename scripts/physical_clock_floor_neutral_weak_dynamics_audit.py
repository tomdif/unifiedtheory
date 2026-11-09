#!/usr/bin/env python3
"""Audit the derived neutral weak dynamics and the Schwartz force balance.

Run with the repository toolchain and verified dependency overlay:
  lake env python3 scripts/physical_clock_floor_neutral_weak_dynamics_audit.py --overlay PATH

Sequential direct Lean checks rebuild four new modules, audit their axioms,
check the root import, and preserve the preceding source hash chain.
This does not invoke lake build and is not a TOE certificate.
"""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess


MODULES = [('KFCausalVanishingForceTests', 5), ('KFCausalSchwartzForceFourier', 6), ('KFCausalWeakForceBalance', 5), ('KFCausalNeutralWeakDynamics', 2)]


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
    logs = overlay/'physical-clock-floor-neutral-weak-dynamics-audit'
    logs.mkdir(exist_ok=True)
    (overlay/'UnifiedTheory/Audit').mkdir(parents=True, exist_ok=True)
    previous_path = root/'data/physical_clock_floor_neutral_local_force_audit.json'
    previous_hash = sha256(previous_path)
    previous = json.loads(previous_path.read_text())
    sources = list(previous['source_sha256'])
    sources += ['UnifiedTheory/Audit/'+name+'.lean' for name, _ in MODULES]
    sources += ['scripts/physical_clock_floor_neutral_weak_dynamics_audit.py']
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
        scope='Every continuous complex test vanishing at infinity on real momentum now extends continuously by zero to the two endpoints of the arctangent compactification. The proof uses the compact-set characterization of vanishing at infinity and the exact arctangent/tangent identities; it does not assume absent endpoint mass. Pullback is exactly the original C0 test. Consequently compactified positive and negative force-measure convergence gives convergence of the local finite signed force-pair action on ALL C0 tests. For every finite real measure, the integral of the Fourier transform of a Schwartz function equals its frequency pairing with the characteristic function at -2*pi*v. Fubini is justified by an integrable product bound. The corresponding signed-force and derivative identities are proved with the exact Fourier convention. The force characteristic norm is at most half its combined positive/negative mass. The previously derived eventual mass bound dominates the frequency integrands by a constant times the norm of a Schwartz multiplier. Dominated convergence and Schwartz Fourier inversion therefore yield the integrated continuity equation: integral f dnu - integral f dmu = J.evaluate(deriv f), for every complex Schwartz test, whenever J is the derived local force limit and the original Fourier responses converge. A generic extraction theorem constructs J and a subsequence converging on all C0 tests from just the mass bound and original Fourier balance; no limiting force or continuity equation is assumed. For the actual fixed-positive-floor and fixed-positive-width model, strictly positive matter coefficients, any admissible nonzero hbar sequence tending to zero, and any positive resolvent scale sequence tending to infinity, the assembled theorem constructs one subsequence and the same weakly continuous all-real-time neutral probability curve with its initial Dirac law, original characteristic convergence at every time/frequency, and weak exact probability convergence at every fixed time. For ANY chosen countable family of ordered real intervals, that same subsequence carries the compactified positive/negative force limits, convergence on all C0 tests to their finite real-line restrictions, and the integrated continuity equation on every Schwartz test for each interval. A second theorem constructs one common neutral probability curve and, for EVERY ordered real interval, an interval-dependent further subsequence and an actual finite force pair with the same C0 convergence and Schwartz continuity equation. It does not claim a common force subsequence for all uncountably many intervals. These are derived integrated weak dynamics of the neutral momentum marginal, not a closed classical evolution law. Global force-pair tightness or vanishing escaped endpoint mass is neither assumed nor proved. Additivity and consistency of the finite signed interval fluxes as a spacetime measure, identification of a classical force functional, uniqueness across semiclassical subsequences, and full phase-space dynamics remain open. The remaining canonical controls, neutral-position and negative-clock-momentum bounds, late-time zero clock defect, fixed-hbar recovery, floor removal, GR/QFT/Standard Model identification and empirical validity are not proved. The positive-floor clock obstruction remains. No model or preceding operator changed, and no necessity of a model change is established. All 965 predecessor source/script hashes are preserved. The TOE remains unproved.')


    target = root/'data/physical_clock_floor_neutral_weak_dynamics_audit.json'
    target.write_text(json.dumps(report, indent=2)+'\n')
    print('Root import passed;', report['audited_declaration_count'],
          'audited declarations;', len(hashes), 'verified source hashes.', flush=True)
    print(target, flush=True)


if __name__ == '__main__':
    main()
