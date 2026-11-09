#!/usr/bin/env python3
"""Audit physical time domination and consistency of actual neutral spacetime force limits.

Run with the repository toolchain and verified dependency overlay:
  lake env python3 scripts/physical_clock_floor_neutral_spacetime_consistency_audit.py --overlay PATH

Sequential direct Lean checks rebuild nine new modules, audit their axioms,
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


MODULES = [('KFCausalCompactWeakDomination', 1), ('KFCausalCompactTimeMarginal', 7), ('KFCausalLocalTimeMarginal', 5), ('KFCausalCompactWeakRestriction', 4), ('KFCausalCompactTimeRestriction', 7), ('KFCausalSpacetimeRestriction', 4), ('KFCausalConsistentSpacetimeWindows', 8), ('KFCausalNeutralSpacetimeConsistency', 6), ('KFCausalNeutralConsistentSpacetimeDynamics', 1)]


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
    logs = overlay/'physical-clock-floor-neutral-spacetime-consistency-audit'
    logs.mkdir(exist_ok=True)
    (overlay/'UnifiedTheory/Audit').mkdir(parents=True, exist_ok=True)
    previous_path = root/'data/physical_clock_floor_neutral_spacetime_force_audit.json'
    previous_hash = sha256(previous_path)
    previous = json.loads(previous_path.read_text())
    sources = list(previous['source_sha256'])
    sources += ['UnifiedTheory/Audit/'+name+'.lean' for name, _ in MODULES]
    sources += ['scripts/physical_clock_floor_neutral_spacetime_consistency_audit.py']
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
        scope='A fixed finite-measure upper bound survives weak convergence on a compact metric space, proved by extracting positive complementary measures. Applying this to the compactified time marginal passes the actual combined physical time-marginal bound to the positive and negative spacetime limits. The dominating compactified Lebesgue measure has no atoms, hence every compactified time slice has zero combined limiting mass. Restriction to the open square followed by the tangent inverse preserves the time-marginal domination on real spacetime. Its combined time marginal is absolutely continuous with respect to Lebesgue measure restricted to the original window; all real time slices and the complement of the window have zero mass. A generic weak-restriction theorem is proved for finite measures on compact metric spaces when the limiting measure gives zero mass to the frontier. Its proof extracts complementary positive restrictions, passes closed support to their limits and identifies them by addition and the null frontier; variable masses are allowed. Compact time strips have frontier contained in their endpoint time slices. Physical time domination therefore makes every ordered real time strip a continuity set. Restriction to a time strip commutes exactly with arctangent compactification and with the recovery of finite real spacetime points. Before any limit, the full spacetime measure constructed from a continuous-mass finite kernel restricts exactly to the measure of every smaller time window, not merely to its momentum projection. This gives exact restriction identities for the actual positive and negative force measures. Every common compactified spacetime limit of the actual model inherits the physical time bound and weak convergence of both positive components on every ordered real subwindow of any chosen window, on the SAME subsequence without further extraction. Uniqueness of weak limits proves exact agreement of restrictions on all shared ordered real subwindows. Full-window restriction is the identity. These derived properties construct a structured family of compactified force measures; returning to finite real points preserves full-window identity, nested-window restriction and agreement on overlaps. Its local combined time marginal obeys the physical bound and absolute continuity, and there are no time atoms. The assembled actual-model existence theorem constructs this family on the same subsequence as the all-real-time weakly continuous neutral probability curve, initial Dirac law, characteristic convergence at every time and frequency, fixed-time weak probability convergence, additive interval-force family, C0 interval convergence, and Schwartz probability balance. It preserves all preceding whole-window C0 spacetime convergence, local mass bounds and cutoff identifications. It additionally proves weak compactified convergence of the actual positive and negative forces and C0 real spacetime force-action convergence on EVERY ordered real subwindow within any chosen member of the countable window family. The physical time bound and consistency lemmas require nonnegative matter coefficients; the full dynamics existence theorem retains fixed positive floor and width, strictly positive matter coefficients, an admissible nonzero hbar sequence tending to zero, and any positive diverging resolvent scale sequence. No limiting time domination, absence of atoms, or consistency is supplied as an extra assumption in that existence theorem. These results close the previously open limit time-marginal, arbitrary subwindow-convergence and overlap-consistency gaps. A single global spacetime force measure has not yet been assembled from the compatible local family. The full continuity equation for general time-dependent spacetime tests remains open. Possible escaped momentum mass remains retained at compactification boundaries; global positive-force tightness and its absence are not assumed or proved. A closed classical force functional, independence across semiclassical subsequences, full phase-space dynamics, remaining canonical controls, neutral-position and negative-clock-momentum bounds, late-time zero clock defect, fixed-hbar recovery, floor removal, GR/QFT/Standard Model identification and empirical validity remain open. The positive-floor clock obstruction persists. No model or preceding operator changed and no necessity of a model change is established. All 984 predecessor source/script hashes are preserved. The TOE remains unproved.')


    target = root/'data/physical_clock_floor_neutral_spacetime_consistency_audit.json'
    target.write_text(json.dumps(report, indent=2)+'\n')
    print('Root import passed;', report['audited_declaration_count'],
          'audited declarations;', len(hashes), 'verified source hashes.', flush=True)
    print(target, flush=True)


if __name__ == '__main__':
    main()
