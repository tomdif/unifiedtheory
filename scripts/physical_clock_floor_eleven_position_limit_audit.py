#!/usr/bin/env python3
"""Audit the all-time position probability curve and eleven-coordinate limits.

Run with the repository toolchain and verified dependency overlay:
  lake env python3 scripts/physical_clock_floor_eleven_position_limit_audit.py --overlay PATH

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


MODULES = [('KFCausalProbabilityFrequencyTail', 4), ('KFCausalJointCharacteristicModulus', 1), ('KFCausalNeutralPositionFrequencyControl', 3), ('KFCausalNeutralPositionTemporalCompactness', 5), ('KFCausalNeutralPositionTemporalProbability', 1), ('KFCausalCanonicalElevenCoordinates', 7), ('KFCausalElevenCharacteristicCompactness', 4), ('KFCausalElevenCountableCharacteristics', 2), ('KFCausalElevenPositionLimit', 2)]


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
    logs = overlay/'physical-clock-floor-eleven-position-limit-audit'
    logs.mkdir(exist_ok=True)
    (overlay/'UnifiedTheory/Audit').mkdir(parents=True, exist_ok=True)
    previous_path = root/'data/physical_clock_floor_position_window_tightness_audit.json'
    previous_hash = sha256(previous_path)
    previous = json.loads(previous_path.read_text())
    sources = list(previous['source_sha256'])
    sources += ['UnifiedTheory/Audit/'+name+'.lean' for name, _ in MODULES]
    sources += ['scripts/physical_clock_floor_eleven_position_limit_audit.py']
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
        expected = {'UnifiedTheory.Audit.'+name+'.'+n for n in
                    re.findall(r'^#print axioms (\S+)', (root/source).read_text(), re.M)}
        assert {n for n, _ in audits} == expected, (name, expected)
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
        scope='Actual neutral-position Born tails now give frequency equicontinuity uniformly over finite time windows and over all base frequencies. The generic probability estimate is norm(charFun(v)-charFun(w)) <= abs(v-w)*R+2*tail(abs(x)>R); no unweighted position moment is assumed. The normalized unitary identity also yields uniform small-frequency displacement of the actual neutral-position phase operator. Combined with the previously derived bare time modulus, these estimates prove eventual joint time-frequency equicontinuity without assuming time Lipschitz continuity or a cutoff-free derivative. For every admissible nonzero hbar sequence tending to zero at fixed positive clock floor and initial clock width, with nonnegative couplings, one subsequence has a weakly continuous neutral-position probability curve on all real times. Its initial law is the origin, its characteristics converge uniformly on every compact time-frequency set, and the same subsequence converges weakly at arbitrary moving times approaching any fixed time. Neutral position is also added to the existing ten canonical directions. The eleven-coordinate continuous linear encoding has a proved left inverse and is injective; clock momentum remains omitted. An exact ordered operator product has no extra scalar phase, and its displacement is bounded by the old ten-coordinate displacement plus the actual neutral-position displacement. This gives uniform small-coefficient control over finite forward windows, continuous positive normalized characteristic limits at bounded moving sampling times, and one common subsequence for any countable collection of independently window-bounded sampling sequences. A final further extraction aligns all these eleven-coordinate kernels with the all-real-time position probability curve. At every convergent sampling sequence their neutral-position restrictions equal that curve at the limiting time. The eleven-coordinate kernels have derived normalization, conjugation symmetry and positive classical difference kernels; an eleven-coordinate representing probability measure, a time-dependent joint eleven-coordinate law, force closure and uniqueness are not asserted here. Full twelve-dimensional phase-space dynamics, negative-clock-momentum control, quantum clock-defect recovery, fixed-hbar and clock-floor removal, GR/QFT/Standard Model identification and empirical validation remain open. The Hamiltonian and model are unchanged. All 1151 predecessor source/script hashes are preserved. The TOE remains unproved.')


    target = root/'data/physical_clock_floor_eleven_position_limit_audit.json'
    target.write_text(json.dumps(report, indent=2)+'\n')
    print('Root import passed;', report['audited_declaration_count'],
          'audited declarations;', len(hashes), 'verified source hashes.', flush=True)
    print(target, flush=True)


if __name__ == '__main__':
    main()
