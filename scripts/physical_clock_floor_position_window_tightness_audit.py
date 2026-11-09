#!/usr/bin/env python3
"""Audit derived neutral-position tightness over full finite time windows.

Run with the repository toolchain and verified dependency overlay:
  lake env python3 scripts/physical_clock_floor_position_window_tightness_audit.py --overlay PATH

Sequential direct Lean checks rebuild sixteen new modules, audit their axioms,
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


MODULES = [('KFCausalDyadicHeatCancellation', 6), ('KFCausalDyadicOscillatoryHeat', 7), ('KFCausalRadialStripGeometry', 11), ('KFCausalMixedDyadicStripResponse', 6), ('KFCausalFiniteMultiplierAverage', 12), ('KFCausalNeutralPositionDyadicShift', 3), ('KFCausalDyadicResponseChoice', 4), ('KFCausalNeutralPositionDyadicOutput', 3), ('KFCausalNeutralPositionDyadicFullResponse', 6), ('KFCausalNeutralPositionDyadicEhrenfest', 5), ('KFCausalNeutralPositionDyadicWindow', 3), ('KFCausalDyadicWindowChoice', 4), ('KFCausalNeutralPositionDyadicApproximation', 2), ('KFCausalNeutralPositionLowFrequencyTime', 1), ('KFCausalUniformCharacteristicTail', 3), ('KFCausalNeutralPositionWindowTightness', 4)]


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
    logs = overlay/'physical-clock-floor-position-window-tightness-audit'
    logs.mkdir(exist_ok=True)
    (overlay/'UnifiedTheory/Audit').mkdir(parents=True, exist_ok=True)
    previous_path = root/'data/physical_clock_floor_neutral_position_time_audit.json'
    previous_hash = sha256(previous_path)
    previous = json.loads(previous_path.read_text())
    sources = list(previous['source_sha256'])
    sources += ['UnifiedTheory/Audit/'+name+'.lean' for name, _ in MODULES]
    sources += ['scripts/physical_clock_floor_position_window_tightness_audit.py']
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
        scope='Finite dyadic averages of the existing charge-compatible radial observables now close the actual neutral-position escape gap on full finite time windows, at fixed positive clock floor. A telescoping Gaussian estimate keeps cancellation across scales before taking norms. The actual analytic clock inverse and radial/shear geometry derive the uniform shift constant C=exp(4*v^2/delta)*(8/(epsilon*N)+2*abs(v)/(epsilon*sqrt(delta))) for N positive scales delta_j=delta*2^j, j<N. It applies to the existing opposite half-clock-shift operators throughout abs(hbar)<=2*pi*epsilon/3, uniformly in all transverse coordinates. The cancellation survives all eight energy rows, the charge average and the completed Hamiltonian form. The full normalized diagonal response is at most C*energy+2*c(epsilon,delta*2^N,v)*norm(state)*sqrt(energy), with the previously derived kinetic constant c. Exact derivative and integral identities are proved for the finite averaged expectation on the existing unbounded unitary propagator, and the actual boosted-state energy bound supplies uniform time-window estimates. The number of scales, their widths and a positive frequency interval can be chosen so the full window constant is arbitrarily small while all widths remain below any prescribed positive threshold. Uniform charged-tail cutoff approximation then proves that the bare canonical position characteristic varies arbitrarily little over an entire time window at sufficiently small frequency. Integrating that derived estimate in frequency, together with the previously proved initial characteristic limit, supplies uniform Born position tails without assuming spatial tightness, negative clock momentum control or energy-output tails. For fixed epsilon>0 and initial clock width a>0, nonnegative couplings, and every admissible nonzero hbar sequence tending to zero, each finite window and positive tolerance admit a compact interval and eventual index containing all but that tolerance of every actual evolved position law throughout the window. Every eventually window-bounded moving-time sequence of these laws is tight as a whole and has a weakly convergent subsequence. No single subsequence valid at all times, position probability limit curve, cutoff-free response derivative, classical force closure or uniqueness is asserted here. Full twelve-dimensional phase-space dynamics, negative-clock-momentum control, quantum clock-defect recovery, fixed-hbar and clock-floor removal, GR/QFT/Standard Model identification and empirical validation remain open. The Hamiltonian and model are unchanged; no necessity of a model change is established. All 1134 predecessor source/script hashes are preserved. The TOE remains unproved.')


    target = root/'data/physical_clock_floor_position_window_tightness_audit.json'
    target.write_text(json.dumps(report, indent=2)+'\n')
    print('Root import passed;', report['audited_declaration_count'],
          'audited declarations;', len(hashes), 'verified source hashes.', flush=True)
    print(target, flush=True)


if __name__ == '__main__':
    main()
