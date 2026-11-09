#!/usr/bin/env python3
"""Recompile and audit the physical displaced phase coordinates, exact Gaussian centering and the clock-plus-shear phase limit.

Run through the repository toolchain, using its previously verified dependencies:
  lake env python3 scripts/physical_clock_floor_displaced_centering_audit.py --overlay PATH

This does not invoke lake build. It rebuilds all six new modules in dependency
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


MODULES = [('KFCausalDisplacedPhysicalPhase', 8), ('KFCausalDisplacedClassicalAverage', 5), ('KFCausalClockFloorCenteredGaussian', 6), ('KFCausalClockFloorDisplacedCentering', 8), ('KFCausalClockFloorDisplacedShiftPhase', 10), ('KFCausalClockFloorDisplacedPhaseLimit', 8)]


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
    logs = overlay/'physical-clock-floor-displaced-centering-audit'
    logs.mkdir(exist_ok=True)
    (overlay/'UnifiedTheory/Audit').mkdir(parents=True, exist_ok=True)
    previous_path = root/'data/physical_clock_floor_displaced_averaged_domain_audit.json'
    previous_hash = sha256(previous_path)
    previous = json.loads(previous_path.read_text())
    sources = list(previous['source_sha256'])
    sources += ['UnifiedTheory/Audit/'+name+'.lean' for name, _ in MODULES]
    sources += ['scripts/physical_clock_floor_displaced_centering_audit.py']
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
        scope='The actual enlarged displacement parameters determine paired physical position centres and canonical momenta: positions are the negatives of the packet translation parameters, and momenta include the exact 2*pi*hbar Fourier scale. Their charge orbit follows the inverse classical rotation; every fixed canonical momentum boost has the exact hbar-independent phase orbit rotate(-theta)(0,toPaired p). A proved periodic-mean change of orientation identifies the classical eight-factor candidate average on these parameter orbits with the existing charge-averaged classical Hamiltonian. No quantum energy limit is inferred from that finite coordinate identity. The displaced analytic Gaussian is rewritten by exact completion of the square before taking norms. The small displacement amplitude and large real source cancel exactly. The proof identifies its physical centre and phase frequencies, proves the exact complex modulus and a centred error bound, and identifies this centred packet with the actual sourced analytic packet including neutral shear. Recentering the real physical flow gives the actual complex shifted position. The inverse-clock derivative yields the derivative of its relative scale and shifted position. The inverse-hbar transverse phase ratio has a proved limit with the physical shear contribution. Together with the previously checked clock ratio, its squared modulus tends to exp((p_clock+shear)/C), C=exp(s)+epsilon. This limit remains valid at sqrt(abs(hbar))-rescaled fluctuations around each centre and is proved on every actual canonical boosted charge parameter orbit, for arbitrary nonzero hbar sequences tending to zero at fixed positive epsilon. These are exact coordinate, Gaussian, local estimate and pointwise phase-factor results. They do not yet prove the corresponding full complex Gaussian density limit, uniform integrable domination, averaged quantum energy convergence, Hamiltonian symbol or commutator control, positive-time quantum transport, fixed-hbar quantum zero-defect convergence, joint small-floor control or physical GR/QFT/Standard Model and empirical identification. The clock distribution is not replaced by a point-localized clock. No model, operator or predecessor source changed. All 731 predecessor source/script hashes are preserved. The TOE remains unproved.')


    target = root/'data/physical_clock_floor_displaced_centering_audit.json'
    target.write_text(json.dumps(report, indent=2)+'\n')
    print('Root import passed;', report['audited_declaration_count'],
          'audited declarations;', len(hashes), 'verified source hashes.', flush=True)
    print(target, flush=True)


if __name__ == '__main__':
    main()
