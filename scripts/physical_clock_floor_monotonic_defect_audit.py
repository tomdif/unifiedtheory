#!/usr/bin/env python3
"""Recompile and audit all-forward-time clock-defect control for the actual averaged evolution.

Run through the repository toolchain, using its previously verified dependencies:
  lake env python3 scripts/physical_clock_floor_monotonic_defect_audit.py --overlay PATH

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


MODULES = [
    ('KFCausalPartialFourierMultiplier', 3),
    ('KFCausalClockFloorChargeDefect', 11),
    ('KFCausalAveragedFormAction', 6),
    ('KFCausalClockFloorAveragedFormDefect', 7),
    ('KFCausalClockFloorAveragedHamiltonianDefect', 1),
    ('KFCausalYosidaSignedPairing', 1),
    ('KFCausalBoundedDefectMonotonicity', 4),
    ('KFCausalClockFloorDefectMonotonicity', 7),
]


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
    logs = overlay/'physical-clock-floor-monotonic-defect-audit'
    logs.mkdir(exist_ok=True)
    (overlay/'UnifiedTheory/Audit').mkdir(parents=True, exist_ok=True)
    previous_path = root/'data/physical_clock_floor_energy_defect_audit.json'
    previous_hash = sha256(previous_path)
    previous = json.loads(previous_path.read_text())
    sources = list(previous['source_sha256'])
    sources += ['UnifiedTheory/Audit/'+name+'.lean' for name, _ in MODULES]
    sources += ['scripts/physical_clock_floor_monotonic_defect_audit.py']
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
        scope='For the optional equal-mobility clock-floor model with epsilon>0, hbar!=0 and abs(hbar)<=2*pi*epsilon/3, the physical clock-defect norm is nonincreasing along the actual charge-averaged nonautonomous unitary evolution on every L2 state. First proved that any measurable contractive spectator-block multiplier commutes with the actual partial Fourier transform on all product L2, using the established tensor density theorem. Transported the physical D=epsilon/C through the actual paired, mixed and charge coordinates and proved that D commutes with the actual charge-circle action. Constructed the bounded action of D on the entire actual charge-averaged form space, with exact physical embedding and exact L2 output R applied pointwise. The signed squared-defect output pairing survives the charge integral. The actual averaged Hamiltonian therefore satisfies hbar*Im(inner(H*f,D^2*f))>=0 on its full operator domain. No preservation of that operator domain by D is assumed. Proved a generic resolvent algebra theorem transferring this sign to bounded Yosida approximants and instantiated it with the constructed averaged resolvent. Proved the norm-square derivative and nonincrease along the actual strongly differentiable bounded Yosida dynamics. Passed to the previously proved whole-sequence strong limit on every L2 state. Consequently norm(D*U(s,t)*f)<=norm(D*f) for every t>=s, and the norm is nonincreasing as final time increases for each fixed initial time and state. Combined this with the constructed normalized zero-charge states in the actual averaged energy domain: for every delta>0 and initial time s there exists such a state whose evolution remains normalized, has exactly zero standing charge, and has defect norm below delta for every t>=s. This closes the previous state-dependent-time-interval gap for fixed-floor norm-defect control. It proves nonincrease, not strict decay or convergence to zero for each fixed state. At fixed positive floor, exact zero defect for a nonzero state remains excluded, and the previously proved large-clock energy cost remains. No model, factor ordering or operator was changed. The canonical quantum clock commutator, controlled quantum-to-classical and finite-capacity limits, GR/QFT/Standard Model recovery and empirical identification remain unproved. All 527 predecessor source hashes are preserved. The TOE remains unproved.')


    target = root/'data/physical_clock_floor_monotonic_defect_audit.json'
    target.write_text(json.dumps(report, indent=2)+'\n')
    print('Root import passed;', report['audited_declaration_count'],
          'audited declarations;', len(hashes), 'verified source hashes.', flush=True)
    print(target, flush=True)


if __name__ == '__main__':
    main()
