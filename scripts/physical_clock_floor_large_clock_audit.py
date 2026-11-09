#!/usr/bin/env python3
"""Recompile and audit admissible large-clock states, localization and clock-energy cost.

Run through the repository toolchain, using its previously verified dependencies:
  lake env python3 scripts/physical_clock_floor_large_clock_audit.py --overlay PATH

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
    ('KFCausalClockFloorDefectOperator', 7),
    ('KFCausalClockLocalizedZeroState', 8),
    ('KFCausalDenseUnitSmallImage', 1),
    ('KFCausalClockFloorSmallDefectStates', 3),
    ('KFCausalClockFloorDefectLocalization', 5),
    ('KFCausalClockFloorDefectEnergy', 6),
    ('KFCausalClockFloorEnergyClockDomain', 2),
    ('KFCausalClockFloorLargeClockFamily', 3),
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
    logs = overlay/'physical-clock-floor-large-clock-audit'
    logs.mkdir(exist_ok=True)
    (overlay/'UnifiedTheory/Audit').mkdir(parents=True, exist_ok=True)
    previous_path = root/'data/physical_clock_floor_model_identification_audit.json'
    previous_hash = sha256(previous_path)
    previous = json.loads(previous_path.read_text())
    sources = list(previous['source_sha256'])
    sources += ['UnifiedTheory/Audit/'+name+'.lean' for name, _ in MODULES]
    sources += ['scripts/physical_clock_floor_large_clock_audit.py']
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
        scope='For the optional equal-mobility clock-floor model, constructed the actual bounded L2 multiplier D=epsilon/(exp(s)+epsilon) and proved it is a contraction and injective at fixed positive epsilon. D measures the classical clock-bracket defect on a state; no equality to a quantum commutator or semiclassical error is assumed. Explicit continuous compact-clock bumps times the already verified physical charge-invariant transverse Gaussian give nonzero, normalized, zero-charge target states above any log-clock threshold. The targets themselves are not asserted energy-admissible. A general density and continuous-normalization theorem transfers a strict bounded-operator estimate to a dense linear domain. The actual proved density of zero-charge averaged-energy states discharges this hypothesis, producing normalized, zero-charge, averaged-energy-admissible states with arbitrarily small D norm under epsilon>0, hbar nonzero and abs(hbar)<=2*pi*epsilon/3. A sequence with D norm tending to zero is constructed. Multiplication by the indicator of log-clock s<=S has norm bounded by (exp(S)+epsilon)/epsilon times the defect norm, so this sequence escapes every fixed upper clock threshold in L2 mass. All zero-charge averaged-energy states are proved to belong to the actual half-clock domain, using the zero-sector form identification and the retained closed joint graph component. The unaveraged closed form satisfies norm(sqrt(C)f)^2<=2*norm(energyOutput)^2. Exact half-clock/inverse-half pairings and Cauchy-Schwarz prove epsilon<=norm(sqrt(C)f)^2*norm(Df) for every normalized state in the actual half-clock domain. At fixed positive epsilon, D-norm recovery cannot occur with uniformly bounded clock energy, and the clock-half norm must tend to infinity along any such family. The final family theorem combines normalization, actual zero-charge graph, actual averaged-energy membership, finite half-clock graph at every member, vanishing defect, vanishing mass below every fixed clock threshold and divergent clock-half norm. The actual previously constructed averaged unitary evolution preserves normalization and zero charge at all times. Strong continuity proves small defect persists for some positive state-dependent time interval; a common interval, quantitative lifetime or small defect at all times for the whole family is not proved. The construction is an existence argument via proved density, not an explicit computational family with uniform energy bounds or an approximation error rate. Fixed-time initial state feasibility is closed; controlled evolution over a prescribed common interval, finite-capacity and semiclassical limits, quantum commutator identification, GR/QFT/Standard Model recovery and empirical identification remain open. The clock floor remains fixed. Identification of the form energy with the ordered seed retains existing nonnegative coefficient assumptions. All predecessor source files and the older model are preserved. The TOE remains unproved.')


    target = root/'data/physical_clock_floor_large_clock_audit.json'
    target.write_text(json.dumps(report, indent=2)+'\n')
    print('Root import passed;', report['audited_declaration_count'],
          'audited declarations;', len(hashes), 'verified source hashes.', flush=True)
    print(target, flush=True)


if __name__ == '__main__':
    main()
