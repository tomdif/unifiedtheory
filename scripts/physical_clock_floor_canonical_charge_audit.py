#!/usr/bin/env python3
"""Audit canonical clock charge invariance, Born tails and sufficient tightness controls.

Run with the repository toolchain and verified dependency overlay:
  lake env python3 scripts/physical_clock_floor_canonical_charge_audit.py --overlay PATH

Sequential direct Lean checks rebuild five new modules, audit their axioms,
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


MODULES = [('KFCausalCanonicalClockCharge', 5), ('KFCausalCanonicalClockChargeGraph', 5), ('KFCausalCanonicalClockProbability', 8), ('KFCausalCanonicalClockTails', 7), ('KFCausalCanonicalClockControl', 5)]


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
    logs = overlay/'physical-clock-floor-canonical-charge-audit'
    logs.mkdir(exist_ok=True)
    (overlay/'UnifiedTheory/Audit').mkdir(parents=True, exist_ok=True)
    previous_path = root/'data/physical_clock_floor_canonical_momentum_bridge_audit.json'
    previous_hash = sha256(previous_path)
    previous = json.loads(previous_path.read_text())
    sources = list(previous['source_sha256'])
    sources += ['UnifiedTheory/Audit/'+name+'.lean' for name, _ in MODULES]
    sources += ['scripts/physical_clock_floor_canonical_charge_audit.py']
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
        scope='Canonical physical clock translations commute exactly with the actual charge circle on every L2 state, proved through the actual paired/mixed coordinate unitaries. Charge action preserves and reflects the entire maximal canonical clock-momentum graph and domain, and preserves output norm. The finite Born measure is constructed as the physical Fourier L2 density pushed forward by 2*pi*hbar*k_clock. Its total mass is the state squared norm, and its characteristic function is the actual clock-translation expectation at hbar*v. Characteristic-function uniqueness proves equality of the whole measure under charge rotation, without a momentum-domain, smoothness, normalization or charge-zero hypothesis. Both two-sided tails and arbitrary-set charge averages are exactly unchanged. The actual maximal momentum graph supplies the Fourier second moment and R^2*tail(R)<=norm(Pf)^2, with a compact-interval probability bound. Square-integrable charge-orbit graph outputs exist if and only if the original state is in the maximal canonical momentum domain; any such output has exactly the same squared L2 norm as the actual momentum output. Thus charge-orbit graph estimates transfer to the original state. The previous differentiable weighted-longitudinal/shear reconstruction supplies a quantitative two-sided tail bound under its explicit L2 controls. Uniform actual momentum-output bounds imply tightness of arbitrary families of the constructed finite measures. All these facts concern the existing canonical clock generator, distinct from weighted transverse operators with similar names. They apply to every actual evolved L2 vector as statements of charge invariance, but they do not supply evolved momentum-domain membership or uniform output bounds. No Hamiltonian form invariance, full-Hamiltonian charge conservation, longitudinal charge symmetry, graph-core density, or exponential form core is inferred. Negative evolved longitudinal tails, canonical clock-momentum tightness for the prescribed evolution, continuous joint eleven-coordinate dynamics, classical force identification, full phase-space transport, quantum clock-defect recovery, regulator removal, GR/QFT/Standard Model identification and empirical validation remain open. No model or Hamiltonian changed. All 1188 predecessor source/script hashes are preserved. The TOE remains unproved.')


    target = root/'data/physical_clock_floor_canonical_charge_audit.json'
    target.write_text(json.dumps(report, indent=2)+'\n')
    print('Root import passed;', report['audited_declaration_count'],
          'audited declarations;', len(hashes), 'verified source hashes.', flush=True)
    print(target, flush=True)


if __name__ == '__main__':
    main()
