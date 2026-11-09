#!/usr/bin/env python3
"""Audit the full averaged eight-factor energy-form lift of actual coherent momentum.

Run with the repository toolchain and verified dependency overlay:
  lake env python3 scripts/coherent_momentum_energy_audit.py --overlay PATH

Sequential direct Lean checks rebuild six new modules, audit their axioms,
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


MODULES = [('KFCausalCoherentMomentumOutputReduction', 4), ('KFCausalBoundedClockMatterGraphs', 6), ('KFCausalCoherentMomentumMatterOrbit', 6), ('KFCausalCoherentMomentumFullOrbit', 5), ('KFCausalCoherentMomentumEnergyLift', 10), ('KFCausalCoherentFullMomentumPairing', 4)]


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
    logs = overlay/'coherent-momentum-energy-audit'
    logs.mkdir(exist_ok=True)
    (overlay/'UnifiedTheory/Audit').mkdir(parents=True, exist_ok=True)
    previous_path = root/'data/coherent_momentum_factor_audit.json'
    previous_hash = sha256(previous_path)
    previous = json.loads(previous_path.read_text())
    sources = list(previous['source_sha256'])
    sources += ['UnifiedTheory/Audit/'+name+'.lean' for name, _ in MODULES]
    sources += ['scripts/coherent_momentum_energy_audit.py']
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
        assert not re.search(r'\b(sorry|admit|axiom|unsafe)\b', (root/source).read_text()), source
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
        scope='An exact operator identity identifies the bounded inverse shifted complex clock with epsilon^-1 times the actual shifted defect. This proves cancellation of the explicit shear-output terms inside T B on each original coherent state. The reduced actual output uses only bounded clock operators on the shifted Gaussian family at widths a and a/2, including the existing commutator correction. This cancellation is within T B and does not remove the shear contribution from the full B,T commutator. Bounded clock multipliers preserve actual physical-field and field-square graphs. The resulting linear and quadratic ordered matter outputs of the actual B f have continuous charge orbits. Finite complex sums with arbitrary coefficients and distinct seed frequencies give all eight actual energy-factor outputs of the SAME B f at every charge angle, continuous and square-integrable, for every f in the existing coherent span. Both f and its actual pure-clock momentum B f lift into the EXISTING full averaged eight-factor energy form at every fixed time. Their complex form pairing equals the integral of the sum of all eight weighted factor pairings. This density is integrable, and (-2/hbar) times the imaginary part of the full form pairing equals the integral of the corresponding signed density, independently of the chosen actual lifts. The assumptions remain epsilon>0, a>0, hbar!=0, abs(hbar)<=2*pi*epsilon/3 and the existing coherent widths; the closed-strip boundary is retained. The lift uses the existing energy weights for arbitrary real coupling parameters, and in particular covers their physical nonnegative range without changing the Hamiltonian. No invariance of the coherent span or form domain under actual Hamiltonian evolution, Hamiltonian form-core density, differentiated momentum expectation along that evolution, full-force positivity, quantitative escape, regulator removal, Einstein/Standard Model identification or octonion necessity is proved. The negative clock contribution and separate ordered matter force control remain relevant. No model change is established; the physical TOE remains unproved. All 1404 predecessor source/script hashes are preserved.')


    target = root/'data/coherent_momentum_energy_audit.json'
    target.write_text(json.dumps(report, indent=2)+'\n')
    print('Root import passed;', report['audited_declaration_count'],
          'audited declarations;', len(hashes), 'verified source hashes.', flush=True)
    print(target, flush=True)


if __name__ == '__main__':
    main()
