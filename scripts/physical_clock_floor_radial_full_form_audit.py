#!/usr/bin/env python3
"""Audit the actual radial test on the full averaged Hamiltonian form.

Run with the repository toolchain and verified dependency overlay:
  lake env python3 scripts/physical_clock_floor_radial_full_form_audit.py --overlay PATH

Sequential direct Lean checks rebuild ten new modules, audit their axioms,
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


MODULES = [('KFCausalClockFloorMultiplicationRelations', 2), ('KFCausalClockFloorTransverseFourierField', 5), ('KFCausalMixedStripFieldGraph', 3), ('KFCausalNeutralPositionRadialMatter', 4), ('KFCausalNeutralPositionRadialEnergy', 7), ('KFCausalNeutralPositionRadialEnergyBound', 7), ('KFCausalNeutralPositionRadialFormAction', 4), ('KFCausalLpOutputCorrection', 2), ('KFCausalNeutralPositionRadialAveragedForm', 8), ('KFCausalNeutralPositionRadialCompletedForm', 5)]


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
    logs = overlay/'physical-clock-floor-radial-full-form-audit'
    logs.mkdir(exist_ok=True)
    (overlay/'UnifiedTheory/Audit').mkdir(parents=True, exist_ok=True)
    previous_path = root/'data/physical_clock_floor_radial_exponential_audit.json'
    previous_hash = sha256(previous_path)
    previous = json.loads(previous_path.read_text())
    sources = list(previous['source_sha256'])
    sources += ['UnifiedTheory/Audit/'+name+'.lean' for name, _ in MODULES]
    sources += ['scripts/physical_clock_floor_radial_full_form_audit.py']
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
        scope='The original charge-compatible radial test P now acts on the full existing regulated energy form. The actual weighted clock straightening preserves and reflects arbitrary unbounded multiplication relations. The physical point-field symbol is derived in the straightened paired coordinates, and its spectator dependence proves preservation and reflection of every natural field-power relation by the physical transverse Fourier change. The actual mixed strip multiplier therefore preserves the natural field and field-square graphs. For positive epsilon and delta, nonzero hbar and abs(hbar)<=2*pi*epsilon/3, these shifted-output identities compose with the previously proved ordered exponential rule to give both actual ordered field-matter rows. All eight natural factor identities enter the simultaneous weighted graph closure, allowing zero weights, and prove preservation of the original closed energy domain by P. The output is R y+C f: R applies P on the first five rows and the constructed Q(-hbar/2) on the final three; C is supported on the second momentum row. Its norm is bounded by B*norm(y)+abs(hbar)*c*norm(f), where B=exp(v^2*hbar^2/(8*delta*epsilon^2)) and c=sqrt(1/2)*(4*sqrt(delta)+abs(v))/sqrt(epsilon), independently of time and matter couplings. A bounded lift to the unaveraged closed graph form is explicitly constructed. The actual charge commutation then constructs a bounded action on the actual charge-averaged form space, proves full averaged energy-domain and graph preservation, and derives the full eight-output L2 identity and the same bound after averaging. A further bounded action is constructed on the completed form of the existing charge-averaged Hamiltonian, with its physical embedding and output identities, the full output bound, and exact commutation with the existing time-transfer maps. No domain-preservation or output identity for P is supplied as a physical hypothesis; the generic section and graph lemmas are instantiated with the derived identities. This is a fixed-regulator form-domain result, not Hamiltonian operator-domain preservation or a response derivative theorem. Adjoint identities, hbar-normalized full Hamiltonian response, neutral-position time variation and tightness, and energy graph-norm cutoff removal remain open. B is not uniform as delta tends to zero at fixed nonzero hbar and v. The small-hbar condition does not supply floor removal at fixed hbar. Full twelve-dimensional dynamics, negative-clock-momentum control, classical force closure and uniqueness, clock-defect recovery, fixed-hbar recovery, floor removal, GR/QFT/Standard Model identification and empirical validation remain open. The Hamiltonian and physical model are unchanged; no necessity of a model change is established. All 1104 predecessor source/script hashes are preserved. The TOE remains unproved.')


    target = root/'data/physical_clock_floor_radial_full_form_audit.json'
    target.write_text(json.dumps(report, indent=2)+'\n')
    print('Root import passed;', report['audited_declaration_count'],
          'audited declarations;', len(hashes), 'verified source hashes.', flush=True)
    print(target, flush=True)


if __name__ == '__main__':
    main()
