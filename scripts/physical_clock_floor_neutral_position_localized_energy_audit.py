#!/usr/bin/env python3
"""Audit the localized action on the full unaveraged closed energy graph.

Run with the repository toolchain and verified dependency overlay:
  lake env python3 scripts/physical_clock_floor_neutral_position_localized_energy_audit.py --overlay PATH

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


MODULES = [('KFCausalGaussianCutoffTaylor', 5), ('KFCausalBoundedLpMultiplier', 3), ('KFCausalLpMultiplierDerivative', 2), ('KFCausalGaussianCutoffOperator', 9), ('KFCausalGaussianCutoffMomentum', 3), ('KFCausalPhysicalGaussianCutoff', 8), ('KFCausalNeutralPositionLocalizedKinetics', 8), ('KFCausalJointGraphBoundedCorrection', 3), ('KFCausalNeutralPositionLocalizedEnergy', 7), ('KFCausalNeutralPositionLocalizedEnergyBound', 9)]


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
    logs = overlay/'physical-clock-floor-neutral-position-localized-energy-audit'
    logs.mkdir(exist_ok=True)
    (overlay/'UnifiedTheory/Audit').mkdir(parents=True, exist_ok=True)
    previous_path = root/'data/physical_clock_floor_neutral_position_localized_audit.json'
    previous_hash = sha256(previous_path)
    previous = json.loads(previous_path.read_text())
    sources = list(previous['source_sha256'])
    sources += ['UnifiedTheory/Audit/'+name+'.lean' for name, _ in MODULES]
    sources += ['scripts/physical_clock_floor_neutral_position_localized_energy_audit.py']
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
        scope='For positive clock floor epsilon and Gaussian width delta, the actual localized neutral-position observable is multiplication by exp(-delta*(x2+x3)^2)*exp(i*v*x4). A uniform quadratic Taylor remainder for the Gaussian gives an operator-norm derivative of the actual shifted L2 multiplier. The translation-generator characterization proves its product rule on the entire natural spectral momentum domain, and the established Euclidean coordinate unitary transports this to the actual physical transverse momentum. Composing with the bare phase and inverse clock gives the exact localized ordered kinetic correction. In direction d its norm is at most abs(hbar)*(2*sqrt(delta)*abs(d2+d3)+abs(v*d4))/sqrt(epsilon)*norm(state). No smooth-state assumption or assumed momentum-domain preservation is used. For hbar nonzero and abs(hbar)<=2*pi*epsilon/3, the same localized input preserves every one of the actual eight unaveraged natural energy graphs: clock half, four ordered kinetic factors, linear and quadratic physical-field matter factors, and ordered exponential. A bounded input/output/state-correction map passes these derived identities through the simultaneous weighted graph closure, including zero weights. Consequently the actual full unaveraged closed energy domain is preserved. The exact transformed output applies the real multiplier to the first five rows and the imaginary-shift multiplier to the last three rows, and adds a bounded weighted kinetic correction. Its norm is at most exp(v^2*hbar^2/(8*delta*epsilon^2))*norm(original output)+abs(hbar)*C*norm(state), with C the square root of the sum of squared weighted directional constants and zero constants on the clock and matter rows. All graph and bound hypotheses are instantiated for the actual physical operators. Matter coupling positivity is not required. The previous fixed-state strong L2 cutoff limit remains available, but convergence in energy graph norm and uniform cutoff removal on changing states are not proved; the shifted bound is not uniform as delta tends to zero at fixed nonzero hbar and v. Charge-compatible localization on the full averaged energy form, a full normalized Hamiltonian response, neutral-position time variation and position tightness remain unproved. Full twelve-dimensional dynamics, negative-clock-momentum control, classical force identification and uniqueness, clock-defect removal, fixed-hbar recovery, floor removal, GR/QFT/Standard Model identification and empirical validation remain open. No preceding physical operator or model is changed and no necessity of a model change is established. All 1054 predecessor source/script hashes are preserved. The TOE remains unproved.')


    target = root/'data/physical_clock_floor_neutral_position_localized_energy_audit.json'
    target.write_text(json.dumps(report, indent=2)+'\n')
    print('Root import passed;', report['audited_declaration_count'],
          'audited declarations;', len(hashes), 'verified source hashes.', flush=True)
    print(target, flush=True)


if __name__ == '__main__':
    main()
