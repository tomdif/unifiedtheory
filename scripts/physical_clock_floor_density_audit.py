#!/usr/bin/env python3
"""Recompile and audit the dense natural common energy domain for the revised clock-floor model.

Run through the repository toolchain, using its previously verified dependencies:
  lake env python3 scripts/physical_clock_floor_density_audit.py --overlay PATH

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
    ('KFCausalClockFloorProductStates', 4),
    ('KFCausalClockFloorCoreWeights', 6),
    ('KFCausalClockFloorCoreStates', 9),
    ('KFCausalClockFloorCoreDerivative', 5),
    ('KFCausalClockFloorCoreGradient', 6),
    ('KFCausalClockFloorCoreMatter', 10),
    ('KFCausalClockFloorCoreDensity', 2),
    ('KFCausalClockFloorCommonDensity', 9),
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
    logs = overlay/'physical-clock-floor-density-audit'
    logs.mkdir(exist_ok=True)
    (overlay/'UnifiedTheory/Audit').mkdir(parents=True, exist_ok=True)
    previous = json.loads((root/'data/physical_clock_floor_common_audit.json').read_text())
    sources = list(previous['source_sha256'])
    sources += ['UnifiedTheory/Audit/'+name+'.lean' for name, _ in MODULES]
    sources += ['scripts/physical_clock_floor_density_audit.py']
    hashes = {p: sha256(root/p) for p in sources}
    assert all(hashes[p] == h for p, h in previous['source_sha256'].items())
    root_hash = sha256(root/'UnifiedTheory.lean')
    root_text = (root/'UnifiedTheory.lean').read_text()
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
    assert all(sha256(root/p) == h for p, h in hashes.items()), 'Sources changed during verification.'
    report = dict(
        modules=checks, root_check=dict(command=['lean', '-j1', 'UnifiedTheory.lean'], exit_code=0,
            empty_log=True, source_sha256=root_hash, log_sha256=sha256(log)),
        audited_declaration_count=sum(n for _, n in MODULES), source_sha256=hashes,
        lean_toolchain=(root/'lean-toolchain').read_text().strip(),
        scope='For the optional equal-mobility clock-floor revision, proved Hilbert-norm density of the exact natural common domain of all eight energy factors for epsilon>0 and abs(hbar)<=pi*epsilon. The result holds for any four transverse momentum directions and any continuous linear transverse field. An explicit family consists of the actual revised coordinate unitary applied to products of modulated scalar damped Gaussians, multiplied by the square root of the shifted clock, and arbitrary Schwartz transverse packets. The scalar clock weights, nonvanishing, and L2 estimates are proved. Generic product Fourier identities are transferred to the actual revised spectral exponential graph, with the exact complex-shifted scalar output. Actual clock-half and inverse-clock-half graphs fix the ordered dressing. All transverse derivatives, including the neutral shear, have a joint integrable majorant and define the actual maximal momentum actions. The real inverse-coordinate flow has a fourth-moment bound that puts the shifted output in both maximal field domains. Thus every family member lies in the eight natural composition domains. Fourier uniqueness gives totality of the scalar-weighted product family, and the onto revised coordinate unitary transfers it to physical Hilbert space; density is not assumed to be preserved by an unbounded multiplication. Each factor domain is consequently dense. The four ordered momentum factors are also proved closable via their densely defined reversed compositions. This is Hilbert-norm density, not an operator graph-core or form-core theorem. Density of the charge-zero intersection or of the averaged energy domain is not asserted. Full matter-factor closability, closed Hamiltonian completion, averaged Hamiltonian and constraint-preserving dynamics remain open for the revision. The previous normalized nonzero charge-zero common-domain witness remains valid in its separately proved range abs(hbar)<=2*pi*epsilon/3 with hbar nonzero. The original model and finite executable are unchanged. Necessity of changing the original model, finite-to-infinite Jordan/Sylvester identification, controlled limits, GR/QFT recovery and empirical identification remain unproved. The parameter bounds do not justify a zero-floor limit at fixed nonzero hbar. The TOE remains unproved.')


    target = root/'data/physical_clock_floor_density_audit.json'
    target.write_text(json.dumps(report, indent=2)+'\n')
    print('Root import passed;', report['audited_declaration_count'],
          'audited declarations;', len(hashes), 'verified source hashes.', flush=True)
    print(target, flush=True)


if __name__ == '__main__':
    main()
