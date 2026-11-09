#!/usr/bin/env python3
"""Recompile and audit the actual physical charge-zero Gaussian and its clock-floor trial bridge.

Run through the repository toolchain, using its previously verified dependencies:
  lake env python3 scripts/physical_charge_gaussian_audit.py --overlay PATH

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


MODULES = [
    ('KFCausalChargeGaussianProducts', 10),
    ('KFCausalChargeGaussianGeometry', 7),
    ('KFCausalChargeGaussianIdentities', 7),
    ('KFCausalPhysicalGaussianCharge', 12),
    ('KFCausalClockFloorInvariantTrial', 12),
    ('KFCausalClockFloorChargeTrialBridge', 8),
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
    logs = overlay/'physical-charge-gaussian-audit'
    logs.mkdir(exist_ok=True)
    (overlay/'UnifiedTheory/Audit').mkdir(parents=True, exist_ok=True)
    previous = json.loads((root/'data/physical_clock_floor_trial_audit.json').read_text())
    sources = list(previous['source_sha256'])
    sources += ['UnifiedTheory/Audit/'+name+'.lean' for name, _ in MODULES]
    sources += ['scripts/physical_charge_gaussian_audit.py']
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
        scope='Constructed a nonzero Gaussian family in the actual physical Hilbert space, with its physical configuration representative proved through the existing paired coordinate and partial Fourier unitaries. Computed the two-dimensional Gaussian Fourier transform with the repository 2*pi normalization. Derived the charged width alpha=1/(2*abs(hbar)) for every nonzero hbar, and proved the transformed Gaussian is radial in the normalized charge rotation planes. The neutral Gaussian width may be any positive beta and the clock factor may be any continuous L2 function. Proved invariance under the actual physical circle action, membership in the maximal standing-charge operator graph with output zero, and fixation by the actual zero-charge projection. Nonzeroness follows when the clock factor at zero is nonzero. For the optional equal-mobility clock-floor revision, constructed the explicit continuous L2 clock factor (1+epsilon*exp(-s))*exp(-a*(exp(s)+epsilon*s)^2), with epsilon,a>0, and chose beta=alpha/32. The resulting physical state is nonzero and has charge zero. Proved that the ordered pointwise expression applying the inverse shifted clock half followed by the candidate inverse half-density coordinate formula is exactly the previously checked full sheared longitudinal Gaussian. Its ordinary clock Fourier transform has finite exponential longitudinal norm for abs(hbar)<=2*pi*epsilon/3. This last bridge is a function identity and Fourier estimate, not a constructed weighted unitary or a proof of membership in a revised longitudinal operator domain. The revised unitary realization, all remaining ordered energy factors, full finite-energy admissibility, common-domain density, averaged Hamiltonian and constraint-preserving dynamics remain open. The original model and finite executable are unchanged. Necessity of changing the model, finite-to-infinite Jordan/Sylvester identification, controlled limits, GR/QFT recovery and empirical identification remain unproved. The TOE remains unproved.')


    target = root/'data/physical_charge_gaussian_audit.json'
    target.write_text(json.dumps(report, indent=2)+'\n')
    print('Root import passed;', report['audited_declaration_count'],
          'audited declarations;', len(hashes), 'verified source hashes.', flush=True)
    print(target, flush=True)


if __name__ == '__main__':
    main()
