#!/usr/bin/env python3
"""Recompile and audit a common semiclassical subsequence carrying the global clock path and countable-time positive canonical characteristic kernels of actual evolved states.

Run through the repository toolchain, using its previously verified dependencies:
  lake env python3 scripts/physical_clock_floor_joint_characteristic_limit_audit.py --overlay PATH

This does not invoke lake build. It rebuilds all five new modules in dependency
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


MODULES = [('KFCausalCountableCharacteristicCompactness', 2), ('KFCausalCharacteristicCompactUniformity', 3), ('KFCausalClockFloorCountableCharacteristics', 2), ('KFCausalClockFloorGlobalClockLimit', 3), ('KFCausalClockFloorJointClockCharacteristics', 1)]


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
    logs = overlay/'physical-clock-floor-joint-characteristic-limit-audit'
    logs.mkdir(exist_ok=True)
    (overlay/'UnifiedTheory/Audit').mkdir(parents=True, exist_ok=True)
    previous_path = root/'data/physical_clock_floor_ten_characteristic_limit_audit.json'
    previous_hash = sha256(previous_path)
    previous = json.loads(previous_path.read_text())
    sources = list(previous['source_sha256'])
    sources += ['UnifiedTheory/Audit/'+name+'.lean' for name, _ in MODULES]
    sources += ['scripts/physical_clock_floor_joint_characteristic_limit_audit.py']
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
        scope='A compact product over a countable family and a countable dense frequency set selects one strictly increasing subsequence for all family members. Eventual local equicontinuity gives continuous pointwise limits at every frequency. A finite-cover argument upgrades such convergence to uniform convergence on every compact frequency set; convergent moving frequencies also retain the pointwise limit. These results apply to the actual evolved boosted states at a countable family of sampling-time sequences. Each family member may have its own finite forward time window; no common bound on those windows is required. The concrete theorem constructs a continuous normalized bounded conjugation-symmetric positive difference kernel for each member, with one common subsequence. A corollary handles any prescribed countable family of fixed future times, including unbounded families. The previously proved eventual clock Lipschitz estimates imply local equicontinuity on the entire real time axis. One subsequence therefore has a continuous clock path on all real times, values in [0,1], the existing Lipschitz bound on each symmetric window, and uniform convergence on every compact time set. The integrated actual quantum comparison rates converge to increments of this same clock path for every pair of real endpoints. Refining this subsequence for the countable characteristic family preserves the global clock limits and balance, yielding one shared subsequence carrying both kinds of limits. All limiting objects are constructed; no pointwise limit, compactness, rate limit or classical evolved measure is assumed in the concrete theorem. The floor and initial width are fixed and positive, the initial time and canonical momentum are fixed, the couplings are nonnegative, and nonzero hbar approaches zero within the existing strip from either or mixed signs. The kernel records proved properties and is not a representing probability measure. Characteristic limits still concern only ten independent frequency directions and a prescribed countable collection of future times; no temporal continuity or all-real-time characteristic evolution is proved. Quantum dynamic control of neutral position and negative clock momentum, representing probability measures, full twelve-dimensional phase-space limits, compatibility of clock limits with such measures, Hamiltonian phase-test domain and commutator estimates, uniqueness and positive-time classical transport remain open. The comparison-rate limit retains quantum energy outputs and is not yet identified with a classical transport rate. Fixed-hbar zero clock defect, floor removal, GR/QFT/Standard Model identification and empirical validity remain open. No model or preceding operator changed; all 861 predecessor source/script hashes are preserved. The TOE remains unproved.')


    target = root/'data/physical_clock_floor_joint_characteristic_limit_audit.json'
    target.write_text(json.dumps(report, indent=2)+'\n')
    print('Root import passed;', report['audited_declaration_count'],
          'audited declarations;', len(hashes), 'verified source hashes.', flush=True)
    print(target, flush=True)


if __name__ == '__main__':
    main()
