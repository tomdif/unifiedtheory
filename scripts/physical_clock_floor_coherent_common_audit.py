#!/usr/bin/env python3
"""Recompile and audit all eight natural domains of the enlarged clock-floor family and its clock-output orbit.

Run through the repository toolchain, using its previously verified dependencies:
  lake env python3 scripts/physical_clock_floor_coherent_common_audit.py --overlay PATH

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
    ('KFCausalClockFloorCoherentMoments', 6),
    ('KFCausalClockFloorCoherentDerivative', 10),
    ('KFCausalClockFloorCoherentClockMomentum', 10),
    ('KFCausalClockFloorCoherentCommonDomain', 9),
    ('KFCausalDominatedL2Continuity', 2),
    ('KFCausalClockFloorCoherentOrbitContinuity', 12),
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
    logs = overlay/'physical-clock-floor-coherent-common-audit'
    logs.mkdir(exist_ok=True)
    (overlay/'UnifiedTheory/Audit').mkdir(parents=True, exist_ok=True)
    previous = json.loads((root/'data/physical_clock_floor_coherent_bridge_audit.json').read_text())
    sources = list(previous['source_sha256'])
    sources += ['UnifiedTheory/Audit/'+name+'.lean' for name, _ in MODULES]
    sources += ['scripts/physical_clock_floor_coherent_common_audit.py']
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
        scope='The enlarged physical charge-modulation family now belongs to every natural clock-half, ordered transverse momentum, ordered exponential and ordered linear/quadratic matter domain for epsilon,a>0, hbar nonzero and abs(hbar)<=2*pi*epsilon/3. Physical sourced Gaussians and their coordinate moments are in L2 by Gaussian absorption. Their exact transverse derivatives, including the complex-source term, are derived and in L2. Combining these with arbitrary L2 clock factors gives explicit actual maximal momentum graphs for each inverse-clock-dressed modulation state. The clock-half domain is also derived. The finite linear span of this family is Hilbert-norm dense, is contained in the common domain of all eight factors for arbitrary four transverse directions and arbitrary continuous linear field, and is preserved by the actual physical charge circle. Every orbit point has an explicit lift into the previously constructed closed unaveraged form, with its embedding and seed energy identified. This is not a graph/form-core theorem and does not yet prove that the full form orbit is measurable or square-integrable. Separately, a proved dominated-L2 continuity criterion applies to physical sourced profiles along the parameter orbit; the actual clock-half output is continuous, lies in L2 of the normalized angle measure, and has finite integrated squared norm. The remaining momentum, exponential and matter output orbits still need their full L2/form-lift assembly. Averaged-domain and zero-charge energy-domain density, an averaged Hamiltonian and constraint-preserving dynamics remain open. The earlier fixed-time unaveraged revised Hamiltonian and normalized averaged-energy witness remain valid. No original-model impossibility or necessity of a model change is established. Finite-to-infinite matching, controlled limits, GR/QFT/SM recovery and empirical identification remain unproved; these bounds do not justify removing the clock floor at fixed nonzero hbar. The TOE remains unproved.')


    target = root/'data/physical_clock_floor_coherent_common_audit.json'
    target.write_text(json.dumps(report, indent=2)+'\n')
    print('Root import passed;', report['audited_declaration_count'],
          'audited declarations;', len(hashes), 'verified source hashes.', flush=True)
    print(target, flush=True)


if __name__ == '__main__':
    main()
