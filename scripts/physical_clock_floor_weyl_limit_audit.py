#!/usr/bin/env python3
"""Recompile and audit the actual canonical Weyl algebra, scaled commutator limit and positivity of limiting quantum characteristics.

Run through the repository toolchain, using its previously verified dependencies:
  lake env python3 scripts/physical_clock_floor_weyl_limit_audit.py --overlay PATH

This does not invoke lake build. It rebuilds all four new modules in dependency
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


MODULES = [('KFCausalCanonicalWeylAlgebra', 10), ('KFCausalCanonicalWeylLimit', 6), ('KFCausalCanonicalWeylDirac', 4), ('KFCausalClockFloorEvolvedCharacteristics', 8)]


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
    logs = overlay/'physical-clock-floor-weyl-limit-audit'
    logs.mkdir(exist_ok=True)
    (overlay/'UnifiedTheory/Audit').mkdir(parents=True, exist_ok=True)
    previous_path = root/'data/physical_clock_floor_classical_transport_audit.json'
    previous_hash = sha256(previous_path)
    previous = json.loads(previous_path.read_text())
    sources = list(previous['source_sha256'])
    sources += ['UnifiedTheory/Audit/'+name+'.lean' for name, _ in MODULES]
    sources += ['scripts/physical_clock_floor_weyl_limit_audit.py']
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
        scope='For the actual L2 ordered modulation/translation phase tests, proves the exact Weyl product W_h(l,v) W_h(m,w) = exp(i*h*m(v)) W_h(l+m,v+w). Quantitative product and commutator bounds hold on every L2 vector, with errors bounded by explicit multiples of abs(h) and the vector norm. The scaled commutator divided by i*h converges to the canonical symplectic coefficient m(v)-l(w) times W_h(l+m,v+w), uniformly over all unit vectors; this is a result for bounded canonical phase tests, not a commutator theorem for the unbounded Hamiltonian. Gram matrix entries differ from the characteristic evaluated at frequency differences by a controlled O(abs(h)) term. Consequently, if normalized-state characteristics converge pointwise along a nonzero h sequence tending to zero, their limit is one at zero, bounded by one, conjugate symmetric, and has real nonnegative finite quadratic forms. This proves positivity of any such limit without assuming it, but assumes pointwise convergence and does not prove existence or continuity of the limit, tightness, or its representation by a probability measure. The generic operators are identified exactly with the existing twelve-frequency physical observables. Applying the estimates to the actual constructed unitary clock-floor propagator gives continuous-time characteristics, uniform bounds, and unscaled and scaled commutator convergence uniform over all real evolution times for normalized initial states. The positive-kernel limit theorem applies even to arbitrary sequences of evolution times, conditional on pointwise characteristic convergence. The uniform-in-time algebra estimates follow from unitary norm preservation; they are not uniform-in-time convergence of quantum dynamics to classical dynamics. No energy-form-domain preservation by these phase tests is asserted. Positive-time state transport to the previously constructed classical Liouville law, convergence of unbounded outputs, controlled full ordered-Hamiltonian symbol identification, fixed-hbar quantum zero-defect convergence, joint small-floor control, GR/QFT/Standard Model recovery and empirical identification remain open. No predecessor model definition or quantum operator changed. All 685 predecessor source/script hashes are preserved. The TOE remains unproved.')


    target = root/'data/physical_clock_floor_weyl_limit_audit.json'
    target.write_text(json.dumps(report, indent=2)+'\n')
    print('Root import passed;', report['audited_declaration_count'],
          'audited declarations;', len(hashes), 'verified source hashes.', flush=True)
    print(target, flush=True)


if __name__ == '__main__':
    main()
