#!/usr/bin/env python3
"""Recompile and audit the actual boosted longitudinal exponential domains and uniform small-hbar output bounds.

Run through the repository toolchain, using its previously verified dependencies:
  lake env python3 scripts/physical_clock_floor_boosted_exponential_audit.py --overlay PATH

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


MODULES = [('KFCausalClockFloorBoostedSpectral', 8), ('KFCausalClockFloorBoostedCommonDomain', 9), ('KFCausalClockFloorBoostedClockPhase', 8), ('KFCausalClockFloorBoostedStripBounds', 8), ('KFCausalClockFloorBoostedExponentialBound', 6)]


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
    logs = overlay/'physical-clock-floor-boosted-exponential-audit'
    logs.mkdir(exist_ok=True)
    (overlay/'UnifiedTheory/Audit').mkdir(parents=True, exist_ok=True)
    previous_path = root/'data/physical_clock_floor_kinetic_modulation_audit.json'
    previous_hash = sha256(previous_path)
    previous = json.loads(previous_path.read_text())
    sources = list(previous['source_sha256'])
    sources += ['UnifiedTheory/Audit/'+name+'.lean' for name, _ in MODULES]
    sources += ['scripts/physical_clock_floor_boosted_exponential_audit.py']
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
        scope='For every fixed six-component canonical momentum p, the actual normalized boost M_(p/h) unitTrial has an explicitly identified graph output under the ordered longitudinal exponential exp(P_long/2) C^(-1/2), at epsilon>0, clock width a>0, nonzero h and abs(h)<=2*pi*epsilon/3. The source identification uses the exact inverse coordinate unitary and arbitrary imaginary Gaussian sources, retaining the full neutral shear. The same boosted states belong to all eight natural energy-factor domains, including both ordered matter factors, and have normalized embeddings in the completed unaveraged energy form. This does not assert operator-domain membership for the full Hamiltonian, charge-zero status, circle-averaged form membership, or evolution invariance. The clock phase ratio exp(i*p_clock/h*(inverseClock(q-i*h/2)-inverseClock(q))) has a uniform norm bound exp(abs(p_clock)/(2*epsilon)) and tends pointwise to exp(p_clock/(2*C)), where C=exp(realInverseClock(q))+epsilon. Its squared norm tends pointwise to exp(p_clock/C); these scalar limits do not assert convergence of integrated or full quantum energies. The imaginary transverse source only uses the imaginary flow coefficient, with effective momentum components (p0,p1,p2+2*p4,p3+2*p4), so its apparent 1/h divergence cancels against the imaginary shift. A joint pointwise source envelope is proved with factor exp(abs(p_clock)/(2*epsilon)+momentumSize/(8*alpha*epsilon^2)) relative to the unsourced half-width Gaussian. At the actual ground width and abs(h)<=1 this gives a finite constant independent of h. Integration and exact graph identification yield the actual ordered exponential output bound norm(output)^2 <= 8*exp(abs(p_clock)/epsilon+momentumSize/(2*epsilon^2))*stripMass/clockMass. Thus one previously uncontrolled unbounded output is uniformly bounded for these boosted states at fixed epsilon and a. The estimates do not prove the full eight-factor energy is uniformly bounded, strong convergence of the full exponential output, its classical integral limit, or positive-time quantum transport. Completing those limits, averaged-domain control, full Hamiltonian commutators, phase-space tightness, fixed-hbar quantum zero-defect convergence, joint small-floor control, GR/QFT/Standard Model recovery and empirical identification remain open. No predecessor model or quantum operator changed. All 696 predecessor source/script hashes are preserved. The TOE remains unproved.')


    target = root/'data/physical_clock_floor_boosted_exponential_audit.json'
    target.write_text(json.dumps(report, indent=2)+'\n')
    print('Root import passed;', report['audited_declaration_count'],
          'audited declarations;', len(hashes), 'verified source hashes.', flush=True)
    print(target, flush=True)


if __name__ == '__main__':
    main()
