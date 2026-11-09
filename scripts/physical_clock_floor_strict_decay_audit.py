#!/usr/bin/env python3
"""Recompile and audit the all-time strict quantum clock-defect decrease and its long-time limit structure in the revised clock-floor model.

Run through the repository toolchain, using its previously verified dependencies:
  lake env python3 scripts/physical_clock_floor_strict_decay_audit.py --overlay PATH

This does not invoke lake build. It rebuilds all ten new modules in dependency
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


MODULES = [('KFCausalClockFloorStrictDefectSign', 10), ('KFCausalStrictMultiplierPairing', 6), ('KFCausalClockFloorVacuumOutputFaithful', 7), ('KFCausalClockFloorStrictOutputRate', 10), ('KFCausalAveragedStrictRate', 1), ('KFCausalClockFloorAveragedStrictRate', 4), ('KFCausalClockFloorStrictQuantumDecay', 4), ('KFCausalClockFloorStrictQuantumLimit', 6), ('KFCausalClockFloorSquaredEhrenfest', 6), ('KFCausalClockFloorStrictQuantumNorm', 5)]


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
    logs = overlay/'physical-clock-floor-strict-decay-audit'
    logs.mkdir(exist_ok=True)
    (overlay/'UnifiedTheory/Audit').mkdir(parents=True, exist_ok=True)
    previous_path = root/'data/physical_clock_floor_initial_rate_audit.json'
    previous_hash = sha256(previous_path)
    previous = json.loads(previous_path.read_text())
    sources = list(previous['source_sha256'])
    sources += ['UnifiedTheory/Audit/'+name+'.lean' for name, _ in MODULES]
    sources += ['scripts/physical_clock_floor_strict_decay_audit.py']
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
        scope='For the optional equal-mobility clock-floor model, proves that at fixed epsilon>0, positive vacuum coupling, and any nonzero hbar with abs(hbar)<=2*pi*epsilon/3, the actual quantum clock-defect expectation has strictly negative derivative at every real time for every nonzero state in the completed charge-averaged energy form. The actual analytic shifted multiplier has a strictly negative velocity coefficient for nonzero hbar. An integrable multiplier pairing is strictly negative on every nonzero L2 output, without assuming a uniform coercive lower bound. The actual ordered exponential has trivial kernel: the bounded inverse-clock-half factor is injective and the longitudinal exponential has a proved inverse graph. Closedness of the ordered factor and the existing joint-closure component theorem show the vacuum output cannot vanish on a nonzero physical vector at positive vacuum coupling. The other seven rate contributions are nonpositive. Strict negativity survives actual unitary charge averaging because every section has nonzero physical embedding. It then passes to the completed form and the constructed form flow by physical norm conservation. The existing exact Ehrenfest derivative yields strict decrease of Re<psi(t),D psi(t)> on the entire real line, where D=epsilon/(exp(s)+epsilon). The result also applies directly to every nonzero vector in the actual averaged energy-operator domain. Normalized zero-charge admissible states exist with this strict decrease and arbitrarily small defect norm retained at every future time. This removes the prior restriction to an initial Gaussian family, sufficiently small hbar, and a possibly hbar-dependent local interval. No semiclassical limit or assumed force convergence is used. The expectation is positive at every finite time and converges to a nonnegative limit strictly below every finite-time value. The integrated negative exact rate converges to the initial expectation minus that limit. The actual inequalities norm(D f)^2<=Re<f,D f><=norm(f)*norm(D f) prove that a zero expectation limit is equivalent to decay of the defect norm under the unitary evolution. The squared analytic defect has the same strict velocity sign. A new exact Ehrenfest identity for D squared is derived from the existing weak form equation and strong form continuity. It proves strictly negative derivative of norm(D psi(t)) squared and hence strict decrease of the physical clock-error norm on the entire real line for every nonzero averaged energy-form state at positive vacuum coupling. Normalized zero-charge energy states with strict norm decrease and arbitrarily small all-future norm defect exist. The norm also has a nonnegative limit strictly below each finite-time value. Neither limiting value is proved to be zero; strict decrease alone does not establish that. A quantum fixed-state zero-defect limit, positive-time quantum-to-classical transport and evolving unbounded-output convergence, full classical-symbol identification and reduced-sector invariance, joint small-floor control, finite-capacity/Jordan limits, GR/QFT/Standard Model recovery, and empirical identification remain open. No prior model, factor order, or operator is changed. All 607 predecessor source/script hashes are preserved. The TOE remains unproved.')


    target = root/'data/physical_clock_floor_strict_decay_audit.json'
    target.write_text(json.dumps(report, indent=2)+'\n')
    print('Root import passed;', report['audited_declaration_count'],
          'audited declarations;', len(hashes), 'verified source hashes.', flush=True)
    print(target, flush=True)


if __name__ == '__main__':
    main()
