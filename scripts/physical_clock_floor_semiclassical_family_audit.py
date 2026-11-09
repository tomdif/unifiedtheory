#!/usr/bin/env python3
"""Recompile and audit a uniform-energy small-Planck family for the actual clock-floor evolution.

Run through the repository toolchain, using its previously verified dependencies:
  lake env python3 scripts/physical_clock_floor_semiclassical_family_audit.py --overlay PATH

This does not invoke lake build. It rebuilds all nine new modules in dependency
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
    ('KFCausalPhysicalGaussianNormalization', 7),
    ('KFCausalPhysicalGaussianGradientBound', 6),
    ('KFCausalClockFloorGaussianEnergyBounds', 6),
    ('KFCausalClockFloorTrialEnergyNorms', 10),
    ('KFCausalClockFloorTrialMatterEnergy', 5),
    ('KFCausalClockFloorTrialUniformEnergy', 6),
    ('KFCausalAveragedFixedEnergy', 2),
    ('KFCausalClockFloorSemiclassicalStates', 9),
    ('KFCausalClockFloorSemiclassicalDynamics', 4),
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
    logs = overlay/'physical-clock-floor-semiclassical-family-audit'
    logs.mkdir(exist_ok=True)
    (overlay/'UnifiedTheory/Audit').mkdir(parents=True, exist_ok=True)
    previous_path = root/'data/physical_clock_floor_exact_ehrenfest_audit.json'
    previous_hash = sha256(previous_path)
    previous = json.loads(previous_path.read_text())
    sources = list(previous['source_sha256'])
    sources += ['UnifiedTheory/Audit/'+name+'.lean' for name, _ in MODULES]
    sources += ['scripts/physical_clock_floor_semiclassical_family_audit.py']
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
        scope='For the optional equal-mobility clock-floor model, constructs an actual normalized zero-charge Gaussian family in the reference completed energy form with a Planck-independent initial-energy bound K. Conditions: fixed epsilon>0, clock width a>0, nonnegative mass2/quartic/vacuum, arbitrary fixed initial time s, hbar!=0, and abs(hbar)<=min(1,2*pi*epsilon/3). K is the explicitly defined energyBudget/clockMass; clockMass is proved positive and all relevant clock moments are integrable. Exact transverse Gaussian normalization, width-halving bounds, and a kinetic mass bound proportional to abs(hbar) control the shrinking transverse widths. The existing analytic-strip estimates bound the actual ordered exponential and linear/quadratic matter outputs relative to the same Gaussian mass. Their exact operator graphs supply the full eight-factor seed energy bound. A generic theorem proves that averaging an invariant state preserves its original form energy exactly. The actual family is lifted into the completed averaged form and normalized without assuming a uniform energy hypothesis. For its actual unbounded evolution, the previously proved exact clock-defect expectation derivative differs from the classical-coefficient pairing on its quantum energy outputs by at most abs(hbar)*(20/epsilon^2)*exp(2*T)*K for all abs(t-s)<=T. An epsilon-delta theorem proves this discrepancy tends uniformly to zero on every bounded time window, with admissible nonzero parameters arbitrarily close to zero. This is a coefficient comparison on an actual evolving state family, not convergence of quantum energy outputs to a classical phase-space density or trajectory. The clock floor and clock profile remain fixed. A joint small-floor limit still needs control of K as epsilon changes; uniform energy control of the prior arbitrarily-small-defect family is not asserted. Classical concentration and transport, finite-capacity and Jordan reconstruction limits, GR/QFT/Standard Model recovery and empirical identification remain open. No model, factor ordering or prior operator changed. All 561 predecessor source/script hashes are preserved. The TOE remains unproved.')


    target = root/'data/physical_clock_floor_semiclassical_family_audit.json'
    target.write_text(json.dumps(report, indent=2)+'\n')
    print('Root import passed;', report['audited_declaration_count'],
          'audited declarations;', len(hashes), 'verified source hashes.', flush=True)
    print(target, flush=True)


if __name__ == '__main__':
    main()
