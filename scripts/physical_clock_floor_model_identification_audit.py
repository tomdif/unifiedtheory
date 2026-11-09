#!/usr/bin/env python3
"""Recompile and audit the classical clock defect and consistent finite reconstruction.

Run through the repository toolchain, using its previously verified dependencies:
  lake env python3 scripts/physical_clock_floor_model_identification_audit.py --overlay PATH

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


MODULES = [
    ('KFCausalClockFloorCanonicalDefect', 13),
    ('KFCausalClockFloorDefectLimits', 10),
    ('KFCausalClockFloorFiniteReconstruction', 11),
    ('KFCausalClockFloorClassicalBackreaction', 9),
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
    logs = overlay/'physical-clock-floor-model-identification-audit'
    logs.mkdir(exist_ok=True)
    (overlay/'UnifiedTheory/Audit').mkdir(parents=True, exist_ok=True)
    previous_path = root/'data/physical_clock_floor_averaged_convergence_audit.json'
    previous_hash = sha256(previous_path)
    previous = json.loads(previous_path.read_text())
    sources = list(previous['source_sha256'])
    sources += ['UnifiedTheory/Audit/'+name+'.lean' for name, _ in MODULES]
    sources += ['scripts/physical_clock_floor_model_identification_audit.py']
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
        scope='Classical symbol and finite constraint identification audit for the optional equal-mobility clock-floor model. With C=exp(s)+epsilon, L=p/C, the canonical (s,p) bracket is {L,C}=-exp(s)/C, with defect epsilon/C, and {L,exp(s)+epsilon*s}=-1. The actual complete longitudinal transport has clock rate exp(s)/C. The existing positive-clock global translation obstruction applies; this is not an impossibility theorem for a commutator on a noninvariant quantum core. Exact differentiation of H=C/2+(E/2+kappa*exp(L))/C gives both clock backreaction components multiplied by exp(s)/C relative to the original equations with the same observables and time. Positive potential produces strictly positive clock-velocity error; the clock-only energy also has nonzero longitudinal-velocity error. With one free matter momentum and E=pi^2, matter-position velocity remains pi/C. At pi=C/2, no common scalar time rescaling restores both this velocity and the original longitudinal velocity. This does not exclude more general variable changes or models, and no quantum-to-classical limit is assumed. Under the sufficient parameter bound used by the current averaged quantum construction, abs(hbar)<=2*pi*epsilon/3, fixed nonzero hbar forces epsilon>=3*abs(hbar)/(2*pi). The bracket defect has a strictly positive lower bound on every log-clock region s<=S, cannot converge to zero there, and any defect-zero limit under that bound must send s to positive infinity. At fixed nonnegative epsilon, the defect tends to zero as s tends to positive infinity; it also tends to zero pointwise as epsilon tends to zero, but that second route cannot retain the stated bound at fixed nonzero hbar. An explicit clock-region accuracy estimate is proved. These are scalar estimates, not localized-state or dynamical control results. In the actual finite six-flavor occupation model, merely shifting the constraint clock while retaining the old regularized longitudinal datum leaves residual mean(source)-epsilon*spatialDeriv(oldL). A new optional finite longitudinal matrix uses the shifted positive clock in the Jordan reconstruction as well as the homogeneous datum. It is Hermitian, its exact local constraint equals mean(source), and that constraint annihilates the zero-charge sector. At epsilon=0 it equals the previous exponential ordering. An exact Jordan resolvent identity gives its correction from the old datum; reduction to inverse-clock multiplication retains an explicit clock/primitive commutation hypothesis. The existing regularized finite model and all predecessor sources are unchanged. No finite-capacity limit, semiclassical limit of ordered or averaged quantum evolution, preservation of a large-clock state regime, GR/QFT/Standard Model recovery, or empirical identification is proved. The revised quantum construction remains valid within its existing scope, but it is not automatically identified with the original canonical physical dynamics. The parameter bound is a sufficient proof condition, not a proved necessary condition for all admissible states. The TOE remains unproved.')


    target = root/'data/physical_clock_floor_model_identification_audit.json'
    target.write_text(json.dumps(report, indent=2)+'\n')
    print('Root import passed;', report['audited_declaration_count'],
          'audited declarations;', len(hashes), 'verified source hashes.', flush=True)
    print(target, flush=True)


if __name__ == '__main__':
    main()
