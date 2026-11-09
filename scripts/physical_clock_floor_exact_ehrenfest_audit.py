#!/usr/bin/env python3
"""Recompile and audit the exact clock-defect Ehrenfest equation for the actual unbounded evolution.

Run through the repository toolchain, using its previously verified dependencies:
  lake env python3 scripts/physical_clock_floor_exact_ehrenfest_audit.py --overlay PATH

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


MODULES = [
    ('KFCausalWeakEnergyContinuity', 3),
    ('KFCausalClockFloorStrongFormEvolution', 5),
    ('KFCausalFormObservableDerivative', 3),
    ('KFCausalClockFloorReferenceDefect', 6),
    ('KFCausalClockFloorExactEhrenfest', 5),
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
    logs = overlay/'physical-clock-floor-exact-ehrenfest-audit'
    logs.mkdir(exist_ok=True)
    (overlay/'UnifiedTheory/Audit').mkdir(parents=True, exist_ok=True)
    previous_path = root/'data/physical_clock_floor_velocity_audit.json'
    previous_hash = sha256(previous_path)
    previous = json.loads(previous_path.read_text())
    sources = list(previous['source_sha256'])
    sources += ['UnifiedTheory/Audit/'+name+'.lean' for name, _ in MODULES]
    sources += ['scripts/physical_clock_floor_exact_ehrenfest_audit.py']
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
        scope='For the optional equal-mobility clock-floor model, proved an exact defect-expectation equation for the actual previously constructed unbounded propagator on every initial energy-form state. Passed the sharp energy bound E_t(formFlow(s,t,w))<=exp(2*abs(t-s))*E_s(w) through the actual weak cutoff limit. Weak form continuity, the sharp restarted energy bound, and form transfer imply strong continuity in the reference completed energy-form space. Proved a generic observable chain rule using this continuity and the locally Lipschitz mass-dual curve with its existing weak derivative; no strong derivative of the form state or invariance of Dom(H) is assumed. Transported the existing physical defect action to the reference graph form space, retaining its exact output identity and compatibility with time transfer. The actual defect expectation is continuously differentiable with derivative (-2/hbar)*Im(inner(g_t,R*g_t)), where g_t is the actual charge-integrated eight-factor energy output of the evolved form state and R is the proved analytic-shift output action. Also proved the corresponding exact integrated equation. Its discrepancy from Re(inner(g_t,Q*g_t)), where Q applies the revised classical drift coefficient to the three exponential outputs, is at most (20*abs(hbar)/epsilon^2)*E_t and hence at most (20*abs(hbar)/epsilon^2)*exp(2*abs(t-s))*E_s. Conditions remain epsilon>0, hbar!=0 and abs(hbar)<=2*pi*epsilon/3. Identification with the intended unclipped seed energy retains the existing nonnegative coefficient assumptions. The exact equation is derived directly from the established weak solution; pointwise convergence of cutoff forces is not claimed. The comparison still uses actual quantum energy outputs, not an identified classical phase-space density. Controlled evolving classical packets, joint small-floor and semiclassical limits with controlled energy-weighted hbar/epsilon^2 error, finite-capacity and Jordan reconstruction limits, GR/QFT/Standard Model recovery and empirical identification remain open. No model, factor ordering or prior operator changed. All 555 predecessor source hashes are preserved. The TOE remains unproved.')


    target = root/'data/physical_clock_floor_exact_ehrenfest_audit.json'
    target.write_text(json.dumps(report, indent=2)+'\n')
    print('Root import passed;', report['audited_declaration_count'],
          'audited declarations;', len(hashes), 'verified source hashes.', flush=True)
    print(target, flush=True)


if __name__ == '__main__':
    main()
