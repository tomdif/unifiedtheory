#!/usr/bin/env python3
"""Audit exact regularized observable dynamics and energy-controlled removal.

Run with the repository toolchain and verified dependency overlay:
  lake env python3 scripts/physical_clock_floor_resolvent_balance_audit.py --overlay PATH

Sequential direct Lean checks rebuild six new modules, audit their axioms,
check the root import, and preserve the preceding source hash chain.
This does not invoke lake build and is not a TOE certificate.
"""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess


MODULES = [('KFCausalFormResolventError', 4), ('KFCausalClockFloorResolventTests', 12), ('KFCausalClockFloorResolventEhrenfest', 3), ('KFCausalClockFloorResolventBalance', 5), ('KFCausalClockFloorResolventWindow', 7), ('KFCausalClockFloorCanonicalResolventBalance', 9)]


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
    logs = overlay/'physical-clock-floor-resolvent-balance-audit'
    logs.mkdir(exist_ok=True)
    (overlay/'UnifiedTheory/Audit').mkdir(parents=True, exist_ok=True)
    previous_path = root/'data/physical_clock_floor_adapted_neutral_form_audit.json'
    previous_hash = sha256(previous_path)
    previous = json.loads(previous_path.read_text())
    sources = list(previous['source_sha256'])
    sources += ['UnifiedTheory/Audit/'+name+'.lean' for name, _ in MODULES]
    sources += ['scripts/physical_clock_floor_resolvent_balance_audit.py']
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
        scope='For the actual charge-averaged Hamiltonian at any frozen time, the scaled shifted resolvent R=Lambda*(Lambda+H)^-1 is a symmetric contraction with a constructed bounded lift from physical Hilbert space to the reference completed energy form. For every bounded physical operator D, R D R and R D.adjoint R have constructed bounded form lifts and the exact physical duality identity. A general variational estimate proves the squared state regularization error is at most the form energy divided by 4*Lambda, requiring only the form domain. The observable error is bounded by 2*norm(D)*norm(state)*sqrt(energy/(4*Lambda)). Along the actual propagator, every such regularized observable has an exact complex expectation derivative, continuous quantum form rate and all-endpoint integral identity. The original bounded observable increments differ from the integrated regularized rate by the derived endpoint errors. For the actual normalized canonically boosted states, fixed positive floor and width, nonnegative mass-squared, quartic and vacuum coefficients, and every admissible nonzero hbar sequence tending to zero, the energy at the frozen initial time is eventually bounded uniformly on each finite symmetric time window by B=exp(4*T)*initialBudget. One eventual index threshold works for every positive Lambda and every bounded contraction test. The expectation error is at most 2*sqrt(B/(4*Lambda)); the integrated balance error is at most 4*sqrt(B/(4*Lambda)). Both errors tend to zero along every positive Lambda sequence tending to infinity, simultaneously with hbar tending to zero, even for moving contraction tests and bounded moving endpoints; no relation between the two parameter scales is assumed. The actual complete canonical Weyl family is explicitly identified with these tests, and the bounds and limits are specialized to its original evolved characteristics at arbitrary moving frequencies. These are regularized observable identities and controlled removal of regularization in expectations and integrated balances. They do not prove that bare canonical tests preserve the averaged form, a derivative formula for the unregularized tests, a uniformly bounded normalized rate, or a classical symbol or transport limit. Full twelve-dimensional tightness and probability evolution, neutral-position and negative-clock-momentum control, limits of unbounded quantum energy-output pairings, subsequence independence, late-time zero clock defect, fixed-hbar recovery, floor removal, physical GR/QFT/Standard Model identification and empirical validity remain open. No model or preceding operator changed; no necessity of changing the model is established. All 916 predecessor source/script hashes are preserved. The TOE remains unproved.')


    target = root/'data/physical_clock_floor_resolvent_balance_audit.json'
    target.write_text(json.dumps(report, indent=2)+'\n')
    print('Root import passed;', report['audited_declaration_count'],
          'audited declarations;', len(hashes), 'verified source hashes.', flush=True)
    print(target, flush=True)


if __name__ == '__main__':
    main()
