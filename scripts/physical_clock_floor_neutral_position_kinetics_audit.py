#!/usr/bin/env python3
"""Audit the actual neutral-position kinetic response and evolved-state bounds.

Run with the repository toolchain and verified dependency overlay:
  lake env python3 scripts/physical_clock_floor_neutral_position_kinetics_audit.py --overlay PATH

Sequential direct Lean checks rebuild five new modules, audit their axioms,
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


MODULES = [('KFCausalNeutralPositionCharge', 3), ('KFCausalNeutralPositionKineticGraph', 7), ('KFCausalNeutralPositionAveragedKinetics', 8), ('KFCausalNeutralPositionKineticCommutator', 7), ('KFCausalNeutralPositionKineticEvolution', 3)]


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
    logs = overlay/'physical-clock-floor-neutral-position-kinetics-audit'
    logs.mkdir(exist_ok=True)
    (overlay/'UnifiedTheory/Audit').mkdir(parents=True, exist_ok=True)
    previous_path = root/'data/physical_clock_floor_neutral_resolvent_independence_audit.json'
    previous_hash = sha256(previous_path)
    previous = json.loads(previous_path.read_text())
    sources = list(previous['source_sha256'])
    sources += ['UnifiedTheory/Audit/'+name+'.lean' for name, _ in MODULES]
    sources += ['scripts/physical_clock_floor_neutral_position_kinetics_audit.py']
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
        scope='The bare neutral-position phase exp(i*v*x4) is proved to commute with the actual physical charge circle on the whole L2 space. The clock half and four ordered kinetic factors have their natural closed graphs. Projection of the existing full closed eight-factor energy graph into these five rows is derived, and its output norm is contractive. Neutral-position modulation preserves this kinetic graph and changes only its second momentum row, with exact correction hbar*v*sqrt(1/2) times the bounded inverse clock half. The correction norm is bounded by abs(hbar)*C(epsilon,v)*norm(f), where C=abs(v)*sqrt(1/2)/sqrt(epsilon). These graph identities lift to actual L2 charge-angle sections. The averaged kinetic output is unique for its physical state. Every actual full averaged-form vector supplies such an output, and the modulated state has a constructed averaged kinetic output with the same correction bound. The kinetic energy difference is bounded by delta*(2*norm(kinetic output)+delta). Duality of the phase action gives the bilinear kinetic form-commutator bound abs(hbar)*C*(norm(output_f)*norm(g)+norm(f)*norm(output_g)); division by nonzero abs(hbar) removes that factor. The estimate transfers to the completed physical form used by the full quantum propagator. Its diagonal bound is 2*C*norm(physical state)*norm(full energy output). Applied to the actual evolved normalized boosted states, the normalized kinetic response is at most 2*C*sqrt(actual time energy). The previously derived physical energy estimate yields an eventual uniform bound 2*C*sqrt(exp(2*T)*initialBudget) on every bounded time window along every admissible nonzero hbar sequence tending to zero. No new propagation assumption is supplied. The static form and graph results do not require positive matter couplings; the semiclassical window theorem uses the established nonnegative-coupling energy estimate. This is only the kinetic contribution, not a full Hamiltonian commutator or a derivative theorem for neutral-position characteristic functions. Preservation or control of the three matter rows, a uniform full neutral-position response, neutral-position tightness, negative-clock-momentum control, full phase-space dynamics, local classical force identification and uniqueness remain open. The constant grows as the positive clock floor tends to zero. Clock-defect removal, fixed-hbar recovery, floor removal, GR/QFT/Standard Model identification and empirical validation are not proved. No operator, model, or preceding physical assumption is changed; no necessity of changing the model is established. All 1040 predecessor source/script hashes are preserved. The TOE remains unproved.')


    target = root/'data/physical_clock_floor_neutral_position_kinetics_audit.json'
    target.write_text(json.dumps(report, indent=2)+'\n')
    print('Root import passed;', report['audited_declaration_count'],
          'audited declarations;', len(hashes), 'verified source hashes.', flush=True)
    print(target, flush=True)


if __name__ == '__main__':
    main()
