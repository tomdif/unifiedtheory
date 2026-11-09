#!/usr/bin/env python3
"""Audit uniform cutoff removal on the actual evolving quantum states.

Run with the repository toolchain and verified dependency overlay:
  lake env python3 scripts/physical_clock_floor_neutral_position_cutoff_removal_audit.py --overlay PATH

Sequential direct Lean checks rebuild four new modules, audit their axioms,
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


MODULES = [('KFCausalNeutralPositionCutoffCharge', 8), ('KFCausalNeutralPositionCutoffTail', 5), ('KFCausalNeutralPositionCutoffEvolution', 6), ('KFCausalNeutralPositionCutoffCharacteristic', 7)]


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
    logs = overlay/'physical-clock-floor-neutral-position-cutoff-removal-audit'
    logs.mkdir(exist_ok=True)
    (overlay/'UnifiedTheory/Audit').mkdir(parents=True, exist_ok=True)
    previous_path = root/'data/physical_clock_floor_neutral_position_localized_energy_audit.json'
    previous_hash = sha256(previous_path)
    previous = json.loads(previous_path.read_text())
    sources = list(previous['source_sha256'])
    sources += ['UnifiedTheory/Audit/'+name+'.lean' for name, _ in MODULES]
    sources += ['scripts/physical_clock_floor_neutral_position_cutoff_removal_audit.py']
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
        scope='The actual physical Gaussian cutoff exp(-delta*(x2+x3)^2) is transported through the existing partial Fourier and paired-coordinate unitaries, giving the multiplier exp(-2*delta*s2^2) in charge coordinates. No charge commutation is assumed. The exact squared L2 difference between the localized neutral-position phase and the bare phase is the integral of (exp(-2*delta*s2^2)-1)^2 against the actual charge-coordinate state density. For every L2 state, every neutral frequency v and real hbar and R, this squared error is at most 4*delta^2*R^4*norm(state)^2+planeTail(hbar,R,1,state). The tail is the existing mixed charged position/momentum tail, not an assumed decay property. On the actual normalized boosted quantum evolution the squared error is at most 4*delta^2*R^4+(1+exp(-2*t))*timeEnergy(t)/R for positive R. For fixed positive epsilon and initial clock width a, fixed initial boost and time, nonnegative mass-squared, quartic and vacuum couplings, and every nonzero admissible hbar sequence tending to zero, the established energy and charged-tail estimates supply uniform cutoff removal on every bounded time window. More precisely, for every positive error tolerance there are a positive cutoff threshold and a sequence index such that every smaller positive cutoff has L2 error below that tolerance, uniformly over all later indices, every time in the window, and every real neutral frequency. Thus every positive cutoff sequence tending to zero works independently of the rate of the hbar sequence. The error tends uniformly to zero as an L2-valued function of frequency and time, including arbitrary moving frequencies and window-bounded moving times. The bare observable is identified with the actual canonical Weyl operator at pure neutral-position frequency and zero translation. Its expectation and the localized expectation have their physical density integral formulas, and their difference tends uniformly to zero on the same frequency/time windows. No existence or uniqueness of a limiting position law, time derivative, position tightness, charge-averaged full-form preservation, energy graph-norm cutoff removal, or full normalized Hamiltonian response is concluded. The shifted matter-output estimate still diverges when delta tends to zero at fixed nonzero hbar and frequency. Full twelve-dimensional dynamics, negative-clock-momentum control, classical force closure and uniqueness, clock-defect removal, fixed-hbar recovery, floor removal, GR/QFT/Standard Model identification and empirical validation remain unproved. No existing physical operator or model is changed, and no necessity of a model change is established. All 1065 predecessor source/script hashes are preserved. The TOE remains unproved.')


    target = root/'data/physical_clock_floor_neutral_position_cutoff_removal_audit.json'
    target.write_text(json.dumps(report, indent=2)+'\n')
    print('Root import passed;', report['audited_declaration_count'],
          'audited declarations;', len(hashes), 'verified source hashes.', flush=True)
    print(target, flush=True)


if __name__ == '__main__':
    main()
