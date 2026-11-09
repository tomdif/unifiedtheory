#!/usr/bin/env python3
"""Recompile and audit a initial phase-space law of the actual uniform-energy clock-floor family.

Run through the repository toolchain, using its previously verified dependencies:
  lake env python3 scripts/physical_clock_floor_initial_phase_space_audit.py --overlay PATH

This does not invoke lake build. It rebuilds all seven new modules in dependency
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


MODULES = [('KFCausalLpPhaseTranslation', 9), ('KFCausalPhysicalGaussianConcentration', 9), ('KFCausalGaussianPhaseSpaceLimit', 12), ('KFCausalProductPhaseTranslation', 5), ('KFCausalClockFloorInitialProduct', 5), ('KFCausalClockFloorInitialClassicalLaw', 12), ('KFCausalClockFloorInitialCharacteristic', 10)]


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
    logs = overlay/'physical-clock-floor-initial-phase-space-audit'
    logs.mkdir(exist_ok=True)
    (overlay/'UnifiedTheory/Audit').mkdir(parents=True, exist_ok=True)
    previous_path = root/'data/physical_clock_floor_semiclassical_family_audit.json'
    previous_hash = sha256(previous_path)
    previous = json.loads(previous_path.read_text())
    sources = list(previous['source_sha256'])
    sources += ['UnifiedTheory/Audit/'+name+'.lean' for name, _ in MODULES]
    sources += ['scripts/physical_clock_floor_initial_phase_space_audit.py']
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
        scope="For the optional equal-mobility clock-floor model, proves the joint initial canonical position/momentum characteristic limit of the same normalized zero-charge Gaussian states previously placed in the completed averaged energy form with a Planck-independent energy bound. Constructs actual modulation and translation unitaries on L2 and proves their exact factorization on product states. Gaussian position moments and exact translated overlaps give an explicit transverse error bound sqrt(abs(hbar)*translationCost(eta))+sqrt(2560*abs(hbar)*directionSize(xi)) tending to zero. The physical unitTrial is proved equal to the normalized clock/transverse product. The clock density is norm(clockFunction(epsilon,a,s))^2/clockMass(epsilon,a), with nonnegativity, integrability and total mass one proved. The classical phase-space probability measure is its pushforward by s -> ((s,0),(0,0)): the clock coordinate remains distributed; transverse positions and all canonical momenta are zero. For every six position and six momentum frequencies, every nonzero real hbar sequence tending to zero has ordered phase-translation expectations converging to this measure's characteristic integral. The theorem is linked to the physical embedding of the actual uniformly energy-bounded form states under abs(hbar)<=min(1,2*pi*epsilon/3), nonnegative mass2/quartic/vacuum, and arbitrary fixed initial time. An explicit admissible nonzero sequence is constructed. The clock floor epsilon>0 and clock width a>0 remain fixed. This is an initial-data theorem, not a propagation theorem: convergence of the evolving quantum states or energy outputs to classical phase-space transport remains open. The tests are explicitly ordered modulation/translation unitaries; no finite-hbar positive joint position/momentum distribution is asserted. No joint removal of the clock floor, uniform energy cost for the old arbitrarily-small-defect family, finite-capacity/Jordan limit, GR/QFT/Standard Model recovery, or empirical identification is proved. No model, factor order, or prior operator is changed. All 571 predecessor source/script hashes are preserved. The TOE remains unproved.")


    target = root/'data/physical_clock_floor_initial_phase_space_audit.json'
    target.write_text(json.dumps(report, indent=2)+'\n')
    print('Root import passed;', report['audited_declaration_count'],
          'audited declarations;', len(hashes), 'verified source hashes.', flush=True)
    print(target, flush=True)


if __name__ == '__main__':
    main()
