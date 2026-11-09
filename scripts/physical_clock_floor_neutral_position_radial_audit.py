#!/usr/bin/env python3
"""Audit the actual charge-compatible radial neutral-position test.

Run with the repository toolchain and verified dependency overlay:
  lake env python3 scripts/physical_clock_floor_neutral_position_radial_audit.py --overlay PATH

Sequential direct Lean checks rebuild nine new modules, audit their axioms,
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


MODULES = [('KFCausalNeutralPositionRadialCutoff', 13), ('KFCausalNeutralPositionHeatMomentum', 8), ('KFCausalNeutralPositionRadialKinetics', 8), ('KFCausalNeutralPositionRadialKineticGraph', 6), ('KFCausalNeutralPositionRadialAveragedKinetics', 8), ('KFCausalNeutralPositionRadialTail', 7), ('KFCausalNeutralPositionRadialEvolution', 8), ('KFCausalChargeSpectatorRelation', 10), ('KFCausalNeutralPositionRadialField', 9)]


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
    logs = overlay/'physical-clock-floor-neutral-position-radial-audit'
    logs.mkdir(exist_ok=True)
    (overlay/'UnifiedTheory/Audit').mkdir(parents=True, exist_ok=True)
    previous_path = root/'data/physical_clock_floor_neutral_position_cutoff_removal_audit.json'
    previous_hash = sha256(previous_path)
    previous = json.loads(previous_path.read_text())
    sources = list(previous['source_sha256'])
    sources += ['UnifiedTheory/Audit/'+name+'.lean' for name, _ in MODULES]
    sources += ['scripts/physical_clock_floor_neutral_position_radial_audit.py']
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
        scope='The actual mixed charge coordinates define the radial test P(hbar,delta,v) with multiplier exp(-2*delta*((2*pi*hbar*xi1)^2+s2^2))*exp(i*v*neutral). The second-plane radius is invariant under the actual charge rotation, so P is contractive on all physical L2 and commutes with the actual charge action. It factors as the preceding physical position-localized phase composed with the added antisymmetric momentum Gaussian. That heat factor commutes with the actual translation groups of all four model momentum directions; differentiation proves preservation of their natural momentum graphs. It also commutes with inverse clock multiplication and preserves clock-half and all four ordered kinetic graphs. For positive epsilon and delta and nonzero hbar, P acts on the actual five-row kinetic graph with an explicit bounded correction supported only on the second momentum row. The weighted correction norm is at most abs(hbar)*C*norm(f), where C=sqrt(1/2)*(4*sqrt(delta)+abs(v))/sqrt(epsilon), independent of time and matter couplings. Charge averaging constructs the actual L2 output section, proves its graph identity and bounds its norm by norm(original kinetic output)+abs(hbar)*C*norm(f). Applied to full physical averaged-form inputs this supplies the kinetic projection and its bound by the full original energy output. This is an upper kinetic-energy estimate; the radial cutoff is contractive and is not asserted to be an isometry. Separately, bounded regularization transports arbitrary measurable unbounded spectator multiplication relations through the actual partial Fourier unitary. Applied to the physical pointField=x2+x3+x4, it proves all natural field-power relations and preservation of the actual field and field-square graphs by both heat and P. No longitudinal exponential graph identity for the heat factor is assumed or concluded. The squared L2 error of P relative to the bare neutral phase is exactly the radial Gaussian-error integral and is at most 4*delta^2*R^4*norm(f)^2+planeTail(hbar,R,1,f). On the actual normalized boosted quantum evolution it is at most 4*delta^2*R^4+(1+exp(-2*t))*timeEnergy(t)/R for positive R. With fixed positive epsilon and initial clock width, fixed initial boost and time, nonnegative matter couplings, and any nonzero admissible hbar sequence tending to zero, the existing energy estimate proves radial cutoff removal uniformly over all neutral frequencies and bounded time windows, for every positive delta sequence tending to zero independently of the hbar rate. Moving times and frequencies and uniform expectation differences are covered. The full ordered matter graphs, full charge-averaged form preservation, energy graph-norm cutoff removal, the normalized full Hamiltonian response, neutral-position time variation and tightness remain unproved. The next concrete analytic obligation is the actual partial-Fourier intertwining of the clock-dependent dilation/shear and its bounded complex-strip continuation. Full twelve-dimensional dynamics, negative-clock-momentum control, classical force closure and uniqueness, clock-defect removal, fixed-hbar recovery, floor removal, GR/QFT/Standard Model identification and empirical validation remain unproved. The Hamiltonian and physical model are unchanged; this constructs a different test operator, and no necessity of a model change is established. All 1070 predecessor source/script hashes are preserved. The TOE remains unproved.')


    target = root/'data/physical_clock_floor_neutral_position_radial_audit.json'
    target.write_text(json.dumps(report, indent=2)+'\n')
    print('Root import passed;', report['audited_declaration_count'],
          'audited declarations;', len(hashes), 'verified source hashes.', flush=True)
    print(target, flush=True)


if __name__ == '__main__':
    main()
