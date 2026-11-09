#!/usr/bin/env python3
"""Recompile and audit the actual momentum-domain covariance and boosted initial kinetic/classical limits.

Run through the repository toolchain, using its previously verified dependencies:
  lake env python3 scripts/physical_clock_floor_kinetic_modulation_audit.py --overlay PATH

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


MODULES = [('KFCausalDirectionalMomentumCovariance', 1), ('KFCausalPhysicalMomentumModulation', 7), ('KFCausalClockFloorKineticModulation', 9), ('KFCausalClockFloorBoostedKineticLimit', 10), ('KFCausalClockFloorBoostedInitialLaw', 12)]


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
    logs = overlay/'physical-clock-floor-kinetic-modulation-audit'
    logs.mkdir(exist_ok=True)
    (overlay/'UnifiedTheory/Audit').mkdir(parents=True, exist_ok=True)
    previous_path = root/'data/physical_clock_floor_weyl_limit_audit.json'
    previous_hash = sha256(previous_path)
    previous = json.loads(previous_path.read_text())
    sources = list(previous['source_sha256'])
    sources += ['UnifiedTheory/Audit/'+name+'.lean' for name, _ in MODULES]
    sources += ['scripts/physical_clock_floor_kinetic_modulation_audit.py']
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
        scope='Derives covariance of the maximal spectral momentum graph by differentiating exact bounded translation covariance. For actual linear phase modulation M_l, all natural physical transverse momentum domains are preserved and P_h,v M_l f = M_l(P_h,v f + h*l(0,v)*f) on the graph. For positive clock floor epsilon, the bounded inverse clock half D commutes with M_l, the natural ordered kinetic graph A_h,v=P_h,v D is closed, and modulation preserves its domain with exact output shift h*l(0,v)*D f. A quantitative graph-output error is bounded by abs(h)*abs(l(0,v))/sqrt(epsilon)*norm(f). Oscillatory modulation M_(l/h) of the explicit normalized trial supplies actual graph vectors at nonzero momentum. Their normalized residual kinetic output has squared norm bounded by abs(h)*kineticMass/clockMass and tends strongly to zero. The boosted ordered kinetic energy converges to l(0,v)^2*dampedMass/clockMass for every fixed direction v and linear l along nonzero h tending to zero, with epsilon and the positive clock width fixed. No strip or h<=1 bound is needed for these kinetic results. For l the canonical frequency associated with any fixed six-component momentum p, all twelve-frequency quantum initial characteristics converge to those of the explicitly constructed probability law with the existing clock density, zero transverse position, and momentum p. The actual kinetic energy limit equals the integral of the classical squared directional momentum divided by exp(s)+epsilon against this same law; integrability is separately proved. This closes initial kinetic calibration away from zero momentum, not a full Hamiltonian symbol or positive-time transport theorem. General boosts are not asserted to preserve zero charge, the longitudinal exponential domain, or the completed averaged energy form. Full ordered-Hamiltonian commutator/symbol control, phase-space tightness and propagated unbounded outputs, identification of evolved quantum measures with the classical Liouville law, fixed-hbar quantum zero-defect convergence, joint small-floor control, GR/QFT/Standard Model recovery and empirical identification remain open. No predecessor model definition or quantum operator changed. All 690 predecessor source/script hashes are preserved. The TOE remains unproved.')


    target = root/'data/physical_clock_floor_kinetic_modulation_audit.json'
    target.write_text(json.dumps(report, indent=2)+'\n')
    print('Root import passed;', report['audited_declaration_count'],
          'audited declarations;', len(hashes), 'verified source hashes.', flush=True)
    print(target, flush=True)


if __name__ == '__main__':
    main()
