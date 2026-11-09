#!/usr/bin/env python3
"""Recompile and audit the complete initial boosted unaveraged energy limits and their physical clock-law identification.

Run through the repository toolchain, using its previously verified dependencies:
  lake env python3 scripts/physical_clock_floor_boosted_energy_limit_audit.py --overlay PATH

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


MODULES = [('KFCausalVaryingDominatedConvergence', 1), ('KFCausalClockFloorBoostedRescaling', 10), ('KFCausalClockFloorBoostedRescaledLimit', 7), ('KFCausalClockFloorBoostedEnergyLimit', 6), ('KFCausalClockFloorBoostedEnergyIdentification', 9)]


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
    logs = overlay/'physical-clock-floor-boosted-energy-limit-audit'
    logs.mkdir(exist_ok=True)
    (overlay/'UnifiedTheory/Audit').mkdir(parents=True, exist_ok=True)
    previous_path = root/'data/physical_clock_floor_boosted_matter_energy_audit.json'
    previous_hash = sha256(previous_path)
    previous = json.loads(previous_path.read_text())
    sources = list(previous['source_sha256'])
    sources += ['UnifiedTheory/Audit/'+name+'.lean' for name, _ in MODULES]
    sources += ['scripts/physical_clock_floor_boosted_energy_limit_audit.py']
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
        scope="For every fixed positive clock floor epsilon, positive clock width a and six-component canonical momentum p, the actual normalized boosted trial now has a proved complete initial unaveraged energy limit along every nonzero sequence h->0 with abs(h)<=min(1,2*pi*epsilon/3). No integrated-energy limit is supplied as an assumption. A general nonnegative varying-majorant convergence theorem is proved by clipping against the limit majorant; it requires and uses convergence of the majorant integrals, not just a pointwise bound. The actual boosted exponential energy is identified exactly with a rescaled sourced-Gaussian density at fixed transverse widths, including the neutral shear and source scaling. The real transverse source tends to zero after rescaling; the complex oscillatory state is not asserted to converge. The squared clock phase ratio has its already proved exponential limit. The rescaled density has a pointwise limit and is dominated by a uniformly scaled half-width shifted Gaussian. The latter's integrals converge by the existing two-sided exponential Fourier-energy continuity theorem. Applying the varying-majorant result proves the actual integrated exponential-energy limit. Exact real sheared-Gaussian integration and the physical clock change of variables identify that limit as integral exp(p_clock/C(s))/C(s) against clockLaw(epsilon,a), where C(s)=exp(s)+epsilon. The limit density is proved integrable. Graph uniqueness transfers the limit to any actual ordered-exponential graph output of the boosted state. Combining this with the seven previously proved factor-energy limits yields convergence of the full eight-factor seed energy and the actual completed unaveraged form energy for nonnegative mass2, quartic and vacuum coefficients. The resulting expression is the clock-plus-transverse-kinetic remainder plus exp(2*t)*vacuum times that physical clock-law integral. The matter contributions vanish on this initial family, whose transverse position concentrates at zero; no general phase-space principal-symbol theorem is asserted. These results are at fixed epsilon, a and p, and do not prove uniformity as epsilon changes or momentum diverges. Circle-averaged form membership and energy limits for general boosts, zero charge of general boosts, full Hamiltonian operator-domain invariance, positive-time quantum transport, fixed-hbar quantum zero-defect convergence, joint small-floor control, GR/QFT/Standard Model recovery and empirical identification remain open. No predecessor model or quantum operator changed. All 707 predecessor source/script hashes are preserved. The TOE remains unproved.")


    target = root/'data/physical_clock_floor_boosted_energy_limit_audit.json'
    target.write_text(json.dumps(report, indent=2)+'\n')
    print('Root import passed;', report['audited_declaration_count'],
          'audited declarations;', len(hashes), 'verified source hashes.', flush=True)
    print(target, flush=True)


if __name__ == '__main__':
    main()
