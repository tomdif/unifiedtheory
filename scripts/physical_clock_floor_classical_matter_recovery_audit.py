#!/usr/bin/env python3
"""Recompile and audit uniform weighted matter coercivity and complete global classical matter clock recovery.

Run through the repository toolchain, using its previously verified dependencies:
  lake env python3 scripts/physical_clock_floor_classical_matter_recovery_audit.py --overlay PATH

This does not invoke lake build. It rebuilds all eight new modules in dependency
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


MODULES = [('KFCausalClassicalMatterHarmonics', 10), ('KFCausalClassicalMatterOverlap', 9), ('KFCausalClassicalMatterProfileCoercivity', 5), ('KFCausalClassicalMatterCoercivity', 6), ('KFCausalClassicalMatterTiltControl', 3), ('KFCausalClassicalMatterAdjustedDrift', 5), ('KFCausalClassicalMatterRecovery', 3), ('KFCausalClassicalMatterCompleteRecovery', 3)]


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
    logs = overlay/'physical-clock-floor-classical-matter-recovery-audit'
    logs.mkdir(exist_ok=True)
    (overlay/'UnifiedTheory/Audit').mkdir(parents=True, exist_ok=True)
    previous_path = root/'data/physical_clock_floor_classical_matter_global_audit.json'
    previous_hash = sha256(previous_path)
    previous = json.loads(previous_path.read_text())
    sources = list(previous['source_sha256'])
    sources += ['UnifiedTheory/Audit/'+name+'.lean' for name, _ in MODULES]
    sources += ['scripts/physical_clock_floor_classical_matter_recovery_audit.py']
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
        scope='For the actual full classical matter candidate at epsilon>0, mass2>=0, quartic>=0 and kappa>0, proves a unique all-real-time canonical trajectory through every initial time and full phase point whose log-clock tends to infinity and whose positive clock defect strictly decreases to zero in the future. Global existence is constructed by the preceding verified theorem, not supplied as a premise of the complete theorem; no special transverse sector or bounded-clock/energy hypothesis is imposed. The new estimate uses the exact finite harmonic degrees: the field is affine in sine and cosine, and the shear is a zero-mean trigonometric polynomial of degree at most two. Real analytic uniqueness proves positive overlap of every nonzero field even power with the positive part of every nonzero shear profile. Continuity and compactness of the coefficient unit spheres give a uniform strictly positive overlap constant. Positive-part domination by the exponential and homogeneity yield a uniform lower bound for the charge mean of each field even power times the shear exponential. Identifying the actual field and shear coefficients and combining the mass, quartic and vacuum terms proves c*mean(V)<=mean(V*exp(S/C)) for a derived constant c>0, uniformly in phase, C and nonnegative couplings. The scalar inequality x*exp(x)>=exp(x)-1 then gives a derived finite N>=0 with F+T>=-N*F, retaining the possibility of negative weighted tilt. The actual clock equations imply that p_clock/C+N*log(C)+t/2 is nondecreasing. If the log-clock were bounded, this estimate would force a uniform positive forward clock speed, contradicting boundedness. Thus the log-clock diverges and epsilon/C tends to zero. Arbitrary initial physical time is handled by the exact time component of the constructed ODE. The frozen negative-tilt witness remains valid and the model is not changed to remove it; its obstruction is overcome by a weaker proved bound. The uniform constants are existential rather than numerically evaluated. These are classical candidate results, not a controlled principal-symbol limit of the unbounded ordered quantum model or quantum clock recovery. Positive-time quantum transport and unbounded outputs, actual fixed-state quantum zero-defect convergence, joint small-floor control, GR/QFT/Standard Model recovery and empirical identification remain open. No predecessor model definition or quantum operator changed. All 666 predecessor source/script hashes are preserved. The TOE remains unproved.')


    target = root/'data/physical_clock_floor_classical_matter_recovery_audit.json'
    target.write_text(json.dumps(report, indent=2)+'\n')
    print('Root import passed;', report['audited_declaration_count'],
          'audited declarations;', len(hashes), 'verified source hashes.', flush=True)
    print(target, flush=True)


if __name__ == '__main__':
    main()
