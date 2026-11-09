#!/usr/bin/env python3
"""Audit the quadratic real clock correction in the actual matter response.

Run with the repository toolchain and verified dependency overlay:
  lake env python3 scripts/matter_correction_quadratic_audit.py --overlay PATH

Sequential direct Lean checks rebuild three new modules, audit their axioms,
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


MODULES = [('KFCausalRealShearCorrectionBound', 4), ('KFCausalFieldCorrectionRealPairing', 4), ('KFCausalMatterCorrectionQuadraticBound', 3)]


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
    logs = overlay/'matter-correction-quadratic-audit'
    logs.mkdir(exist_ok=True)
    (overlay/'UnifiedTheory/Audit').mkdir(parents=True, exist_ok=True)
    previous_path = root/'data/coherent_matter_shear_correction_audit.json'
    previous_hash = sha256(previous_path)
    previous = json.loads(previous_path.read_text())
    sources = list(previous['source_sha256'])
    sources += ['UnifiedTheory/Audit/'+name+'.lean' for name, _ in MODULES]
    sources += ['scripts/matter_correction_quadratic_audit.py']
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
        assert not re.search(r'\b(sorry|admit|axiom|unsafe)\b', (root/source).read_text()), source
        command = ['lean', '-j1', '-o', str(overlay/'UnifiedTheory/Audit'/f'{name}.olean'), source]
        result = subprocess.run(command, cwd=root, env=env, text=True,
                                stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
        log = logs/(name+'.log')
        log.write_text(result.stdout)
        assert result.returncode == 0, f'{name}: exit {result.returncode}; see {log}'
        assert not re.search(r': error|: warning|sorryAx', result.stdout), str(log)
        audits = re.findall(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]", result.stdout)
        assert len(audits) == count, (name, len(audits), count)
        expected = {'UnifiedTheory.Audit.'+name+'.'+n for n in
                    re.findall(r'^#print axioms (\S+)', (root/source).read_text(), re.M)}
        declared = {'UnifiedTheory.Audit.'+name+'.'+n for n in re.findall(r'^theorem (\S+)', (root/source).read_text(), re.M)}
        assert {n for n, _ in audits} == expected == declared, (name, expected, declared)
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
        scope='The real part of the actual complex-shifted clock defect differs from the physical defect by at most (10*hbar^2/epsilon^2)*D(s)^3 on the existing closed strip. This follows from the previously proved complex Taylor remainder: its first-order term is imaginary and drops from the real part. The bounded real correction operator A=(D-Re Z)/epsilon is constructed and satisfies norm(A f)<=(10*hbar^2/epsilon^3)*norm(D(D(D f))). Between any two real multipliers of the same arbitrary complex L2 wavefunction, Re inner(u,C_J d)=Re inner(u,A d), where C_J=(D-Z)/epsilon. Hence the actual field derivative correction E=2*Re inner(u,C_J d), u=F G and d=(v dot grad F)G, has absolute bound (20*hbar^2/epsilon^3)*norm(u)*norm(D(D(D d))), for F=l or l^2 and every real transverse linear field l. This improves the earlier linear-in-abs(hbar) estimate for this correction and gains a cubic defect weight. It does not bound or eliminate the remaining weighted shear expectation. The actual coherent matter weak response retains its exact longitudinal-plus-weighted-shear-minus-correction formula, with all field, derivative and shear graphs constructed and the new quadratic error estimate. For continuous actual charge orbits, the absolute correction mean is bounded by (10*hbar^2/epsilon^3) times the sum of integral norm(FG)^2 and integral norm(D^3 d)^2. Both moments are finite. The first is the squared norm moment of the existing matter factor; the second remains an additional derived field-derivative moment with no proved control by the full Hamiltonian energy. The actual averaged matter rate consequently has lower bound weightedMean-(10*hbar^2/epsilon^3)*(matterFactorMoment+cubicDefectDerivativeMoment), using the proved nonnegative longitudinal mean. This is a quantitative partial bound, not a closed one-sided energy estimate for the full response. No sign or adequate energy bound for weighted matter shear is supplied. Conditions remain epsilon>0, a>0, hbar!=0, abs(hbar)<=2*pi*epsilon/3 and the existing coherent widths. No extra initial-state moment premise or Hamiltonian modification is introduced. The coefficient is uniform in clock position but is not a regulator-uniform estimate and does not establish a semiclassical limit for hbar-dependent states. Common Hamiltonian form-core regularity, operator-domain membership, evolution invariance, the actual evolution identity, long-time quantum clock recovery, regulator removal and physical Standard Model/Einstein identification remain open. No model change is established and the physical TOE remains unproved. All 1432 predecessor source/script hashes are preserved.')


    target = root/'data/matter_correction_quadratic_audit.json'
    target.write_text(json.dumps(report, indent=2)+'\n')
    print('Root import passed;', report['audited_declaration_count'],
          'audited declarations;', len(hashes), 'verified source hashes.', flush=True)
    print(target, flush=True)


if __name__ == '__main__':
    main()
