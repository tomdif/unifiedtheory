#!/usr/bin/env python3
"""Audit the exact signed vacuum shear response and its natural weighted domain.

Run with the repository toolchain and verified dependency overlay:
  lake env python3 scripts/physical_clock_floor_signed_shear_audit.py --overlay PATH

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


MODULES = [('KFCausalClockShearRealMultiplier', 4), ('KFCausalClockFloorShearWeight', 9), ('KFCausalClockFloorSignedShearResponse', 11), ('KFCausalClockFloorWeightedShearDomain', 15)]


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
    logs = overlay/'physical-clock-floor-signed-shear-audit'
    logs.mkdir(exist_ok=True)
    (overlay/'UnifiedTheory/Audit').mkdir(parents=True, exist_ok=True)
    previous_path = root/'data/physical_clock_floor_pure_clock_factors_audit.json'
    previous_hash = sha256(previous_path)
    previous = json.loads(previous_path.read_text())
    sources = list(previous['source_sha256'])
    sources += ['UnifiedTheory/Audit/'+name+'.lean' for name, _ in MODULES]
    sources += ['scripts/physical_clock_floor_signed_shear_audit.py']
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
        assert {n for n, _ in audits} == expected, (name, expected)
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
        scope='For the unchanged positive-floor quantum candidate, real bounded clock multipliers preserve the full actual shear momentum graph and have real mixed shear pairings. Thus the real defect term cancels from the imaginary force pairing. At epsilon>0, hbar!=0 and abs(hbar)<=2*pi*epsilon/3, the derived real clock weight Q has coefficient sqrt(epsilon*Im(Z)/(2*hbar)), with zero<=Q(s)<=D(s), D=epsilon/C. The proof derives the sign and bound from the actual shifted defect symbol and establishes norm(Qf)<=norm(Df). Q preserves Dom(J) and JQf=QJf there. The actual shifted operator is decomposed as Re(Z)+(2*i*hbar/epsilon)*Q^2. For Jg=j the pure-clock vacuum response is exactly R_L(g)+(4/epsilon^2)*Re inner(Qg,Qj). Its difference from R_L is bounded by (4/epsilon^2)*norm(Qg)*norm(Qj), and hence by (4/epsilon^2)*norm(Dg)*norm(Dj). This balanced estimate and the previous norm(g)*norm(D^2 j) estimate are different bounds; no universal ordering between them is asserted. The identity is connected to the actual B,T weak response on the previously constructed joint momentum core, with all B,T composition outputs supplied. The natural weighted momentum M=JQ is constructed with exact maximal composition domain {g | Qg belongs to Dom(J)}. M is closed, densely defined and shear-transport invariant. Orbit averaging constructs a dense M graph core with J on both input and output. On this core the existing response agrees with the graph-continuous function R_L(g)+(4/epsilon^2)*Re inner(Qg,Mg); convergent core sequences and uniqueness of this extension to the entire M graph are proved. This is not extension to the T graph alone or to the Hamiltonian energy form domain. No positivity of the total response, bounded-energy obstruction, charge-orbit admissible counterexample, averaged energy-form bound, ordered matter response, Hamiltonian momentum evolution law or long-time defect recovery is established. The actual energy has exp(2*t) weights and is not treated as conserved. Regulator removal and GR/QFT/Standard Model and empirical identification remain open. No model or Hamiltonian changed. All 1308 predecessor source/script hashes are preserved. The TOE remains unproved.')


    target = root/'data/physical_clock_floor_signed_shear_audit.json'
    target.write_text(json.dumps(report, indent=2)+'\n')
    print('Root import passed;', report['audited_declaration_count'],
          'audited declarations;', len(hashes), 'verified source hashes.', flush=True)
    print(target, flush=True)


if __name__ == '__main__':
    main()
