#!/usr/bin/env python3
"""Audit the actual ordered matter response and its field-weighted shear contribution.

Run with the repository toolchain and verified dependency overlay:
  lake env python3 scripts/coherent_matter_response_audit.py --overlay PATH

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


MODULES = [('KFCausalFieldWeightedShearMoments', 3), ('KFCausalCoherentWeightedShearDomains', 4), ('KFCausalFieldWeightedClockCommutator', 8), ('KFCausalCoherentMatterWeakResponse', 3), ('KFCausalCoherentMatterResponseAverage', 2), ('KFCausalFullMatterShearReduction', 1)]


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
    logs = overlay/'coherent-matter-response-audit'
    logs.mkdir(exist_ok=True)
    (overlay/'UnifiedTheory/Audit').mkdir(parents=True, exist_ok=True)
    previous_path = root/'data/coherent_full_response_audit.json'
    previous_hash = sha256(previous_path)
    previous = json.loads(previous_path.read_text())
    sources = list(previous['source_sha256'])
    sources += ['UnifiedTheory/Audit/'+name+'.lean' for name, _ in MODULES]
    sources += ['scripts/coherent_matter_response_audit.py']
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
        scope='Fourth physical-coordinate moments of the actual complex-shifted Gaussian are derived from the existing L2 Gaussian envelope on the entire closed clock strip. These imply field-square and linear-field domains for every actual J T f output on the coherent span. No higher-moment hypothesis is added to the initial states. The two physical field powers preserve the graphs of the bounded clock corrections and commute with pure-clock momentum on the proved composition graphs. This gives actual B(F T f) and F T B f compositions and identifies each signed matter weak pairing with the existing two-vector response evaluated on u=F T f and j=F J T f, for F=Phi or Phi^2. The order F J is retained; F J T f is not silently replaced by J F T f. Each matter rate has a pointwise lower bound -(4/epsilon^2)*norm(u)*norm(D(D j)) and the corresponding longitudinal-plus-error upper bound; this is a bound in an additional derived weighted shear moment, not in Hamiltonian energy alone. On the actual eight-factor charge-orbit family, the signed field-weighted shear scalar pairing is continuous and integrable, as proved through the weak-response identity and continuous actual factor curves, without assuming continuity of an unbounded field map. The two matter rates split exactly as r_(5+i)=L_i-S_i, where L_i is the nonnegative averaged longitudinal response and S_i=(2/(hbar*epsilon))*integral Im inner(Phi^(i+1) T U f,(D-Z) Phi^(i+1) J T U f). Consequently the previous matter residual is M_t=L_t-S_t with L_t>=0, using the existing mass and quartic weights. Actual pure-clock momentum, full energy-form lifts and all required output graphs are constructed for every coherent-span input, and the full signed form response satisfies R_t>=-S_t-norm(f)^2/2. This requires an upper bound on the signed S_t (or its positive part) for further force control; no such energy estimate or sign is assumed or proved here. Parameters remain epsilon>0, a>0, hbar!=0, abs(hbar)<=2*pi*epsilon/3, the existing coherent widths and nonnegative mass2, quartic and vacuum couplings. No Hamiltonian change, stricter strip or initial-state moment condition is introduced. The result is at fixed time, not a differentiated momentum expectation along Hamiltonian evolution. Common Hamiltonian form-core regularity, operator-domain membership, invariance, the evolution identity, quantitative long-time quantum clock recovery, regulator removal and physical Einstein/Standard Model identification remain open. No model change is established; the physical TOE remains unproved. All 1417 predecessor source/script hashes are preserved.')


    target = root/'data/coherent_matter_response_audit.json'
    target.write_text(json.dumps(report, indent=2)+'\n')
    print('Root import passed;', report['audited_declaration_count'],
          'audited declarations;', len(hashes), 'verified source hashes.', flush=True)
    print(target, flush=True)


if __name__ == '__main__':
    main()
