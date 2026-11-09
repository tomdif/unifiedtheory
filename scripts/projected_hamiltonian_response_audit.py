#!/usr/bin/env python3
"""Audit the complete projected Hamiltonian response and uniform clock/kinetic bound.

Run with the repository toolchain and verified dependency overlay:
  lake env python3 scripts/projected_hamiltonian_response_audit.py --overlay PATH

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


MODULES = [('KFCausalProjectedFactorMeans', 5), ('KFCausalStructuredProjectedHamiltonian', 8), ('KFCausalProjectedKineticResponse', 9), ('KFCausalProjectedClockResponse', 6)]


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
    logs = overlay/'projected-hamiltonian-response-audit'
    logs.mkdir(exist_ok=True)
    (overlay/'UnifiedTheory/Audit').mkdir(parents=True, exist_ok=True)
    previous_path = root/'data/structured_charge_response_audit.json'
    previous_hash = sha256(previous_path)
    previous = json.loads(previous_path.read_text())
    sources = list(previous['source_sha256'])
    sources += ['UnifiedTheory/Audit/'+name+'.lean' for name, _ in MODULES]
    sources += ['scripts/projected_hamiltonian_response_audit.py']
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
        scope='For positive epsilon and nonzero hbar of either sign on the closed admissible strip, bounded coordinate projections identify the Bochner mean of the actual weighted eight-factor output with the weighted means of its individual factor outputs. This derives the full projected energy and signed-response decompositions on arbitrary finite complex superpositions of admissible normalized displaced packets. The physical decomposition retains the clock factor, all four kinetic factors, the linear-field, quadratic-field and vacuum factors, with all time and coupling weights. The three ordered-factor rates are identified with both the full weak-response integrals and the configuration-first reduced-response integrals from the predecessor checkpoint. Closed-graph integration proves that the means of the four kinetic outputs are the actual kinetic outputs of the zero-charge projected input and of its actual projected pure-clock momentum. Their signed responses are nonnegative and at most their unweighted factor energies divided by 4*epsilon. A derived sourced-Gaussian clock-half/momentum composition, normalized packet scaling, finite complex summation and closed-graph integration establish the analogous missing momentum graph for the projected clock-half output. Its response lies between minus its factor energy divided by 4*epsilon and zero, and also between minus the squared projected-input norm and zero. For all nonnegative physical couplings and all real time parameters, the exact bound abs(projectedResponse-orderedResponse) <= projectedEnergy/(4*epsilon) controls the complete five-factor clock/kinetic contribution, uniformly in structured-state size, positive individual widths, admissible centres and frequencies, and complex coefficients. The constant depends on epsilon and is not regulator-uniform. The orderedResponse is the actual sum of the three proved reduced kernel integrals with their physical coefficients, including the vacuum contribution. All 28 public theorem dependency lists use only standard axioms and cover private helpers transitively. This closes the projected eight-factor assembly and the uniform clock/kinetic remainder estimate. The state-uniform lower bound for the remaining combined ordered response, required form/core and evolution identities, quantum clock escape, controlled regulator limits, physical identification, octonion necessity, model revision and the physical TOE remain unproved. Joint absolute integrability and arbitrary integration reordering of the reduced density are still not asserted. No new numerical evidence is claimed. All 1534 predecessor source/script hashes are preserved.')


    target = root/'data/projected_hamiltonian_response_audit.json'
    target.write_text(json.dumps(report, indent=2)+'\n')
    print('Root import passed;', report['audited_declaration_count'],
          'audited declarations;', len(hashes), 'verified source hashes.', flush=True)
    print(target, flush=True)


if __name__ == '__main__':
    main()
