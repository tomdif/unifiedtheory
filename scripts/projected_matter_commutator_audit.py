#!/usr/bin/env python3
"""Audit the actual projected matter commutator and its absorbed lower response.

Run with lake env python3 and the verified overlay. Sequential direct Lean
checks preserve every predecessor hash. Numerical matrices remain floating
exploratory evidence, not a proof of their sign or of a uniform estimate.
"""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess


MODULES = [
    ('KFCausalBoundedPolynomialShearContinuity', 2),
    ('KFCausalStructuredPolynomialShearOrbit', 6),
    ('KFCausalProjectedMatterShearGraphs', 5),
    ('KFCausalProjectedFieldSlopeMultiplier', 4),
    ('KFCausalProjectedMatterCommutatorResponse', 9),
    ('KFCausalProjectedHamiltonianMatterLower', 1),
]


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
    logs = overlay/'projected-matter-commutator-audit'
    logs.mkdir(exist_ok=True)
    (overlay/'UnifiedTheory/Audit').mkdir(parents=True, exist_ok=True)
    previous_path = root/'data/projected_structured_vacuum_sign_audit.json'
    previous_hash = sha256(previous_path)
    previous = json.loads(previous_path.read_text())
    sources = list(previous['source_sha256'])
    sources += ['UnifiedTheory/Audit/'+name+'.lean' for name, _ in MODULES]
    sources += ['scripts/projected_matter_commutator_audit.py']
    hashes = {p: sha256(root/p) for p in sources}
    assert all(hashes[p] == h for p, h in previous['source_sha256'].items())
    numeric_path = root/'data/projected_integrated_response_probe.json'
    validation_path = root/'data/projected_integrated_response_validation.json'
    numeric = json.loads(numeric_path.read_text())
    validation = json.loads(validation_path.read_text())
    assert all(sha256(root/p) == h for p,h in numeric['source_sha256'].items())
    assert validation['probe_report_sha256'] == sha256(numeric_path)
    assert validation['verifier_sha256'] == sha256(root/'scripts/verify_projected_integrated_response.py')
    assert len(numeric['cases']) == 5 and len(validation['checks']) == 10
    numerical_evidence = dict(report=dict(path=str(numeric_path.relative_to(root)), sha256=sha256(numeric_path)),
        validation=dict(path=str(validation_path.relative_to(root)), sha256=sha256(validation_path)),
        interpretation='Floating finite-subspace tests only; no certified sign, tail, uniform lower bound or evolution claim.')
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
    assert sha256(numeric_path) == numerical_evidence['report']['sha256']
    assert sha256(validation_path) == numerical_evidence['validation']['sha256']
    report = dict(
        numerical_evidence=numerical_evidence, modules=checks, root_check=dict(command=['lean', '-j1', 'UnifiedTheory.lean'], exit_code=0,
            empty_log=True, source_sha256=root_hash, log_sha256=sha256(log)),
        audited_declaration_count=sum(n for _, n in MODULES), source_sha256=hashes,
        previous_report=dict(path=str(previous_path.relative_to(root)), sha256=previous_hash),
        lean_toolchain=(root/'lean-toolchain').read_text().strip(),
        scope='Twenty-seven public theorem dependency lists derive the actual projected field-power and field-shear composition graphs on every finite structured state under epsilon>0, h!=0, abs(h)<=2*pi*epsilon/3, with independent positive widths, zero clock centres, arbitrary remaining displacements, real frequencies and complex amplitudes. Joint source/path L2 continuity for polynomial-weighted Gaussian paths is established by a common derived envelope. Closed-graph charge integration gives the two weighted shear outputs, the corrected actual shear graph, and an a.e. representative of the averaged slope via a maximal real multiplier. Composition uniqueness identifies the physical matter output means with these constructed field outputs. Each actual matter response equals its positive longitudinal response plus its corrected root-weighted shear expectation minus the explicit real field-slope correction. The latter is bounded by the longitudinal response plus coefficient(epsilon,h) times the actual slope moment, whose density is D^5*(1-D). This yields a full projected Hamiltonian lower comparison with the two derived matter bounds and minus half the squared projected input norm, retaining all interference and nonnegative physical couplings at every real time. The weighted shear expectations need not be positive, and neither they nor the slope moments have been uniformly controlled by Hamiltonian energy. The required uniform lower estimate, form-core extension, evolution identity, quantum clock escape, controlled limits, physical identification, octonion necessity, model revision and physical TOE remain unproved. The preceding vacuum positivity and norm lower comparison are preserved. All 1552 predecessor source/script hashes and all earlier numerical reports remain unchanged.')


    target = root/'data/projected_matter_commutator_audit.json'
    target.write_text(json.dumps(report, indent=2)+'\n')
    print('Root import passed;', report['audited_declaration_count'],
          'audited declarations;', len(hashes), 'verified source hashes.', flush=True)
    print(target, flush=True)


if __name__ == '__main__':
    main()
