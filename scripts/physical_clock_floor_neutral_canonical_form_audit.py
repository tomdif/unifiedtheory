#!/usr/bin/env python3
"""Recompile and audit actual neutral canonical phase-test domains and semiclassically uniform form commutator bounds.

Run through the repository toolchain, using its previously verified dependencies:
  lake env python3 scripts/physical_clock_floor_neutral_canonical_form_audit.py --overlay PATH

This does not invoke lake build. It rebuilds all twelve new modules in dependency
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


MODULES = [('KFCausalNeutralTranslationCoordinates', 9), ('KFCausalNeutralTranslationFactors', 8), ('KFCausalNeutralTranslationMatter', 8), ('KFCausalNeutralTranslationOutput', 3), ('KFCausalNeutralTranslationJointGraph', 7), ('KFCausalNeutralTranslationForm', 5), ('KFCausalNeutralTranslationBounds', 7), ('KFCausalNeutralTranslationCharge', 4), ('KFCausalNeutralTranslationAveragedForm', 6), ('KFCausalNeutralTranslationCommutator', 8), ('KFCausalNeutralTranslationPhysicalCommutator', 5), ('KFCausalNeutralCanonicalForm', 4)]


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
    logs = overlay/'physical-clock-floor-neutral-canonical-form-audit'
    logs.mkdir(exist_ok=True)
    (overlay/'UnifiedTheory/Audit').mkdir(parents=True, exist_ok=True)
    previous_path = root/'data/physical_clock_floor_probability_clock_compatibility_audit.json'
    previous_hash = sha256(previous_path)
    previous = json.loads(previous_path.read_text())
    sources = list(previous['source_sha256'])
    sources += ['UnifiedTheory/Audit/'+name+'.lean' for name, _ in MODULES]
    sources += ['scripts/physical_clock_floor_neutral_canonical_form_audit.py']
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
        scope='Neutral configuration translation is the actual existing canonical neutral-momentum phase test. It commutes with clock-floor straightening and with the actual physical charge circle. Exact covariance is derived for the maximal longitudinal exponential, clock and inverse-clock halves, all transverse momenta, ordered kinetic and exponential factors, and both ordered matter factors. Natural matter and common domains are preserved. The linear field output shifts by a multiple of the ordered exponential output; the quadratic field output has the exact triangular degree-two correction. Bounded mixing of the eight outputs preserves the weighted joint graph and its topological closure when all weights are nonzero. Positive mass-squared, quartic and vacuum coefficients ensure this condition and give a bounded invertible lift to the complete unaveraged physical energy form. Derived charge commutation gives a bounded invertible lift to the entire actual charge-averaged form, with exact pointwise L2 output covariance and domain preservation in both directions. The output deviation from a pure unitary translation is bounded by a polynomial of degree two in displacement, uniformly over all outputs. The corresponding bilinear form commutator is bounded on arbitrary output vectors and L2 families. For the actual physical point field, the shift equals the translation distance. At canonical displacement hbar*v, dividing the averaged form commutator bound by abs(hbar) gives a constant independent of nonzero hbar in a bounded interval, multiplied by the two actual energy-output norms. The energy weights, and hence that coefficient at each fixed time, do not depend on hbar. No commutator, domain preservation, charge commutation, graph-core equality or dynamical correspondence is assumed. These new completed-form results explicitly require strictly positive mass-squared, quartic and vacuum coefficients; extension to zero-coupling cases is not claimed. The preceding nonnegative-coupling model and probability results remain unchanged. This controls one canonical momentum phase-test direction. It does not establish a propagator expectation derivative, temporal equicontinuity, neutral-position control, negative-clock-momentum control, full twelve-dimensional tightness, quantum-to-classical transport, subsequence independence, late-time zero clock defect, fixed-hbar recovery or floor removal. GR/QFT/Standard Model identification and empirical validity remain open. No model or preceding operator changed; all 889 predecessor source/script hashes are preserved. The TOE remains unproved.')


    target = root/'data/physical_clock_floor_neutral_canonical_form_audit.json'
    target.write_text(json.dumps(report, indent=2)+'\n')
    print('Root import passed;', report['audited_declaration_count'],
          'audited declarations;', len(hashes), 'verified source hashes.', flush=True)
    print(target, flush=True)


if __name__ == '__main__':
    main()
