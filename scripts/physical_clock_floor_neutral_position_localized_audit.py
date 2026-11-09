#!/usr/bin/env python3
"""Audit the actual localized neutral-position exponential and matter graphs.

Run with the repository toolchain and verified dependency overlay:
  lake env python3 scripts/physical_clock_floor_neutral_position_localized_audit.py --overlay PATH

Sequential direct Lean checks rebuild seven new modules, audit their axioms,
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


MODULES = [('KFCausalNeutralPositionStripPhase', 10), ('KFCausalGaussianStripFamily', 8), ('KFCausalStripFamilyExponentialGraph', 15), ('KFCausalStripFamilyPhysicalMultiplier', 3), ('KFCausalNeutralPositionLocalizedMultiplier', 9), ('KFCausalNeutralPositionLocalizedMatter', 10), ('KFCausalNeutralPositionLocalizedLimit', 4)]


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
    logs = overlay/'physical-clock-floor-neutral-position-localized-audit'
    logs.mkdir(exist_ok=True)
    (overlay/'UnifiedTheory/Audit').mkdir(parents=True, exist_ok=True)
    previous_path = root/'data/physical_clock_floor_neutral_position_kinetics_audit.json'
    previous_hash = sha256(previous_path)
    previous = json.loads(previous_path.read_text())
    sources = list(previous['source_sha256'])
    sources += ['UnifiedTheory/Audit/'+name+'.lean' for name, _ in MODULES]
    sources += ['scripts/physical_clock_floor_neutral_position_localized_audit.py']
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
        scope='For positive clock floor epsilon and nonzero neutral frequency v, the bare phase exp(i*v*x4) has an analytic continuation in the actual straightened clock coordinates that is pointwise unbounded along a charged-coordinate ray at every nonreal clock point in the target strip. This is an analytic multiplier obstruction, not a proof that the bare phase fails to preserve the full energy domain or that the model is invalid. The explicit localized physical observable exp(-delta*(x2+x3)^2)*exp(i*v*x4), for delta>0, is a contraction on all physical L2. Its actual analytic continuation is bounded uniformly in transverse position by exp(v^2*Im(q)^2/(2*delta*epsilon^2)) on abs(Im(q))<=pi*epsilon/3. A transverse-dependent bounded analytic family is proved to satisfy the full Fourier shift, and the identity extends from the established Gaussian graph core to the entire natural half-exponential graph by closedness. The abstract family hypotheses are all proved for the actual localized observable. The physical representative is derived through the existing weighted coordinate unitary on all L2 states. For abs(hbar)<=2*pi*epsilon/3, the localized observable preserves the full natural graph of the longitudinal half exponential, the ordered exponential, and the linear and quadratic physical-field matter factors. In each exponential or matter graph, the transformed output is the explicit imaginary-shift multiplier applied to the original output, with norm at most exp(v^2*hbar^2/(8*delta*epsilon^2))*norm(output). Multiplication graphs for clock half, inverse half, and physical fields are also preserved. These natural-graph theorems require no matter coupling positivity, no propagation premise, and no nonzero-hbar premise. Along every positive delta sequence tending to zero, the localized input operator converges strongly on each fixed physical L2 state to the bare neutral-position phase. This is not uniform convergence on varying states or convergence in graph norm. The shifted-output bound is not uniform as delta tends to zero at fixed nonzero hbar and v. The cutoff does not yet have a proved action on the charge-averaged full energy form; localized kinetic correction bounds and a full normalized Hamiltonian response remain unproved. No full neutral-position derivative, position tightness, negative-clock-momentum control, full twelve-dimensional dynamics, classical force closure or uniqueness is asserted. Clock-defect removal, fixed-hbar recovery, floor removal, GR/QFT/Standard Model identification and empirical validation remain unproved. No physical operator or preceding model is changed, and no necessity of a model change is established. All 1046 predecessor source/script hashes are preserved. The TOE remains unproved.')


    target = root/'data/physical_clock_floor_neutral_position_localized_audit.json'
    target.write_text(json.dumps(report, indent=2)+'\n')
    print('Root import passed;', report['audited_declaration_count'],
          'audited declarations;', len(hashes), 'verified source hashes.', flush=True)
    print(target, flush=True)


if __name__ == '__main__':
    main()
