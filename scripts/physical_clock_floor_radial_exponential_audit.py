#!/usr/bin/env python3
"""Audit the actual radial test on the natural clock exponential graphs.

Run with the repository toolchain and verified dependency overlay:
  lake env python3 scripts/physical_clock_floor_radial_exponential_audit.py --overlay PATH

Sequential direct Lean checks rebuild eight new modules, audit their axioms,
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


MODULES = [('KFCausalL2FourierIsometry', 4), ('KFCausalFullFourierProduct', 6), ('KFCausalTransverseFourierClock', 9), ('KFCausalClockFloorTransverseFourierGraph', 5), ('KFCausalMixedStripExponentialGraph', 5), ('KFCausalMixedRadialStripFamily', 5), ('KFCausalNeutralPositionRadialExponential', 4), ('KFCausalNeutralPositionRadialOrdered', 4)]


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
    logs = overlay/'physical-clock-floor-radial-exponential-audit'
    logs.mkdir(exist_ok=True)
    (overlay/'UnifiedTheory/Audit').mkdir(parents=True, exist_ok=True)
    previous_path = root/'data/physical_clock_floor_mixed_radial_strip_audit.json'
    previous_hash = sha256(previous_path)
    previous = json.loads(previous_path.read_text())
    sources = list(previous['source_sha256'])
    sources += ['UnifiedTheory/Audit/'+name+'.lean' for name, _ in MODULES]
    sources += ['scripts/physical_clock_floor_radial_exponential_audit.py']
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
        scope='The actual L2 Fourier unitary is equivariant under real linear isometry equivalences, derived from the Fourier-integral identity and dense Schwartz states. On split Euclidean product coordinates, the actual full Fourier unitary equals the composition of the existing two partial Fourier unitaries; integral factorization and dense compact product tests prove the identity on all L2 states. These results identify the actual paired and charge-coordinate Fourier diagrams. The actual transverse partial Fourier unitary, returned to the six-dimensional Euclidean coordinates, commutes with the full Fourier unitary and preserves and reflects all measurable unbounded spectator multiplication relations, including arbitrary clock-only relations. Conjugating this transverse unitary by the original physical clock straightening proves preservation and reflection of the entire natural longitudinal exponential graph for every real hbar and exponent, at fixed positive epsilon. This closes the spectral-exponential compatibility obligation left by the preceding mixed-coordinate multiplier checkpoint. The existing bounded analytic strip-family theorem is transported through that proved graph equivalence. The actual radial multiplier is expressed in its required five-dimensional tail coordinates, with analyticity, joint real-slice continuity and strip bounds proved from its explicit formula. An actual bounded shifted operator is constructed by unitary conjugation of the existing physical strip multiplier. Its zero-shift value equals the original charge-compatible radial test P(hbar,delta,v) on every physical L2 vector. For positive epsilon and delta and abs(hbar)<=2*pi*epsilon/3, every pair (f,g) in the full natural longitudinal half-exponential graph is mapped to (P f,Q(-hbar/2) g) in that same graph. The shifted output norm is at most exp(v^2*hbar^2/(8*delta*epsilon^2))*norm(g). The inverse-clock-half graph is preserved by P using the preceding proved clock-half graph identity. Composition in the prescribed order proves the same P/Q graph rule and full natural-domain preservation for the actual orderedExponential, including its inverse-clock factor. Neither a smooth-state restriction nor a domain-preservation assumption for P is used. This is a natural unaveraged clock/ordered-exponential result. Preservation of the physical field and field-square graphs by the shifted OUTPUT Q, the two ordered field-matter rows, the full eight-factor joint closure, full charge-averaged form action, energy graph-norm cutoff removal, normalized full Hamiltonian response, neutral-position time variation and tightness remain unproved. Earlier field-domain results for the INPUT P do not supply the required shifted-output field identities. The output bound is not uniform as delta tends to zero at fixed nonzero hbar and v. Full twelve-dimensional dynamics, negative-clock-momentum control, classical force closure and uniqueness, clock-defect removal, fixed-hbar recovery, floor removal, GR/QFT/Standard Model identification and empirical validation remain open. The Hamiltonian and physical model are unchanged; no necessity of a model change is established. All 1095 predecessor source/script hashes are preserved. The TOE remains unproved.')


    target = root/'data/physical_clock_floor_radial_exponential_audit.json'
    target.write_text(json.dumps(report, indent=2)+'\n')
    print('Root import passed;', report['audited_declaration_count'],
          'audited declarations;', len(hashes), 'verified source hashes.', flush=True)
    print(target, flush=True)


if __name__ == '__main__':
    main()
