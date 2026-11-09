#!/usr/bin/env python3
"""Recompile and audit the analytic clock-defect multipliers and physical exponential commutators.

Run through the repository toolchain, using its previously verified dependencies:
  lake env python3 scripts/physical_clock_floor_defect_commutator_audit.py --overlay PATH

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


MODULES = [
    ('KFCausalClockFloorComplexDefect', 8),
    ('KFCausalClockFloorDefectShift', 6),
    ('KFCausalClockFloorAnalyticMultiplier', 7),
    ('KFCausalClockFloorMultiplierGraph', 7),
    ('KFCausalClockFloorDefectCoordinates', 2),
    ('KFCausalClockFloorDefectPowerGraph', 6),
    ('KFCausalClockFloorDefectCommutator', 3),
    ('KFCausalClockFloorDefectForm', 6),
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
    logs = overlay/'physical-clock-floor-defect-commutator-audit'
    logs.mkdir(exist_ok=True)
    (overlay/'UnifiedTheory/Audit').mkdir(parents=True, exist_ok=True)
    previous_path = root/'data/physical_clock_floor_large_clock_audit.json'
    previous_hash = sha256(previous_path)
    previous = json.loads(previous_path.read_text())
    sources = list(previous['source_sha256'])
    sources += ['UnifiedTheory/Audit/'+name+'.lean' for name, _ in MODULES]
    sources += ['scripts/physical_clock_floor_defect_commutator_audit.py']
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
        scope='For the optional equal-mobility clock-floor model at fixed epsilon>0, analytically continued the actual defect D=epsilon/(exp(s)+epsilon) through the already constructed complex clock inverse. On the third strip abs(Im q)<=pi*epsilon/3, the complex clock has norm at least half the real clock at Re q, and the complex defect has norm at most twice the real defect, hence at most two. The vertical defect difference is bounded by (4*abs(Im q)/epsilon)*d^2; its squared difference and squared imaginary part are bounded by (12*abs(Im q)/epsilon)*d^3. At the actual half-exponential shift q-i*hbar/2 these constants become 2*abs(hbar)/epsilon and 6*abs(hbar)/epsilon. A generic bounded analytic clock multiplier preserves the joint L1/L2 coherent strip estimates and the exact clock-fiber Fourier shift. The full six-dimensional Fourier identity, transported through the existing physical unitaries, proves an actual exp(L/2) graph pair without assuming operator-domain preservation. The previously constructed bounded physical defect multiplier is identified exactly in straightened Euclidean coordinates. For all finite defect powers of the constructed sheared coherent states, the initial state, its defect multiple and its squared-defect multiple belong to the actual exp(L/2) domain. Their outputs are the explicit analytically shifted profiles. Under a>0, alpha>0, beta>0, 32*beta<=alpha, arbitrary real clock modulation and complex transverse sources, and abs(hbar)<=2*pi*epsilon/3, A=exp(L/2) satisfies norm(A D f-D A f)<=(2*abs(hbar)/epsilon)*norm(D^2 A f), norm(A D f)<=2*norm(D A f), and norm(A D^2 f-D^2 A f)<=(6*abs(hbar)/epsilon)*norm(D^3 A f) on that family. The physical defect multiplier is symmetric on all L2, and the actual form pairing obeys abs(Im inner(A f,A D^2 f))<=(6*abs(hbar)/epsilon)*norm(A f)*norm(D^3 A f). These are fixed-floor continuum operator and form estimates for an explicitly constructed class, not an asserted graph core or a theorem for all energy-domain states. No preservation of that class by the full Hamiltonian evolution is proved. No estimate identifies initial small defect with small weighted defect of the exponential output. The previous density-constructed small-defect zero-charge family is not identified with these analytic packets. Extension to the closed ordered interaction and averaged Hamiltonian form, quantitative large-clock packet bounds, and control on a common time interval remain open. No canonical clock-position/momentum commutator identity, quantum-to-classical evolution convergence, finite-capacity limit, GR/QFT/Standard Model recovery or empirical identification is claimed. All 492 predecessor source hashes and the older model are preserved; the TOE remains unproved.')


    target = root/'data/physical_clock_floor_defect_commutator_audit.json'
    target.write_text(json.dumps(report, indent=2)+'\n')
    print('Root import passed;', report['audited_declaration_count'],
          'audited declarations;', len(hashes), 'verified source hashes.', flush=True)
    print(target, flush=True)


if __name__ == '__main__':
    main()
