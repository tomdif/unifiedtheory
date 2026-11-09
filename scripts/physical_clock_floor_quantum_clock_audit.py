#!/usr/bin/env python3
"""Recompile and audit the actual quantum clock commutator and its evolving error.

Run through the repository toolchain, using its previously verified dependencies:
  lake env python3 scripts/physical_clock_floor_quantum_clock_audit.py --overlay PATH

This does not invoke lake build. It rebuilds all seven new modules in dependency
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
    ('KFCausalClockFloorDefectTransportScalar', 7),
    ('KFCausalQuadraticRemainderDerivative', 1),
    ('KFCausalClockFloorDefectTransportOperator', 8),
    ('KFCausalClockFloorClockOperator', 8),
    ('KFCausalClockFloorDefectMomentum', 6),
    ('KFCausalClockFloorQuantumClockCommutator', 9),
    ('KFCausalClockFloorQuantumClockEvolution', 3),
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
    logs = overlay/'physical-clock-floor-quantum-clock-audit'
    logs.mkdir(exist_ok=True)
    (overlay/'UnifiedTheory/Audit').mkdir(parents=True, exist_ok=True)
    previous_path = root/'data/physical_clock_floor_monotonic_defect_audit.json'
    previous_hash = sha256(previous_path)
    previous = json.loads(previous_path.read_text())
    sources = list(previous['source_sha256'])
    sources += ['UnifiedTheory/Audit/'+name+'.lean' for name, _ in MODULES]
    sources += ['scripts/physical_clock_floor_quantum_clock_audit.py']
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
        scope='For the optional equal-mobility clock-floor model at epsilon>0, constructed the maximal positive self-adjoint clock C=exp(s)+epsilon on the physical L2 space and proved CD=epsilon*I for the actual bounded D=epsilon/C, including Dom(C)=range(D) and dense range of D. Proved a uniform quadratic remainder for D along the complete longitudinal transport and lifted it to operator-norm differentiability of the actual transported multiplier. This proves that D preserves the full actual longitudinal momentum domain, with L*D*f=D*L*f+(i*hbar/epsilon)*D^2*(I-D)*f. No preservation premise is added. Proved that D(Dom(L)) is dense and is exactly the domain of the composition L*C; both unbounded products L*C and C*L are defined there. On the full common composition domain the actual commutator is [L,C]*f=-i*hbar*(I-D)*f. Its bounded extension is unique. For every nonzero hbar, the normalized bounded extension N=(i/hbar)*[L,C]_ext equals I-D exactly, so its canonical error I-N is the existing physical defect D. Exact canonical equality on a nonzero state is impossible at fixed positive floor. These commutator results require no strip restriction on hbar. Under the additional established condition abs(hbar)<=2*pi*epsilon/3, the actual charge-averaged nonautonomous unitary evolution satisfies norm(U(s,t)*f-N*U(s,t)*f)<=norm(f-N*f) for every L2 state and t>=s, and the error norm is nonincreasing as final time increases. For every positive tolerance and initial time, there is a normalized zero-charge state in the actual initial averaged energy domain whose evolved normalized commutator error stays below that tolerance at every future time. The evolution assertions use the unique bounded extension on all L2; preservation of the unbounded common composition domain by Hamiltonian evolution is not proved or assumed. Strict error decay, fixed-state convergence to zero, uniform energy cost and a controlled quantum-to-classical limit are not claimed. No model, factor ordering, or prior operator was changed. Controlled quantum-to-classical and finite-capacity limits, Jordan reconstruction, GR/QFT/Standard Model recovery and empirical identification remain open. All 536 predecessor source hashes are preserved. The TOE remains unproved.')


    target = root/'data/physical_clock_floor_quantum_clock_audit.json'
    target.write_text(json.dumps(report, indent=2)+'\n')
    print('Root import passed;', report['audited_declaration_count'],
          'audited declarations;', len(hashes), 'verified source hashes.', flush=True)
    print(target, flush=True)


if __name__ == '__main__':
    main()
