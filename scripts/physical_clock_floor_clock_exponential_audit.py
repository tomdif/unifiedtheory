#!/usr/bin/env python3
"""Audit actual clock/exponential compositions and the controlled first-order response.

Run with the repository toolchain and verified dependency overlay:
  lake env python3 scripts/physical_clock_floor_clock_exponential_audit.py --overlay PATH

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


MODULES = [('KFCausalClockFloorClockShiftDifference', 8), ('KFCausalClockFloorClockShiftCommutator', 5), ('KFCausalClockFloorClockExponentialCommutator', 3), ('KFCausalClockFloorClockEnergyCommutator', 7), ('KFCausalClockFloorClockShiftTaylor', 5), ('KFCausalClockFloorClockExponentialResponse', 6)]


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
    logs = overlay/'physical-clock-floor-clock-exponential-audit'
    logs.mkdir(exist_ok=True)
    (overlay/'UnifiedTheory/Audit').mkdir(parents=True, exist_ok=True)
    previous_path = root/'data/physical_clock_floor_momentum_commutator_audit.json'
    previous_hash = sha256(previous_path)
    previous = json.loads(previous_path.read_text())
    sources = list(previous['source_sha256'])
    sources += ['UnifiedTheory/Audit/'+name+'.lean' for name, _ in MODULES]
    sources += ['scripts/physical_clock_floor_clock_exponential_audit.py']
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
        scope='For the existing equal-mobility clock-floor model, epsilon>0 and abs(hbar)<=2*pi*epsilon/3, the actual imaginary half-exponential shift of C=exp(s)+epsilon defines a bounded physical multiplier Delta with norm(Delta f)<=abs(hbar)*norm(f). The shifted defect B obeys the actual clock graph identity C(Bg)=epsilon*g+Delta(Bg). The inverse relation D=epsilon/C and the previously proved full-domain identity E D=B E construct both actual unbounded compositions on Dom(E C)=D(Dom E), a dense domain for E=exp(L/2). On that domain [C,E]f=Delta(Ef), with norm([C,E]f)<=abs(hbar)*norm(Ef). The argument also constructs a shared dense domain D(commonEnergyDomain), exactly the states with an actual clock output Cf in all eight natural energy-factor domains. Every factor T_i then has both compositions T_i(Cf) and C(T_i f). The clock-half and four kinetic factors commute with C there; both physical-field matter factors and the ordered exponential have the same Delta correction. Arbitrary complex weights give the corresponding L2 joint-output bound by abs(hbar) times the weighted original output norm. An analytic derivative and convex-interval estimate prove the pointwise expansion Delta=(i*hbar/2)*rho+R, rho=exp(s)/C, with abs(R)<=hbar^2*D^2/epsilon. The actual bounded remainder operator satisfies norm(Rg)<=hbar^2/epsilon*norm(D^2 g) on all physical L2 states. This yields a first-order response bound for actual C/E compositions and for every energy factor on the stated common composition domain. The ordered factor T=E C^(-1/2) has its own dense natural Dom(T C)=D(Dom T), where both compositions and their first-order remainder bound are constructed. No smooth representative, compact-state exponential core, or desired composition graph is supplied as an assumption to the domain-construction capstones. The scalar and physical-operator statements include hbar=0. Density here is Hilbert-space density, not graph-norm density of these composition domains. Equality of the reverse composition domains, extension to the completed or charge-averaged Hamiltonian, the canonical physical clock-momentum/exponential commutator, and evolved-state estimates are not asserted. The hbar-squared remainder does not eliminate the physical floor defect epsilon/C. Canonical clock-momentum tightness for the prescribed evolution, negative evolved longitudinal tails, continuous joint eleven-coordinate dynamics, classical force identification, full phase-space transport, regulator removal, GR/QFT/Standard Model identification and empirical validation remain open. No model or Hamiltonian changed. All 1199 predecessor source/script hashes are preserved. The TOE remains unproved.')


    target = root/'data/physical_clock_floor_clock_exponential_audit.json'
    target.write_text(json.dumps(report, indent=2)+'\n')
    print('Root import passed;', report['audited_declaration_count'],
          'audited declarations;', len(hashes), 'verified source hashes.', flush=True)
    print(target, flush=True)


if __name__ == '__main__':
    main()
