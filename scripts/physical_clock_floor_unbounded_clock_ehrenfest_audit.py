#!/usr/bin/env python3
"""Audit the actual unbounded-clock Ehrenfest law from bounded resolvents.

Run with the repository toolchain and verified dependency overlay:
  lake env python3 scripts/physical_clock_floor_unbounded_clock_ehrenfest_audit.py --overlay PATH

Sequential direct Lean checks rebuild eleven new modules, audit their axioms,
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


MODULES = [('KFCausalContractiveResidualResolvent', 7), ('KFCausalClosedGraphDiagonalAction', 2), ('KFCausalResidualResolventApproximation', 8), ('KFCausalClockFloorReferenceClockCore', 10), ('KFCausalClockFloorClockResolvent', 10), ('KFCausalClockFloorAveragedClockResolvent', 13), ('KFCausalClockFloorClockMoment', 6), ('KFCausalAveragedOutputTimeContinuity', 2), ('KFCausalClockFloorClockReferenceRate', 11), ('KFCausalClockFloorClockRegularizedEhrenfest', 3), ('KFCausalClockFloorUnboundedClockEhrenfest', 13)]


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
    logs = overlay/'physical-clock-floor-unbounded-clock-ehrenfest-audit'
    logs.mkdir(exist_ok=True)
    (overlay/'UnifiedTheory/Audit').mkdir(parents=True, exist_ok=True)
    previous_path = root/'data/physical_clock_floor_averaged_clock_form_audit.json'
    previous_hash = sha256(previous_path)
    previous = json.loads(previous_path.read_text())
    sources = list(previous['source_sha256'])
    sources += ['UnifiedTheory/Audit/'+name+'.lean' for name, _ in MODULES]
    sources += ['scripts/physical_clock_floor_unbounded_clock_ehrenfest_audit.py']
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
        scope='For the existing clock-floor model with epsilon>0, hbar nonzero and abs(hbar)<=2*pi*epsilon/3, this audit proves the exact evolution of the unbounded positive clock expectation along the actual charge-averaged unitary propagator for every initial vector in the completed reference form domain. The physical clock is C=exp(s)+epsilon and D=epsilon/C. A generic Banach-space resolvent construction inverts F+bI whenever I-F is contractive, and proves its inverse identities, norm bound and intertwining. If F has dense range, S_b=F(F+bI)^(-1) converges strongly to I as b tends to zero through positive values; its norm is at most 2. The actual reference form defect is constructed from graph preservation and is proved to have dense range. Its resolvents intertwine the physical and averaged-output resolvents, preserve the form domain, and commute with the actual time transport. The bounded physical clock approximants C_b=epsilon(D+bI)^(-1) have the real positive multiplier C/(1+(b/epsilon)C), are symmetric, satisfy C(S_b f)=C_b f, and their expectations converge by dominated convergence to the finite physical moment integral of C times abs(f)^2 on the half-clock domain. On the full completed form domain, the exact C_b commutator equals the continuous clock-response form evaluated on S_b u and S_b v. This identity follows from the actual clock graph and cancellation of the real resolvent cross terms. The approximate rates are bounded by 8 times the actual instantaneous energy, uniformly in b, and converge to the clock-response rate bounded by 2 times that energy. Joint time/state continuity is proved for the averaged energy output, response rate and energy. The weak form equation and constructed bounded form lifts give the exact bounded C_b expectation derivative and integral balance along the actual propagator. With the explicit positive sequence b_n=1/(n+1), dominated convergence removes the cutoff on every finite real time interval. The resulting physical clock moment is finite and continuously differentiable at every real time; its exact integral balance and both complex and real derivative statements are proved. The clock rate is also bounded by 2*exp(2*abs(t-s))*E_s(w). No clock-operator-domain premise, Hamiltonian-domain invariance, assumed core or assumed evolution identity is used. These are expectation/form results; neither strong operator commutators nor Hamiltonian-domain invariance are asserted. No quantum long-time clock-defect decay, canonical clock-momentum tightness, closed joint eleven-coordinate dynamics, full phase-space transport, regulator removal, GR/QFT/Standard Model identification or empirical validation is proved. The model and Hamiltonian are unchanged. All 1222 predecessor source/script hashes are preserved. The TOE remains unproved.')


    target = root/'data/physical_clock_floor_unbounded_clock_ehrenfest_audit.json'
    target.write_text(json.dumps(report, indent=2)+'\n')
    print('Root import passed;', report['audited_declaration_count'],
          'audited declarations;', len(hashes), 'verified source hashes.', flush=True)
    print(target, flush=True)


if __name__ == '__main__':
    main()
