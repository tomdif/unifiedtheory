#!/usr/bin/env python3
"""Audit the actual ordered vacuum longitudinal-momentum core and response form.

Run with the repository toolchain and verified dependency overlay:
  lake env python3 scripts/physical_clock_floor_vacuum_momentum_form_audit.py --overlay PATH

Sequential direct Lean checks rebuild ten new modules, audit their axioms,
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


MODULES = [('KFCausalClockFloorInverseHalfTransportScalar', 8), ('KFCausalClockFloorInverseHalfTransportOperator', 9), ('KFCausalClockFloorInverseHalfMomentum', 4), ('KFCausalClockFloorExponentialMomentumGraph', 3), ('KFCausalClockFloorOrderedMomentumCommutator', 6), ('KFCausalClockFloorShiftedMomentumSign', 6), ('KFCausalClockFloorVacuumMomentumResponse', 10), ('KFCausalClockFloorExponentialMomentumCore', 6), ('KFCausalClockFloorOrderedMomentumCore', 6), ('KFCausalClockFloorVacuumMomentumForm', 6)]


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
    logs = overlay/'physical-clock-floor-vacuum-momentum-form-audit'
    logs.mkdir(exist_ok=True)
    (overlay/'UnifiedTheory/Audit').mkdir(parents=True, exist_ok=True)
    previous_path = root/'data/physical_clock_floor_clock_production_dissipation_audit.json'
    previous_hash = sha256(previous_path)
    previous = json.loads(previous_path.read_text())
    sources = list(previous['source_sha256'])
    sources += ['UnifiedTheory/Audit/'+name+'.lean' for name, _ in MODULES]
    sources += ['scripts/physical_clock_floor_vacuum_momentum_form_audit.py']
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
        scope='For the existing clock-floor model with epsilon>0, hbar nonzero and abs(hbar)<=2*pi*epsilon/3, this audit proves an actual longitudinal-momentum composition core and positive weak momentum response for the ordered vacuum factor T=exp(L/2)*C^(-1/2), where C=exp(x)+epsilon and L is the coupled longitudinal momentum. The model and Hamiltonian are unchanged. Uniform scalar transport differentiation of C^(-1/2), with an explicit quadratic remainder, is lifted to operator-norm differentiation of the actual physical L2 multiplier. It follows that R=C^(-1/2) preserves the full maximal L domain and [L,R]f=(i*hbar/(2*epsilon))*D*(1-D)*R*f, with D=epsilon/C and correction norm at most abs(hbar)/(2*epsilon)*norm(R*f). Fourier identities prove exact interchange of L and exp(a*L), including equality of their composition domains on the common input domain. For T, within Dom(L) intersect Dom(T), L*f belongs to Dom(T) if and only if T*f belongs to Dom(L). Both compositions are constructed from either one, and [L,T]f=(i*hbar/(2*epsilon))*Z*(1-Z)*T*f, where Z is the actual shifted-defect multiplier. The shifted defect satisfies norm(Z(x))^2<Re Z(x). Consequently Re(Z(x)*(1-Z(x))) is strictly positive and at most 1/2, and norm(Z(x)*(1-Z(x)))<=1/2. The operator commutator therefore has the sharper bound abs(hbar)/(4*epsilon)*norm(T*f). The derived quadratic response q(f)=Re inner(T*f,Z*(1-Z)*T*f)/epsilon is continuous in the T graph norm, nonnegative, at most norm(T*f)^2/(2*epsilon), and strictly positive for each nonzero f in Dom(T). On the actual common-composition domain it equals (-2/hbar)*Im inner(T*f,T*L*f), the longitudinal vacuum weak momentum response. A common-composition graph core is constructed rather than assumed: Gaussian packets and their exponential outputs have both signs of exponential moments and hence belong to the maximal L domain; they give a core for exp(L/2) with input and output in Dom(L). Defect multiplication preserves this regular graph. The inverse-half-clock graph map, its exact square R^2=D/epsilon, and strong real/shifted defect-residual decay transfer that core to the actual ordered factor T. Every pair (f,T*f) is approximated in both components by pairs where both L*T and T*L are defined. The actual weak rates on this core converge to q(f), which is the unique continuous extension on the T graph. This is a graph-core and quadratic-form result for the longitudinal vacuum factor. It does not prove a graph core for L or the full Hamiltonian, domain invariance under the Hamiltonian evolution, a full charge-averaged momentum evolution law, canonical clock-momentum control, or long-time quantum clock-defect recovery. L is not the canonical clock momentum and cannot simply be assumed charge invariant. Matter and kinetic momentum responses, the necessary averaging estimates, full joint phase-space dynamics, regulator removal, GR/QFT/Standard Model identification and empirical validation remain open. All 1246 predecessor source/script hashes are preserved. The TOE remains unproved.')


    target = root/'data/physical_clock_floor_vacuum_momentum_form_audit.json'
    target.write_text(json.dumps(report, indent=2)+'\n')
    print('Root import passed;', report['audited_declaration_count'],
          'audited declarations;', len(hashes), 'verified source hashes.', flush=True)
    print(target, flush=True)


if __name__ == '__main__':
    main()
