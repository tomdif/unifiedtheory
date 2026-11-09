#!/usr/bin/env python3
"""Recompile and audit the Hamiltonian clock-velocity comparison and actual expectation control.

Run through the repository toolchain, using its previously verified dependencies:
  lake env python3 scripts/physical_clock_floor_velocity_audit.py --overlay PATH

This does not invoke lake build. It rebuilds all ten new modules in dependency
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
    ('KFCausalClockFloorComplexDefectDerivative', 4),
    ('KFCausalClockFloorQuantumVelocityScalar', 5),
    ('KFCausalMultiplierVelocityPairing', 2),
    ('KFCausalClockFloorQuantumVelocityPairing', 5),
    ('KFCausalClockFloorQuantumVelocityOutput', 7),
    ('KFCausalClockFloorQuantumVelocityClassical', 2),
    ('KFCausalClockFloorHamiltonianVelocity', 5),
    ('KFCausalYosidaObservableVelocity', 5),
    ('KFCausalClockFloorEhrenfestVelocity', 5),
    ('KFCausalClockFloorDefectExpectationControl', 3),
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
    logs = overlay/'physical-clock-floor-velocity-audit'
    logs.mkdir(exist_ok=True)
    (overlay/'UnifiedTheory/Audit').mkdir(parents=True, exist_ok=True)
    previous_path = root/'data/physical_clock_floor_quantum_clock_audit.json'
    previous_hash = sha256(previous_path)
    previous = json.loads(previous_path.read_text())
    sources = list(previous['source_sha256'])
    sources += ['UnifiedTheory/Audit/'+name+'.lean' for name, _ in MODULES]
    sources += ['scripts/physical_clock_floor_velocity_audit.py']
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
        scope='For the optional equal-mobility clock-floor model, proved the derivative of the actual analytic clock inverse and complex defect on the established strip. Derived a uniform quadratic vertical-shift remainder with cubic real-defect weight. For epsilon>0, hbar!=0 and abs(hbar)<=2*pi*epsilon/3, the actual coefficient v(q)=(-2/hbar)*Im(complexDefect(epsilon,q-i*hbar/2)) differs from P(d)=-d^2*(1-d)/epsilon by at most 20*abs(hbar)*d^3/epsilon^2, uniformly in q. Identified P(d)*W/C with the canonical defect velocity of the revised homogeneous classical symbol H=C/2+(E/2+W)/C, W=kappa*exp(L), holding E and kappa fixed in clock partial derivatives. Lifted the scalar error to the physical L2 multipliers, retaining a weighted bound by 20*abs(hbar)/epsilon^2*Re(inner(D*g,D^2*g)). Summed all eight actual energy factors and integrated the actual charge circle. The full averaged Hamiltonian form commutator differs from the classical-coefficient pairing of its own quantum energy outputs by at most 20*abs(hbar)/epsilon^2 times its energy expectation, on its full operator domain. No preservation of that operator domain by D is assumed. The classical output action is zero on the first five factors and P(D) on the three matter/exponential factors. This is an actual coefficient comparison within the quantum energy form, not a classical phase-space-density or trajectory identification. Identification of the constructed positive form with the stated ordered seed energy retains the existing nonnegative coefficient assumptions. Proved an exact generic resolvent observable pairing and expectation derivative, and instantiated them on the actual bounded Yosida dynamics. The exact derivative uses the smoothed operator-domain state a*(H+a)^(-1)*psi. Its classical-coefficient error for initial form energy E_s is at most (20*abs(hbar)/epsilon^2)*exp(2*abs(t-s))*E_s, independently of cutoff. Also proved a rate magnitude bound with coefficient B=20*abs(hbar)/epsilon^2+1/epsilon. Passed the resulting expectation increment bound through the previously verified whole-cutoff strong limit: actual unbounded evolution satisfies abs(expect_D(U(s,t)*f)-expect_D(U(s,r)*f))<=B*exp(2*T)*E_s*abs(t-r) whenever abs(r-s)<=T and abs(t-s)<=T. Thus its defect expectation is locally Lipschitz for every initial energy-form state. The exact derivative identity here is proved for bounded approximants; passing the force itself to the unbounded limit, controlled evolving classical packets and phase-space concentration remain open. The small-hbar coefficient error is energy-weighted; a joint small-floor limit needs that displayed energy-weighted hbar/epsilon^2 factor to vanish, which does not follow from the strip bound alone. No model, factor ordering or prior operator changed. Finite-capacity and Jordan reconstruction limits, GR/QFT/Standard Model recovery and empirical identification remain open. All 544 predecessor source hashes are preserved. The TOE remains unproved.')


    target = root/'data/physical_clock_floor_velocity_audit.json'
    target.write_text(json.dumps(report, indent=2)+'\n')
    print('Root import passed;', report['audited_declaration_count'],
          'audited declarations;', len(hashes), 'verified source hashes.', flush=True)
    print(target, flush=True)


if __name__ == '__main__':
    main()
