#!/usr/bin/env python3
"""Audit the physical longitudinal differential graph and canonical clock reconstruction.

Run with the repository toolchain and verified dependency overlay:
  lake env python3 scripts/physical_clock_floor_canonical_momentum_bridge_audit.py --overlay PATH

Sequential direct Lean checks rebuild five new modules, audit their axioms,
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


MODULES = [('KFCausalClockFloorTransportDerivative', 8), ('KFCausalClockFloorDifferentialMomentum', 9), ('KFCausalCanonicalClockDerivative', 5), ('KFCausalClockFloorCanonicalReconstruction', 11), ('KFCausalClockFloorCompactMomentumReconstruction', 4)]


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
    logs = overlay/'physical-clock-floor-canonical-momentum-bridge-audit'
    logs.mkdir(exist_ok=True)
    (overlay/'UnifiedTheory/Audit').mkdir(parents=True, exist_ok=True)
    previous_path = root/'data/physical_clock_floor_initial_longitudinal_control_audit.json'
    previous_hash = sha256(previous_path)
    previous = json.loads(previous_path.read_text())
    sources = list(previous['source_sha256'])
    sources += ['UnifiedTheory/Audit/'+name+'.lean' for name, _ in MODULES]
    sources += ['scripts/physical_clock_floor_canonical_momentum_bridge_audit.py']
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
        scope='The actual equal-mobility clock-floor transport has the derived physical differential expression A(f)=b*(partial_s f+v dot grad_x f)+(b-exp(s)/(2*C^2))*f, where C=exp(s)+epsilon and b=1/C. For every positive epsilon and nonzero hbar, a differentiable physical L2 function whose A(f) is L2 belongs to the existing maximal longitudinal momentum graph with output -i*hbar*A(f). This is proved using the full coordinate unitary, the L2 directional Fourier derivative theorem, and the actual maximal Fourier graph. Every C1 compactly supported physical test satisfies these hypotheses. The existing canonical clock translation generator is identified with the physical Fourier multiplier 2*pi*hbar*k_clock; its derivative graph is derived for differentiable L2 functions with L2 clock derivative. Canonical reconstruction is partial_s f=C*A(f)-(v dot grad_x f+f)+(exp(s)/C)*f/2. If C*A(f) and the shear derivative v dot grad_x f+f are L2, both actual momentum graphs are supplied and canonical output is bounded by the norm of the clock-weighted longitudinal output plus the shear momentum norm plus abs(hbar)/2 times the state norm. The correction estimate is derived from 0<exp(s)/C<1. For every C1 compactly supported state, all integrability hypotheses are discharged and the theorem constructs actual longitudinal and canonical outputs l,p, an L2 vector w=C*l, the shear output d, and correction r=-i*hbar*exp(s)/(2*C)*f with p=w-d+r and the stated norm bound. No operator or Hamiltonian is replaced. This is a common smooth domain result, not graph-core density, a Hamiltonian exponential-form core theorem, an evolved-state regularity theorem, or a bound for the actual quantum trajectory. Control and propagation of the required weighted and shear outputs, negative evolved longitudinal tails, canonical clock-momentum tightness, continuous joint eleven-coordinate dynamics, classical force identification, full phase-space transport, quantum clock-defect recovery, regulator removal, GR/QFT/Standard Model identification and empirical validation remain open. All 1182 predecessor source/script hashes are preserved. The TOE remains unproved.')


    target = root/'data/physical_clock_floor_canonical_momentum_bridge_audit.json'
    target.write_text(json.dumps(report, indent=2)+'\n')
    print('Root import passed;', report['audited_declaration_count'],
          'audited declarations;', len(hashes), 'verified source hashes.', flush=True)
    print(target, flush=True)


if __name__ == '__main__':
    main()
