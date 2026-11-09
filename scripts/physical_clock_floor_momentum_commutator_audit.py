#!/usr/bin/env python3
"""Audit the actual canonical/longitudinal momentum commutator and its relative bound.

Run with the repository toolchain and verified dependency overlay:
  lake env python3 scripts/physical_clock_floor_momentum_commutator_audit.py --overlay PATH

Sequential direct Lean checks rebuild four new modules, audit their axioms,
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


MODULES = [('KFCausalClockFloorMomentumCoefficients', 9), ('KFCausalClockFloorDifferentialCommutator', 6), ('KFCausalClockFloorMomentumResponse', 6), ('KFCausalClockFloorCompactMomentumCommutator', 3)]


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
    logs = overlay/'physical-clock-floor-momentum-commutator-audit'
    logs.mkdir(exist_ok=True)
    (overlay/'UnifiedTheory/Audit').mkdir(parents=True, exist_ok=True)
    previous_path = root/'data/physical_clock_floor_canonical_charge_audit.json'
    previous_hash = sha256(previous_path)
    previous = json.loads(previous_path.read_text())
    sources = list(previous['source_sha256'])
    sources += ['UnifiedTheory/Audit/'+name+'.lean' for name, _ in MODULES]
    sources += ['scripts/physical_clock_floor_momentum_commutator_audit.py']
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
        scope='For the existing equal-mobility clock-floor model with positive epsilon, the actual longitudinal differential expression A and the physical clock derivative satisfy [partial_s,A]f=-rho*A(f)-r*f on every C2 physical function, where rho=exp(s)/(exp(s)+epsilon) and r=b*rho*(1-rho)/2 with b=1/(exp(s)+epsilon). The proof differentiates the actual coefficients and vector field and cancels second derivatives using real Hessian symmetry. The scalar remainder is nonnegative and at most 1/(8*epsilon). Rho is represented on all physical L2 states by the bounded operator Q=id-D, where D is the existing clock-defect multiplier. The remainder is represented by M=(1/(2*epsilon))*D^2*Q and obeys norm(Mf)<=norm(f)/(8*epsilon), while Q is contractive. The existing full-domain defect graph theorem supplies response graph invariance: if (f,l) is in the actual maximal longitudinal graph then (Qf,Ql-2*i*hbar*Mf) is in that same graph. For every C2 compactly supported physical function, all L2 conditions and both actual momentum compositions are derived. The capstone constructs actual outputs l=Lf, p=Pf, pl=P(Lf), lp=L(Pf), and rl=L(Qf), and proves pl-lp=i*hbar*Ql+hbar^2*Mf=(i*hbar/2)*(Ql+rl). It also proves norm(pl-lp)<=abs(hbar)*norm(l)+hbar^2/(8*epsilon)*norm(f). Here P is the canonical physical clock translation generator and L is the existing equal-mobility longitudinal generator. No formal derivative or desired composition graph is assumed for the compact-state capstone. The commutator is proved on this actual C2 compact common composition domain; no graph-core density, extension of the P/L composition identity to all common maximal-domain vectors, longitudinal exponential-form commutator, or Hamiltonian evolution estimate is asserted. The bounded response and remainder operators and the response graph identity do hold on the stated full L2/maximal-L domains. Quantum clock-defect recovery is not implied by the hbar-squared commutator remainder. Canonical clock-momentum tightness for the prescribed evolution, negative evolved longitudinal tails, continuous joint eleven-coordinate dynamics, classical force identification, full phase-space transport, regulator removal, GR/QFT/Standard Model identification and empirical validation remain open. No model or Hamiltonian changed. All 1194 predecessor source/script hashes are preserved. The TOE remains unproved.')


    target = root/'data/physical_clock_floor_momentum_commutator_audit.json'
    target.write_text(json.dumps(report, indent=2)+'\n')
    print('Root import passed;', report['audited_declaration_count'],
          'audited declarations;', len(hashes), 'verified source hashes.', flush=True)
    print(target, flush=True)


if __name__ == '__main__':
    main()
